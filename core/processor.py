# -*- coding: utf-8 -*-
"""
Core de processamento geométrico — ANM Poligonal.

PREMISSAS INEGOCIÁVEIS:
  - Todo processamento e saída ocorre em SIRGAS 2000 geográfico (EPSG:4674).
  - Segmento N-S: ΔX = 0 bit-a-bit exato (longitude COPIADA do acumulador).
  - Segmento L-O: ΔY = 0 bit-a-bit exato (latitude COPIADA do acumulador).
  - Área calculada sobre o elipsoide GRS80, conforme o sistema ANM.
  - Coordenadas exibidas em graus°minutos'segundos"milésimos — ex.: -15°30'43"700.

FORMATOS DE EXPORTAÇÃO:
  TXT (leitura humana / conferência):
    Vértice  Latitude          Longitude
    1        -15°30'43"700     -47°57'27"555
    Separador: tabulação. Milésimos após aspas dupla, sem ponto ou vírgula.

  CSV (inserção em lote no REPEM/ANM):
    -;015;30;43;700;-;047;57;27;555
    Separador: ponto-e-vírgula. Sem cabeçalho. Todos os campos como texto.

Compatibilidade: QGIS 3.22+ e QGIS 4.0+ (Qt5/Qt6).
"""

import math
import warnings
from typing import List, Tuple, Optional

from qgis.core import (
    QgsGeometry,
    QgsPointXY,
    QgsField,
    QgsFields,
    QgsFeature,
    QgsWkbTypes,
    QgsCoordinateReferenceSystem,
    QgsCoordinateTransform,
    QgsDistanceArea,
    QgsProject,
    QgsVectorLayer,
    QgsVectorFileWriter,
)
from qgis.PyQt.QtCore import QVariant

from ..utils.compat import (
    WKB_Polygon,
    WKB_MultiPolygon,
    WKB_GeometryCollection,
    wkb_flatType,
    wkb_displayString,
    VFW_NoError,
)


# ---------------------------------------------------------------------------
# Constantes globais
# ---------------------------------------------------------------------------

# SRC de saída obrigatório: SIRGAS 2000 geográfico
CRS_ANM = QgsCoordinateReferenceSystem('EPSG:4674')

# Tolerância para classificar um segmento como estritamente N-S ou L-O.
# Abaixo desse delta angular (em graus), a variação é tratada como zero.
EPS_ORTHO = 1e-10


# ---------------------------------------------------------------------------
# Alias de tipo
# ---------------------------------------------------------------------------

# Ponto como (longitude, latitude) em graus decimais — ordem GIS padrão (x, y)
Point = Tuple[float, float]


# ---------------------------------------------------------------------------
# Conversão decimal → formato DMS exibição (TXT)
# ---------------------------------------------------------------------------

def decimal_to_dms_anm(degrees: float) -> str:
    """
    Converte graus decimais para a string de exibição no formato ANM:
      -15°30'43"700

    Os milésimos do segundo ficam após as aspas duplas, sem ponto ou vírgula.
    Sinal negativo prefixado; valores positivos não levam sinal.

    Exemplos:
      -15.512139° → -15°30'43"700
      -47.957654° → -47°57'27"555
    """
    neg = degrees < 0
    d = abs(degrees)

    deg_int    = int(d)
    remainder  = (d - deg_int) * 60
    min_int    = int(remainder)
    sec_total  = (remainder - min_int) * 60
    sec_int    = int(sec_total)
    millesimos = round((sec_total - sec_int) * 1000)

    # Carry por arredondamento: 999.5 → 1000 → propaga para segundos, minutos, graus
    if millesimos >= 1000:
        millesimos = 0
        sec_int += 1
    if sec_int >= 60:
        sec_int = 0
        min_int += 1
    if min_int >= 60:
        min_int = 0
        deg_int += 1

    sign = '-' if neg else ''
    return f'{sign}{deg_int:d}\xb0{min_int:02d}\'{sec_int:02d}"{millesimos:03d}'


# ---------------------------------------------------------------------------
# Decomposição decimal → componentes DMS independentes (CSV / REPEM)
# ---------------------------------------------------------------------------

def decimal_to_dms_components(degrees: float):
    """
    Decompõe graus decimais em cinco strings independentes para montagem
    do CSV de inserção em lote no REPEM:

      (sinal, graus, minutos, segundos, milésimos)

    Formatação obrigatória pelo sistema ANM:
      sinal     — '-' ou '+'  (coluna independente, nunca concatenado)
      graus     — 3 dígitos   ex.: '015', '047', '018'
      minutos   — 2 dígitos   ex.: '05', '30'
      segundos  — 2 dígitos   ex.: '03', '43'
      milésimos — 3 dígitos   ex.: '700', '421', '000'

    Todos os retornos são str para preservar zeros à esquerda, inclusive
    ao abrir o arquivo no Excel com configuração PT-BR.

    O carry de arredondamento é idêntico ao de decimal_to_dms_anm, garantindo
    que TXT e CSV mostrem exatamente o mesmo valor para cada vértice.
    """
    neg = degrees < 0
    d = abs(degrees)

    deg_int    = int(d)
    remainder  = (d - deg_int) * 60
    min_int    = int(remainder)
    sec_total  = (remainder - min_int) * 60
    sec_int    = int(sec_total)
    millesimos = round((sec_total - sec_int) * 1000)

    if millesimos >= 1000:
        millesimos = 0
        sec_int += 1
    if sec_int >= 60:
        sec_int = 0
        min_int += 1
    if min_int >= 60:
        min_int = 0
        deg_int += 1

    sinal = '-' if neg else '+'
    return (
        sinal,
        str(deg_int).zfill(3),
        str(min_int).zfill(2),
        str(sec_int).zfill(2),
        str(millesimos).zfill(3),
    )


# ---------------------------------------------------------------------------
# Área geodésica em EPSG:4674
# ---------------------------------------------------------------------------

def area_geodesica_ha(geom: QgsGeometry) -> float:
    """
    Calcula a área geodésica em hectares usando QgsDistanceArea com o
    elipsoide GRS80 — o mesmo que o sistema ANM usa para validação interna.

    A geometria deve estar em EPSG:4674. Retorna -1.0 em caso de falha.
    """
    try:
        da = QgsDistanceArea()
        da.setSourceCrs(CRS_ANM, QgsProject.instance().transformContext())
        da.setEllipsoid('GRS80')
        area_m2 = da.measureArea(geom)
        return round(area_m2 / 10_000.0, 4)
    except Exception:
        return -1.0


# ---------------------------------------------------------------------------
# Normalização de geometria
# ---------------------------------------------------------------------------

def _force_single_polygon(geom: QgsGeometry, context: str = '') -> QgsGeometry:
    """
    Garante que a geometria seja um Polygon simples.

    MultiPolygon ou GeometryCollection são decompostos e retorna-se o maior
    componente por área plana. Emite warning se houver mais de um componente,
    pois isso geralmente indica auto-interseções no esboço de entrada.

    makeValid() às vezes promove Polygon → MultiPolygon; essa função é chamada
    após cada makeValid() para manter o tipo correto em toda a cadeia.
    """
    wkb_type = wkb_flatType(geom.wkbType())

    if wkb_type == WKB_Polygon:
        return geom

    parts: List[QgsGeometry] = []

    if wkb_type == WKB_MultiPolygon:
        for ring_list in geom.asMultiPolygon():
            parts.append(QgsGeometry.fromPolygonXY(ring_list))

    elif wkb_type == WKB_GeometryCollection:
        n = geom.constGet().numGeometries()
        for i in range(n):
            part = QgsGeometry(geom.constGet().geometryN(i).clone())
            pt = wkb_flatType(part.wkbType())
            if pt == WKB_Polygon:
                parts.append(part)
            elif pt == WKB_MultiPolygon:
                for sub in part.asMultiPolygon():
                    parts.append(QgsGeometry.fromPolygonXY(sub))
    else:
        raise ValueError(
            f"Tipo '{wkb_displayString(geom.wkbType())}' "
            f"incompatível com polígono ANM. {context}"
        )

    if not parts:
        raise ValueError(f"Nenhum componente poligonal encontrado. {context}")

    largest = max(parts, key=lambda g: g.area())

    if len(parts) > 1:
        warnings.warn(
            f"[ANM Poligonal] MultiPolygon {context}: usando maior componente "
            f"({len(parts)} total). Verifique auto-interseções no esboço.",
            stacklevel=3,
        )

    return largest


# ---------------------------------------------------------------------------
# Classificação de segmentos ortogonais
# ---------------------------------------------------------------------------

def _is_ns(p1: Point, p2: Point) -> bool:
    """Retorna True se o segmento p1→p2 é estritamente Norte-Sul (ΔX ≈ 0)."""
    return abs(p2[0] - p1[0]) < EPS_ORTHO


def _is_lo(p1: Point, p2: Point) -> bool:
    """Retorna True se o segmento p1→p2 é estritamente Leste-Oeste (ΔY ≈ 0)."""
    return abs(p2[1] - p1[1]) < EPS_ORTHO


# ---------------------------------------------------------------------------
# Ortogonalização de segmento diagonal → escadaria N-S / L-O
# ---------------------------------------------------------------------------

def _orthogonalize_segment(p1: Point, p2: Point,
                            n_steps: int,
                            first_direction: str = 'auto') -> List[Point]:
    """
    Transforma um segmento diagonal em uma escadaria de n_steps "dentes",
    alternando passos L-O e N-S.

    Em cada mini-passo, a coordenada que permanece fixa é COPIADA do
    acumulador atual (não recalculada), garantindo ΔX = 0 ou ΔY = 0 exatos
    sem acúmulo de erro de ponto flutuante.

    Parâmetros:
      first_direction — 'H' (Horizontal/L-O primeiro), 'V' (Vertical/N-S
                        primeiro) ou 'auto' (escolhe pelo maior delta angular).

    Segmentos já ortogonais são retornados imediatamente sem modificação.
    """
    if _is_ns(p1, p2):
        return [p1, (p1[0], p2[1])]
    if _is_lo(p1, p2):
        return [p1, (p2[0], p1[1])]

    n_steps = max(1, n_steps)
    dx = p2[0] - p1[0]
    dy = p2[1] - p1[1]
    step_x = dx / n_steps
    step_y = dy / n_steps

    if first_direction == 'auto':
        first_direction = 'H' if abs(dx) >= abs(dy) else 'V'

    pts: List[Point] = [p1]
    lon_cur: float = p1[0]
    lat_cur: float = p1[1]

    for _ in range(n_steps):
        if first_direction == 'H':
            lon_cur += step_x
            pts.append((lon_cur, lat_cur))   # lat copiada → ΔY = 0
            lat_cur += step_y
            pts.append((lon_cur, lat_cur))   # lon copiado → ΔX = 0
        else:
            lat_cur += step_y
            pts.append((lon_cur, lat_cur))   # lon copiado → ΔX = 0
            lon_cur += step_x
            pts.append((lon_cur, lat_cur))   # lat copiada → ΔY = 0

    # Substitui o último ponto calculado pelo p2 exato para evitar drift
    pts[-1] = p2
    return pts


def _remove_collinear_ortho(pts: List[Point]) -> List[Point]:
    """
    Remove vértices intermediários colineares em segmentos ortogonais.

    Três pontos são colineares ortogonalmente se os dois segmentos que formam
    compartilham a mesma longitude (ambos N-S) ou a mesma latitude (ambos L-O).
    Esses pontos não alteram a geometria, mas produzem vértices desnecessários
    nos arquivos de saída.
    """
    if len(pts) < 3:
        return pts
    result = [pts[0]]
    for i in range(1, len(pts) - 1):
        prev = result[-1]
        curr = pts[i]
        nxt  = pts[i + 1]
        same_x = abs(prev[0] - curr[0]) < EPS_ORTHO and abs(curr[0] - nxt[0]) < EPS_ORTHO
        same_y = abs(prev[1] - curr[1]) < EPS_ORTHO and abs(curr[1] - nxt[1]) < EPS_ORTHO
        if not (same_x or same_y):
            result.append(curr)
    result.append(pts[-1])
    return result


# ---------------------------------------------------------------------------
# Reprojeção para EPSG:4674
# ---------------------------------------------------------------------------

def reproject_to_epsg4674(geom: QgsGeometry,
                           src_crs: QgsCoordinateReferenceSystem) -> QgsGeometry:
    """
    Reprojeta a geometria para EPSG:4674.
    Se o SRC de origem já for EPSG:4674, retorna uma cópia sem transformação.
    """
    if src_crs.authid() == 'EPSG:4674':
        return QgsGeometry(geom)
    transform = QgsCoordinateTransform(src_crs, CRS_ANM, QgsProject.instance())
    geom_out = QgsGeometry(geom)
    geom_out.transform(transform)
    return geom_out


# ---------------------------------------------------------------------------
# Processador principal
# ---------------------------------------------------------------------------

class ANMPolygonProcessor:
    """
    Transforma um polígono esboço em polígono ANM com bordas estritamente
    N-S ou L-O (rumos verdadeiros). Saída sempre em EPSG:4674.

    Fluxo interno:
      1. Reprojeção para EPSG:4674 (se necessário).
      2. Validação e correção de geometria via makeValid().
      3. Injeção de snap vertices no anel externo.
      4. Ortogonalização segmento a segmento (escadaria de dentes).
      5. Remoção de vértices colineares redundantes.
      6. Fechamento do anel e validação final da geometria resultante.
    """

    # Snap vertices mais distantes que SNAP_TOL * 100 do anel são ignorados
    SNAP_TOL = 1e-5

    def __init__(self,
                 n_steps: int = 3,
                 first_direction: str = 'auto',
                 snap_vertices: Optional[List[Point]] = None,
                 src_crs: Optional[QgsCoordinateReferenceSystem] = None):
        self.n_steps         = max(1, n_steps)
        self.first_direction = first_direction
        self.snap_vertices   = snap_vertices or []
        self.src_crs         = src_crs or CRS_ANM

    def process(self, sketch_geom: QgsGeometry) -> QgsGeometry:
        """Executa o pipeline completo e retorna o polígono ANM em EPSG:4674."""
        geom_4674 = reproject_to_epsg4674(sketch_geom, self.src_crs)

        if geom_4674.isEmpty():
            raise ValueError("Geometria vazia após reprojeção para EPSG:4674.")

        if not geom_4674.isGeosValid():
            geom_4674 = geom_4674.makeValid()
            if geom_4674 is None or geom_4674.isEmpty():
                raise ValueError(
                    "Geometria inválida e irrecuperável. Use "
                    "Vetor → Ferramentas de Geometria → Corrigir geometrias."
                )

        geom_4674 = _force_single_polygon(geom_4674, context='(entrada)')

        pts = self._extract_ring(geom_4674)
        if len(pts) < 3:
            raise ValueError("Polígono precisa ter pelo menos 3 vértices.")

        if self.snap_vertices:
            pts = self._inject_snap_vertices(pts)

        ortho_pts = self._build_orthogonal_ring(pts)
        ortho_pts = _remove_collinear_ortho(ortho_pts)

        # Garante fechamento do anel
        if not ortho_pts or ortho_pts[0] != ortho_pts[-1]:
            ortho_pts.append(ortho_pts[0])

        result = QgsGeometry.fromPolygonXY([
            [QgsPointXY(lon, lat) for lon, lat in ortho_pts]
        ])

        if not result.isGeosValid():
            result = result.makeValid()
            result = _force_single_polygon(result, context='(resultado)')

        return result

    def get_vertex_list(self, geom: QgsGeometry) -> List[Point]:
        """
        Retorna a lista de vértices do anel externo, incluindo o ponto de
        fechamento (primeiro vértice repetido ao final).
        """
        pts = self._extract_ring(geom)
        if pts and pts[0] != pts[-1]:
            pts.append(pts[0])
        return pts

    def validate_orthogonality(self, geom: QgsGeometry) -> List[str]:
        """
        Verifica se todos os segmentos do anel externo são estritamente
        N-S ou L-O. Retorna lista de strings descrevendo cada falha.
        Lista vazia indica polígono 100% ortogonal.
        """
        errors = []
        pts = self._extract_ring(geom)
        n = len(pts)
        for i in range(n):
            p1 = pts[i]
            p2 = pts[(i + 1) % n]
            if not (_is_ns(p1, p2) or _is_lo(p1, p2)):
                errors.append(
                    f"Seg V{i+1:03d}\u2192V{(i+1)%n+1:03d}: "
                    f"\u0394Lon={abs(p2[0]-p1[0]):.2e}\xb0, \u0394Lat={abs(p2[1]-p1[1]):.2e}\xb0"
                )
        return errors

    def _extract_ring(self, geom: QgsGeometry) -> List[Point]:
        """
        Extrai os vértices do anel externo como lista de (lon, lat).
        O vértice de fechamento (igual ao primeiro) é removido se presente.
        Suporta Polygon simples e MultiPolygon (usa o primeiro componente).
        """
        poly = geom.asPolygon()
        if not poly:
            mpoly = geom.asMultiPolygon()
            poly = mpoly[0] if mpoly else []
        if not poly:
            return []
        pts = [(p.x(), p.y()) for p in poly[0]]
        if len(pts) > 1 and pts[0] == pts[-1]:
            pts = pts[:-1]
        return pts

    def _build_orthogonal_ring(self, pts: List[Point]) -> List[Point]:
        """
        Percorre todos os segmentos do anel e os ortogonaliza em sequência.
        O primeiro segmento contribui com seu ponto inicial; os demais apenas
        com o trecho novo, evitando duplicação no ponto de junção.
        """
        result: List[Point] = []
        n = len(pts)
        for i in range(n):
            seg = _orthogonalize_segment(
                pts[i], pts[(i + 1) % n], self.n_steps, self.first_direction
            )
            result.extend(seg[1:] if result else seg)
        return result

    def _inject_snap_vertices(self, pts: List[Point]) -> List[Point]:
        """Injeta cada snap vertex no segmento do anel mais próximo a ele."""
        result = list(pts)
        for snap in self.snap_vertices:
            result = self._inject_one(result, snap)
        return result

    def _inject_one(self, pts: List[Point], snap: Point) -> List[Point]:
        """
        Encontra o segmento mais próximo do snap vertex e insere nele a
        projeção ortogonal do snap. Snap vertices muito distantes do anel
        (> SNAP_TOL * 100) são ignorados silenciosamente.
        """
        best_idx, best_dist, best_proj = -1, float('inf'), None
        n = len(pts)
        for i in range(n):
            proj, dist = _project_on_segment(snap, pts[i], pts[(i + 1) % n])
            if dist < best_dist:
                best_dist, best_idx, best_proj = dist, i, proj
        if best_proj is None or best_dist > self.SNAP_TOL * 100:
            return pts
        result = list(pts)
        result.insert(best_idx + 1, best_proj)
        return result


# ---------------------------------------------------------------------------
# Utilitário geométrico
# ---------------------------------------------------------------------------

def _project_on_segment(p: Point, a: Point, b: Point) -> Tuple[Point, float]:
    """
    Projeta o ponto p sobre o segmento a→b e retorna (ponto_projetado, distância).
    O parâmetro t é limitado a [0, 1] para manter a projeção dentro do segmento.
    Em segmento degenerado (a == b), retorna o próprio a como projeção.
    """
    ax, ay = a; bx, by = b; px, py = p
    dx, dy = bx - ax, by - ay
    sq = dx * dx + dy * dy
    if sq < 1e-20:
        return a, math.hypot(px - ax, py - ay)
    t = max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / sq))
    qx, qy = ax + t * dx, ay + t * dy
    return (qx, qy), math.hypot(px - qx, py - qy)


# ---------------------------------------------------------------------------
# Exportação — Shapefile (EPSG:4674, área geodésica GRS80)
# ---------------------------------------------------------------------------

def export_shapefile(geom: QgsGeometry,
                     output_path: str,
                     attributes: Optional[dict] = None) -> bool:
    """
    Exporta o polígono ANM como shapefile em EPSG:4674.

    Campos do shapefile:
      id         Int    — sempre 1 (cada chamada gera um único polígono)
      area_ha    Double — área geodésica em hectares (GRS80)
      perim_km   Double — perímetro geodésico em quilômetros (GRS80)
      src        String — 'EPSG:4674' (constante informativa)
      obs        String — observação livre, via attributes['obs']

    Usa QgsVectorFileWriter.create() (API QGIS 3.10+ / 4.0) com fallback
    automático para o construtor legado em versões mais antigas.
    """
    if not output_path.lower().endswith('.shp'):
        output_path += '.shp'

    fields = QgsFields()
    fields.append(QgsField('id',       QVariant.Int))
    fields.append(QgsField('area_ha',  QVariant.Double))
    fields.append(QgsField('perim_km', QVariant.Double))
    fields.append(QgsField('src',      QVariant.String))
    fields.append(QgsField('obs',      QVariant.String))

    # Tenta a API moderna — evita DeprecationWarning no QGIS 3.20+
    writer = None
    writer_error = None
    try:
        options = QgsVectorFileWriter.SaveVectorOptions()
        options.driverName   = 'ESRI Shapefile'
        options.fileEncoding = 'UTF-8'
        writer, writer_error, _, _ = QgsVectorFileWriter.create(
            output_path, fields,
            WKB_Polygon,
            CRS_ANM,
            QgsProject.instance().transformContext(),
            options,
        )
    except (AttributeError, TypeError):
        # Fallback para QGIS < 3.10
        writer = QgsVectorFileWriter(
            output_path, 'UTF-8', fields,
            WKB_Polygon,
            CRS_ANM,
            'ESRI Shapefile',
        )
        writer_error = writer.hasError()

    if writer is None or (hasattr(writer, 'hasError') and
                          writer.hasError() != VFW_NoError):
        err_msg = writer_error if isinstance(writer_error, str) else (
            writer.errorMessage() if writer else 'writer não criado')
        raise IOError(f"Erro ao criar shapefile: {err_msg}")

    # Calcula área e perímetro geodésicos para preencher os atributos do polígono
    area_ha  = -1.0
    perim_km = -1.0
    try:
        da = QgsDistanceArea()
        da.setSourceCrs(CRS_ANM, QgsProject.instance().transformContext())
        da.setEllipsoid('GRS80')
        area_ha  = round(da.measureArea(geom)      / 10_000.0, 4)
        perim_km = round(da.measurePerimeter(geom) /  1_000.0, 4)
    except Exception:
        pass  # -1.0 sinaliza falha no atributo sem impedir a criação do arquivo

    feat = QgsFeature(fields)
    feat.setGeometry(geom)
    feat['id']       = 1
    feat['area_ha']  = area_ha
    feat['perim_km'] = perim_km
    feat['src']      = 'EPSG:4674'
    feat['obs']      = (attributes or {}).get('obs', '')

    writer.addFeature(feat)
    del writer  # fecha e faz flush do arquivo
    return True


# ---------------------------------------------------------------------------
# Exportação — TXT ANM (leitura humana, separador tabulação)
# ---------------------------------------------------------------------------

def export_txt_anm(vertices: List[Point],
                   output_path: str,
                   include_header: bool = True) -> bool:
    """
    Exporta os vértices no formato TXT da ANM, adequado para conferência
    manual e colagem direta no campo de coordenadas do SIGMINE.

    Formato de cada linha:
        <nº>\\t<lat_dms>\\t<lon_dms>

    O vértice 1 é repetido na última linha com numeração N+1, conforme
    o padrão de fechamento exigido pela ANM.

    Parâmetros
    ----------
    vertices       : lista [(lon, lat)] em EPSG:4674. O ponto de fechamento
                     duplicado é removido antes da escrita, se presente.
    output_path    : caminho de saída (.txt).
    include_header : se True, insere a linha de cabeçalho com nomes das colunas.
    """
    if not output_path.lower().endswith('.txt'):
        output_path += '.txt'

    pts = list(vertices)
    # Remove duplicata de fechamento — será readicionada como linha final
    if len(pts) > 1 and pts[0] == pts[-1]:
        pts = pts[:-1]

    lines = []
    if include_header:
        lines.append('V\u00e9rtice\tLatitude\tLongitude')

    for i, (lon, lat) in enumerate(pts, start=1):
        lines.append(f'{i}\t{decimal_to_dms_anm(lat)}\t{decimal_to_dms_anm(lon)}')

    # Linha de fechamento: vértice 1 repetido com número N+1
    if pts:
        lon0, lat0 = pts[0]
        closing_n  = len(pts) + 1
        lines.append(f'{closing_n}\t{decimal_to_dms_anm(lat0)}\t{decimal_to_dms_anm(lon0)}')

    with open(output_path, 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(lines))
        fh.write('\n')

    return True


# ---------------------------------------------------------------------------
# Exportação — CSV ANM (inserção em lote no REPEM)
# ---------------------------------------------------------------------------

def export_csv_anm(vertices: List[Point],
                   output_path: str) -> bool:
    """
    Exporta os vértices em CSV para upload direto na tela de inserção em
    lote do sistema REPEM (ANM).

    Formato de cada linha — separador ponto-e-vírgula, SEM cabeçalho:
        Sinal_Lat;Graus_Lat;Min_Lat;Seg_Lat;Mil_Lat;Sinal_Lon;Graus_Lon;Min_Lon;Seg_Lon;Mil_Lon

    Exemplo concreto:
        -;015;30;43;700;-;047;57;27;555

    Regras críticas exigidas pelo REPEM:
      - Todos os campos exportados como texto — nunca numérico — para preservar zeros.
      - Sinal em coluna independente ('-' Sul/Oeste, '+' Norte/Leste), jamais
        concatenado aos graus.
      - Graus com 3 dígitos, minutos e segundos com 2, milésimos com 3.
      - Sem linha de cabeçalho (o sistema não aceita header na importação em lote).
      - O primeiro vértice é repetido na última linha para fechamento explícito.
      - Encoding UTF-8; newline='' para controle correto de CRLF multiplataforma.

    Parâmetros
    ----------
    vertices    : lista [(lon, lat)] em EPSG:4674. O ponto de fechamento
                  duplicado é removido antes do processamento, se presente.
    output_path : caminho de saída (.csv).
    """
    if not output_path.lower().endswith('.csv'):
        output_path += '.csv'

    pts = list(vertices)
    # Remove duplicata de fechamento para não gerar dois vértices finais iguais
    if len(pts) > 1 and pts[0] == pts[-1]:
        pts = pts[:-1]

    lines = []
    for lon, lat in pts:
        s_lat, g_lat, m_lat, seg_lat, mil_lat = decimal_to_dms_components(lat)
        s_lon, g_lon, m_lon, seg_lon, mil_lon = decimal_to_dms_components(lon)
        lines.append(
            f'{s_lat};{g_lat};{m_lat};{seg_lat};{mil_lat};'
            f'{s_lon};{g_lon};{m_lon};{seg_lon};{mil_lon}'
        )

    # Linha de fechamento: primeiro vértice repetido ao final
    if pts:
        lon0, lat0 = pts[0]
        s_lat, g_lat, m_lat, seg_lat, mil_lat = decimal_to_dms_components(lat0)
        s_lon, g_lon, m_lon, seg_lon, mil_lon = decimal_to_dms_components(lon0)
        lines.append(
            f'{s_lat};{g_lat};{m_lat};{seg_lat};{mil_lat};'
            f'{s_lon};{g_lon};{m_lon};{seg_lon};{mil_lon}'
        )

    with open(output_path, 'w', encoding='utf-8', newline='') as fh:
        fh.write('\n'.join(lines))
        fh.write('\n')

    return True


# ---------------------------------------------------------------------------
# Carregamento de camada no canvas do QGIS
# ---------------------------------------------------------------------------

def load_layer_to_canvas(path: str, layer_name: str) -> Optional[QgsVectorLayer]:
    """
    Cria um QgsVectorLayer a partir do caminho informado e o adiciona ao
    projeto atual. Retorna None se o arquivo não puder ser lido como camada válida.
    """
    layer = QgsVectorLayer(path, layer_name, 'ogr')
    if not layer.isValid():
        return None
    QgsProject.instance().addMapLayer(layer)
    return layer


# ---------------------------------------------------------------------------
# Pipeline de recorte + reortogonalização (camadas de restrição)
# ---------------------------------------------------------------------------

def clip_and_reortogonalize(
    anm_geom: QgsGeometry,
    restriction_layers: list,
    n_steps: int = 3,
    first_direction: str = 'auto',
    snap_vertices: Optional[List[Point]] = None,
) -> List[dict]:
    """
    Aplica restrições espaciais ao polígono ANM em dois estágios:

    Estágio 1 — Recorte (difference):
      Faz a union de todos os polígonos das camadas de restrição
      (reprojetados para EPSG:4674) e aplica difference no polígono ANM:
        resultado = anm_geom.difference(union_restricoes)
      MultiPolygon resultante tem cada componente tratado separadamente.

    Estágio 2 — Reortogonalização:
      Cada componente sólido do difference é repassado ao ANMPolygonProcessor,
      reconstituindo bordas estritamente N-S e L-O.

    NOTA: A reortogonalização pode alterar levemente a área, pois bordas não
    ortogonais geradas pelo recorte são aproximadas por escadaria. Isso é
    esperado — rumos verdadeiros têm precedência sobre o recorte exato.

    Parâmetros
    ----------
    anm_geom           : polígono ANM já processado (em EPSG:4674).
    restriction_layers : lista de QgsVectorLayer com as áreas de restrição.
    n_steps            : dentes por segmento (repassado ao processador).
    first_direction    : 'auto', 'H' ou 'V' (repassado ao processador).
    snap_vertices      : pontos de snap opcionais (repassados ao processador).

    Retorna lista de dicts ordenada por área DECRESCENTE:
      [{'geom': QgsGeometry, 'vertices': [...], 'area_ha': float,
        'ortho_errors': [...], 'suffix': ''|'_a'|'_b'|...}, ...]
    """
    ctx = QgsProject.instance().transformContext()

    # --- Estágio 1: union de todas as geometrias de restrição ---
    union_restr: Optional[QgsGeometry] = None

    for lyr in restriction_layers:
        xf = QgsCoordinateTransform(lyr.crs(), CRS_ANM, ctx)
        for feat in lyr.getFeatures():
            g = QgsGeometry(feat.geometry())
            g.transform(xf)
            if not g.isGeosValid():
                g = g.makeValid()
            if g.isEmpty():
                continue
            union_restr = g if union_restr is None else union_restr.combine(g)

    if union_restr is None or union_restr.isEmpty():
        # Nenhuma restrição válida: retorna o polígono original sem alteração
        proc  = ANMPolygonProcessor(
            n_steps=n_steps,
            first_direction=first_direction,
            snap_vertices=snap_vertices or [],
            src_crs=CRS_ANM,
        )
        verts = proc.get_vertex_list(anm_geom)
        errs  = proc.validate_orthogonality(anm_geom)
        return [{
            'geom':         anm_geom,
            'vertices':     verts,
            'area_ha':      area_geodesica_ha(anm_geom),
            'ortho_errors': errs,
            'suffix':       '',
        }]

    # Difference: porção do polígono ANM que não está coberta pelas restrições
    diff = anm_geom.difference(union_restr)

    if diff is None or diff.isEmpty():
        return []  # Polígono inteiramente dentro das restrições — descartado

    # -----------------------------------------------------------------------
    # Helpers internos para extração de componentes sólidos (sem furos)
    # -----------------------------------------------------------------------

    def _cut_by_lo_line(poly: QgsGeometry, cut_lat: float) -> List[QgsGeometry]:
        """
        Divide o polígono em dois usando uma linha L-O na latitude cut_lat.
        Estratégia para eliminar furos: cada furo é convertido em uma linha
        de corte que separa o polígono em duas partes sólidas.
        """
        bbox   = poly.boundingBox()
        margin = max(abs(bbox.width()), abs(bbox.height()), 0.01) * 2.0
        x_min  = bbox.xMinimum() - margin
        x_max  = bbox.xMaximum() + margin

        rect_sul = QgsGeometry.fromPolygonXY([[
            QgsPointXY(x_min, bbox.yMinimum() - margin),
            QgsPointXY(x_max, bbox.yMinimum() - margin),
            QgsPointXY(x_max, cut_lat),
            QgsPointXY(x_min, cut_lat),
            QgsPointXY(x_min, bbox.yMinimum() - margin),
        ]])

        rect_norte = QgsGeometry.fromPolygonXY([[
            QgsPointXY(x_min, cut_lat),
            QgsPointXY(x_max, cut_lat),
            QgsPointXY(x_max, bbox.yMaximum() + margin),
            QgsPointXY(x_min, bbox.yMaximum() + margin),
            QgsPointXY(x_min, cut_lat),
        ]])

        results_cut = []
        for rect in (rect_sul, rect_norte):
            piece = poly.intersection(rect)
            if piece and not piece.isEmpty():
                piece = _strip_holes(piece)
                if piece and not piece.isEmpty():
                    results_cut.append(piece)

        return results_cut if results_cut else [poly]

    def _strip_holes(geom: QgsGeometry) -> QgsGeometry:
        """
        Remove todos os furos internos, devolvendo apenas o anel externo.
        Aplicado após cada interseção para garantir geometrias sólidas.
        """
        wkb = wkb_flatType(geom.wkbType())
        if wkb == WKB_Polygon:
            raw = geom.asPolygon()
            if raw:
                return QgsGeometry.fromPolygonXY([raw[0]])  # raw[0] = anel externo
            return geom
        elif wkb == WKB_MultiPolygon:
            parts_solid = []
            for ring_list in geom.asMultiPolygon():
                if ring_list:
                    parts_solid.append(QgsGeometry.fromPolygonXY([ring_list[0]]))
            if not parts_solid:
                return geom
            merged = parts_solid[0]
            for p in parts_solid[1:]:
                merged = merged.combine(p)
            return merged
        return geom

    def _collect_solid(geom: QgsGeometry, output: List[QgsGeometry]):
        """
        Extrai recursivamente todos os componentes poligonais sem furos.
        Polígonos com furos são cortados por linhas L-O passando pelo centroide
        de cada furo, eliminando-os e preservando a área externa integralmente.
        """
        wkb = wkb_flatType(geom.wkbType())

        if wkb == WKB_Polygon:
            raw = geom.asPolygon()
            if not raw:
                return
            holes = raw[1:]  # raw[0] = anel externo; raw[1:] = furos internos
            if not holes:
                output.append(geom)
                return

            # Para cada furo, corta o polígono por uma linha L-O no centroide do furo
            pending = [geom]
            for hole_ring in holes:
                hole_geom = QgsGeometry.fromPolygonXY([hole_ring])
                cut_lat   = hole_geom.centroid().asPoint().y()
                next_pending = []
                for poly_piece in pending:
                    next_pending.extend(_cut_by_lo_line(poly_piece, cut_lat))
                pending = next_pending

            for piece in pending:
                if piece and not piece.isEmpty():
                    output.append(piece)

        elif wkb == WKB_MultiPolygon:
            for ring_list in geom.asMultiPolygon():
                _collect_solid(QgsGeometry.fromPolygonXY(ring_list), output)

        elif wkb == WKB_GeometryCollection:
            n = geom.constGet().numGeometries()
            for i in range(n):
                pg = QgsGeometry(geom.constGet().geometryN(i).clone())
                _collect_solid(pg, output)

    # Coleta todos os componentes sólidos resultantes do difference
    parts: List[QgsGeometry] = []
    _collect_solid(diff, parts)

    if not parts:
        return []

    # --- Estágio 2: reortogonaliza cada componente individualmente ---
    results = []
    for part in parts:
        if part.isEmpty():
            continue
        try:
            proc    = ANMPolygonProcessor(
                n_steps=n_steps,
                first_direction=first_direction,
                snap_vertices=snap_vertices or [],
                src_crs=CRS_ANM,
            )
            reortho = proc.process(part)
            verts   = proc.get_vertex_list(reortho)
            errs    = proc.validate_orthogonality(reortho)
            results.append({
                'geom':         reortho,
                'vertices':     verts,
                'area_ha':      area_geodesica_ha(reortho),
                'ortho_errors': errs,
                'suffix':       '',
            })
        except Exception as e:
            warnings.warn(f'[ANM] Erro na reortogonalização de componente: {e}')

    if not results:
        return []

    # Ordena por área decrescente e atribui sufixos: _a (maior), _b, _c...
    # Polígono único não recebe sufixo.
    results.sort(key=lambda r: r['area_ha'], reverse=True)
    for idx, r in enumerate(results):
        r['suffix'] = f'_{chr(ord("a") + idx)}' if len(results) > 1 else ''

    return results
