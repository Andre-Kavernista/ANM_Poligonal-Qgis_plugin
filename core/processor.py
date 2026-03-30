# -*- coding: utf-8 -*-
"""
Core de processamento geométrico ANM — EPSG:4674 obrigatório.

PREMISSAS INEGOCIÁVEIS:
  - Todo processamento e saída ocorre em SIRGAS 2000 geográfico (EPSG:4674).
  - Segmento N-S: ΔX = 0 bit-a-bit exato (longitude COPIADA).
  - Segmento L-O: ΔY = 0 bit-a-bit exato (latitude COPIADA).
  - Área calculada em EPSG:4674 conforme sistema ANM
    (fórmula esférica de Girard / área geodésica).
  - Formato de coordenadas ANM: graus°minutos'segundos"milésimos
    ex.: -15°30'43"700

FORMATO TXT ANM:
  Vértice  Latitude              Longitude
  1        -15°30'43"700        -47°57'27"555
  A parte decimal do segundo vem após o símbolo (") aspas dupla.

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
# Constantes
# ---------------------------------------------------------------------------

CRS_ANM = QgsCoordinateReferenceSystem('EPSG:4674')  # SIRGAS 2000 geográfico
EPS_ORTHO = 1e-10


# ---------------------------------------------------------------------------
# Tipos
# ---------------------------------------------------------------------------

Point = Tuple[float, float]  # (longitude, latitude) em graus decimais


# ---------------------------------------------------------------------------
# Conversão decimal → DMS no formato ANM
# ---------------------------------------------------------------------------

def decimal_to_dms_anm(degrees: float) -> str:
    """
    Converte graus decimais para o formato ANM:
      -15°30'43"700 

    Onde "700 representa a parte decimal dos segundos (milésimos de segundo).
    O símbolo de segundo-de-arco é aspas dupla ("), conforme notação correta.

    Exemplos:
      -15.512139...° → -15°30'43"700 
      -47.957654...° → -47°57'27"555
    """
    neg = degrees < 0
    d = abs(degrees)

    deg_int = int(d)
    remainder = (d - deg_int) * 60
    min_int = int(remainder)
    sec_total = (remainder - min_int) * 60

    sec_int = int(sec_total)
    millesimos = round((sec_total - sec_int) * 1000)

    # Overflow de arredondamento
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
    return f'{sign}{deg_int:d}°{min_int:02d}\'{sec_int:02d}"{millesimos:03d}'


# ---------------------------------------------------------------------------
# Área geodésica em EPSG:4674 (conforme ANM)
# ---------------------------------------------------------------------------

def area_geodesica_ha(geom: QgsGeometry) -> float:
    """
    Calcula a área geodésica do polígono em hectares usando QgsDistanceArea
    configurado com o elipsoide do SIRGAS 2000 (GRS80), que é o mesmo que
    o sistema ANM utiliza internamente para validação de área.

    A geometria DEVE estar em EPSG:4674.

    Retorna área em hectares (float), ou -1.0 em caso de falha.
    """
    try:
        da = QgsDistanceArea()
        da.setSourceCrs(CRS_ANM, QgsProject.instance().transformContext())
        da.setEllipsoid('GRS80')  # elipsoide do SIRGAS 2000
        area_m2 = da.measureArea(geom)
        return round(area_m2 / 10_000.0, 4)
    except Exception:
        return -1.0


# ---------------------------------------------------------------------------
# Normalização de geometria
# ---------------------------------------------------------------------------

def _force_single_polygon(geom: QgsGeometry, context: str = '') -> QgsGeometry:
    """
    Garante Polygon simples. Em caso de Multi/Collection, retorna o maior.
    makeValid() pode promover para Multi — tratado aqui em todos os pontos
    de entrada e saída do processador.
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
# Verificação de ortogonalidade
# ---------------------------------------------------------------------------

def _is_ns(p1: Point, p2: Point) -> bool:
    return abs(p2[0] - p1[0]) < EPS_ORTHO


def _is_lo(p1: Point, p2: Point) -> bool:
    return abs(p2[1] - p1[1]) < EPS_ORTHO


# ---------------------------------------------------------------------------
# Ortogonalização de segmento
# ---------------------------------------------------------------------------

def _orthogonalize_segment(p1: Point, p2: Point,
                            n_steps: int,
                            first_direction: str = 'auto') -> List[Point]:
    """
    Converte segmento diagonal em escadaria N-S/L-O com n_steps dentes.
    Coordenada fixa em cada passo é COPIADA do acumulador (ΔX ou ΔY = 0 exato).
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
            pts.append((lon_cur, lat_cur))   # lat COPIADA → ΔY=0
            lat_cur += step_y
            pts.append((lon_cur, lat_cur))   # lon COPIADO → ΔX=0
        else:
            lat_cur += step_y
            pts.append((lon_cur, lat_cur))   # lon COPIADO → ΔX=0
            lon_cur += step_x
            pts.append((lon_cur, lat_cur))   # lat COPIADA → ΔY=0

    pts[-1] = p2
    return pts


def _remove_collinear_ortho(pts: List[Point]) -> List[Point]:
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
# Reprojeção
# ---------------------------------------------------------------------------

def reproject_to_epsg4674(geom: QgsGeometry,
                           src_crs: QgsCoordinateReferenceSystem) -> QgsGeometry:
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
    Transforma polígono esboço → polígono ANM com rumos verdadeiros N-S/L-O.
    SAÍDA SEMPRE EM EPSG:4674.
    """

    SNAP_TOL = 1e-5

    def __init__(self,
                 n_steps: int = 3,
                 first_direction: str = 'auto',
                 snap_vertices: Optional[List[Point]] = None,
                 src_crs: Optional[QgsCoordinateReferenceSystem] = None):
        self.n_steps = max(1, n_steps)
        self.first_direction = first_direction
        self.snap_vertices = snap_vertices or []
        self.src_crs = src_crs or CRS_ANM

    def process(self, sketch_geom: QgsGeometry) -> QgsGeometry:
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
        pts = self._extract_ring(geom)
        if pts and pts[0] != pts[-1]:
            pts.append(pts[0])
        return pts

    def validate_orthogonality(self, geom: QgsGeometry) -> List[str]:
        errors = []
        pts = self._extract_ring(geom)
        n = len(pts)
        for i in range(n):
            p1 = pts[i]
            p2 = pts[(i + 1) % n]
            if not (_is_ns(p1, p2) or _is_lo(p1, p2)):
                errors.append(
                    f"Seg V{i+1:03d}→V{(i+1)%n+1:03d}: "
                    f"ΔLon={abs(p2[0]-p1[0]):.2e}°, ΔLat={abs(p2[1]-p1[1]):.2e}°"
                )
        return errors

    def _extract_ring(self, geom: QgsGeometry) -> List[Point]:
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
        result: List[Point] = []
        n = len(pts)
        for i in range(n):
            seg = _orthogonalize_segment(
                pts[i], pts[(i + 1) % n], self.n_steps, self.first_direction
            )
            result.extend(seg[1:] if result else seg)
        return result

    def _inject_snap_vertices(self, pts: List[Point]) -> List[Point]:
        result = list(pts)
        for snap in self.snap_vertices:
            result = self._inject_one(result, snap)
        return result

    def _inject_one(self, pts: List[Point], snap: Point) -> List[Point]:
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
    ax, ay = a; bx, by = b; px, py = p
    dx, dy = bx - ax, by - ay
    sq = dx * dx + dy * dy
    if sq < 1e-20:
        return a, math.hypot(px - ax, py - ay)
    t = max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / sq))
    qx, qy = ax + t * dx, ay + t * dy
    return (qx, qy), math.hypot(px - qx, py - qy)


# ---------------------------------------------------------------------------
# Exportação — Shapefile (EPSG:4674 hardcoded, área geodésica GRS80)
# ---------------------------------------------------------------------------

def export_shapefile(geom: QgsGeometry,
                     output_path: str,
                     attributes: Optional[dict] = None) -> bool:
    """
    Exporta polígono ANM como shapefile em EPSG:4674.

    Campos:
      id         Int    — identificador sequencial
      area_ha    Double — área geodésica em hectares (GRS80 / EPSG:4674)
      perim_km   Double — perímetro geodésico em quilômetros (GRS80 / EPSG:4674)
      src        String — 'EPSG:4674'
      obs        String — observação livre

    Compatibilidade: usa QgsVectorFileWriter.create() (QGIS 3.10+/4.0)
    com fallback para o construtor legado (QGIS < 3.10).
    """
    if not output_path.lower().endswith('.shp'):
        output_path += '.shp'

    fields = QgsFields()
    fields.append(QgsField('id',       QVariant.Int))
    fields.append(QgsField('area_ha',  QVariant.Double))
    fields.append(QgsField('perim_km', QVariant.Double))
    fields.append(QgsField('src',      QVariant.String))
    fields.append(QgsField('obs',      QVariant.String))

    # Tenta a API moderna (QGIS 3.10+ / 4.0) — evita DeprecationWarning
    writer = None
    writer_error = None
    try:
        options = QgsVectorFileWriter.SaveVectorOptions()
        options.driverName    = 'ESRI Shapefile'
        options.fileEncoding  = 'UTF-8'
        writer, writer_error, _, _ = QgsVectorFileWriter.create(
            output_path, fields,
            WKB_Polygon,
            CRS_ANM,
            QgsProject.instance().transformContext(),
            options,
        )
    except (AttributeError, TypeError):
        # Fallback: construtor legado para versões antigas
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

    # Área e perímetro geodésicos via QgsDistanceArea / GRS80 / EPSG:4674
    area_ha  = -1.0
    perim_km = -1.0
    try:
        da = QgsDistanceArea()
        da.setSourceCrs(CRS_ANM, QgsProject.instance().transformContext())
        da.setEllipsoid('GRS80')
        area_ha  = round(da.measureArea(geom)      / 10_000.0, 4)
        perim_km = round(da.measurePerimeter(geom) /  1_000.0, 4)
    except Exception:
        pass

    feat = QgsFeature(fields)
    feat.setGeometry(geom)
    feat['id']       = 1
    feat['area_ha']  = area_ha
    feat['perim_km'] = perim_km
    feat['src']      = 'EPSG:4674'
    feat['obs']      = (attributes or {}).get('obs', '')

    writer.addFeature(feat)
    del writer
    return True


# ---------------------------------------------------------------------------
# Exportação — TXT/CSV ANM (formato DMS com milésimos de segundo)
# ---------------------------------------------------------------------------

def export_txt_anm(vertices: List[Point],
                   output_path: str,
                   include_header: bool = True) -> bool:
    """
    Exporta vértices no formato TXT da ANM.

    Formato exato:
        Vértice  Latitude          Longitude
        1        -15°30'43"700     -47°57'27"555

    Onde "NNN = milésimos do segundo (3 dígitos, sem ponto/vírgula).
    Separador: tabulação (\\t) — compatível com cola direta no sistema ANM.

    Parâmetros
    ----------
    vertices       : [(lon, lat), ...] em EPSG:4674
    output_path    : caminho do arquivo .txt
    include_header : inclui linha de cabeçalho
    """
    if not output_path.lower().endswith(('.txt', '.csv')):
        output_path += '.txt'

    pts = list(vertices)
    if len(pts) > 1 and pts[0] == pts[-1]:
        pts = pts[:-1]

    lines = []
    if include_header:
        lines.append('Vértice\tLatitude\tLongitude')

    for i, (lon, lat) in enumerate(pts, start=1):
        lat_dms = decimal_to_dms_anm(lat)
        lon_dms = decimal_to_dms_anm(lon)
        lines.append(f'{i}\t{lat_dms}\t{lon_dms}')

    # Fechamento explícito: último vértice = primeiro ponto, numerado N+1
    # Ex.: retângulo → 4 vértices únicos + vértice 5 (igual ao 1) = 5 linhas
    if pts:
        lon0, lat0 = pts[0]
        closing_n  = len(pts) + 1
        lines.append(f'{closing_n}\t{decimal_to_dms_anm(lat0)}\t{decimal_to_dms_anm(lon0)}')

    with open(output_path, 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(lines))
        fh.write('\n')

    return True


# ---------------------------------------------------------------------------
# Carregamento no canvas
# ---------------------------------------------------------------------------

def load_layer_to_canvas(path: str, layer_name: str) -> Optional[QgsVectorLayer]:
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
    Pipeline de dois estágios para tratar sobreposição com restrições:

    Estágio 1 — Recorte:
      Calcula a union de todos os polígonos das camadas de restrição
      (reprojetados para EPSG:4674), depois aplica difference:
        resultado = anm_geom.difference(union_restricoes)
      Se resultar em MultiPolygon, cada componente é tratado separadamente.

    Estágio 2 — Reortogonalização:
      Cada componente do difference é usado como novo esboço de entrada
      no ANMPolygonProcessor, gerando polígono com bordas estritamente
      N-S e L-O.

    NOTA IMPORTANTE:
      As bordas geradas pelo recorte não são ortogonais. Após a
      reortogonalização, a área resultante pode diferir levemente da
      área exata do recorte — esse é o comportamento correto e esperado,
      pois a regra ANM de rumos verdadeiros tem precedência.

    Parâmetros
    ----------
    anm_geom           : polígono ANM já processado (em EPSG:4674)
    restriction_layers : lista de QgsVectorLayer com as restrições
    n_steps            : dentes por segmento (repassado ao processador)
    first_direction    : direção do 1º passo (repassado ao processador)
    snap_vertices      : snap vertices opcionais (repassados ao processador)

    Retorna lista de dicts ordenada por área DECRESCENTE:
      [{'geom': QgsGeometry, 'vertices': [...], 'area_ha': float,
        'ortho_errors': [...], 'suffix': '_a'|'_b'|...}, ...]
    """
    ctx = QgsProject.instance().transformContext()

    # --- Estágio 1: union das restrições ---
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
        # Sem restrições válidas — retorna o polígono original intacto
        proc = ANMPolygonProcessor(
            n_steps=n_steps,
            first_direction=first_direction,
            snap_vertices=snap_vertices or [],
            src_crs=CRS_ANM,
        )
        verts = proc.get_vertex_list(anm_geom)
        errs  = proc.validate_orthogonality(anm_geom)
        return [{
            'geom': anm_geom,
            'vertices': verts,
            'area_ha': area_geodesica_ha(anm_geom),
            'ortho_errors': errs,
            'suffix': '',
        }]

    # --- Difference ---
    diff = anm_geom.difference(union_restr)

    if diff is None or diff.isEmpty():
        return []  # Polígono completamente dentro das restrições

    # ---------------------------------------------------------------------------
    # Extração de componentes com tratamento de furos por linha de corte L-O
    # ---------------------------------------------------------------------------

    def _cut_by_lo_line(poly: QgsGeometry, cut_lat: float) -> List[QgsGeometry]:
        """
        Divide poly em dois sólidos usando uma linha L-O na latitude cut_lat.
        """
        bbox = poly.boundingBox()
        margin = max(abs(bbox.width()), abs(bbox.height()), 0.01) * 2.0

        x_min = bbox.xMinimum() - margin
        x_max = bbox.xMaximum() + margin

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
        """Remove todos os furos, retornando apenas os anéis externos."""
        wkb = wkb_flatType(geom.wkbType())
        if wkb == WKB_Polygon:
            raw = geom.asPolygon()
            if raw:
                return QgsGeometry.fromPolygonXY([raw[0]])
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
        """Coleta componentes poligonais sólidos (sem furos)."""
        wkb = wkb_flatType(geom.wkbType())

        if wkb == WKB_Polygon:
            raw = geom.asPolygon()
            if not raw:
                return
            holes = raw[1:]
            if not holes:
                output.append(geom)
                return

            pending = [geom]
            for hole_ring in holes:
                hole_geom = QgsGeometry.fromPolygonXY([hole_ring])
                centroid  = hole_geom.centroid()
                cut_lat   = centroid.asPoint().y()

                next_pending = []
                for poly_piece in pending:
                    cut_results = _cut_by_lo_line(poly_piece, cut_lat)
                    next_pending.extend(cut_results)
                pending = next_pending

            for piece in pending:
                if piece and not piece.isEmpty():
                    output.append(piece)

        elif wkb == WKB_MultiPolygon:
            for ring_list in geom.asMultiPolygon():
                sub = QgsGeometry.fromPolygonXY(ring_list)
                _collect_solid(sub, output)

        elif wkb == WKB_GeometryCollection:
            n = geom.constGet().numGeometries()
            for i in range(n):
                pg = QgsGeometry(geom.constGet().geometryN(i).clone())
                _collect_solid(pg, output)

    # Coleta todos os componentes sólidos
    parts: List[QgsGeometry] = []
    _collect_solid(diff, parts)

    if not parts:
        return []

    # --- Estágio 2: reortogonalização de cada componente ---
    results = []
    for part in parts:
        if part.isEmpty():
            continue
        try:
            proc = ANMPolygonProcessor(
                n_steps=n_steps,
                first_direction=first_direction,
                snap_vertices=snap_vertices or [],
                src_crs=CRS_ANM,
            )
            reortho = proc.process(part)
            verts   = proc.get_vertex_list(reortho)
            errs    = proc.validate_orthogonality(reortho)
            results.append({
                'geom': reortho,
                'vertices': verts,
                'area_ha': area_geodesica_ha(reortho),
                'ortho_errors': errs,
                'suffix': '',
            })
        except Exception as e:
            warnings.warn(f'[ANM] Erro na reortogonalização de componente: {e}')

    if not results:
        return []

    # --- Ordena por área decrescente e atribui sufixos _a, _b, _c... ---
    results.sort(key=lambda r: r['area_ha'], reverse=True)
    suffixes = [chr(ord('a') + i) for i in range(len(results))]
    for r, suf in zip(results, suffixes):
        r['suffix'] = f'_{suf}' if len(results) > 1 else ''

    return results
