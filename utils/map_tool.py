# -*- coding: utf-8 -*-
"""
Ferramentas de mapa (MapTools) e auxiliares visuais para o plugin ANM Poligonal.

Classes:
  DrawPolygonMapTool   — captura interativa de polígono (rubber band clique-a-clique)
  SnapCaptureMapTool   — captura de snap vertices pontuais sobre esboço existente
  SketchHighlighter    — rubber band de destaque do polígono ANM gerado
  OverlapHighlighter   — rubber bands de destaque de sobreposições com restrições

Compatibilidade: QGIS 3.22+ e QGIS 4.0+ (Qt5/Qt6).
"""

from typing import List, Tuple, Optional

from qgis.PyQt.QtCore import Qt, pyqtSignal
from qgis.PyQt.QtGui import QColor, QCursor

from qgis.core import (
    QgsPointXY,
    QgsGeometry,
    QgsWkbTypes,
    QgsVectorLayer,
    QgsFeature,
    QgsField,
    QgsFields,
    QgsProject,
    QgsCoordinateTransform,
    QgsCoordinateReferenceSystem,
    QgsMemoryProviderUtils,
)
from qgis.gui import (
    QgsMapTool,
    QgsMapCanvas,
    QgsRubberBand,
    QgsVertexMarker,
)
from qgis.PyQt.QtCore import QVariant

from .compat import (
    MB_Left,
    MB_Right,
    CS_Cross,
    PS_DashLine,
    Key_Escape,
    Key_Return,
    Key_Enter,
    GeomType_Polygon,
    GeomType_Line,
    VM_ICON_CIRCLE,
    cross_cursor,
)


Point = Tuple[float, float]
CRS_ANM = QgsCoordinateReferenceSystem('EPSG:4674')


# ---------------------------------------------------------------------------
# DrawPolygonMapTool — desenho interativo de polígono no canvas
# ---------------------------------------------------------------------------

class DrawPolygonMapTool(QgsMapTool):
    """
    MapTool para desenho interativo de polígono esboço diretamente no canvas.

    Comportamento:
      - Clique esquerdo: adiciona vértice
      - Movimento do mouse: mostra aresta dinâmica (rubber band preview)
      - Duplo clique esquerdo: fecha o polígono e emite `polygon_drawn`
      - Botão direito: fecha o polígono (mín. 3 vértices) ou cancela se sem vértices
      - Enter: fecha o polígono (mín. 3 vértices)
      - ESC: cancela e emite `drawing_cancelled`
      - Mínimo de 3 vértices para fechar

    Sinais:
      polygon_drawn(QgsGeometry)   — polígono fechado nas coordenadas do mapa
      drawing_cancelled()          — usuário cancelou com ESC
    """

    polygon_drawn    = pyqtSignal(object)   # QgsGeometry
    drawing_cancelled = pyqtSignal()

    def __init__(self, canvas: QgsMapCanvas):
        super().__init__(canvas)
        self.canvas = canvas
        self._points: List[QgsPointXY] = []
        self._last_click_was_double = False

        # Rubber band do polígono em construção
        self._band = QgsRubberBand(canvas, GeomType_Polygon)
        self._band.setColor(QColor(255, 100, 0, 160))   # laranja translúcido
        self._band.setFillColor(QColor(255, 150, 0, 40))
        self._band.setWidth(2)

        # Rubber band da aresta dinâmica (último ponto → cursor)
        self._edge_band = QgsRubberBand(canvas, GeomType_Line)
        self._edge_band.setColor(QColor(255, 100, 0, 200))
        self._edge_band.setWidth(1)
        self._edge_band.setLineStyle(PS_DashLine)

        self.setCursor(cross_cursor())

    # ------------------------------------------------------------------
    # Eventos do canvas
    # ------------------------------------------------------------------

    def canvasPressEvent(self, event):
        """Registra o clique mas aguarda release para distinguir duplo clique."""
        pass

    def canvasReleaseEvent(self, event):
        if self._last_click_was_double:
            self._last_click_was_double = False
            return

        if event.button() == MB_Left:
            pt = self._snapped(event)
            self._points.append(pt)
            self._update_band()

        elif event.button() == MB_Right:
            # Comportamento padrão do QGIS: botão direito fecha o polígono
            # se há vértices suficientes, ou cancela se ainda não iniciou.
            if len(self._points) >= 3:
                self._close_polygon()
            else:
                self._cancel()

    def canvasDoubleClickEvent(self, event):
        """Duplo clique esquerdo: fecha o polígono."""
        self._last_click_was_double = True
        if event.button() == MB_Left:
            pt = self._snapped(event)
            self._points.append(pt)
            self._close_polygon()

    def canvasMoveEvent(self, event):
        """Atualiza aresta dinâmica enquanto o mouse se move."""
        if not self._points:
            return
        pt = self._snapped(event)
        self._edge_band.reset(GeomType_Line)
        self._edge_band.addPoint(self._points[-1])
        self._edge_band.addPoint(pt)
        # Fecha visualmente até o primeiro ponto
        if len(self._points) >= 2:
            self._edge_band.addPoint(self._points[0])

    def keyPressEvent(self, event):
        if event.key() == Key_Escape:
            self._cancel()
        elif event.key() == Key_Return or event.key() == Key_Enter:
            if len(self._points) >= 3:
                self._close_polygon()

    # ------------------------------------------------------------------
    # Controle interno
    # ------------------------------------------------------------------

    def _snapped(self, event) -> QgsPointXY:
        match = self.canvas.snappingUtils().snapToMap(event.pos())
        if match.isValid():
            return match.point()
        return self.toMapCoordinates(event.pos())

    def _update_band(self):
        self._band.reset(GeomType_Polygon)
        for pt in self._points:
            self._band.addPoint(pt, False)
        if self._points:
            self._band.addPoint(self._points[0], True)  # fecha visualmente

    def _close_polygon(self):
        if len(self._points) < 3:
            return

        geom = QgsGeometry.fromPolygonXY([self._points])
        self._clear_bands()
        self.polygon_drawn.emit(geom)

    def _cancel(self):
        self._clear_bands()
        self._points.clear()
        self.drawing_cancelled.emit()

    def _clear_bands(self):
        self._band.reset(GeomType_Polygon)
        self._edge_band.reset(GeomType_Line)

    def deactivate(self):
        self._clear_bands()
        super().deactivate()

    def reset(self):
        """Reinicia a ferramenta para novo desenho."""
        self._points.clear()
        self._last_click_was_double = False
        self._clear_bands()


# ---------------------------------------------------------------------------
# Helpers — memory layer para esboço desenhado
# ---------------------------------------------------------------------------

def create_sketch_memory_layer(geom: QgsGeometry,
                                canvas_crs: QgsCoordinateReferenceSystem
                                ) -> QgsVectorLayer:
    """
    Cria uma memory layer temporária com o esboço desenhado.
    A geometria é armazenada no CRS do canvas (reprojeção para EPSG:4674
    é feita pelo processador ANM normalmente).

    Retorna a layer (não adicionada ao projeto — o caller decide se adiciona).
    """
    uri = f'Polygon?crs={canvas_crs.authid()}'
    layer = QgsVectorLayer(uri, 'Esboço ANM (temporário)', 'memory')
    layer.startEditing()
    feat = QgsFeature()
    feat.setGeometry(geom)
    layer.addFeature(feat)
    layer.commitChanges()
    return layer


# ---------------------------------------------------------------------------
# SnapCaptureMapTool — captura de snap vertices pontuais
# ---------------------------------------------------------------------------

class SnapCaptureMapTool(QgsMapTool):
    """
    MapTool para captura interativa de snap vertices sobre esboço existente.
    Clique esquerdo → captura ponto | Botão direito / ESC → encerra.
    """

    vertex_captured = pyqtSignal(float, float)
    finished        = pyqtSignal()

    def __init__(self, canvas: QgsMapCanvas):
        super().__init__(canvas)
        self.canvas = canvas
        self._markers: List[QgsVertexMarker] = []
        self.setCursor(cross_cursor())

    def canvasReleaseEvent(self, event):
        if event.button() == MB_Left:
            pt = self._snapped(event)
            self._markers.append(self._add_marker(pt))
            self.vertex_captured.emit(pt.x(), pt.y())
        elif event.button() == MB_Right:
            self.finished.emit()

    def keyPressEvent(self, event):
        if event.key() == Key_Escape:
            self.finished.emit()

    def _snapped(self, event) -> QgsPointXY:
        match = self.canvas.snappingUtils().snapToMap(event.pos())
        if match.isValid():
            return match.point()
        return self.toMapCoordinates(event.pos())

    def _add_marker(self, point: QgsPointXY) -> QgsVertexMarker:
        m = QgsVertexMarker(self.canvas)
        m.setCenter(point)
        m.setColor(QColor(255, 165, 0))
        m.setIconSize(10)
        m.setIconType(VM_ICON_CIRCLE)
        m.setPenWidth(2)
        return m

    def clear_markers(self):
        for m in self._markers:
            self.canvas.scene().removeItem(m)
        self._markers.clear()

    def deactivate(self):
        super().deactivate()


# ---------------------------------------------------------------------------
# SketchHighlighter — destaque do polígono ANM gerado
# ---------------------------------------------------------------------------

class SketchHighlighter:
    """Rubber band sobre o polígono ANM gerado (magenta)."""

    def __init__(self, canvas: QgsMapCanvas):
        self.canvas = canvas
        self._band: Optional[QgsRubberBand] = None

    def highlight(self, geom: QgsGeometry):
        self.clear()
        self._band = QgsRubberBand(self.canvas, GeomType_Polygon)
        self._band.setColor(QColor(220, 0, 120, 220))
        self._band.setFillColor(QColor(220, 0, 120, 30))
        self._band.setWidth(2)
        self._band.setToGeometry(geom, None)

    def clear(self):
        if self._band:
            self.canvas.scene().removeItem(self._band)
            self._band = None


# ---------------------------------------------------------------------------
# OverlapHighlighter — destaque das áreas de sobreposição com restrições
# ---------------------------------------------------------------------------

class OverlapHighlighter:
    """
    Gerencia rubber bands de sobreposição entre o polígono ANM e camadas
    de restrição. Cada sobreposição é destacada em vermelho translúcido.
    """

    def __init__(self, canvas: QgsMapCanvas):
        self.canvas = canvas
        self._bands: List[QgsRubberBand] = []

    def show_overlaps(self, overlap_geoms: List[QgsGeometry]):
        """Exibe cada geometria de sobreposição com rubber band vermelho."""
        self.clear()
        for geom in overlap_geoms:
            band = QgsRubberBand(self.canvas, GeomType_Polygon)
            band.setColor(QColor(200, 0, 0, 240))
            band.setFillColor(QColor(255, 0, 0, 80))
            band.setWidth(2)
            band.setToGeometry(geom, None)
            self._bands.append(band)

    def clear(self):
        for b in self._bands:
            self.canvas.scene().removeItem(b)
        self._bands.clear()
