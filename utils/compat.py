# -*- coding: utf-8 -*-
"""
Camada de compatibilidade Qt5/Qt6 + QGIS 3.x/4.0.

Centraliza TODOS os shims de enums que mudaram de namespace entre
PyQt5 (QGIS 3.x) e PyQt6 (QGIS 4.0+).

Uso nos demais módulos:
    from ..utils.compat import SP_Expanding, SP_Fixed, ...

Princípio: tenta o nome Qt6 primeiro (namespaceado);
se falhar, cai no nome Qt5 (flat).
"""

# ---- PyQt ----
from qgis.PyQt.QtWidgets import QSizePolicy, QFrame
from qgis.PyQt.QtCore import Qt
from qgis.PyQt.QtGui import QCursor

# ---------------------------------------------------------------------------
# QSizePolicy.Policy  (Qt6)  vs  QSizePolicy  (Qt5)
# ---------------------------------------------------------------------------
try:
    SP_Expanding  = QSizePolicy.Policy.Expanding
    SP_Fixed      = QSizePolicy.Policy.Fixed
    SP_Preferred  = QSizePolicy.Policy.Preferred
    SP_Minimum    = QSizePolicy.Policy.Minimum
    SP_Maximum    = QSizePolicy.Policy.Maximum
except AttributeError:
    SP_Expanding  = QSizePolicy.Expanding
    SP_Fixed      = QSizePolicy.Fixed
    SP_Preferred  = QSizePolicy.Preferred
    SP_Minimum    = QSizePolicy.Minimum
    SP_Maximum    = QSizePolicy.Maximum

# ---------------------------------------------------------------------------
# QFrame.Shape  (Qt6)  vs  QFrame  (Qt5)
# ---------------------------------------------------------------------------
try:
    Frame_HLine = QFrame.Shape.HLine
    Frame_VLine = QFrame.Shape.VLine
except AttributeError:
    Frame_HLine = QFrame.HLine
    Frame_VLine = QFrame.VLine

# ---------------------------------------------------------------------------
# Qt.ScrollBarPolicy  (Qt6)  vs  Qt  (Qt5)
# ---------------------------------------------------------------------------
try:
    SB_AlwaysOff  = Qt.ScrollBarPolicy.ScrollBarAlwaysOff
    SB_AsNeeded   = Qt.ScrollBarPolicy.ScrollBarAsNeeded
    SB_AlwaysOn   = Qt.ScrollBarPolicy.ScrollBarAlwaysOn
except AttributeError:
    SB_AlwaysOff  = Qt.ScrollBarAlwaysOff
    SB_AsNeeded   = Qt.ScrollBarAsNeeded
    SB_AlwaysOn   = Qt.ScrollBarAlwaysOn

# ---------------------------------------------------------------------------
# Qt.TextInteractionFlag  (Qt6)  vs  Qt  (Qt5)
# ---------------------------------------------------------------------------
try:
    TI_SelectableByMouse = Qt.TextInteractionFlag.TextSelectableByMouse
except AttributeError:
    TI_SelectableByMouse = Qt.TextSelectableByMouse

# ---------------------------------------------------------------------------
# Qt.MouseButton  (Qt6)  vs  Qt  (Qt5)
# ---------------------------------------------------------------------------
try:
    MB_Left  = Qt.MouseButton.LeftButton
    MB_Right = Qt.MouseButton.RightButton
except AttributeError:
    MB_Left  = Qt.LeftButton
    MB_Right = Qt.RightButton

# ---------------------------------------------------------------------------
# Qt.CursorShape  (Qt6)  vs  Qt  (Qt5)
# ---------------------------------------------------------------------------
try:
    CS_Cross = Qt.CursorShape.CrossCursor
except AttributeError:
    CS_Cross = Qt.CrossCursor

# ---------------------------------------------------------------------------
# Qt.PenStyle  (Qt6)  vs  Qt  (Qt5)
# ---------------------------------------------------------------------------
try:
    PS_DashLine = Qt.PenStyle.DashLine
except AttributeError:
    PS_DashLine = Qt.DashLine

# ---------------------------------------------------------------------------
# Qt.Key  (Qt6)  vs  Qt  (Qt5)
# ---------------------------------------------------------------------------
try:
    Key_Escape = Qt.Key.Key_Escape
    Key_Return = Qt.Key.Key_Return
    Key_Enter  = Qt.Key.Key_Enter
except AttributeError:
    Key_Escape = Qt.Key_Escape
    Key_Return = Qt.Key_Return
    Key_Enter  = Qt.Key_Enter

# ---------------------------------------------------------------------------
# QgsWkbTypes  →  Qgis  (QGIS 4.0 migrou enums para a classe Qgis)
# ---------------------------------------------------------------------------
try:
    from qgis.core import Qgis
    # Tipo de geometria (usado em geometryType())
    _geom_polygon = Qgis.GeometryType.Polygon
    _geom_line    = Qgis.GeometryType.Line
    _geom_point   = Qgis.GeometryType.Point
except (ImportError, AttributeError):
    from qgis.core import QgsWkbTypes as _Wkb
    _geom_polygon = _Wkb.PolygonGeometry
    _geom_line    = _Wkb.LineGeometry
    _geom_point   = _Wkb.PointGeometry

GeomType_Polygon = _geom_polygon
GeomType_Line    = _geom_line
GeomType_Point   = _geom_point

# WKB type IDs (usados com flatType e construtores de geometria)
from qgis.core import QgsWkbTypes
try:
    from qgis.core import Qgis as _Q
    WKB_Polygon            = _Q.WkbType.Polygon
    WKB_MultiPolygon       = _Q.WkbType.MultiPolygon
    WKB_GeometryCollection = _Q.WkbType.GeometryCollection
    WKB_LineString         = _Q.WkbType.LineString
except (ImportError, AttributeError):
    WKB_Polygon            = QgsWkbTypes.Polygon
    WKB_MultiPolygon       = QgsWkbTypes.MultiPolygon
    WKB_GeometryCollection = QgsWkbTypes.GeometryCollection
    WKB_LineString         = QgsWkbTypes.LineString

# flatType — a função em si permanece em QgsWkbTypes em ambas versões
wkb_flatType = QgsWkbTypes.flatType

# displayString
try:
    wkb_displayString = QgsWkbTypes.displayString
except AttributeError:
    wkb_displayString = lambda t: str(t)

# ---------------------------------------------------------------------------
# QgsVectorFileWriter.WriterError  (QGIS 4.0)  vs  QgsVectorFileWriter  (3.x)
# ---------------------------------------------------------------------------
from qgis.core import QgsVectorFileWriter
try:
    VFW_NoError = QgsVectorFileWriter.WriterError.NoError
except AttributeError:
    VFW_NoError = QgsVectorFileWriter.NoError

# ---------------------------------------------------------------------------
# QgsVertexMarker.IconType  (QGIS 4.0)  vs  QgsVertexMarker  (3.x)
# ---------------------------------------------------------------------------
from qgis.gui import QgsVertexMarker
try:
    VM_ICON_CIRCLE = QgsVertexMarker.IconType.ICON_CIRCLE
except AttributeError:
    VM_ICON_CIRCLE = QgsVertexMarker.ICON_CIRCLE

# ---------------------------------------------------------------------------
# Utilitário: cursor cross compatível
# ---------------------------------------------------------------------------
def cross_cursor():
    """Retorna QCursor com CrossCursor, compatível com Qt5 e Qt6."""
    return QCursor(CS_Cross)
