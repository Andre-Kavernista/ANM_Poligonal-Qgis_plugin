# -*- coding: utf-8 -*-
"""
ANM Poligonal Plugin
Plugin QGIS para geração de polígonos em rumos verdadeiros conforme normas ANM.
"""

def classFactory(iface):
    from .plugin import ANMPoligonalPlugin
    return ANMPoligonalPlugin(iface)
