# -*- coding: utf-8 -*-
"""
Classe principal do plugin ANM Poligonal.
"""

import os
from qgis.PyQt.QtWidgets import QAction, QMessageBox
from qgis.PyQt.QtGui import QIcon
from qgis.PyQt.QtCore import Qt
from qgis.core import QgsProject, QgsVectorLayer

from .ui.dialog_main import ANMPoligonalDialog


class ANMPoligonalPlugin:
    """Plugin principal para geração de polígonos ANM."""

    def __init__(self, iface):
        self.iface = iface
        self.plugin_dir = os.path.dirname(__file__)
        self.action = None
        self.dialog = None

    def initGui(self):
        """Inicializa a interface gráfica do plugin."""
        icon_path = os.path.join(self.plugin_dir, 'icons', 'anm_icon.png')
        
        self.action = QAction(
            QIcon(icon_path),
            'ANM Poligonal',
            self.iface.mainWindow()
        )
        self.action.setToolTip(
            'Gerar polígono ANM em rumos verdadeiros (N-S / L-O)'
        )
        self.action.triggered.connect(self.run)

        # Adiciona ao menu Vetor e à barra de ferramentas
        self.iface.addPluginToVectorMenu('&ANM Poligonal', self.action)
        self.iface.addToolBarIcon(self.action)

    def unload(self):
        """Remove o plugin da interface."""
        self.iface.removePluginVectorMenu('&ANM Poligonal', self.action)
        self.iface.removeToolBarIcon(self.action)
        if self.dialog:
            self.dialog.close()

    def run(self):
        """Executa o plugin — abre o diálogo principal."""
        if self.dialog is None:
            self.dialog = ANMPoligonalDialog(self.iface)
        self.dialog.populate_layers()
        self.dialog.show()
        self.dialog.raise_()
        self.dialog.activateWindow()
