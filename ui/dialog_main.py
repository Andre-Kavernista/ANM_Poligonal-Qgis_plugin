# -*- coding: utf-8 -*-
"""
Diálogo principal — ANM Poligonal v1.0.0
Compatível com QGIS 3.22+ e QGIS 4.0+ (Qt5/Qt6).

"""

import os
from typing import Optional, List, Tuple, Dict

from qgis.PyQt.QtWidgets import (
    QDialog, QVBoxLayout, QHBoxLayout, QGridLayout,
    QLabel, QComboBox, QSpinBox, QPushButton,
    QLineEdit, QFileDialog, QCheckBox, QGroupBox,
    QTextEdit, QSizePolicy, QMessageBox, QProgressBar,
    QTabWidget, QWidget, QFrame, QScrollArea,
    QRadioButton, QButtonGroup,
)
from qgis.PyQt.QtCore import Qt, QSettings
from qgis.PyQt.QtGui import QColor

from ..utils.compat import (
    SP_Expanding,
    SP_Fixed,
    Frame_HLine,
    SB_AlwaysOff,
    SB_AsNeeded,
    TI_SelectableByMouse,
    GeomType_Polygon,
)

from qgis.core import (
    QgsProject,
    QgsVectorLayer,
    QgsWkbTypes,
    QgsFeature,
    QgsGeometry,
    QgsCoordinateReferenceSystem,
    QgsFeatureRequest,
)
from qgis.gui import QgsMapCanvas

from ..core.processor import (
    ANMPolygonProcessor,
    clip_and_reortogonalize,
    export_shapefile,
    export_txt_anm,
    export_csv_anm,
    load_layer_to_canvas,
    area_geodesica_ha,
    decimal_to_dms_anm,
    decimal_to_dms_components,
    CRS_ANM,
)
from ..utils.map_tool import (
    DrawPolygonMapTool,
    SnapCaptureMapTool,
    SketchHighlighter,
    OverlapHighlighter,
    create_sketch_memory_layer,
)

Point = Tuple[float, float]
MAX_POLY          = 999
MAX_RESTR_TOTAL   = 50   # limite absoluto de camadas de restrição
RESTR_BLOCK_SIZE  = 5    # quantas linhas adicionadas por clique

# ---------------------------------------------------------------------------
# Paleta e estilos
# ---------------------------------------------------------------------------
C = {
    'primary':    '#1B4F72',
    'secondary':  '#2E86C1',
    'accent':     '#D35400',
    'success':    '#1E8449',
    'danger':     '#C0392B',
    'warning':    '#7D6608',
    'bg':         '#F0F3F4',
    'border':     '#AAB7B8',
    'text':       '#17202A',
    'text_muted': '#626567',
    'sel_bg':     '#1A5276',
    'sel_fg':     '#FFFFFF',
    'info_bg':    '#D6EAF8',
    'info_bd':    '#2E86C1',
    'warn_bg':    '#FEF9E7',
    'warn_bd':    '#D4AC0D',
}

STYLE = f"""
QDialog {{
    background: {C['bg']};
    font-family: 'Segoe UI', Arial, sans-serif;
    font-size: 12px;
    color: {C['text']};
}}
QComboBox {{
    border: 1.5px solid {C['border']};
    border-radius: 4px;
    padding: 3px 8px;
    background: white;
    min-height: 24px;
    color: {C['text']};
}}
QComboBox:focus {{ border-color: {C['secondary']}; }}
QComboBox QAbstractItemView {{
    background: white;
    color: {C['text']};
    selection-background-color: {C['sel_bg']};
    selection-color: {C['sel_fg']};
    outline: none;
}}
QComboBox QAbstractItemView::item {{
    padding: 4px 8px; min-height: 22px;
}}
QComboBox QAbstractItemView::item:selected {{
    background: {C['sel_bg']}; color: {C['sel_fg']}; font-weight: bold;
}}
QComboBox QAbstractItemView::item:hover {{
    background: #AED6F1; color: {C['text']};
}}
QLineEdit, QSpinBox {{
    border: 1.5px solid {C['border']};
    border-radius: 4px; padding: 3px 8px;
    background: white; min-height: 24px; color: {C['text']};
}}
QLineEdit:focus, QSpinBox:focus {{ border-color: {C['secondary']}; }}
QPushButton {{
    background: {C['primary']}; color: white; border: none;
    border-radius: 4px; padding: 6px 14px; font-weight: bold; min-height: 26px;
}}
QPushButton:hover  {{ background: {C['secondary']}; }}
QPushButton:pressed {{ background: #154360; }}
QPushButton:disabled {{ background: {C['border']}; color: #ECF0F1; }}
QGroupBox {{
    border: 1.5px solid {C['border']}; border-radius: 5px;
    margin-top: 10px; padding-top: 6px;
    font-weight: bold; color: {C['primary']};
}}
QGroupBox::title {{ subcontrol-origin: margin; left: 10px; padding: 0 4px; }}
QTextEdit {{
    border: 1px solid {C['border']}; border-radius: 4px;
    background: white; font-family: 'Consolas','Courier New',monospace;
    font-size: 11px; color: {C['text']};
}}
QProgressBar {{
    border: 1px solid {C['border']}; border-radius: 3px;
    text-align: center; max-height: 16px; color: {C['text']};
}}
QProgressBar::chunk {{ background: {C['secondary']}; border-radius: 2px; }}
QTabWidget::pane {{ border: 1px solid {C['border']}; border-radius: 4px; }}
QTabBar::tab {{
    background: #D5D8DC; color: {C['text']};
    padding: 5px 12px; border-top-left-radius: 4px;
    border-top-right-radius: 4px; margin-right: 2px;
}}
QTabBar::tab:selected {{ background: {C['primary']}; color: white; font-weight: bold; }}
QTabBar::tab:hover {{ background: #AEB6BF; }}
QRadioButton, QCheckBox {{ color: {C['text']}; spacing: 6px; }}
QScrollArea {{ border: none; background: {C['bg']}; }}
"""


def _style_btn(btn: QPushButton, bg: str, hover: str) -> None:
    btn.setStyleSheet(
        f'QPushButton {{ background:{bg}; color:white; font-weight:bold; '
        f'border:none; border-radius:4px; padding:6px 14px; min-height:26px; }}'
        f'QPushButton:hover {{ background:{hover}; }}'
        f'QPushButton:pressed {{ background:{bg}; }}'
        f'QPushButton:disabled {{ background:#AAB7B8; color:#ECF0F1; }}'
    )


def _banner(text: str, bg: str, bd: str) -> QLabel:
    lbl = QLabel(text)
    lbl.setWordWrap(True)
    lbl.setStyleSheet(
        f'background:{bg}; border:1px solid {bd}; border-radius:4px; '
        f'padding:7px; color:{C["primary"]}; font-size:11px;'
    )
    return lbl


def _read_plugin_version() -> str:
    """Lê a versão do metadata.txt em tempo de execução."""
    try:
        import configparser, os as _os
        _meta = configparser.ConfigParser()
        _meta_path = _os.path.join(_os.path.dirname(_os.path.dirname(__file__)), 'metadata.txt')
        _meta.read(_meta_path, encoding='utf-8')
        return _meta.get('general', 'version', fallback='?')
    except Exception:
        return '?'


def _all_polygon_layers() -> List[QgsVectorLayer]:
    """Retorna todas as camadas de polígono do projeto."""
    return [
        l for l in QgsProject.instance().mapLayers().values()
        if isinstance(l, QgsVectorLayer)
        and l.geometryType() == GeomType_Polygon
    ]


# ---------------------------------------------------------------------------
# Diálogo principal
# ---------------------------------------------------------------------------

class ANMPoligonalDialog(QDialog):

    def __init__(self, iface, parent=None):
        super().__init__(parent or iface.mainWindow())
        self.iface  = iface
        self.canvas: QgsMapCanvas = iface.mapCanvas()

        self._snap_tool: Optional[SnapCaptureMapTool] = None
        self._draw_tool: Optional[DrawPolygonMapTool]  = None
        self._prev_tool = None

        self._snap_vertices: List[Point] = []
        self._drawn_geom:  Optional[QgsGeometry]   = None
        self._drawn_layer: Optional[QgsVectorLayer] = None

        self._results:       List[Dict] = []
        self._final_results: List[Dict] = []

        self._highlighter = SketchHighlighter(self.canvas)
        self._overlap_hl  = OverlapHighlighter(self.canvas)

        # Linhas de restrição: lista de (QCheckBox, QComboBox)
        self._restr_rows: List[Tuple[QCheckBox, QComboBox]] = []
        # Layout interno da grade de restrições (preenchido em _tab_restrictions)
        self._restr_grid_layout: Optional[QVBoxLayout] = None

        # Lê versão do metadata uma única vez e reutiliza no título e cabeçalho
        self._plugin_version = _read_plugin_version()

        self.setWindowTitle(f'ANM Poligonal — Rumos Verdadeiros EPSG:4674 | v{self._plugin_version}')
        self.setMinimumWidth(840)
        self.setMaximumWidth(1020)
        self.setMinimumHeight(540)
        self.setMaximumHeight(660)
        self.setStyleSheet(STYLE)

        self._build_ui()
        self._connect_signals()
        self._restore_settings()

    # -----------------------------------------------------------------------
    # UI raiz
    # -----------------------------------------------------------------------

    def _build_ui(self):
        root = QVBoxLayout(self)
        root.setContentsMargins(12, 10, 12, 10)
        root.setSpacing(8)

        hdr = QHBoxLayout()

        # Lê versão diretamente do metadata.txt para nunca ficar desatualizada
        _version = self._plugin_version

        # Bloco de identidade (título + autoria)
        identity = QVBoxLayout()
        identity.setSpacing(1)

        t = QLabel('⬡ <b>ANM Poligonal</b>')
        t.setStyleSheet(f'font-size:15px; color:{C["primary"]};')

        autor = QLabel('André Cunha de Souza')
        autor.setStyleSheet(
            f'font-size:11px; color:{C["secondary"]}; '
            f'font-family: "Segoe UI", Arial, sans-serif; '
            f'letter-spacing: 0.2px;'
        )
        autor.setTextInteractionFlags(TI_SelectableByMouse)

        crea = QLabel('Geólogo (CREA 29753/D-DF)')
        crea.setStyleSheet(
            f'font-size:10px; color:{C["secondary"]}; '
            f'font-family: "Segoe UI", Arial, sans-serif; '
            f'letter-spacing: 0.2px;'
        )
        crea.setTextInteractionFlags(TI_SelectableByMouse)

        feedback = QLabel('Envie seu feedback para andre.kavernista@gmail.com')
        feedback.setStyleSheet(
            f'font-size:10px; color:{C["secondary"]}; '
            f'font-family: "Segoe UI", Arial, sans-serif; '
            f'letter-spacing: 0.2px;'
        )
        feedback.setTextInteractionFlags(TI_SelectableByMouse)

        identity.addWidget(t)
        identity.addWidget(autor)
        identity.addWidget(crea)
        identity.addWidget(feedback)

        s = QLabel(f'EPSG:4674 — v{_version}')
        s.setStyleSheet(f'color:{C["text_muted"]}; font-size:11px;')

        btn_recenter = QPushButton('⊕')
        btn_recenter.setMaximumWidth(28)
        btn_recenter.setMaximumHeight(24)
        btn_recenter.setToolTip('Recentrar janela na tela')
        btn_recenter.setStyleSheet(
            f'QPushButton {{ background:transparent; color:{C["text_muted"]}; '
            f'border:1px solid {C["border"]}; border-radius:3px; font-size:14px; }}'
            f'QPushButton:hover {{ background:{C["border"]}; color:{C["text"]}; }}'
        )
        btn_recenter.clicked.connect(self._center_on_parent)

        hdr.addLayout(identity)
        hdr.addStretch()
        hdr.addWidget(s)
        hdr.addSpacing(8); hdr.addWidget(btn_recenter)
        root.addLayout(hdr)

        sep = QFrame(); sep.setFrameShape(Frame_HLine)
        sep.setStyleSheet(f'color:{C["border"]};')
        root.addWidget(sep)

        self.tabs = QTabWidget()
        self.tabs.setSizePolicy(SP_Expanding, SP_Expanding)
        root.addWidget(self.tabs, stretch=1)

        self.tabs.addTab(self._tab_config(),       '⚙  Configuração')
        self.tabs.addTab(self._tab_draw(),         '✏  Desenhar Esboço')
        self.tabs.addTab(self._tab_snap(),         '📍 Snap Vertices')
        self.tabs.addTab(self._tab_restrictions(), '🚫 Restrições')
        self.tabs.addTab(self._tab_log(),          '📋 Log / Vértices')

        self.progress = QProgressBar()
        self.progress.setVisible(False)
        root.addWidget(self.progress)

        # Barra inferior fixa
        bot = QFrame()
        bot.setStyleSheet(f'background:{C["bg"]}; border-top:1px solid {C["border"]};')
        bl = QHBoxLayout(bot); bl.setContentsMargins(0,6,0,0); bl.setSpacing(8)

        self.btn_preview  = QPushButton('👁  Pré-visualizar')
        self.btn_generate = QPushButton('⬇  Gerar Arquivos')
        self.btn_close    = QPushButton('✖  Fechar')
        _style_btn(self.btn_preview,  C['accent'],  '#E67E22')
        _style_btn(self.btn_generate, C['success'], '#27AE60')
        _style_btn(self.btn_close,    C['danger'],  '#E74C3C')

        self.lbl_status = QLabel('Aguardando configuração...')
        self.lbl_status.setStyleSheet(f'color:{C["text_muted"]}; font-size:11px;')

        bl.addWidget(self.btn_preview); bl.addWidget(self.btn_generate)
        bl.addSpacing(10); bl.addWidget(self.lbl_status, stretch=1)
        bl.addWidget(self.btn_close)
        root.addWidget(bot)

    # -----------------------------------------------------------------------
    # Aba 1 — Configuração
    # -----------------------------------------------------------------------

    def _tab_config(self) -> QWidget:
        outer = QWidget(); ol = QVBoxLayout(outer); ol.setContentsMargins(0,0,0,0)
        scroll = QScrollArea(); scroll.setWidgetResizable(True)
        scroll.setHorizontalScrollBarPolicy(SB_AlwaysOff)
        inner = QWidget(); lay = QVBoxLayout(inner)
        lay.setContentsMargins(10,10,10,10); lay.setSpacing(10)

        lay.addWidget(_banner(
            '🔒 <b>SRC de saída: EPSG:4674 — SIRGAS 2000 Geográfico</b>  |  '
            'Segmentos estritamente N-S ou L-O. Reprojeção automática da entrada.',
            C['info_bg'], C['info_bd']
        ))

        # Origem
        grp_src = QGroupBox('Origem do Esboço de Entrada')
        sg = QVBoxLayout(grp_src)
        self.rb_from_layer  = QRadioButton('Usar camada existente no projeto')
        self.rb_from_canvas = QRadioButton('Usar esboço desenhado (aba "✏ Desenhar Esboço")')
        self.rb_from_file   = QRadioButton('Carregar shapefile externo do disco')
        self.rb_from_canvas.setChecked(True)  # padrão: fluxo de desenho direto no canvas
        self._src_group = QButtonGroup()
        self._src_group.addButton(self.rb_from_layer,  0)
        self._src_group.addButton(self.rb_from_canvas, 1)
        self._src_group.addButton(self.rb_from_file,   2)
        sg.addWidget(self.rb_from_layer)
        sg.addWidget(self.rb_from_canvas)
        sg.addWidget(self.rb_from_file)

        # Subpainel camada
        self._pnl_layer = QWidget()
        lg = QGridLayout(self._pnl_layer); lg.setContentsMargins(0,4,0,0)
        lg.setHorizontalSpacing(8); lg.setVerticalSpacing(5)
        lg.addWidget(QLabel('Camada (polígono):'), 0, 0)
        self.cb_layer = QComboBox()
        self.cb_layer.setSizePolicy(SP_Expanding, SP_Fixed)
        lg.addWidget(self.cb_layer, 0, 1, 1, 2)  # ocupa as 2 colunas restantes
        lg.addWidget(QLabel('Polígonos:'), 1, 0)
        rf = QFrame(); rl = QHBoxLayout(rf); rl.setContentsMargins(0,0,0,0); rl.setSpacing(14)
        self.rb_selected = QRadioButton('Somente selecionados')
        self.rb_all      = QRadioButton('Todos'); self.rb_all.setChecked(True)
        self._feat_grp = QButtonGroup()
        self._feat_grp.addButton(self.rb_selected, 0); self._feat_grp.addButton(self.rb_all, 1)
        rl.addWidget(self.rb_selected); rl.addWidget(self.rb_all); rl.addStretch()
        lg.addWidget(rf, 1, 1, 1, 2)
        self.lbl_feat_count = QLabel('')
        self.lbl_feat_count.setStyleSheet(f'color:{C["text_muted"]}; font-size:11px;')
        lg.addWidget(self.lbl_feat_count, 2, 1, 1, 2)
        # _pnl_layer adicionado ao layout mas oculto (canvas é o padrão)
        sg.addWidget(self._pnl_layer); self._pnl_layer.setVisible(False)

        # Subpainel esboço desenhado — visível por padrão (opção marcada)
        self._pnl_canvas = QWidget()
        cl = QHBoxLayout(self._pnl_canvas); cl.setContentsMargins(0,4,0,0)
        self.lbl_drawn_status = QLabel('Nenhum esboço desenhado ainda.')
        self.lbl_drawn_status.setStyleSheet(f'color:{C["text_muted"]}; font-size:11px;')
        btn_go = QPushButton('✏ Ir para Desenhar'); btn_go.setMaximumWidth(180)
        btn_go.clicked.connect(lambda: self.tabs.setCurrentIndex(1))
        cl.addWidget(self.lbl_drawn_status); cl.addWidget(btn_go); cl.addStretch()
        sg.addWidget(self._pnl_canvas); self._pnl_canvas.setVisible(True)

        # Subpainel shapefile externo — oculto por padrão
        self._pnl_file = QWidget()
        fl = QHBoxLayout(self._pnl_file); fl.setContentsMargins(0,4,0,0); fl.setSpacing(6)
        self.le_ext_shp = QLineEdit()
        self.le_ext_shp.setPlaceholderText('Caminho do shapefile de entrada (.shp)...')
        self.le_ext_shp.setSizePolicy(SP_Expanding, SP_Fixed)
        btn_ext = QPushButton('📂 Procurar')
        btn_ext.setMaximumWidth(100)
        btn_ext.clicked.connect(self._browse_ext_shp)
        fl.addWidget(self.le_ext_shp); fl.addWidget(btn_ext)
        sg.addWidget(self._pnl_file); self._pnl_file.setVisible(False)

        # Aviso legal — Portaria DNPM 155/2016
        lbl_portaria = QLabel(
            '⚖ <b>Atenção:</b> Para regimes de aproveitamento mineral, observe os limites '
            'de área impostos na <b>Portaria DNPM Nº 155/2016</b>, artigos 42 a 44.'
        )
        lbl_portaria.setWordWrap(True)
        lbl_portaria.setStyleSheet(
            f'background:#EAF2FF; border:1px solid #85B4E8; border-radius:4px; '
            f'padding:6px 8px; color:#1A3A5C; font-size:11px; margin-top:4px;'
        )
        sg.addWidget(lbl_portaria)
        lay.addWidget(grp_src)

        # Parâmetros
        grp_p = QGroupBox('Parâmetros de Ortogonalização')
        pg = QGridLayout(grp_p); pg.setHorizontalSpacing(10); pg.setVerticalSpacing(6)
        pg.addWidget(QLabel('Dentes por segmento:'), 0, 0)
        self.spin_steps = QSpinBox(); self.spin_steps.setRange(1,50); self.spin_steps.setValue(3)
        self.spin_steps.setMaximumWidth(70)
        pg.addWidget(self.spin_steps, 0, 1)
        pg.addWidget(QLabel('Direção do 1º passo:'), 0, 2)
        self.cb_direction = QComboBox()
        self.cb_direction.addItems(['Auto (ângulo dominante)',
                                    'Horizontal primeiro (L-O → N-S)',
                                    'Vertical primeiro (N-S → L-O)'])
        self.cb_direction.setMinimumWidth(200)
        pg.addWidget(self.cb_direction, 0, 3)
        lay.addWidget(grp_p)

        # Saída
        grp_out = QGroupBox('Arquivos de Saída')
        og = QGridLayout(grp_out); og.setHorizontalSpacing(8); og.setVerticalSpacing(6)
        og.setColumnStretch(1, 1)

        # --- Shapefile ---
        og.addWidget(QLabel('Shapefile (.shp):'), 0, 0)
        self.le_shp = QLineEdit(); self.le_shp.setPlaceholderText('Caminho base (deixe vazio para temporário)')
        og.addWidget(self.le_shp, 0, 1)
        bs = QPushButton('...'); bs.setMaximumWidth(30); bs.clicked.connect(self._browse_shp)
        og.addWidget(bs, 0, 2)

        # --- Checkbox de propagação automática ---
        self.chk_mirror_paths = QCheckBox('Repetir destino do shapefile aos demais arquivos de saída')
        self.chk_mirror_paths.setChecked(True)
        self.chk_mirror_paths.setToolTip(
            'Ao definir o caminho do shapefile, os caminhos do TXT e do CSV\n'
            'serão preenchidos automaticamente com o mesmo nome e diretório\n'
            '(apenas a extensão muda). Desmarque para definir cada um manualmente.'
        )
        og.addWidget(self.chk_mirror_paths, 1, 0, 1, 3)

        # --- TXT ANM ---
        og.addWidget(QLabel('TXT ANM:'), 2, 0)
        self.le_txt = QLineEdit(); self.le_txt.setPlaceholderText('Caminho base (deixe vazio para temporário)')
        og.addWidget(self.le_txt, 2, 1)
        bt = QPushButton('...'); bt.setMaximumWidth(30); bt.clicked.connect(self._browse_txt)
        og.addWidget(bt, 2, 2)

        # --- CSV ANM (inserção em lote no REPEM) ---
        og.addWidget(QLabel('CSV REPEM:'), 3, 0)
        self.le_csv = QLineEdit(); self.le_csv.setPlaceholderText('Caminho base (deixe vazio para temporário)')
        og.addWidget(self.le_csv, 3, 1)
        bc = QPushButton('...'); bc.setMaximumWidth(30); bc.clicked.connect(self._browse_csv)
        og.addWidget(bc, 3, 2)

        # --- Observação ---
        og.addWidget(QLabel('Observação:'), 4, 0)
        self.le_obs = QLineEdit(); self.le_obs.setPlaceholderText('Ex.: Requerimento ANM #12345')
        og.addWidget(self.le_obs, 4, 1, 1, 2)

        # --- Checkboxes de opções ---
        self.chk_load = QCheckBox('Carregar resultado no mapa automaticamente')
        self.chk_load.setChecked(True); og.addWidget(self.chk_load, 5, 0, 1, 3)
        self.chk_header = QCheckBox('Incluir cabeçalho no TXT')
        self.chk_header.setChecked(True); og.addWidget(self.chk_header, 6, 0, 1, 3)

        lay.addWidget(grp_out)
        lay.addStretch()
        scroll.setWidget(inner); ol.addWidget(scroll)
        return outer

    # -----------------------------------------------------------------------
    # Aba 2 — Desenhar Esboço
    # -----------------------------------------------------------------------

    def _tab_draw(self) -> QWidget:
        w = QWidget(); lay = QVBoxLayout(w)
        lay.setContentsMargins(10,10,10,10); lay.setSpacing(10)
        lay.addWidget(_banner(
            '✏ <b>Desenhe o esboço do polígono diretamente no mapa.</b><br>'
            '• Clique esquerdo: adiciona vértice.<br>'
            '• <b>Botão direito</b> ou <b>Enter</b>: fecha e aceita o polígono (mín. 3 vértices).<br>'
            '• <b>ESC</b>: cancela o desenho sem aceitar.<br>'
            '• Após aceitar, selecione <b>"Usar esboço desenhado"</b> na aba Configuração.',
            C['info_bg'], C['info_bd']
        ))
        br = QHBoxLayout()
        self.btn_start_draw  = QPushButton('✏  Iniciar Desenho')
        self.btn_cancel_draw = QPushButton('ESC  Cancelar')
        self.btn_clear_draw  = QPushButton('🗑  Limpar Esboço')
        _style_btn(self.btn_start_draw,  C['primary'], C['secondary'])
        _style_btn(self.btn_cancel_draw, C['warning'], '#B7770D')
        _style_btn(self.btn_clear_draw,  C['danger'],  '#E74C3C')
        self.btn_cancel_draw.setEnabled(False)
        br.addWidget(self.btn_start_draw); br.addWidget(self.btn_cancel_draw)
        br.addWidget(self.btn_clear_draw); br.addStretch()
        lay.addLayout(br)
        self.lbl_draw_state = QLabel('Nenhum esboço ativo.')
        self.lbl_draw_state.setStyleSheet(f'color:{C["text_muted"]}; font-size:12px; padding:4px;')
        lay.addWidget(self.lbl_draw_state)
        self.grp_draw_result = QGroupBox('Esboço Aceito')
        dr = QVBoxLayout(self.grp_draw_result)
        self.lbl_draw_info = QLabel('—')
        self.lbl_draw_info.setStyleSheet(f'font-size:12px; color:{C["text"]};')
        dr.addWidget(self.lbl_draw_info)
        self.grp_draw_result.setVisible(False)
        lay.addWidget(self.grp_draw_result)
        lay.addStretch()
        return w

    # -----------------------------------------------------------------------
    # Aba 3 — Snap Vertices
    # -----------------------------------------------------------------------

    def _tab_snap(self) -> QWidget:
        w = QWidget(); lay = QVBoxLayout(w)
        lay.setContentsMargins(10,10,10,10); lay.setSpacing(8)
        lay.addWidget(_banner(
            '📍 <b>Snap Vertices</b> forçam subdivisões em pontos específicos do esboço.<br>'
            '• Ativar Captura → clique no mapa sobre o esboço.<br>'
            '• Snap nativo do QGIS é respeitado. Botão direito / ESC encerra.',
            C['info_bg'], C['info_bd']
        ))
        br = QHBoxLayout()
        self.btn_activate_snap = QPushButton('📍 Ativar Captura')
        self.btn_clear_snap    = QPushButton('🗑 Limpar')
        _style_btn(self.btn_activate_snap, C['accent'], '#E67E22')
        _style_btn(self.btn_clear_snap,    C['danger'], '#E74C3C')
        br.addWidget(self.btn_activate_snap); br.addWidget(self.btn_clear_snap); br.addStretch()
        lay.addLayout(br)
        self.lbl_snap_count = QLabel('Snap vertices capturados: <b>0</b>')
        lay.addWidget(self.lbl_snap_count)
        grp = QGroupBox('Coordenadas capturadas')
        gl = QVBoxLayout(grp)
        self.txt_snap = QTextEdit(); self.txt_snap.setReadOnly(True)
        self.txt_snap.setMaximumHeight(150)
        self.txt_snap.setPlaceholderText('Nenhum snap vertex capturado...')
        gl.addWidget(self.txt_snap); lay.addWidget(grp); lay.addStretch()
        return w

    # -----------------------------------------------------------------------
    # Aba 4 — Restrições  (scroll + linhas dinâmicas)
    # -----------------------------------------------------------------------

    def _tab_restrictions(self) -> QWidget:
        outer = QWidget()
        outer_lay = QVBoxLayout(outer)
        outer_lay.setContentsMargins(10,10,10,10)
        outer_lay.setSpacing(10)

        outer_lay.addWidget(_banner(
            '🚫 <b>Camadas de Restrição</b> — áreas que o polígono ANM não deve sobrepor.<br>'
            '<b>Pipeline ao clicar "Aplicar Restrições":</b><br>'
            '  1. Recorta o polígono ANM (difference com a union das restrições).<br>'
            '  2. Reortogonaliza cada componente resultante (bordas N-S/L-O).<br>'
            '  3. Múltiplos polígonos: <b>_a</b> = maior área, <b>_b</b>, <b>_c</b>...<br>'
            '<b>Nota:</b> a reortogonalização pode alterar levemente a área — '
            'rumos verdadeiros têm precedência sobre o recorte exato.',
            C['warn_bg'], C['warn_bd']
        ))

        # Scroll para a lista de camadas
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setHorizontalScrollBarPolicy(SB_AlwaysOff)
        scroll.setVerticalScrollBarPolicy(SB_AsNeeded)
        scroll.setMinimumHeight(160)
        scroll.setMaximumHeight(280)

        scroll_inner = QWidget()
        scroll_lay = QVBoxLayout(scroll_inner)
        scroll_lay.setContentsMargins(6, 6, 6, 6)
        scroll_lay.setSpacing(6)

        # GroupBox dentro do scroll
        self._restr_grp = QGroupBox('Camadas de Restrição')
        self._restr_grp_lay = QVBoxLayout(self._restr_grp)
        self._restr_grp_lay.setSpacing(4)
        scroll_lay.addWidget(self._restr_grp)

        # Botão "Adicionar mais 5"
        self.btn_add_restr = QPushButton(f'➕  Adicionar mais {RESTR_BLOCK_SIZE} linhas')
        _style_btn(self.btn_add_restr, C['secondary'], C['primary'])
        self.btn_add_restr.clicked.connect(self._add_restr_block)
        scroll_lay.addWidget(self.btn_add_restr)
        scroll_lay.addStretch()

        scroll.setWidget(scroll_inner)
        outer_lay.addWidget(scroll)

        # Primeira leva de linhas
        for _ in range(RESTR_BLOCK_SIZE):
            self._add_restr_row()
        self._update_add_btn_state()

        # Botões de ação (fora do scroll)
        br = QHBoxLayout()
        self.btn_apply_restr = QPushButton('⚙  Aplicar Restrições e Reortogonalizar')
        self.btn_clear_restr = QPushButton('✖  Limpar Resultado')
        _style_btn(self.btn_apply_restr, C['warning'], '#B7770D')
        _style_btn(self.btn_clear_restr, C['danger'],  '#E74C3C')
        br.addWidget(self.btn_apply_restr); br.addWidget(self.btn_clear_restr); br.addStretch()
        outer_lay.addLayout(br)

        # Relatório
        grp_rep = QGroupBox('Relatório do Pipeline')
        rl = QVBoxLayout(grp_rep)
        self.txt_restr_report = QTextEdit(); self.txt_restr_report.setReadOnly(True)
        self.txt_restr_report.setMinimumHeight(100)
        self.txt_restr_report.setPlaceholderText(
            'Gere o polígono ANM (Pré-visualizar) e depois clique "Aplicar Restrições"...'
        )
        rl.addWidget(self.txt_restr_report)
        outer_lay.addWidget(grp_rep, stretch=1)

        return outer

    def _add_restr_row(self):
        """Adiciona uma linha (checkbox + combobox) à grade de restrições."""
        if len(self._restr_rows) >= MAX_RESTR_TOTAL:
            return

        row_idx = len(self._restr_rows) + 1
        row_w   = QWidget()
        row_lay = QHBoxLayout(row_w)
        row_lay.setContentsMargins(0, 0, 0, 0)
        row_lay.setSpacing(8)

        chk = QCheckBox(f'#{row_idx}')
        chk.setFixedWidth(42)
        chk.setChecked(False)

        cb = QComboBox()
        cb.setSizePolicy(SP_Expanding, SP_Fixed)
        cb.setEnabled(False)
        cb.setMinimumWidth(300)
        cb.addItem('— selecione a camada —', None)   # placeholder inicial

        # Quando marcado: popula e habilita o combo
        def on_toggle(checked, combo=cb):
            combo.setEnabled(checked)
            if checked and combo.count() <= 1:
                # Ainda não populado — popula agora
                self._fill_combo(combo)

        chk.toggled.connect(on_toggle)

        row_lay.addWidget(chk)
        row_lay.addWidget(cb)
        self._restr_grp_lay.addWidget(row_w)
        self._restr_rows.append((chk, cb))

    def _add_restr_block(self):
        """Adiciona mais RESTR_BLOCK_SIZE linhas."""
        remaining = MAX_RESTR_TOTAL - len(self._restr_rows)
        to_add = min(RESTR_BLOCK_SIZE, remaining)
        for _ in range(to_add):
            self._add_restr_row()
        self._update_add_btn_state()

    def _update_add_btn_state(self):
        can_add = len(self._restr_rows) < MAX_RESTR_TOTAL
        self.btn_add_restr.setEnabled(can_add)
        remaining = MAX_RESTR_TOTAL - len(self._restr_rows)
        if can_add:
            add_n = min(RESTR_BLOCK_SIZE, remaining)
            self.btn_add_restr.setText(f'➕  Adicionar mais {add_n} linhas ({remaining} restantes)')
        else:
            self.btn_add_restr.setText(f'Limite de {MAX_RESTR_TOTAL} camadas atingido')

    def _fill_combo(self, cb: QComboBox):
        """Popula um combo de restrição com todas as camadas de polígono do projeto."""
        prev = cb.currentData()
        cb.blockSignals(True)
        cb.clear()
        cb.addItem('— selecione a camada —', None)
        for lyr in _all_polygon_layers():
            cb.addItem(lyr.name(), lyr.id())
        # Restaura seleção anterior se ainda existir
        if prev:
            idx = cb.findData(prev)
            if idx >= 0:
                cb.setCurrentIndex(idx)
        cb.blockSignals(False)

    def _get_active_restr_layers(self) -> List[QgsVectorLayer]:
        """Retorna camadas ativas e válidas das linhas de restrição."""
        out = []
        seen = set()
        for chk, cb in self._restr_rows:
            if not chk.isChecked():
                continue
            lid = cb.currentData()
            if not lid or lid in seen:
                continue
            lyr = QgsProject.instance().mapLayer(lid)
            if lyr and lyr.isValid():
                out.append(lyr)
                seen.add(lid)
        return out

    # -----------------------------------------------------------------------
    # Aba 5 — Log
    # -----------------------------------------------------------------------

    def _tab_log(self) -> QWidget:
        w = QWidget(); lay = QVBoxLayout(w)
        lay.setContentsMargins(10,10,10,10); lay.setSpacing(6)
        lay.addWidget(QLabel('Log de operações e coordenadas dos vértices (formato ANM):'))
        self.txt_log = QTextEdit(); self.txt_log.setReadOnly(True)
        self.txt_log.setPlaceholderText('Coordenadas aparecerão aqui após o processamento...')
        lay.addWidget(self.txt_log)
        btn_copy = QPushButton('📋 Copiar para área de transferência')
        btn_copy.clicked.connect(self._copy_log)
        lay.addWidget(btn_copy)
        return w

    # -----------------------------------------------------------------------
    # Sinais
    # -----------------------------------------------------------------------

    def _connect_signals(self):
        # Troca de origem do esboço → alterna visibilidade dos subpainéis
        self.rb_from_layer.toggled.connect(self._on_source_changed)
        self.rb_from_canvas.toggled.connect(self._on_source_changed)
        self.rb_from_file.toggled.connect(self._on_source_changed)
        self.cb_layer.currentIndexChanged.connect(self._on_layer_changed)
        self.rb_selected.toggled.connect(self._update_feat_count)

        # Atualiza a lista de camadas automaticamente quando o projeto muda
        QgsProject.instance().layersAdded.connect(self._on_project_layers_changed)
        QgsProject.instance().layersRemoved.connect(self._on_project_layers_changed)

        # Qualquer mudança nos parâmetros de processamento invalida o cache de resultados
        for sig in [self.cb_layer.currentIndexChanged,
                    self.rb_selected.toggled, self.rb_all.toggled,
                    self.spin_steps.valueChanged,
                    self.cb_direction.currentIndexChanged,
                    self.rb_from_layer.toggled, self.rb_from_canvas.toggled,
                    self.rb_from_file.toggled]:
            sig.connect(self._invalidate_cache)

        self.btn_preview.clicked.connect(self._on_preview)
        self.btn_generate.clicked.connect(self._on_generate)
        self.btn_close.clicked.connect(self._on_close)
        self.btn_start_draw.clicked.connect(self._start_drawing)
        self.btn_cancel_draw.clicked.connect(self._cancel_drawing)
        self.btn_clear_draw.clicked.connect(self._clear_drawing)
        self.btn_activate_snap.clicked.connect(self._activate_snap_capture)
        self.btn_clear_snap.clicked.connect(self._clear_snap_vertices)
        self.btn_apply_restr.clicked.connect(self._apply_restrictions)
        self.btn_clear_restr.clicked.connect(self._clear_restrictions)

        # Propaga o caminho do SHP para TXT e CSV quando o checkbox estiver marcado
        self.le_shp.textChanged.connect(self._on_shp_path_changed)

    # -----------------------------------------------------------------------
    # Origem e camadas
    # -----------------------------------------------------------------------

    def _on_source_changed(self):
        use_layer  = self.rb_from_layer.isChecked()
        use_canvas = self.rb_from_canvas.isChecked()
        use_file   = self.rb_from_file.isChecked()
        self._pnl_layer.setVisible(use_layer)
        self._pnl_canvas.setVisible(use_canvas)
        self._pnl_file.setVisible(use_file)
        self._invalidate_cache()

    def populate_layers(self):
        self.cb_layer.blockSignals(True); self.cb_layer.clear()
        lyrs = _all_polygon_layers()
        if not lyrs:
            self.cb_layer.addItem('— Nenhuma camada de polígono —')
        else:
            for l in lyrs: self.cb_layer.addItem(l.name(), l.id())
        self.cb_layer.blockSignals(False)
        self._on_layer_changed()
        # Repopula combos de restrição que já estiverem habilitados
        for chk, cb in self._restr_rows:
            if chk.isChecked():
                self._fill_combo(cb)

    def _on_project_layers_changed(self, *args):
        """Chamado automaticamente quando camadas são adicionadas ou removidas do projeto."""
        self.populate_layers()

    def _on_layer_changed(self):
        self._update_feat_count(); self._invalidate_cache()

    def _update_feat_count(self):
        lyr = self._get_layer()
        if not lyr: self.lbl_feat_count.setText(''); return
        tot = lyr.featureCount(); sel = lyr.selectedFeatureCount()
        if self.rb_selected.isChecked():
            msg = f'{sel} selecionado(s) de {tot}'; col = C['danger'] if sel==0 else C['text_muted']
            if sel == 0: msg += '  ⚠ Nenhum!'
        else:
            msg = f'{tot} polígono(s)'; col = C['text_muted']
            if tot > MAX_POLY: msg += f' — máx {MAX_POLY}'
        self.lbl_feat_count.setText(msg)
        self.lbl_feat_count.setStyleSheet(f'color:{col}; font-size:11px;')

    def _get_layer(self) -> Optional[QgsVectorLayer]:
        lid = self.cb_layer.currentData()
        return QgsProject.instance().mapLayer(lid) if lid else None

    def _get_features(self) -> List[QgsFeature]:
        lyr = self._get_layer()
        if not lyr: return []
        if self.rb_selected.isChecked():
            return list(lyr.selectedFeatures())[:MAX_POLY]
        return list(lyr.getFeatures(QgsFeatureRequest().setLimit(MAX_POLY)))

    # -----------------------------------------------------------------------
    # Desenho
    # -----------------------------------------------------------------------

    def _start_drawing(self):
        if self._draw_tool: return
        self._prev_tool = self.canvas.mapTool()
        self._draw_tool = DrawPolygonMapTool(self.canvas)
        self._draw_tool.polygon_drawn.connect(self._on_polygon_drawn)
        self._draw_tool.drawing_cancelled.connect(self._on_drawing_cancelled)
        self.canvas.setMapTool(self._draw_tool)
        self.btn_start_draw.setEnabled(False); self.btn_cancel_draw.setEnabled(True)
        self.lbl_draw_state.setText(
            '🖊  Desenhando... Botão direito ou Enter para aceitar. ESC para cancelar.')
        self.lbl_draw_state.setStyleSheet(f'color:{C["accent"]}; font-size:12px; padding:4px;')
        self.hide()

    def _on_polygon_drawn(self, geom: QgsGeometry):
        self._draw_tool = None
        if self._prev_tool: self.canvas.setMapTool(self._prev_tool)
        self._drawn_geom  = geom
        canvas_crs = self.canvas.mapSettings().destinationCrs()
        self._drawn_layer = create_sketch_memory_layer(geom, canvas_crs)
        pts = geom.asPolygon()
        n_pts = len(pts[0]) - 1 if pts else 0
        self.lbl_draw_state.setText(f'✔ Esboço aceito — {n_pts} vértices.')
        self.lbl_draw_state.setStyleSheet(f'color:{C["success"]}; font-size:12px; padding:4px;')
        self.grp_draw_result.setVisible(True)
        self.lbl_draw_info.setText(
            f'Vértices: <b>{n_pts}</b>  |  CRS canvas: <b>{canvas_crs.authid()}</b><br>'
            'Selecione <b>"Usar esboço desenhado"</b> na aba Configuração.'
        )
        self.rb_from_canvas.setChecked(True)
        self.lbl_drawn_status.setText(f'✔ Esboço com {n_pts} vértices pronto.')
        self.lbl_drawn_status.setStyleSheet(f'color:{C["success"]}; font-size:11px;')
        self.btn_start_draw.setEnabled(True); self.btn_cancel_draw.setEnabled(False)
        self._invalidate_cache()
        self.show(); self.raise_(); self.activateWindow()

    def _on_drawing_cancelled(self):
        self._draw_tool = None
        if self._prev_tool: self.canvas.setMapTool(self._prev_tool)
        self.btn_start_draw.setEnabled(True); self.btn_cancel_draw.setEnabled(False)
        self.lbl_draw_state.setText('Desenho cancelado.')
        self.lbl_draw_state.setStyleSheet(f'color:{C["text_muted"]}; font-size:12px; padding:4px;')
        self.show(); self.raise_(); self.activateWindow()

    def _cancel_drawing(self):
        if self._draw_tool: self._draw_tool.deactivate(); self._on_drawing_cancelled()

    def _clear_drawing(self):
        if self._draw_tool: self._cancel_drawing()
        self._drawn_geom = None; self._drawn_layer = None
        self.grp_draw_result.setVisible(False)
        self.lbl_draw_state.setText('Esboço limpo.')
        self.lbl_draw_state.setStyleSheet(f'color:{C["text_muted"]}; font-size:12px; padding:4px;')
        self.lbl_drawn_status.setText('Nenhum esboço desenhado ainda.')
        self.lbl_drawn_status.setStyleSheet(f'color:{C["text_muted"]}; font-size:11px;')
        self._invalidate_cache()

    # -----------------------------------------------------------------------
    # Snap
    # -----------------------------------------------------------------------

    def _activate_snap_capture(self):
        if self._snap_tool: self._deactivate_snap(); return
        self._prev_tool = self.canvas.mapTool()
        self._snap_tool = SnapCaptureMapTool(self.canvas)
        self._snap_tool.vertex_captured.connect(self._on_snap_vertex)
        self._snap_tool.finished.connect(self._deactivate_snap)
        self.canvas.setMapTool(self._snap_tool)
        self.btn_activate_snap.setText('🛑 Encerrar (dir. ou ESC)')
        self.hide()

    def _deactivate_snap(self):
        if self._prev_tool: self.canvas.setMapTool(self._prev_tool)
        self._snap_tool = None
        self.btn_activate_snap.setText('📍 Ativar Captura')
        self.show(); self.raise_(); self.activateWindow()

    def _on_snap_vertex(self, x, y):
        self._snap_vertices.append((x, y)); self._update_snap_display(); self._invalidate_cache()

    def _clear_snap_vertices(self):
        self._snap_vertices.clear(); self._update_snap_display()
        if self._snap_tool: self._snap_tool.clear_markers()
        self._invalidate_cache()

    def _update_snap_display(self):
        n = len(self._snap_vertices)
        self.lbl_snap_count.setText(f'Snap vertices capturados: <b>{n}</b>')
        lines = [f'{i+1:03d}  Lon={x:.8f}  Lat={y:.8f}' for i,(x,y) in enumerate(self._snap_vertices)]
        self.txt_snap.setPlainText('\n'.join(lines))

    # -----------------------------------------------------------------------
    # Cache
    # -----------------------------------------------------------------------

    def _invalidate_cache(self):
        # Descarta resultados anteriores para forçar reprocessamento na próxima ação
        self._results.clear(); self._final_results.clear()
        self._overlap_hl.clear()
        self._set_status('Configuração alterada — clique Pré-visualizar ou Gerar Arquivos.')

    # -----------------------------------------------------------------------
    # Processamento ANM base
    # -----------------------------------------------------------------------

    def _direction_str(self) -> str:
        return {0:'auto',1:'H',2:'V'}.get(self.cb_direction.currentIndex(),'auto')

    def _make_proc(self, src_crs) -> ANMPolygonProcessor:
        return ANMPolygonProcessor(
            n_steps=self.spin_steps.value(),
            first_direction=self._direction_str(),
            snap_vertices=list(self._snap_vertices),
            src_crs=src_crs,
        )

    def _process_feature(self, feat: QgsFeature, lyr: QgsVectorLayer) -> Optional[Dict]:
        try:
            proc = self._make_proc(lyr.crs())
            rg   = proc.process(feat.geometry())
            return {
                'geom':         rg,
                'vertices':     proc.get_vertex_list(rg),
                'fid':          feat.id(),
                'ortho_errors': proc.validate_orthogonality(rg),
                'area_ha':      area_geodesica_ha(rg),
                'suffix':       '',
            }
        except Exception as e:
            self._log(f'  ⚠ FID {feat.id()} — {e}'); return None

    def _on_preview(self):
        self._results.clear(); self._final_results.clear()
        self.txt_log.clear(); self._overlap_hl.clear()

        if self.rb_from_canvas.isChecked():
            # --- Modo esboço desenhado ---
            if not self._drawn_geom or not self._drawn_layer:
                QMessageBox.warning(self,'ANM Poligonal',
                    'Nenhum esboço desenhado.\nVá para "✏ Desenhar Esboço".'); return
            feat = next(self._drawn_layer.getFeatures())
            res = self._process_feature(feat, self._drawn_layer)
            if res: self._results.append(res)

        elif self.rb_from_file.isChecked():
            # --- Modo shapefile externo ---
            path = self.le_ext_shp.text().strip()
            if not path:
                QMessageBox.warning(self,'ANM Poligonal',
                    'Selecione um shapefile de entrada na aba Configuração.'); return
            if not os.path.isfile(path):
                QMessageBox.warning(self,'ANM Poligonal',
                    f'Arquivo não encontrado:\n{path}'); return
            ext_lyr = QgsVectorLayer(path, 'ext_input', 'ogr')
            if not ext_lyr.isValid():
                QMessageBox.critical(self,'ANM Poligonal',
                    'Não foi possível carregar o shapefile.\nVerifique se o arquivo é válido.'); return
            if ext_lyr.geometryType() != GeomType_Polygon:
                QMessageBox.warning(self,'ANM Poligonal',
                    'O shapefile selecionado não é do tipo polígono.'); return
            feats = list(ext_lyr.getFeatures(QgsFeatureRequest().setLimit(MAX_POLY)))
            self.progress.setVisible(True); self.progress.setMaximum(len(feats))
            for i, feat in enumerate(feats):
                self.progress.setValue(i+1)
                res = self._process_feature(feat, ext_lyr)
                if res: self._results.append(res)
            self.progress.setVisible(False)

        else:
            # --- Modo camada existente no projeto ---
            feats = self._get_features()
            if not feats:
                QMessageBox.warning(self,'ANM Poligonal','Nenhuma feature para processar.'); return
            lyr = self._get_layer()
            self.progress.setVisible(True); self.progress.setMaximum(len(feats))
            for i, feat in enumerate(feats):
                self.progress.setValue(i+1)
                res = self._process_feature(feat, lyr)
                if res: self._results.append(res)
            self.progress.setVisible(False)

        if not self._results:
            QMessageBox.critical(self,'ANM Poligonal','Nenhum polígono processado.'); return

        self._final_results = list(self._results)
        self._highlighter.highlight(self._results[0]['geom'])
        self._display_log(self._final_results)
        self.tabs.setCurrentIndex(4)
        tot_v = sum(len(r['vertices']) for r in self._final_results)
        self._set_status(
            f'✔ {len(self._final_results)} polígono(s) — {tot_v} vértices totais.',
            C['success']
        )

    # -----------------------------------------------------------------------
    # Pipeline de restrições
    # -----------------------------------------------------------------------

    def _apply_restrictions(self):
        # Se ainda não processou o polígono ANM base, faz agora
        if not self._results:
            self._on_preview()
            if not self._results:
                return  # _on_preview já exibiu o erro

        restr_layers = self._get_active_restr_layers()
        if not restr_layers:
            QMessageBox.information(self,'ANM Poligonal',
                'Nenhuma camada de restrição selecionada.\n'
                'Marque o checkbox e escolha uma camada na aba Restrições.'); return

        self.txt_restr_report.clear(); self._overlap_hl.clear()
        all_final: List[Dict] = []
        report = ['RELATÓRIO — PIPELINE DE RESTRIÇÕES', '='*52,
                  f'Camadas de restrição: {", ".join(l.name() for l in restr_layers)}',
                  '']

        self.progress.setVisible(True); self.progress.setMaximum(len(self._results))

        for poly_idx, base_res in enumerate(self._results):
            self.progress.setValue(poly_idx + 1)
            report.append(f'Polígono {poly_idx+1:03d} (FID {base_res["fid"]})')
            report.append(f'  Área ANM original: {base_res["area_ha"]:.4f} ha')

            try:
                clipped = clip_and_reortogonalize(
                    anm_geom          = base_res['geom'],
                    restriction_layers= restr_layers,
                    n_steps           = self.spin_steps.value(),
                    first_direction   = self._direction_str(),
                    snap_vertices     = list(self._snap_vertices),
                )
            except Exception as e:
                report.append(f'  ✗ Erro: {e}')
                clipped = [dict(base_res, suffix='')]

            if not clipped:
                report.append('  ✗ Completamente dentro das restrições — descartado.')
                report.append('')
                continue

            n_parts = len(clipped)
            if n_parts == 1 and clipped[0]['suffix'] == '':
                report.append('  ✔ Sem sobreposição — mantido intacto.')
            else:
                report.append(f'  ✔ Recortado em {n_parts} componente(s):')
                for r in clipped:
                    report.append(
                        f'    • _poly_{poly_idx+1:03d}{r["suffix"]}: '
                        f'{r["area_ha"]:.4f} ha | {len(r["vertices"])-1} vértices'
                    )
                # Destaca área removida no canvas
                union_clipped: Optional[QgsGeometry] = None
                for r in clipped:
                    union_clipped = (r['geom'] if union_clipped is None
                                     else union_clipped.combine(r['geom']))
                if union_clipped:
                    removed = base_res['geom'].difference(union_clipped)
                    if removed and not removed.isEmpty():
                        self._overlap_hl.show_overlaps([removed])

            for r in clipped:
                r['fid'] = base_res['fid']
                r['_poly_idx'] = poly_idx
            all_final.extend(clipped)
            report.append('')

        self.progress.setVisible(False)

        if not all_final:
            self.txt_restr_report.setPlainText(
                '\n'.join(report) + '\n⚠ Nenhum polígono restou.')
            return

        self._final_results = all_final
        report += ['='*52, f'Total final: {len(all_final)} polígono(s)']
        self.txt_restr_report.setPlainText('\n'.join(report))
        self._display_log(self._final_results)
        self._highlighter.highlight(self._final_results[0]['geom'])
        self.tabs.setCurrentIndex(4)
        self._set_status(
            f'✔ Restrições aplicadas — {len(all_final)} polígono(s) final(is).',
            C['success']
        )

    def _clear_restrictions(self):
        self._final_results = [dict(r, suffix='') for r in self._results]
        self._overlap_hl.clear(); self.txt_restr_report.clear()
        if self._results:
            self._highlighter.highlight(self._results[0]['geom'])
            self._display_log(self._final_results)
        self._set_status('Resultado de restrições limpo.')

    # -----------------------------------------------------------------------
    # Exportação
    # -----------------------------------------------------------------------

    def _on_generate(self):
        shp = self.le_shp.text().strip()
        txt = self.le_txt.text().strip()
        csv_out = self.le_csv.text().strip()

        # Se nenhum caminho foi indicado, gera em diretório temporário do SO e
        # carrega tudo no projeto (comportamento equivalente ao "teste rápido")
        use_temp = not shp and not txt and not csv_out
        if use_temp:
            import tempfile, uuid
            tmp_dir  = tempfile.gettempdir()
            tmp_base = os.path.join(tmp_dir, f'anm_{uuid.uuid4().hex[:8]}')
            shp     = tmp_base
            txt     = tmp_base
            csv_out = tmp_base
            # Força carregamento automático quando usando temporário
            _orig_load = self.chk_load.isChecked()
            self.chk_load.setChecked(True)

        # Só reprocessa se não houver nenhum resultado ainda.
        if not self._final_results:
            self._on_preview()
            if not self._final_results:
                if use_temp:
                    self.chk_load.setChecked(_orig_load)
                return

        results = self._final_results
        n = len(results); batch = n > 1
        self.progress.setVisible(True); self.progress.setMaximum(n); erros = []

        for i, res in enumerate(results):
            self.progress.setValue(i + 1)
            poly_suf = res.get('suffix', '')
            num_suf  = f'_poly_{res.get("_poly_idx", i) + 1:03d}' if batch else ''
            full_suf = f'{num_suf}{poly_suf}'
            try:
                if shp:
                    base = shp[:-4] if shp.lower().endswith('.shp') else shp
                    p = f'{base}{full_suf}.shp'
                    export_shapefile(res['geom'], p, {'obs': self.le_obs.text()})
                    self._log(f'✔ SHP: {os.path.basename(p)}')
                    if self.chk_load.isChecked():
                        load_layer_to_canvas(p, f'ANM_{os.path.splitext(os.path.basename(p))[0]}')

                if txt:
                    base = txt
                    for _ext in ('.txt', '.TXT'):
                        if base.endswith(_ext):
                            base = base[:-len(_ext)]
                            break
                    p = f'{base}{full_suf}.txt'
                    export_txt_anm(res['vertices'], p,
                                   include_header=self.chk_header.isChecked())
                    self._log(f'✔ TXT: {os.path.basename(p)}')
                    if use_temp or self.chk_load.isChecked():
                        txt_name = os.path.splitext(os.path.basename(p))[0]
                        p_uri = p.replace('\\', '/')
                        uri = (f'file:///{p_uri}'
                               f'?delimiter=%09'
                               f'&useHeader=yes'
                               f'&type=csv'
                               f'&geomType=none')
                        txt_lyr = QgsVectorLayer(uri, f'TXT_{txt_name}', 'delimitedtext')
                        if txt_lyr.isValid():
                            QgsProject.instance().addMapLayer(txt_lyr)
                            self._log('  ℹ TXT carregado como tabela no projeto.')
                        else:
                            self._log(f'  ℹ TXT salvo em: {p}')

                if csv_out:
                    base = csv_out
                    for _ext in ('.csv', '.CSV'):
                        if base.endswith(_ext):
                            base = base[:-len(_ext)]
                            break
                    p = f'{base}{full_suf}.csv'
                    export_csv_anm(res['vertices'], p)
                    self._log(f'✔ CSV REPEM: {os.path.basename(p)}')
                    if use_temp or self.chk_load.isChecked():
                        csv_name = os.path.splitext(os.path.basename(p))[0]
                        p_uri = p.replace('\\', '/')
                        uri = (f'file:///{p_uri}'
                               f'?delimiter=%3B'
                               f'&useHeader=no'
                               f'&type=csv'
                               f'&geomType=none')
                        csv_lyr = QgsVectorLayer(uri, f'CSV_{csv_name}', 'delimitedtext')
                        if csv_lyr.isValid():
                            QgsProject.instance().addMapLayer(csv_lyr)
                            self._log('  ℹ CSV REPEM carregado como tabela no projeto.')
                        else:
                            self._log(f'  ℹ CSV REPEM salvo em: {p}')

            except Exception as e:
                erros.append(str(e)); self._log(f'✗ {e}')

        self.progress.setVisible(False); self._save_settings()

        if use_temp:
            self.chk_load.setChecked(_orig_load)

        if erros:
            QMessageBox.warning(self, 'ANM Poligonal',
                f'Concluído com {len(erros)} erro(s):\n' + '\n'.join(erros))
        elif use_temp:
            self._set_status(
                f'✔ {n} arquivo(s) temporário(s) gerado(s) e carregado(s) no mapa.',
                C['success'])
        else:
            QMessageBox.information(self, 'ANM Poligonal',
                f'{n} polígono(s) exportado(s) com sucesso!')
            self._set_status(f'✔ {n} arquivo(s) gerado(s).', C['success'])

    # -----------------------------------------------------------------------
    # Log / exibição
    # -----------------------------------------------------------------------

    def _display_log(self, results: List[Dict]):
        self.txt_log.clear()
        for i, res in enumerate(results, 1):
            verts = res['vertices']
            pts   = verts[:-1] if len(verts)>1 and verts[0]==verts[-1] else verts
            suf   = res.get('suffix','')
            n_pts = len(pts)
            self.txt_log.append(
                f'{"="*62}\n'
                f'POLÍGONO {i:03d}{suf.upper()}  |  FID {res["fid"]}  |  '
                f'{n_pts+1} vértices (fechado)  |  {res.get("area_ha",-1):.4f} ha\n'
                f'{"="*62}\n'
                f'{"Vértice":<10} {"Latitude":<24} {"Longitude":<24}\n'
                f'{"-"*62}'
            )
            for j, (lon, lat) in enumerate(pts, 1):
                self.txt_log.append(
                    f'{j:<10} {decimal_to_dms_anm(lat):<24} {decimal_to_dms_anm(lon):<24}'
                )
            # Fechamento: vértice N+1 = igual ao vértice 1
            if pts:
                lon0, lat0 = pts[0]
                closing_n  = n_pts + 1
                self.txt_log.append(
                    f'{closing_n:<10} {decimal_to_dms_anm(lat0):<24} {decimal_to_dms_anm(lon0):<24}'
                )
            if res.get('ortho_errors'):
                self.txt_log.append('⚠ Erros ortogonais:')
                for e in res['ortho_errors']: self.txt_log.append(f'  {e}')
            else:
                self.txt_log.append('✔ Validação ortogonal OK')
            self.txt_log.append('')

    def _log(self, msg: str): self.txt_log.append(msg)

    def _set_status(self, msg: str, color: str = ''):
        self.lbl_status.setText(msg)
        self.lbl_status.setStyleSheet(f'color:{color or C["text_muted"]}; font-size:11px;')

    def _copy_log(self):
        from qgis.PyQt.QtWidgets import QApplication
        QApplication.clipboard().setText(self.txt_log.toPlainText())
        self._set_status('Log copiado.', C['secondary'])

    # -----------------------------------------------------------------------
    # Arquivos
    # -----------------------------------------------------------------------

    def _browse_shp(self):
        p, _ = QFileDialog.getSaveFileName(self, 'Salvar Shapefile ANM', '', 'Shapefile (*.shp)')
        if p:
            self.le_shp.setText(p)
            # _on_shp_path_changed é disparado automaticamente via textChanged

    def _browse_txt(self):
        p, _ = QFileDialog.getSaveFileName(self, 'Salvar TXT ANM', '', 'Arquivo de texto (*.txt)')
        if p:
            self.le_txt.setText(p)

    def _browse_csv(self):
        p, _ = QFileDialog.getSaveFileName(self, 'Salvar CSV REPEM (ANM)', '', 'Arquivo CSV (*.csv)')
        if p:
            self.le_csv.setText(p)

    def _on_shp_path_changed(self, shp_path: str):
        """
        Propaga o caminho do shapefile para TXT e CSV quando o checkbox
        'Repetir destino do shapefile aos demais arquivos de saída' estiver marcado.
        Troca apenas a extensão, preservando diretório e nome base.
        """
        if not self.chk_mirror_paths.isChecked():
            return
        if not shp_path.strip():
            self.le_txt.setText('')
            self.le_csv.setText('')
            return
        base = shp_path
        for ext in ('.shp', '.SHP'):
            if base.endswith(ext):
                base = base[:-len(ext)]
                break
        self.le_txt.setText(base + '.txt')
        self.le_csv.setText(base + '.csv')

    def _browse_ext_shp(self):
        """Abre diálogo para selecionar shapefile externo como entrada."""
        p, _ = QFileDialog.getOpenFileName(
            self, 'Selecionar Shapefile de Entrada', '', 'Shapefile (*.shp)'
        )
        if p:
            self.le_ext_shp.setText(p)
            self._invalidate_cache()

    # -----------------------------------------------------------------------
    # Persistência
    # -----------------------------------------------------------------------

    def _save_settings(self):
        s = QSettings('ANMPoligonal', 'Plugin')
        s.setValue('shp',          self.le_shp.text())
        s.setValue('txt',          self.le_txt.text())
        s.setValue('csv',          self.le_csv.text())
        s.setValue('mirror_paths', self.chk_mirror_paths.isChecked())
        s.setValue('steps',        self.spin_steps.value())
        s.setValue('load',         self.chk_load.isChecked())
        s.setValue('header',       self.chk_header.isChecked())
        s.setValue('dir',          self.cb_direction.currentIndex())
        s.setValue('rb_all',       self.rb_all.isChecked())
        # Salva geometria da janela (posição + tamanho)
        s.setValue('window_geometry', self.saveGeometry())

    def _restore_settings(self):
        s = QSettings('ANMPoligonal', 'Plugin')
        # Desconecta temporariamente o sinal para evitar propagação durante restore
        self.le_shp.textChanged.disconnect(self._on_shp_path_changed)
        self.le_shp.setText(s.value('shp', ''))
        self.le_txt.setText(s.value('txt', ''))
        self.le_csv.setText(s.value('csv', ''))
        self.chk_mirror_paths.setChecked(s.value('mirror_paths', True, type=bool))
        self.le_shp.textChanged.connect(self._on_shp_path_changed)
        self.spin_steps.setValue(int(s.value('steps', 3)))
        self.chk_load.setChecked(s.value('load', True, type=bool))
        self.chk_header.setChecked(s.value('header', True, type=bool))
        self.cb_direction.setCurrentIndex(int(s.value('dir', 0)))
        self.rb_all.setChecked(s.value('rb_all', True, type=bool))
        self.rb_selected.setChecked(not self.rb_all.isChecked())
        # Restaura geometria da janela — validada logo em seguida no showEvent
        geom = s.value('window_geometry')
        if geom:
            self.restoreGeometry(geom)

    def _ensure_on_screen(self):
        """
        Garante que a janela esteja inteiramente visível em algum monitor.
        """
        from qgis.PyQt.QtWidgets import QApplication
        from qgis.PyQt.QtCore import QRect

        win_rect: QRect = self.frameGeometry()

        # União de todas as telas disponíveis
        screen_union = QRect()
        for screen in QApplication.screens():
            screen_union = screen_union.united(screen.availableGeometry())

        # Verifica se o centro da janela está na área visível
        center = win_rect.center()
        if screen_union.contains(center):
            x = max(screen_union.left(),
                    min(win_rect.left(),
                        screen_union.right() - win_rect.width()))
            y = max(screen_union.top(),
                    min(win_rect.top(),
                        screen_union.bottom() - win_rect.height()))
            if x != win_rect.left() or y != win_rect.top():
                self.move(x, y)
        else:
            # Centro fora de qualquer tela — recentra sobre a janela do QGIS
            self._center_on_parent()

    def _center_on_parent(self):
        """Recentra o diálogo sobre a janela principal do QGIS."""
        parent_rect = self.iface.mainWindow().frameGeometry()
        x = parent_rect.center().x() - self.width()  // 2
        y = parent_rect.center().y() - self.height() // 2
        self.move(x, y)

    def showEvent(self, event):
        """Valida posição em toda exibição da janela."""
        super().showEvent(event)
        from qgis.PyQt.QtCore import QTimer
        QTimer.singleShot(0, self._ensure_on_screen)

    # -----------------------------------------------------------------------
    # Fechamento
    # -----------------------------------------------------------------------

    def _on_close(self):
        self._save_settings()
        self._highlighter.clear(); self._overlap_hl.clear()
        if self._draw_tool: self._cancel_drawing()
        if self._snap_tool: self._deactivate_snap()
        # Desconecta sinais do projeto para evitar referências pendentes
        try:
            QgsProject.instance().layersAdded.disconnect(self._on_project_layers_changed)
            QgsProject.instance().layersRemoved.disconnect(self._on_project_layers_changed)
        except Exception:
            pass
        self.hide()

    def closeEvent(self, event):
        self._on_close(); event.ignore()
