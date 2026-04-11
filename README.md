# ANM Poligonal — Plugin QGIS 3.22+

Plugin para geração automática de polígonos em **rumos verdadeiros (N-S e L-O)** conforme as normas técnicas da **Agência Nacional de Mineração (ANM)**.

---

## Funcionalidades

| Recurso | Descrição |
|---|---|
| Ortogonalização automática | Transforma qualquer esboço em polígono com segmentos N-S e L-O |
| Controle de dentes | Usuário define a quantidade de steps por segmento diagonal |
| Snap vertices | Captura interativa de pontos de controle no mapa para forçar subdivisões |
| Exportação Shapefile | Gera `.shp` com campos de área, perímetro e observação |
| Exportação TXT/CSV ANM | Gera lista de vértices numerados, pronta para o sistema ANM |
| Carregamento automático | Resultado pode ser carregado diretamente no canvas |
| Persistência de configurações | Caminhos e parâmetros são salvos entre sessões |

---

## Instalação

### Opção A — Via gerenciador de plugins do QGIS (quando publicado)
1. Plugins → Gerenciar e Instalar Plugins → Buscar "ANM Poligonal"

### Opção B — Instalação manual (pasta de plugins)
```bash
# Linux / macOS
cp -r anm_poligonal ~/.local/share/QGIS/QGIS3/profiles/default/python/plugins/

# Windows
copy anm_poligonal %APPDATA%\QGIS\QGIS3\profiles\default\python\plugins\
```
Depois: Plugins → Gerenciar e Instalar Plugins → Instalados → Habilitar "ANM Poligonal"

---

## Uso

### Fluxo básico

```
1. Desenhe o esboço do polígono normalmente no QGIS
   (shapefile de polígono — pode ser irregular/diagonal)

2. Abra: Menu Vetor → ANM Poligonal → ANM Poligonal
   (ou pelo ícone ⬡ na barra de ferramentas)

3. Aba "Configuração":
   - Selecione a camada de esboço
   - Defina o número de dentes (steps) — padrão: 3
   - Escolha a direção do 1º passo (automático recomendado)
   - Defina os caminhos de saída (.shp e .txt)

4. [Opcional] Aba "Snap Vertices":
   - Ative a captura e clique no mapa para forçar subdivisões
   - Útil para detalhamento em trechos específicos (ex: curvas de rio)

5. Clique "Pré-visualizar" para conferir no canvas
6. Clique "Gerar Arquivos" para exportar .shp e .txt
```

### Sobre os "dentes" (steps)

Cada segmento diagonal do esboço é convertido em uma escadaria de N dentes ortogonais:

```
Esboço diagonal:          Resultado com 3 dentes:
                          
    /                         ┐
   /        →            ─┐   │
  /                       │   ─┐
 /                        └──  └──
```

- **Mais dentes** = polígono mais fiel ao esboço, mais vértices
- **Menos dentes** = polígono mais simplificado
- **Snap vertices** forçam quebras em pontos específicos

---

## Formato TXT de saída (compatível ANM)

```
Vértice	Latitude	Longitude
1	-15°47'54"429	-47°51'54"229
2	-15°47'54"429	-47°51'42"736
3	-15°48'01"577	-47°51'42"736
...
```

## Estrutura do projeto

```
anm_poligonal/
├── __init__.py           # Entry point QGIS
├── plugin.py             # Classe principal do plugin
├── metadata.txt          # Metadados QGIS Plugin Manager
├── core/
│   ├── __init__.py
│   └── processor.py      # Lógica de ortogonalização + exportação
├── ui/
│   ├── __init__.py
│   └── dialog_main.py    # Interface gráfica (3 abas)
├── utils/
│   ├── __init__.py
│   └── map_tool.py       # MapTool de captura de snap vertices
└── icons/
    ├── anm_icon.png       # Ícone do plugin (32x32 px)
    └── generate_icon.py   # Script gerador do ícone
```

---

## Requisitos técnicos

- QGIS ≥ 3.22
- Python 3.9+
- Sem dependências externas (usa apenas PyQGIS e stdlib)

---

## Notas técnicas

### CRS
- O plugin respeita o CRS da camada de entrada
- Coordenadas geográficas (lat/lon) e projetadas (UTM) são suportadas
- Para submissão ANM, **recomenda-se SIRGAS 2000 geográfico (EPSG:4674)**

### Snap do QGIS
- O snap nativo do QGIS funciona automaticamente durante a captura de snap vertices
- Configure em: Projeto → Opções de Snap (ou ícone de ímã na barra de ferramentas)

### Precisão numérica
- Erros de ponto flutuante são eliminados na geração dos vértices finais
- Vértices colineares redundantes são removidos automaticamente

---


## Versão e autoria

- Versão: 1.0.0
- Compatibilidade: QGIS 3.22 – 3.44+
- Licença: GPL v2

---

*Plugin desenvolvido para atendimento às normas técnicas ANM de delimitação de polígonos de requerimentos minerários.*
