#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Script auxiliar para gerar o ícone do plugin ANM em PNG.
Execute este script UMA VEZ para gerar icons/anm_icon.png.
Requer: Pillow (pip install Pillow) OU use o SVG diretamente no QGIS.

O QGIS aceita ícones PNG ou SVG. Caso não queira usar este script,
basta colocar qualquer PNG 32x32 em icons/anm_icon.png.
"""

import os
import struct
import zlib


def _create_minimal_png(path: str, size: int = 32):
    """Gera um PNG mínimo válido (ícone azul ANM) sem dependências externas."""
    
    def png_chunk(chunk_type: bytes, data: bytes) -> bytes:
        c = struct.pack('>I', len(data)) + chunk_type + data
        return c + struct.pack('>I', zlib.crc32(chunk_type + data) & 0xFFFFFFFF)

    # IHDR
    ihdr_data = struct.pack('>IIBBBBB', size, size, 8, 2, 0, 0, 0)
    
    # Pixels: hexágono azul ANM (#1B4F72) com borda laranja (#F39C12)
    primary = (0x1B, 0x4F, 0x72)
    accent  = (0xF3, 0x9C, 0x12)
    bg      = (0xF4, 0xF6, 0xF7)

    rows = []
    cx, cy = size // 2, size // 2
    r = size // 2 - 2

    for y in range(size):
        row = [0]  # filtro None
        for x in range(size):
            dx, dy = x - cx, y - cy
            dist = (dx*dx + dy*dy) ** 0.5
            # Borda laranja
            if r - 3 < dist <= r:
                row.extend(accent)
            # Interior azul
            elif dist <= r - 3:
                row.extend(primary)
            # Fundo
            else:
                row.extend(bg)
        rows.append(bytes(row))

    raw = b''.join(rows)
    compressed = zlib.compress(raw, 9)
    idat_data = compressed

    png_bytes = (
        b'\x89PNG\r\n\x1a\n'
        + png_chunk(b'IHDR', ihdr_data)
        + png_chunk(b'IDAT', idat_data)
        + png_chunk(b'IEND', b'')
    )

    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'wb') as f:
        f.write(png_bytes)
    print(f'Ícone gerado: {path}')


if __name__ == '__main__':
    script_dir = os.path.dirname(os.path.abspath(__file__))
    icon_path = os.path.join(script_dir, '..', 'icons', 'anm_icon.png')
    _create_minimal_png(icon_path)
