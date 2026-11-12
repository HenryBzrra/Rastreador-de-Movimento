"""
Escritor de GIF animado em Python puro (só numpy + struct).
Sem Pillow, sem ffmpeg: é o que permite gerar o timelapse dentro do executável.

Só regrava a região que mudou entre um quadro e outro, então o arquivo e o tempo de
geração ficam pequenos mesmo em timelapses longos.
"""
import struct

import numpy as np


def lzw(dados, bits=8):
    """Compressão LZW no formato GIF. 'dados' = bytes com índices de paleta."""
    limpar, fim = 1 << bits, (1 << bits) + 1
    out = bytearray()
    buf = 0
    n = 0
    tam = bits + 1
    prox = fim + 1
    dic = {}

    def emitir(cod, t):
        nonlocal buf, n
        buf |= cod << n
        n += t
        while n >= 8:
            out.append(buf & 255)
            buf >>= 8
            n -= 8

    emitir(limpar, tam)
    pref = dados[0]
    for b in dados[1:]:
        k = (pref << 8) | b
        c = dic.get(k)
        if c is not None:
            pref = c
            continue
        emitir(pref, tam)
        dic[k] = prox
        prox += 1
        if prox > (1 << tam) and tam < 12:
            tam += 1
        if prox == 4096:                       # tabela cheia: reinicia
            emitir(limpar, tam)
            dic.clear()
            prox = fim + 1
            tam = bits + 1
        pref = b
    emitir(pref, tam)
    prox += 1
    if prox > (1 << tam) and tam < 12:
        tam += 1
    emitir(fim, tam)
    if n:
        out.append(buf & 255)
    return bytes(out)


def _chaves(rgb):
    r = rgb.reshape(-1, 3).astype(np.uint32)
    return (r[:, 0] << 16) | (r[:, 1] << 8) | r[:, 2]


def paleta_de(rgb):
    """Paleta de 256 cores: as mais frequentes de um quadro (use o quadro final)."""
    uniq, cont = np.unique(_chaves(rgb), return_counts=True)
    cores = uniq[np.argsort(-cont)[:256]]
    pal = np.zeros((256, 3), np.uint8)
    pal[:len(cores), 0] = (cores >> 16) & 255
    pal[:len(cores), 1] = (cores >> 8) & 255
    pal[:len(cores), 2] = cores & 255
    return pal


class GifWriter:
    def __init__(self, caminho, largura, altura, atraso_cs, paleta):
        self.w, self.h, self.atraso = int(largura), int(altura), int(atraso_cs)
        self.pal = np.asarray(paleta, np.uint8).reshape(256, 3)
        pal_int = self.pal.astype(np.int32)
        self._pal_int = pal_int
        self.cache = {}
        for i in range(255, -1, -1):           # índice menor vence em caso de cor repetida
            r, g, b = (int(v) for v in self.pal[i])
            self.cache[(r << 16) | (g << 8) | b] = i
        self.f = open(caminho, "wb")
        self.f.write(b"GIF89a" + struct.pack("<HHBBB", self.w, self.h, 0xF7, 0, 0))
        self.f.write(self.pal.tobytes())
        self.f.write(b"\x21\xff\x0bNETSCAPE2.0\x03\x01\x00\x00\x00")   # repetir para sempre
        self.prev = None
        self.pend = None

    def _quantizar(self, reg):
        uniq, inv = np.unique(_chaves(reg), return_inverse=True)
        mapa = np.empty(len(uniq), np.uint8)
        for k, u in enumerate(uniq.tolist()):
            v = self.cache.get(u)
            if v is None:
                c = np.array([(u >> 16) & 255, (u >> 8) & 255, u & 255], np.int32)
                v = int(((self._pal_int - c) ** 2).sum(axis=1).argmin())
                self.cache[u] = v
            mapa[k] = v
        return mapa[inv.reshape(-1)].reshape(reg.shape[:2])

    def adicionar(self, rgb):
        """rgb: array (altura, largura, 3) uint8."""
        if self.prev is None:
            x0, y0, x1, y1 = 0, 0, self.w, self.h
        else:
            dif = (rgb != self.prev).any(axis=2)
            if not dif.any():                  # quadro igual: só alonga o anterior
                if self.pend:
                    self.pend[2] += self.atraso
                return
            ys = np.flatnonzero(dif.any(axis=1))
            xs = np.flatnonzero(dif.any(axis=0))
            x0, x1, y0, y1 = int(xs[0]), int(xs[-1]) + 1, int(ys[0]), int(ys[-1]) + 1
        self._descarregar()
        idx = self._quantizar(rgb[y0:y1, x0:x1])
        self.pend = [(x0, y0, x1 - x0, y1 - y0), lzw(idx.tobytes()), self.atraso]
        self.prev = rgb

    def _descarregar(self):
        if not self.pend:
            return
        (x, y, w, h), dados, atraso = self.pend
        f = self.f
        f.write(b"\x21\xf9\x04\x04" + struct.pack("<H", min(atraso, 65535)) + b"\x00\x00")
        f.write(b"\x2c" + struct.pack("<HHHH", x, y, w, h) + b"\x00")
        f.write(b"\x08")
        for i in range(0, len(dados), 255):
            bloco = dados[i:i + 255]
            f.write(bytes([len(bloco)]) + bloco)
        f.write(b"\x00")
        self.pend = None

    def fechar(self):
        try:
            self._descarregar()
            self.f.write(b"\x3b")
        finally:
            self.f.close()
