"""
Rastreador de Mouse (PySide6) - rastro, cliques, mapa de calor e timelapse.

Executável pronto: veja a página de Releases do repositório (não precisa instalar nada).
Rodando pelo código:  pip install -r requirements.txt  &&  python rastreador_mouse.py

Atalhos padrão (globais, funcionam com a janela minimizada; dá para trocar em AJUSTES):
    F8 iniciar/retomar   F9 pausar   F10 parar e salvar

Use apenas no seu próprio computador ou com o consentimento de quem o usa.
"""

import csv
import json
import math
import os
import re
import shutil
import sys
import time
from bisect import bisect_right
from collections import deque
from datetime import datetime
from pathlib import Path

import numpy as np
from pynput import keyboard, mouse

from gif_writer import GifWriter, paleta_de
from PySide6.QtCore import (QEasingCurve, QObject, QPoint, QPointF, QRectF, QSize, QSizeF, Qt,
                            QTimer, QUrl, QVariantAnimation, Signal)
from PySide6.QtGui import (QBrush, QColor, QDesktopServices, QFont, QGuiApplication, QIcon, QImage,
                           QKeySequence, QLinearGradient, QPainter, QPainterPath, QPen, QPixmap,
                           QPolygonF)
from PySide6.QtWidgets import (QAbstractItemView, QApplication, QCheckBox, QColorDialog, QComboBox,
                               QDialog, QFileDialog, QFrame, QHBoxLayout, QInputDialog,
                               QKeySequenceEdit, QLabel, QLineEdit, QListWidget, QListWidgetItem,
                               QMessageBox, QProgressBar, QPushButton, QSizeGrip, QSizePolicy,
                               QSlider, QStackedWidget, QVBoxLayout, QWidget)

# ----------------------------------------------------------------------------------------
# Configuração
# ----------------------------------------------------------------------------------------
PASTA = Path.home() / ".rastreador_mouse"
PASTA_CLIQUES = PASTA / "meus_cliques"
ARQ_CONFIG = PASTA / "config_v2.json"
ARQ_ANTIGO = PASTA / "config.json"

PADRAO = {
    "atalhos": {"iniciar": "F8", "pausar": "F9", "parar": "F10"},
    "cor_risco": "#ff000000",     # preto
    "cor_ponto": "#ffffffff",     # branco
    "cor_fundo": "#a0bec0c6",     # cinza translúcido
    "espessura": 1.2,
    "vidro": 18,                  # opacidade do vidro (0 = mais transparente)
    "desfoque": 3,
    "calor_suave": 2,             # suavização do mapa de calor (menor = mais nítido)
    "topo": False,
    "nome": "Usuário",
    "foto": "",
}
DIM = 80  # escurecimento fixo do fundo desfocado (mantém o texto legível mesmo com vidro mínimo)


def carregar_config():
    cfg = json.loads(json.dumps(PADRAO))
    for arq, so in ((ARQ_ANTIGO, ("nome", "foto", "atalhos")), (ARQ_CONFIG, None)):
        try:
            dados = json.loads(arq.read_text(encoding="utf-8"))
        except Exception:
            continue
        for k, v in dados.items():
            if so is not None and k not in so:
                continue
            if k == "atalhos" and isinstance(v, dict):
                cfg["atalhos"].update(v)
            elif k in cfg:
                cfg[k] = v
    return cfg


def salvar_config(cfg):
    PASTA.mkdir(parents=True, exist_ok=True)
    ARQ_CONFIG.write_text(json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8")


# ----------------------------------------------------------------------------------------
# Teclas Qt -> pynput
# ----------------------------------------------------------------------------------------
MODS = {"ctrl": "<ctrl>", "shift": "<shift>", "alt": "<alt>", "meta": "<cmd>"}
ESPECIAIS = {"space": "<space>", "esc": "<esc>", "escape": "<esc>", "return": "<enter>",
             "enter": "<enter>", "tab": "<tab>", "backspace": "<backspace>", "del": "<delete>",
             "delete": "<delete>", "ins": "<insert>", "insert": "<insert>", "home": "<home>",
             "end": "<end>", "pgup": "<page_up>", "pgdown": "<page_down>", "up": "<up>",
             "down": "<down>", "left": "<left>", "right": "<right>"}


def qt_para_pynput(txt):
    saida, teclas = [], 0
    for p in [p.strip() for p in (txt or "").split("+") if p.strip()]:
        low = p.lower()
        if low in MODS:
            saida.append(MODS[low])
            continue
        if re.fullmatch(r"f\d{1,2}", low):
            saida.append(f"<{low}>")
        elif low in ESPECIAIS:
            saida.append(ESPECIAIS[low])
        elif len(p) == 1:
            saida.append(low)
        else:
            return None
        teclas += 1
    return "+".join(saida) if teclas == 1 else None


# ----------------------------------------------------------------------------------------
# Monitores
# ----------------------------------------------------------------------------------------
def area_monitores():
    """Retângulo (em pixels físicos, mesmo sistema de coordenadas do pynput) que cobre todos
    os monitores, e a lista com o retângulo de cada um."""
    rects = []
    for s in QGuiApplication.screens():
        g = s.geometry()
        d = 1.0 if sys.platform == "darwin" else s.devicePixelRatio()  # no macOS o pynput usa "points"
        rects.append(QRectF(g.x() * d, g.y() * d, g.width() * d, g.height() * d))
    u = QRectF(rects[0])
    for r in rects[1:]:
        u = u.united(r)
    return u, rects


# ----------------------------------------------------------------------------------------
# Rastreador
#   Os callbacks do mouse (thread do pynput) só colocam o evento numa fila: isso mantém o mouse
#   do sistema sem travar. Todo o processamento acontece na thread da interface (processar()).
# ----------------------------------------------------------------------------------------
MOV, CLK, SOLTA, ROL, NOVO_RISCO = 0, 1, 2, 3, 9


class Rastreador:
    PARADO, RASTREANDO, PAUSADO = "parado", "rastreando", "pausado"

    def __init__(self):
        self.estado = self.PARADO
        self.listener = None
        self.fila = deque()
        self._inicio = 0.0
        self._acum = 0.0
        self.versao = 0
        self.contador = 0
        self.multi_s = max(0.35, QGuiApplication.styleHints().mouseDoubleClickInterval() / 1000)
        self.resetar()

    def resetar(self):
        self.fila.clear()
        u, self.telas = area_monitores()
        self.ox, self.oy = u.x(), u.y()
        self.sw, self.sh = max(1.0, u.width()), max(1.0, u.height())
        self.esc = max(1, round(self.sw / 960))                  # resolução do mapa de calor
        self.gw, self.gh = math.ceil(self.sw / self.esc), math.ceil(self.sh / self.esc)
        self.dens = np.zeros((self.gh, self.gw), np.float32)
        self.calor_sujo = False
        self.tracos, self.pontos, self.eventos = [], [], []     # pontos: (x, y, botao, n_cliques)
        self.cliques = self.movimentos = 0
        self.distancia = 0.0
        self._acum = 0.0
        self._ultima = None
        self._novo = True
        self._ult_clique = None
        self.raio_multi = 8 * (1 if sys.platform == "darwin" else QGuiApplication.primaryScreen().devicePixelRatio())
        self.versao += 1
        self.contador += 1

    def tempo_ativo(self):
        return self._acum + (time.time() - self._inicio if self.estado == self.RASTREANDO else 0)

    # ---- callbacks (thread do pynput): o mínimo possível ----
    def _on_move(self, x, y):
        if self.estado == self.RASTREANDO:
            t = time.time()
            self.fila.append((MOV, x, y, t, self._acum + t - self._inicio))

    def _on_click(self, x, y, botao, pressionado):
        if self.estado == self.RASTREANDO:
            t = time.time()
            self.fila.append((CLK if pressionado else SOLTA, x, y, t, self._acum + t - self._inicio, botao.name))

    def _on_scroll(self, x, y, dx, dy):
        if self.estado == self.RASTREANDO:
            t = time.time()
            self.fila.append((ROL, x, y, t, self._acum + t - self._inicio, f"dx={dx};dy={dy}"))

    # ---- processamento (thread da interface) ----
    def processar(self):
        q = self.fila
        for _ in range(len(q)):
            ev = q.popleft()
            k, x, y, t, tempo = ev[:5]
            if k == MOV:
                self._mov(x, y, t, tempo)
            elif k == CLK:
                self._clique(x, y, t, tempo, ev[5])
            elif k == SOLTA:
                self.eventos.append((t, tempo, "clique_up", x, y, ev[5]))
            elif k == ROL:
                self.eventos.append((t, tempo, "rolagem", x, y, ev[5]))
            elif k == NOVO_RISCO:
                self._novo, self._ultima = True, None
                self.eventos.append((t, tempo, "retomar", 0, 0, ""))

    def _ponto_no_risco(self, x, y):
        if self._novo or not self.tracos:
            self.tracos.append([])
            self._novo = False
        if not self.tracos[-1] or self.tracos[-1][-1] != (x, y):
            self.tracos[-1].append((x, y))

    def _mov(self, x, y, t, tempo):
        p = (x, y)
        if p == self._ultima:
            return
        if self._ultima is None:
            self._calor_pt(x, y, 1.0)
        else:
            self.distancia += math.dist(self._ultima, p)
            self._calor_seg(self._ultima, p)
        self._ultima = p
        self.movimentos += 1
        self._ponto_no_risco(x, y)
        self.eventos.append((t, tempo, "movimento", x, y, ""))
        self.contador += 1

    def _clique(self, x, y, t, tempo, botao):
        self.cliques += 1
        self._ponto_no_risco(x, y)              # o risco passa exatamente pelo clique
        self._ultima = (x, y)
        self._calor_pt(x, y, 30.0)
        u = self._ult_clique                    # u = (t, x, y, botao, n, indice)
        if u and u[3] == botao and t - u[0] <= self.multi_s and math.dist((x, y), (u[1], u[2])) <= self.raio_multi:
            n, idx = u[4] + 1, u[5]             # clique múltiplo: soma no mesmo ponto
            self.pontos[idx] = (u[1], u[2], botao, n)
            self._ult_clique = (t, u[1], u[2], botao, n, idx)
        else:
            self.pontos.append((x, y, botao, 1))
            self._ult_clique = (t, x, y, botao, 1, len(self.pontos) - 1)
        self.eventos.append((t, tempo, "clique_down", x, y, botao))
        self.contador += 1

    # ---- mapa de calor ----
    def _calor_pt(self, x, y, peso):
        gx, gy = int((x - self.ox) / self.esc), int((y - self.oy) / self.esc)
        if 0 <= gx < self.gw and 0 <= gy < self.gh:
            self.dens[gy, gx] += peso
            self.calor_sujo = True

    def _calor_seg(self, a, b):
        dx, dy = (b[0] - a[0]) / self.esc, (b[1] - a[1]) / self.esc
        n = int(max(abs(dx), abs(dy)))
        if n <= 1:
            self._calor_pt(b[0], b[1], 1.0)
            return
        k = np.linspace(0, 1, n + 1)[1:]
        xs = ((a[0] - self.ox) / self.esc + dx * k).astype(np.int32)
        ys = ((a[1] - self.oy) / self.esc + dy * k).astype(np.int32)
        ok = (xs >= 0) & (xs < self.gw) & (ys >= 0) & (ys < self.gh)
        if ok.any():
            np.add.at(self.dens, (ys[ok], xs[ok]), 1.0)
            self.calor_sujo = True

    # ---- controle ----
    def iniciar(self):
        if self.estado == self.RASTREANDO:
            return
        if self.estado == self.PARADO:
            self.resetar()
            self.listener = mouse.Listener(on_move=self._on_move, on_click=self._on_click,
                                           on_scroll=self._on_scroll)
            self.listener.start()
        self._inicio = time.time()
        self.estado = self.RASTREANDO
        self.fila.append((NOVO_RISCO, 0, 0, time.time(), self._acum))

    def pausar(self):
        if self.estado == self.RASTREANDO:
            self._acum += time.time() - self._inicio
            self.estado = self.PAUSADO

    def parar(self):
        self.pausar()
        if self.listener:
            self.listener.stop()
            self.listener = None
        self.estado = self.PARADO
        self.processar()

    def tem_dados(self):
        return bool(self.pontos) or any(self.tracos)

    def meta(self):
        """Geometria dos monitores da sessão (salva em .json ao lado do .csv, usada pelo timelapse)."""
        return {"ox": self.ox, "oy": self.oy, "sw": self.sw, "sh": self.sh,
                "telas": [[r.x(), r.y(), r.width(), r.height()] for r in self.telas],
                "multi_s": self.multi_s, "raio": self.raio_multi}

    def salvar_csv(self, caminho):
        with open(caminho, "w", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            w.writerow(["data_hora", "tempo_ativo_s", "evento", "x", "y", "detalhe"])
            for t, tempo, tipo, x, y, det in self.eventos:
                w.writerow([datetime.fromtimestamp(t).isoformat(timespec="milliseconds"),
                            round(tempo, 3), tipo, x, y, det])


# ----------------------------------------------------------------------------------------
# Desenho
# ----------------------------------------------------------------------------------------
def alvo_tela(rect, sw, sh, margem=6):
    """Maior retângulo com a proporção exata dos monitores que cabe em 'rect'."""
    W, H = rect.width() - 2 * margem, rect.height() - 2 * margem
    esc = max(0.01, min(W / sw, H / sh))
    w, h = sw * esc, sh * esc
    return QRectF(rect.x() + (rect.width() - w) / 2, rect.y() + (rect.height() - h) / 2, w, h)


def desenhar_pontos(p, alvo, ox, oy, esc, inicios, cliques, estilo, fator=1.0, cabeca=None):
    """Pontos dos cliques (com anéis e número quando há cliques múltiplos), início dos riscos e cursor."""
    p.save()
    p.setRenderHint(QPainter.Antialiasing)

    def m(x, y):
        return QPointF(alvo.left() + (x - ox) * esc, alvo.top() + (y - oy) * esc)

    ponto = QColor(estilo["ponto"])
    contorno = QColor(0, 0, 0, min(120, ponto.alpha()))
    anel = QColor(ponto)
    anel.setAlpha(int(ponto.alpha() * 0.75))
    p.setBrush(Qt.NoBrush)
    p.setPen(QPen(anel, 0.9 * fator))
    for x, y in inicios:
        p.drawEllipse(m(x, y), 4 * fator, 4 * fator)

    fonte = QFont(p.font())
    fonte.setPixelSize(max(7, int(9.5 * fator)))
    p.setFont(fonte)
    for x, y, _b, n in cliques:
        c = m(x, y)
        if n > 1:
            p.setBrush(Qt.NoBrush)
            p.setPen(QPen(anel, 0.8 * fator))
            for k in range(1, min(n, 5)):
                r = (3.4 + 3.2 * k) * fator
                p.drawEllipse(c, r, r)
            rmax = (3.4 + 3.2 * (min(n, 5) - 1)) * fator
            p.setPen(ponto)
            p.drawText(QPointF(c.x() + rmax * 0.75 + 2 * fator, c.y() - rmax * 0.75), f"×{n}")
        p.setPen(QPen(contorno, 0.8 * fator))
        p.setBrush(ponto)
        p.drawEllipse(c, 3.4 * fator, 3.4 * fator)
    if cabeca:
        p.setBrush(Qt.NoBrush)
        p.setPen(QPen(QColor(255, 255, 255, 200), 1 * fator))
        p.drawEllipse(m(*cabeca), 3 * fator, 3 * fator)
    p.restore()


def desenhar_export(p, W, H, t, estilo):
    """Imagem PNG do rastro com a proporção exata dos monitores."""
    fator = W / 900
    alvo = QRectF(0, 0, W, H)
    p.setRenderHint(QPainter.Antialiasing)
    rr = QPainterPath()
    rr.addRoundedRect(alvo, 12 * fator, 12 * fator)
    p.fillPath(rr, QBrush(QColor(estilo["fundo"])))
    p.setClipPath(rr)
    esc = W / t.sw
    p.save()
    p.scale(esc, esc)
    p.translate(-t.ox, -t.oy)
    pen = QPen(QColor(estilo["risco"]), estilo["espessura"] * fator, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin)
    pen.setCosmetic(True)
    p.setPen(pen)
    p.setBrush(Qt.NoBrush)
    for s in t.tracos:
        if len(s) > 1:
            p.drawPolyline(QPolygonF([QPointF(x, y) for x, y in s]))
    p.restore()
    desenhar_pontos(p, alvo, t.ox, t.oy, esc, [s[0] for s in t.tracos if s], list(t.pontos), estilo, fator)


def desenhar_icone(p, tipo, r, cor):
    p.save()
    p.setRenderHint(QPainter.Antialiasing)
    p.setPen(QPen(cor, 1.3, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
    p.setBrush(Qt.NoBrush)
    w = r.width()

    def P(x, y):
        return QPointF(r.left() + x * w, r.top() + y * r.height())

    if tipo == "menu":
        for y in (0.24, 0.5, 0.76):
            p.drawLine(P(0.1, y), P(0.9, y))
    elif tipo == "cursor":
        p.drawPolygon(QPolygonF([P(.2, .08), P(.2, .82), P(.4, .64), P(.55, .95),
                                 P(.7, .88), P(.55, .58), P(.82, .55)]))
    elif tipo == "heat":
        for x in (.1, .55):
            for y in (.1, .55):
                p.drawRoundedRect(QRectF(P(x, y), QSizeF(.35 * w, .35 * w)), 3, 3)
    elif tipo == "image":
        p.drawRoundedRect(QRectF(P(.08, .15), P(.92, .85)), 4, 4)
        p.drawEllipse(P(.32, .38), 2.0, 2.0)
        p.drawPolyline(QPolygonF([P(.12, .78), P(.4, .52), P(.6, .7), P(.72, .58), P(.9, .78)]))
    elif tipo == "gear":
        c = P(.5, .5)
        p.drawEllipse(c, w * .16, w * .16)
        p.drawEllipse(c, w * .3, w * .3)
        for i in range(8):
            a = math.radians(i * 45)
            d = QPointF(math.cos(a), math.sin(a))
            p.drawLine(c + d * w * .36, c + d * w * .46)
    elif tipo == "play":
        p.drawEllipse(P(.5, .5), w * .42, w * .42)
        p.drawPolygon(QPolygonF([P(.42, .32), P(.42, .68), P(.7, .5)]))
    elif tipo == "user":
        p.drawEllipse(P(.5, .32), w * .17, w * .17)
        c = QPainterPath()
        c.moveTo(P(.15, .92))
        c.cubicTo(P(.15, .58), P(.85, .58), P(.85, .92))
        p.drawPath(c)
    p.restore()


def avatar_pixmap(foto, nome, tam):
    dpr = 2
    px = QPixmap(tam * dpr, tam * dpr)
    px.fill(Qt.transparent)
    p = QPainter(px)
    p.setRenderHint(QPainter.Antialiasing)
    p.setRenderHint(QPainter.SmoothPixmapTransform)
    clip = QPainterPath()
    clip.addEllipse(0, 0, tam * dpr, tam * dpr)
    p.setClipPath(clip)
    src = QPixmap(foto) if foto and os.path.exists(foto) else QPixmap()
    if not src.isNull():
        src = src.scaled(tam * dpr, tam * dpr, Qt.KeepAspectRatioByExpanding, Qt.SmoothTransformation)
        p.drawPixmap((tam * dpr - src.width()) // 2, (tam * dpr - src.height()) // 2, src)
    else:
        g = QLinearGradient(0, 0, tam * dpr, tam * dpr)
        g.setColorAt(0, QColor("#3a3d4a"))
        g.setColorAt(1, QColor("#14151c"))
        p.fillRect(px.rect(), g)
        f = QFont()
        f.setPixelSize(int(tam * dpr * 0.42))
        f.setWeight(QFont.Light)
        p.setFont(f)
        p.setPen(QColor(255, 255, 255, 220))
        p.drawText(px.rect(), Qt.AlignCenter, (nome or "?")[:1].upper())
    p.setClipping(False)
    p.setPen(QPen(QColor(255, 255, 255, 70), 1.5 * dpr))
    p.setBrush(Qt.NoBrush)
    p.drawEllipse(QRectF(dpr, dpr, (tam - 2) * dpr, (tam - 2) * dpr))
    p.end()
    px.setDevicePixelRatio(dpr)
    return px


def rotulo(txt, px=12, peso=QFont.Light, esp=0.0, alfa=235, caps=False):
    """QLabel com fonte fina e espaçamento entre letras."""
    l = QLabel(txt.upper() if caps else txt)
    f = QFont()
    f.setPixelSize(px)
    f.setWeight(peso)
    f.setLetterSpacing(QFont.AbsoluteSpacing, esp)
    l.setFont(f)
    l.setStyleSheet(f"color: rgba(255,255,255,{alfa});")
    return l


# ----------------------------------------------------------------------------------------
# Estilo
# ----------------------------------------------------------------------------------------
QSS = """
* { color: #eceef4; }
QLabel { background: transparent; }
QFrame#vidro { background: rgba(255,255,255,12); border: 1px solid rgba(255,255,255,30); border-radius: 16px; }
QDialog, QMessageBox, QInputDialog, QColorDialog { background: #14151c; }
QPushButton { background: rgba(255,255,255,12); border: 1px solid rgba(255,255,255,38); border-radius: 10px; padding: 8px 14px; }
QPushButton:hover { background: rgba(255,255,255,30); border-color: rgba(255,255,255,85); }
QPushButton:pressed { background: rgba(255,255,255,52); }
QPushButton:disabled { color: rgba(255,255,255,70); background: rgba(255,255,255,6); border-color: rgba(255,255,255,16); }
QPushButton[variant="primary"] { background: rgba(244,245,248,235); border: none; color: #0a0a10; }
QPushButton[variant="primary"]:hover { background: #ffffff; }
QPushButton[variant="primary"]:disabled { background: rgba(244,245,248,55); color: rgba(10,10,16,110); }
QPushButton[variant="danger"] { background: transparent; border: 1px solid rgba(255,90,106,190); color: #ff5a6a; }
QPushButton[variant="danger"]:hover { background: rgba(255,90,106,38); }
QPushButton[variant="danger"]:disabled { border-color: rgba(255,90,106,55); color: rgba(255,90,106,85); }
QPushButton[variant="ghost"] { border: none; background: transparent; border-radius: 15px; padding: 0; font-size: 18px; }
QPushButton[variant="ghost"]:hover { background: rgba(255,255,255,28); }
QLineEdit, QKeySequenceEdit { background: rgba(0,0,0,60); border: 1px solid rgba(255,255,255,34); border-radius: 9px; padding: 7px 11px; selection-background-color: rgba(255,255,255,70); }
QLineEdit:focus, QKeySequenceEdit:focus { border: 1px solid rgba(255,255,255,150); }
QSlider::groove:horizontal { height: 2px; background: rgba(255,255,255,50); border-radius: 1px; }
QSlider::sub-page:horizontal { background: rgba(255,255,255,210); border-radius: 1px; }
QSlider::handle:horizontal { background: white; width: 10px; height: 10px; margin: -4px 0; border-radius: 5px; }
QCheckBox { spacing: 8px; background: transparent; }
QCheckBox::indicator { width: 16px; height: 16px; border-radius: 5px; border: 1px solid rgba(255,255,255,80); background: rgba(0,0,0,60); }
QCheckBox::indicator:checked { background: rgba(255,255,255,230); }
QListWidget { background: transparent; border: none; outline: 0; }
QListWidget::item { background: rgba(255,255,255,10); border: 1px solid rgba(255,255,255,24); border-radius: 12px; padding: 8px; margin: 6px; }
QListWidget::item:selected { background: rgba(255,255,255,26); border: 1px solid rgba(255,255,255,120); }
QScrollBar:vertical { background: transparent; width: 8px; margin: 4px; }
QScrollBar::handle:vertical { background: rgba(255,255,255,55); border-radius: 3px; min-height: 30px; }
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; }
QComboBox { background: rgba(0,0,0,60); border: 1px solid rgba(255,255,255,34); border-radius: 9px; padding: 6px 10px; }
QComboBox:hover { border-color: rgba(255,255,255,90); }
QComboBox::drop-down { border: none; width: 22px; }
QComboBox QAbstractItemView { background: #1b1c26; border: 1px solid rgba(255,255,255,40); selection-background-color: rgba(255,255,255,40); outline: 0; }
QProgressBar { background: rgba(255,255,255,26); border: none; border-radius: 2px; max-height: 4px; min-height: 4px; }
QProgressBar::chunk { background: rgba(255,255,255,220); border-radius: 2px; }
QSizeGrip { background: transparent; image: none; }
QLabel#toast { background: rgba(14,15,22,230); border: 1px solid rgba(255,255,255,45); border-radius: 14px; padding: 9px 18px; }
QToolTip { background: #1b1c26; color: white; border: 1px solid rgba(255,255,255,40); padding: 4px; }
"""


# ----------------------------------------------------------------------------------------
# Widgets
# ----------------------------------------------------------------------------------------
class Vidro(QFrame):
    def __init__(self):
        super().__init__()
        self.setObjectName("vidro")


class NavBtn(QPushButton):
    def __init__(self, tipo, texto, checkable=True):
        super().__init__()
        self.tipo, self.texto = tipo, texto
        self.setCheckable(checkable)
        self.setFixedHeight(44)
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        self.setCursor(Qt.PointingHandCursor)
        self.setAttribute(Qt.WA_Hover, True)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        r = QRectF(self.rect()).adjusted(4, 2, -4, -2)
        ativo = self.isChecked()
        if ativo:
            p.setBrush(QColor(255, 255, 255, 34))
            p.setPen(QPen(QColor(255, 255, 255, 70), 1))
            p.drawRoundedRect(r, 12, 12)
        elif self.underMouse():
            p.setBrush(QColor(255, 255, 255, 18))
            p.setPen(Qt.NoPen)
            p.drawRoundedRect(r, 12, 12)
        cor = QColor(255, 255, 255, 255 if (ativo or self.underMouse()) else 170)
        desenhar_icone(p, self.tipo, QRectF(r.left() + 13, r.center().y() - 10, 20, 20), cor)
        if self.width() > 110 and self.texto:
            f = QFont(self.font())
            f.setPixelSize(11)
            f.setLetterSpacing(QFont.AbsoluteSpacing, 2.2)
            p.setFont(f)
            p.setPen(cor)
            p.drawText(QRectF(r.left() + 46, r.top(), r.width() - 50, r.height()),
                       Qt.AlignVCenter | Qt.AlignLeft, self.texto.upper())


class CorBtn(QPushButton):
    mudou = Signal(QColor)

    def __init__(self, rotulo_txt, cor):
        super().__init__(rotulo_txt)
        self.cor = QColor(cor)
        self.setCursor(Qt.PointingHandCursor)
        self.setStyleSheet("padding: 6px 34px 6px 12px;")
        self.clicked.connect(self.escolher)

    def escolher(self):
        c = QColorDialog.getColor(self.cor, self.window(), "", QColorDialog.ColorDialogOption.ShowAlphaChannel)
        if c.isValid():
            self.cor = c
            self.update()
            self.mudou.emit(c)

    def paintEvent(self, e):
        super().paintEvent(e)
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        p.setBrush(self.cor)
        p.setPen(QPen(QColor(255, 255, 255, 150), 1))
        p.drawEllipse(QPointF(self.width() - 18, self.height() / 2), 6, 6)


class TracoWidget(QWidget):
    """Risco ao vivo. As linhas novas são desenhadas direto numa camada (sem redesenhar tudo),
    por isso não há atraso mesmo com muitos pontos."""

    def __init__(self, tracker, estilo):
        super().__init__()
        self.t, self.estilo = tracker, estilo
        self.dica = ""
        self._layer = None
        self._cont = []
        self._versao = self._marca = -1
        self._alvo = QRectF()
        self._timer = QTimer(self)
        self._timer.setSingleShot(True)
        self._timer.setInterval(25)
        self._timer.timeout.connect(self.reconstruir)
        self.setMinimumSize(420, 260)

    def estilo_mudou(self):
        self._timer.start()

    def resizeEvent(self, e):
        self._timer.start()

    def reconstruir(self):
        t = self.t
        dpr = self.devicePixelRatioF()
        w, h = max(1, self.width()), max(1, self.height())
        self._layer = QPixmap(int(w * dpr), int(h * dpr))
        self._layer.setDevicePixelRatio(dpr)
        self._layer.fill(Qt.transparent)
        self._alvo = alvo_tela(QRectF(0, 0, w, h), t.sw, t.sh)
        self._cont, self._versao, self._marca = [], t.versao, t.contador
        self._desenhar_novos()
        self.update()

    def _desenhar_novos(self):
        t, alvo = self.t, self._alvo
        esc = alvo.width() / t.sw
        p = QPainter(self._layer)
        p.setRenderHint(QPainter.Antialiasing)
        p.setPen(QPen(QColor(self.estilo["risco"]), self.estilo["espessura"], Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
        for i in range(len(t.tracos)):
            pts = t.tracos[i]
            n = len(pts)
            while len(self._cont) <= i:
                self._cont.append(0)
            c0 = self._cont[i]
            if n > c0:
                trecho = pts[max(c0 - 1, 0):n]
                if len(trecho) >= 2:
                    p.drawPolyline(QPolygonF([QPointF(alvo.left() + (x - t.ox) * esc,
                                                      alvo.top() + (y - t.oy) * esc) for x, y in trecho]))
                self._cont[i] = n
        p.end()

    def tick(self):
        t = self.t
        if self._layer is None or t.versao != self._versao:
            self.reconstruir()
        elif self._marca != t.contador:
            self._marca = t.contador
            self._desenhar_novos()
            self.update()

    def paintEvent(self, e):
        if self._layer is None:
            self.reconstruir()
        t, alvo = self.t, self._alvo
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        rr = QPainterPath()
        rr.addRoundedRect(alvo, 12, 12)
        p.fillPath(rr, QBrush(QColor(self.estilo["fundo"])))
        p.setPen(QPen(QColor(255, 255, 255, 50), 1))
        p.drawPath(rr)
        esc = alvo.width() / t.sw
        if len(t.telas) > 1:                                  # contorno de cada monitor
            p.setPen(QPen(QColor(255, 255, 255, 40), 1, Qt.DashLine))
            for r in t.telas:
                p.drawRect(QRectF(alvo.left() + (r.x() - t.ox) * esc, alvo.top() + (r.y() - t.oy) * esc,
                                  r.width() * esc, r.height() * esc))
        p.drawPixmap(0, 0, self._layer)
        cab = t.tracos[-1][-1] if (t.estado == t.RASTREANDO and t.tracos and t.tracos[-1]) else None
        desenhar_pontos(p, alvo, t.ox, t.oy, esc, [s[0] for s in t.tracos if s], list(t.pontos), self.estilo, 1.0, cab)
        if not t.tracos and not t.pontos:
            p.setPen(QColor(0, 0, 0, 130))
            p.drawText(alvo, Qt.AlignCenter, self.dica)


def _caixa(a, r):
    """Desfoque de caixa rápido (cumsum) nos dois eixos."""
    k = 2 * r + 1
    for ax in (1, 0):
        pad = [(0, 0), (0, 0)]
        pad[ax] = (r + 1, r)
        c = np.cumsum(np.pad(a, pad), axis=ax, dtype=np.float32)
        a = (c[:, k:] - c[:, :-k]) / k if ax == 1 else (c[k:, :] - c[:-k, :]) / k
    return a


def criar_lut():
    stops = [(0.00, (0, 0, 0, 0)), (0.10, (36, 14, 92, 80)), (0.30, (112, 26, 132, 175)),
             (0.55, (222, 52, 82, 215)), (0.80, (255, 152, 42, 236)), (1.00, (255, 242, 176, 250))]
    xs = [s[0] for s in stops]
    lut = np.zeros((256, 4), np.uint8)
    for c in range(4):
        lut[:, c] = np.interp(np.linspace(0, 1, 256), xs, [s[1][c] for s in stops])
    return lut


LUT = criar_lut()


class CalorWidget(QWidget):
    """Mapa de calor contínuo: densidade acumulada ao longo do trajeto, suavizada e colorida."""

    def __init__(self, tracker):
        super().__init__()
        self.t = tracker
        self._img = None
        self._versao = -1
        self._ultimo = 0.0
        self.suave = 2
        self.setMinimumSize(420, 260)

    def tick(self):
        t = self.t
        agora = time.time()
        if t.versao != self._versao or (t.calor_sujo and agora - self._ultimo > 0.4):
            self._versao, self._ultimo, t.calor_sujo = t.versao, agora, False
            self.construir()
            self.update()

    def construir(self):
        b = self.t.dens
        if not b.any():
            self._img = None
            return
        r = self.suave + 1                      # raio da caixa (antes ~6; agora 3 por padrão)
        for _ in range(3):                       # 3 passes de caixa ~ gaussiana
            b = _caixa(b, r)
        pos = b[b > 1e-3]
        if pos.size == 0:
            self._img = None
            return
        mx = float(np.percentile(pos, 99.6)) or 1.0
        v = np.clip(b / mx, 0, 1) ** 0.6
        rgba = np.ascontiguousarray(LUT[(v * 255).astype(np.uint8)])
        h, w = v.shape
        self._img = QImage(rgba.data, w, h, w * 4, QImage.Format.Format_RGBA8888).copy()

    def paintEvent(self, e):
        t = self.t
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        p.setRenderHint(QPainter.SmoothPixmapTransform)
        alvo = alvo_tela(QRectF(self.rect()), t.sw, t.sh)
        rr = QPainterPath()
        rr.addRoundedRect(alvo, 12, 12)
        p.fillPath(rr, QBrush(QColor(6, 7, 12, 150)))
        p.save()
        p.setClipPath(rr)
        if self._img is not None:
            p.drawImage(alvo, self._img)
        p.restore()
        p.setPen(QPen(QColor(255, 255, 255, 45), 1))
        p.drawPath(rr)
        if len(t.telas) > 1:
            esc = alvo.width() / t.sw
            p.setPen(QPen(QColor(255, 255, 255, 35), 1, Qt.DashLine))
            for r in t.telas:
                p.drawRect(QRectF(alvo.left() + (r.x() - t.ox) * esc, alvo.top() + (r.y() - t.oy) * esc,
                                  r.width() * esc, r.height() * esc))
        if self._img is None:
            p.setPen(QColor(255, 255, 255, 90))
            p.drawText(alvo, Qt.AlignCenter, "—")


# ----------------------------------------------------------------------------------------
# Timelapse
# ----------------------------------------------------------------------------------------
class LinhaTempo:
    """Reconstrói a sessão (riscos, pontos, cliques múltiplos) a partir dos eventos."""

    def __init__(self, eventos, m):
        self.ox, self.oy = m["ox"], m["oy"]
        self.sw, self.sh = max(1.0, m["sw"]), max(1.0, m["sh"])
        self.telas = [QRectF(*r) for r in m.get("telas", [])]
        multi, raio = m.get("multi_s", 0.4), m.get("raio", 8)
        self.tm, self.px, self.py, self.sid = [], [], [], []
        self.inicios, self.inicios_t, self.cliques = [], [], []
        sid, novo, ant, ult = -1, True, None, None
        for t, tempo, tipo, x, y, det in eventos:
            if tipo == "retomar":
                novo = True
                continue
            if tipo not in ("movimento", "clique_down"):
                continue
            if ant and (t - ant[0]) - (tempo - ant[1]) > 0.5:      # pausa sem marcador (arquivos antigos)
                novo = True
            ant = (t, tempo)
            if novo:
                sid += 1
                novo = False
                self.inicios.append((x, y))
                self.inicios_t.append(tempo)
            if not self.tm or self.sid[-1] != sid or (self.px[-1], self.py[-1]) != (x, y):
                self.tm.append(tempo)
                self.px.append(x)
                self.py.append(y)
                self.sid.append(sid)
            if tipo == "clique_down":
                if ult and ult["b"] == det and t - ult["t"] <= multi and \
                        math.dist((x, y), (ult["x"], ult["y"])) <= raio:
                    ult["tempos"].append(tempo)
                    ult["t"] = t
                else:
                    ult = {"b": det, "t": t, "x": x, "y": y, "tempos": [tempo]}
                    self.cliques.append(ult)
        fins = [self.tm[-1]] if self.tm else [0.0]
        fins += [c["tempos"][-1] for c in self.cliques]
        self.total = max(fins)


def ler_sessao(csv_path):
    """Lê um CSV salvo (e o .json com a geometria dos monitores) e devolve a LinhaTempo."""
    ev = []
    with open(csv_path, newline="", encoding="utf-8") as f:
        for lin in csv.DictReader(f):
            try:
                t = datetime.fromisoformat(lin["data_hora"]).timestamp()
                ev.append((t, float(lin["tempo_ativo_s"]), lin["evento"],
                           int(float(lin["x"])), int(float(lin["y"])), lin["detalhe"]))
            except (ValueError, KeyError):
                continue
    try:
        m = json.loads(Path(csv_path).with_suffix(".json").read_text(encoding="utf-8"))
    except Exception:
        u, telas = area_monitores()
        m = {"ox": u.x(), "oy": u.y(), "sw": u.width(), "sh": u.height(),
             "telas": [[r.x(), r.y(), r.width(), r.height()] for r in telas]}
    return LinhaTempo(ev, m)


class Renderizador:
    """Desenha a sessão até o instante T. Avançando no tempo só desenha o trecho novo."""

    def __init__(self, lt, estilo, W, H, fator=1.0, dpr=1.0, margem=0):
        self.lt, self.estilo, self.fator = lt, estilo, fator
        self.W, self.H, self.dpr = int(W), int(H), dpr
        self.alvo = alvo_tela(QRectF(0, 0, self.W, self.H), lt.sw, lt.sh, margem)
        self.esc = self.alvo.width() / lt.sw
        self.reiniciar()

    def reiniciar(self):
        self.layer = QImage(int(self.W * self.dpr), int(self.H * self.dpr),
                            QImage.Format.Format_ARGB32_Premultiplied)
        self.layer.setDevicePixelRatio(self.dpr)
        self.layer.fill(Qt.transparent)
        self.i = 0

    def mapa(self, x, y):
        return QPointF(self.alvo.left() + (x - self.lt.ox) * self.esc,
                       self.alvo.top() + (y - self.lt.oy) * self.esc)

    def avancar(self, T):
        lt = self.lt
        j = bisect_right(lt.tm, T)
        if j < self.i:
            self.reiniciar()
        if j > self.i:
            p = QPainter(self.layer)
            p.setRenderHint(QPainter.Antialiasing)
            p.setPen(QPen(QColor(self.estilo["risco"]), self.estilo["espessura"] * self.fator,
                          Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
            corrida = []
            for k in range(max(self.i - 1, 0), j):
                if corrida and lt.sid[k] != lt.sid[k - 1]:
                    if len(corrida) > 1:
                        p.drawPolyline(QPolygonF(corrida))
                    corrida = []
                corrida.append(self.mapa(lt.px[k], lt.py[k]))
            if len(corrida) > 1:
                p.drawPolyline(QPolygonF(corrida))
            p.end()
            self.i = j

    def pintar(self, p, T):
        lt = self.lt
        self.avancar(T)
        p.setRenderHint(QPainter.Antialiasing)
        rr = QPainterPath()
        rr.addRoundedRect(self.alvo, 12 * self.fator, 12 * self.fator)
        p.fillPath(rr, QBrush(QColor(self.estilo["fundo"])))
        p.setPen(QPen(QColor(255, 255, 255, 50), max(1.0, self.fator)))
        p.drawPath(rr)
        p.drawImage(0, 0, self.layer)
        cliq = []
        for c in lt.cliques:
            if c["tempos"][0] > T:
                break
            cliq.append((c["x"], c["y"], c["b"], bisect_right(c["tempos"], T)))
        cab = (lt.px[self.i - 1], lt.py[self.i - 1]) if self.i > 0 else None
        desenhar_pontos(p, self.alvo, lt.ox, lt.oy, self.esc,
                        lt.inicios[:bisect_right(lt.inicios_t, T)], cliq, self.estilo, self.fator, cab)


class TimelapseWidget(QWidget):
    def __init__(self, estilo):
        super().__init__()
        self.estilo, self.lt, self.rend, self.progresso = estilo, None, None, 0.0
        self.setMinimumSize(420, 260)

    def definir(self, lt):
        self.lt, self.rend, self.progresso = lt, None, 0.0
        self.update()

    def invalidar(self):
        self.rend = None
        self.update()

    def set_progresso(self, f):
        self.progresso = min(1.0, max(0.0, f))
        self.update()

    def resizeEvent(self, e):
        self.rend = None

    def paintEvent(self, e):
        p = QPainter(self)
        if self.lt is None:
            p.setRenderHint(QPainter.Antialiasing)
            r = QRectF(self.rect()).adjusted(6, 6, -6, -6)
            rr = QPainterPath()
            rr.addRoundedRect(r, 12, 12)
            p.fillPath(rr, QBrush(QColor(255, 255, 255, 12)))
            p.setPen(QPen(QColor(255, 255, 255, 45), 1))
            p.drawPath(rr)
            p.setPen(QColor(255, 255, 255, 90))
            p.drawText(r, Qt.AlignCenter, "—")
            return
        if self.rend is None:
            self.rend = Renderizador(self.lt, self.estilo, self.width(), self.height(),
                                     1.0, self.devicePixelRatioF(), 6)
        self.rend.pintar(p, self.progresso * self.lt.total)


class ExportadorGif(QObject):
    """Gera o GIF aos poucos (um pedaço por ciclo do laço de eventos): a interface continua
    fluida e dá para cancelar."""
    progresso = Signal(int)
    terminou = Signal(str, str)          # (caminho, erro); os dois vazios = cancelado

    def __init__(self, lt, estilo, destino, largura, duracao, fps=10, parent=None):
        super().__init__(parent)
        self.lt, self.estilo, self.destino, self.fps = lt, dict(estilo), destino, fps
        self.W = int(largura)
        self.H = max(1, round(self.W * lt.sh / lt.sw))
        self.n = max(2, int(duracao * fps))
        self.i = 0
        self.cancelado = False
        self.gif = None
        self.rend = None
        self.img = QImage(self.W, self.H, QImage.Format.Format_RGB32)

    def _novo_rend(self):
        return Renderizador(self.lt, self.estilo, self.W, self.H, self.W / 900)

    def _quadro(self, rend, T):
        self.img.fill(QColor(22, 23, 31))
        p = QPainter(self.img)
        rend.pintar(p, T)
        p.end()
        bpl = self.img.bytesPerLine()
        a = np.frombuffer(self.img.constBits(), np.uint8, count=bpl * self.H).reshape(self.H, bpl)
        return a[:, :self.W * 4].reshape(self.H, self.W, 4)[:, :, [2, 1, 0]].copy()

    def iniciar(self):
        try:
            paleta = paleta_de(self._quadro(self._novo_rend(), self.lt.total))
            self.rend = self._novo_rend()
            self.gif = GifWriter(self.destino, self.W, self.H, max(2, round(100 / self.fps)), paleta)
        except Exception as ex:
            self._fim(str(ex))
            return
        QTimer.singleShot(0, self._passo)

    def cancelar(self):
        self.cancelado = True

    def _passo(self):
        if self.cancelado:
            self._fim(cancelado=True)
            return
        t0 = time.perf_counter()
        try:
            while self.i < self.n:
                T = self.lt.total * self.i / (self.n - 1)
                self.gif.adicionar(self._quadro(self.rend, T))
                self.i += 1
                if time.perf_counter() - t0 > 0.012:
                    break
        except Exception as ex:
            self._fim(str(ex))
            return
        self.progresso.emit(int(100 * self.i / self.n))
        if self.i >= self.n:
            self._fim()
        else:
            QTimer.singleShot(0, self._passo)

    def _fim(self, erro="", cancelado=False):
        if self.gif:
            try:
                self.gif.fechar()
            except Exception:
                pass
        if erro or cancelado:
            try:
                os.remove(self.destino)
            except OSError:
                pass
            self.terminou.emit("", erro)
        else:
            self.terminou.emit(self.destino, "")


class Sinais(QObject):
    iniciar, pausar, parar = Signal(), Signal(), Signal()


# ----------------------------------------------------------------------------------------
# Janela principal
# ----------------------------------------------------------------------------------------
class Janela(QWidget):
    PAGINAS = [("cursor", "Rastreio"), ("heat", "Calor"), ("play", "Timelapse"),
               ("image", "Cliques"), ("gear", "Ajustes"), ("user", "Perfil")]
    PG_RASTREIO, PG_CALOR, PG_TIMELAPSE, PG_CLIQUES, PG_AJUSTES, PG_PERFIL = range(6)

    def __init__(self):
        super().__init__()
        PASTA_CLIQUES.mkdir(parents=True, exist_ok=True)
        self.cfg = carregar_config()
        self.estilo = {"risco": QColor(self.cfg["cor_risco"]), "ponto": QColor(self.cfg["cor_ponto"]),
                       "fundo": QColor(self.cfg["cor_fundo"]), "espessura": float(self.cfg["espessura"])}
        self.tracker = Rastreador()
        self.sinais = Sinais()
        self.hk = None
        self._foto_nova = None
        self._cache_ui = None
        self._n = 0
        self.img_tela = self.bg = self.bg_geo = None
        self.bg_k = 1.0
        self._cache = None
        self._cache_key = None

        self.setWindowTitle("Rastreador de Mouse")
        self.setWindowFlags(Qt.Window | Qt.FramelessWindowHint |
                            (Qt.WindowStaysOnTopHint if self.cfg["topo"] else Qt.Widget))
        self.setAttribute(Qt.WA_TranslucentBackground, True)
        self.resize(1200, 740)
        self.setMinimumSize(1000, 620)
        self.setStyleSheet(QSS)

        self.capturar_fundo()
        self.montar_ui()
        self.grip = QSizeGrip(self)

        self.sinais.iniciar.connect(self.ao_iniciar)
        self.sinais.pausar.connect(self.ao_pausar)
        self.sinais.parar.connect(self.ao_parar)
        self.reiniciar_atalhos()

        self.timer = QTimer(self)
        self.timer.setTimerType(Qt.PreciseTimer)
        self.timer.timeout.connect(self.tick)
        self.timer.start(16)                      # ~60 quadros por segundo
        self.atualizar_perfil()
        self.atualizar_galeria()
        self.atualizar_ui(forcar=True)

    # ---------- fundo desfocado ----------
    def capturar_fundo(self):
        scr = self.screen() or QGuiApplication.primaryScreen()
        pix = scr.grabWindow(0)
        if pix.isNull():
            self.img_tela = self.bg = None
            return
        self.img_tela, self.bg_geo = pix.toImage(), scr.geometry()
        self.aplicar_desfoque()

    def aplicar_desfoque(self):
        if self.img_tela is None:
            return
        img, (w, h) = self.img_tela, (self.img_tela.width(), self.img_tela.height())
        f = max(6, self.cfg["desfoque"] * 7)
        s = img.scaled(max(1, w // 3), max(1, h // 3), Qt.IgnoreAspectRatio, Qt.SmoothTransformation)
        s = s.scaled(max(1, w // f), max(1, h // f), Qt.IgnoreAspectRatio, Qt.SmoothTransformation)
        k = max(2, f // 3)
        s = s.scaled(max(1, w // k), max(1, h // k), Qt.IgnoreAspectRatio, Qt.SmoothTransformation)
        self.bg = QPixmap.fromImage(s.scaled(w, h, Qt.IgnoreAspectRatio, Qt.SmoothTransformation))
        qp = QPainter(self.bg)
        qp.fillRect(self.bg.rect(), QColor(0, 0, 0, DIM))
        qp.end()
        self.bg_k = w / max(1, self.bg_geo.width())
        self.invalidar_fundo()

    def atualizar_fundo(self):
        self.setWindowOpacity(0.0)

        def refazer():
            self.capturar_fundo()
            self.setWindowOpacity(1.0)
            self.toast("Fundo atualizado")
        QTimer.singleShot(260, refazer)

    def invalidar_fundo(self):
        self._cache = None
        self.update()

    def fundo_pronto(self):
        W, H, dpr = self.width(), self.height(), self.devicePixelRatioF()
        pos = self.mapToGlobal(QPoint(0, 0))
        chave = (W, H, dpr, pos.x(), pos.y(), self.cfg["vidro"])
        if self._cache is not None and self._cache_key == chave:
            return self._cache
        px = QPixmap(int(W * dpr), int(H * dpr))
        px.setDevicePixelRatio(dpr)
        px.fill(Qt.transparent)
        p = QPainter(px)
        p.setRenderHint(QPainter.Antialiasing)
        borda = QPainterPath()
        borda.addRoundedRect(QRectF(0.5, 0.5, W - 1, H - 1), 26, 26)
        p.setClipPath(borda)
        if self.bg is not None:
            o, k = pos - self.bg_geo.topLeft(), self.bg_k
            p.drawPixmap(QRectF(0, 0, W, H), self.bg, QRectF(o.x() * k, o.y() * k, W * k, H * k))
        else:
            g = QLinearGradient(0, 0, W, H)
            g.setColorAt(0, QColor(34, 34, 48))
            g.setColorAt(1, QColor(14, 16, 24))
            p.fillRect(QRectF(0, 0, W, H), g)
        p.fillRect(QRectF(0, 0, W, H), QColor(10, 11, 18, self.cfg["vidro"]))
        brilho = QLinearGradient(0, 0, 0, H)
        brilho.setColorAt(0, QColor(255, 255, 255, 22))
        brilho.setColorAt(1, QColor(255, 255, 255, 0))
        p.fillRect(QRectF(0, 0, W, H), brilho)
        p.setClipping(False)
        p.setPen(QPen(QColor(255, 255, 255, 50), 1))
        p.setBrush(Qt.NoBrush)
        p.drawPath(borda)
        p.end()
        self._cache, self._cache_key = px, chave
        return px

    def paintEvent(self, e):
        p = QPainter(self)
        p.drawPixmap(0, 0, self.fundo_pronto())

    def moveEvent(self, e):
        self.update()

    def resizeEvent(self, e):
        if hasattr(self, "grip"):
            self.grip.move(self.width() - 24, self.height() - 24)
        if hasattr(self, "_toast") and self._toast.isVisible():
            self.posicionar_toast()

    def mousePressEvent(self, e):
        if e.button() == Qt.LeftButton and e.position().y() < 84 and self.windowHandle():
            self.windowHandle().startSystemMove()

    # ---------- interface ----------
    def montar_ui(self):
        raiz = QHBoxLayout(self)
        raiz.setContentsMargins(16, 16, 16, 16)
        raiz.setSpacing(12)

        self.barra = Vidro()
        self.barra.setFixedWidth(62)
        bl = QVBoxLayout(self.barra)
        bl.setContentsMargins(5, 10, 5, 10)
        bl.setSpacing(3)
        self.btn_menu = NavBtn("menu", "Menu", checkable=False)
        self.btn_menu.clicked.connect(self.alternar_barra)
        bl.addWidget(self.btn_menu)
        bl.addSpacing(12)
        self.nav = []
        for i, (ico, nome) in enumerate(self.PAGINAS):
            b = NavBtn(ico, nome)
            b.clicked.connect(lambda _=False, i=i: self.ir_para(i))
            bl.addWidget(b)
            self.nav.append(b)
        bl.addStretch()
        self.anim = QVariantAnimation(self)
        self.anim.setDuration(240)
        self.anim.setEasingCurve(QEasingCurve.OutCubic)
        self.anim.valueChanged.connect(lambda v: self.barra.setFixedWidth(int(v)))
        raiz.addWidget(self.barra)

        col = QVBoxLayout()
        col.setSpacing(12)
        raiz.addLayout(col, 1)

        cab = Vidro()
        cab.setFixedHeight(56)
        cl = QHBoxLayout(cab)
        cl.setContentsMargins(22, 0, 12, 0)
        cl.setSpacing(10)
        self.lbl_titulo = rotulo("", 11, QFont.Normal, 4, 200, True)
        cl.addWidget(self.lbl_titulo)
        cl.addStretch()
        self.lbl_estado = QLabel()
        cl.addWidget(self.lbl_estado)
        cl.addSpacing(10)
        self.av_cab = QLabel()
        self.av_cab.setFixedSize(32, 32)
        self.nome_cab = rotulo("", 12, QFont.Light, 0.5, 220)
        cl.addWidget(self.av_cab)
        cl.addWidget(self.nome_cab)
        cl.addSpacing(6)
        for txt, fn in (("–", self.showMinimized), ("×", self.close)):
            b = QPushButton(txt)
            b.setProperty("variant", "ghost")
            b.setFixedSize(30, 30)
            b.setCursor(Qt.PointingHandCursor)
            b.clicked.connect(fn)
            cl.addWidget(b)
        col.addWidget(cab)

        self.pilha = QStackedWidget()
        for pg in (self.pagina_rastreio(), self.pagina_calor(), self.pagina_timelapse(),
                   self.pagina_galeria(), self.pagina_ajustes(), self.pagina_perfil()):
            self.pilha.addWidget(pg)
        col.addWidget(self.pilha, 1)

        self._toast = QLabel(self)
        self._toast.setObjectName("toast")
        self._toast.hide()
        self.ir_para(0)

    def alternar_barra(self):
        ini = self.barra.width()
        self.anim.stop()
        self.anim.setStartValue(ini)
        self.anim.setEndValue(176 if ini < 110 else 62)
        self.anim.start()

    def ir_para(self, i):
        self.pilha.setCurrentIndex(i)
        for k, b in enumerate(self.nav):
            b.setChecked(k == i)
        self.lbl_titulo.setText(self.PAGINAS[i][1].upper())
        if i != self.PG_TIMELAPSE and self.tl_tocando:
            self.tl_tocando = False
            self.btn_play.setText("reproduzir")
        if i == self.PG_CLIQUES:
            self.atualizar_galeria()
        elif i == self.PG_TIMELAPSE:
            self.atualizar_fontes()

    # ---------- rastreio ----------
    def pagina_rastreio(self):
        pg = QWidget()
        lay = QHBoxLayout(pg)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(12)

        esq = QVBoxLayout()
        esq.setSpacing(10)
        self.traco = TracoWidget(self.tracker, self.estilo)
        esq.addWidget(self.traco, 1)

        tb = Vidro()
        tb.setFixedHeight(50)
        tl = QHBoxLayout(tb)
        tl.setContentsMargins(12, 0, 14, 0)
        tl.setSpacing(8)
        for chave, nome in (("risco", "risco"), ("ponto", "ponto"), ("fundo", "fundo")):
            b = CorBtn(nome, self.estilo[chave])
            b.mudou.connect(lambda c, k=chave: self.mudar_estilo(k, c))
            tl.addWidget(b)
        tl.addSpacing(10)
        tl.addWidget(rotulo("traço", 11, QFont.Light, 1, 160))
        s = QSlider(Qt.Horizontal)
        s.setRange(5, 40)
        s.setValue(int(self.estilo["espessura"] * 10))
        s.setFixedWidth(110)
        s.valueChanged.connect(lambda v: self.mudar_estilo("espessura", v / 10))
        tl.addWidget(s)
        tl.addStretch()
        esq.addWidget(tb)
        lay.addLayout(esq, 1)

        lat = Vidro()
        lat.setFixedWidth(196)
        ll = QVBoxLayout(lat)
        ll.setContentsMargins(20, 20, 20, 18)
        ll.setSpacing(6)
        ll.addWidget(rotulo("tempo", 10, QFont.Normal, 3, 110, True))
        self.lbl_tempo = QLabel("00:00:00")
        f = QFont()
        f.setFamilies(["Cascadia Mono", "Consolas", "Menlo", "DejaVu Sans Mono"])
        f.setPixelSize(30)
        f.setWeight(QFont.ExtraLight)
        self.lbl_tempo.setFont(f)
        ll.addWidget(self.lbl_tempo)
        ll.addSpacing(14)
        self.stats = {}
        for chave, rot in (("cliques", "cliques"), ("movimentos", "mov."), ("distancia", "px")):
            linha = QHBoxLayout()
            linha.addWidget(rotulo(rot, 10, QFont.Normal, 2.5, 110, True))
            linha.addStretch()
            self.stats[chave] = rotulo("0", 14, QFont.Light, 0.5, 240)
            linha.addWidget(self.stats[chave])
            ll.addLayout(linha)
        ll.addStretch()
        self.b_ini, self.b_pau, self.b_par = QPushButton(), QPushButton(), QPushButton()
        self.b_ini.setProperty("variant", "primary")
        self.b_par.setProperty("variant", "danger")
        self.b_ini.clicked.connect(self.ao_iniciar)
        self.b_pau.clicked.connect(self.ao_pausar)
        self.b_par.clicked.connect(self.ao_parar)
        for b in (self.b_ini, self.b_pau, self.b_par):
            b.setCursor(Qt.PointingHandCursor)
            b.setMinimumHeight(38)
            ll.addWidget(b)
        b_lim = QPushButton("limpar")
        b_lim.setProperty("variant", "ghost")
        b_lim.setStyleSheet("font-size: 12px; color: rgba(255,255,255,130); padding: 6px;")
        b_lim.setCursor(Qt.PointingHandCursor)
        b_lim.clicked.connect(self.limpar)
        ll.addWidget(b_lim)
        lay.addWidget(lat)
        return pg

    def mudar_estilo(self, chave, valor):
        self.estilo[chave] = float(valor) if chave == "espessura" else QColor(valor)
        self.traco.estilo_mudou()
        self.traco.update()
        self.tl_w.invalidar()

    # ---------- calor ----------
    def pagina_calor(self):
        self.calor = CalorWidget(self.tracker)
        self.calor.suave = self.cfg["calor_suave"]
        return self.calor

    # ---------- galeria ----------
    def pagina_galeria(self):
        v = Vidro()
        lay = QVBoxLayout(v)
        lay.setContentsMargins(20, 16, 20, 16)
        topo = QHBoxLayout()
        topo.addStretch()
        for txt, fn in (("timelapse", self.abrir_timelapse), ("renomear", self.renomear),
                        ("exportar", self.exportar), ("excluir", self.excluir),
                        ("pasta", self.abrir_pasta)):
            b = QPushButton(txt)
            b.clicked.connect(lambda _=False, f=fn: f())
            topo.addWidget(b)
        lay.addLayout(topo)
        self.lista = QListWidget()
        self.lista.setViewMode(QListWidget.IconMode)
        self.lista.setResizeMode(QListWidget.Adjust)
        self.lista.setMovement(QListWidget.Static)
        self.lista.setIconSize(QSize(240, 135))
        self.lista.setGridSize(QSize(268, 196))
        self.lista.setWordWrap(True)
        self.lista.setSelectionMode(QAbstractItemView.SingleSelection)
        self.lista.itemDoubleClicked.connect(self.previa)
        lay.addWidget(self.lista, 1)
        self.lbl_vazio = rotulo("nada salvo ainda", 12, QFont.Light, 2, 110, True)
        self.lbl_vazio.setAlignment(Qt.AlignCenter)
        lay.addWidget(self.lbl_vazio)
        return v

    def atualizar_galeria(self):
        self.lista.clear()
        arqs = sorted(PASTA_CLIQUES.glob("*.png"), key=lambda a: a.stat().st_mtime, reverse=True)
        for a in arqs:
            pm = QPixmap(str(a)).scaled(240, 135, Qt.KeepAspectRatio, Qt.SmoothTransformation)
            it = QListWidgetItem(QIcon(pm), a.stem)
            it.setData(Qt.UserRole, str(a))
            self.lista.addItem(it)
        self.lbl_vazio.setVisible(not arqs)
        self.lista.setVisible(bool(arqs))

    def _selecionado(self):
        it = self.lista.currentItem()
        if not it:
            self.toast("Selecione uma imagem")
            return None
        return Path(it.data(Qt.UserRole))

    def renomear(self, arq=None):
        arq = arq or self._selecionado()
        if not arq:
            return
        nome, ok = QInputDialog.getText(self, "Nome", "", text=arq.stem)
        nome = re.sub(r'[\\/:*?"<>|]+', "_", nome).strip()
        if not ok or not nome or nome == arq.stem:
            return
        novo = arq.with_name(nome + ".png")
        if novo.exists():
            QMessageBox.warning(self, "", "Esse nome já existe.")
            return
        arq.rename(novo)
        for ext in (".csv", ".json"):
            if arq.with_suffix(ext).exists():
                arq.with_suffix(ext).rename(novo.with_suffix(ext))
        self.atualizar_galeria()

    def exportar(self, arq=None):
        arq = arq or self._selecionado()
        if not arq:
            return
        destino, _ = QFileDialog.getSaveFileName(self, "Exportar", f"{arq.stem}.png", "PNG (*.png)")
        if destino:
            shutil.copy(arq, destino)
            self.toast("Exportado")

    def excluir(self):
        arq = self._selecionado()
        if arq and QMessageBox.question(self, "", f"Excluir '{arq.stem}'?") == QMessageBox.Yes:
            for ext in (".png", ".csv", ".json"):
                arq.with_suffix(ext).unlink(missing_ok=True)
            self.atualizar_galeria()

    def abrir_pasta(self):
        QDesktopServices.openUrl(QUrl.fromLocalFile(str(PASTA_CLIQUES)))

    def previa(self, item):
        arq = Path(item.data(Qt.UserRole))
        d = QDialog(self)
        d.setWindowTitle(arq.stem)
        lay = QVBoxLayout(d)
        img = QLabel()
        img.setPixmap(QPixmap(str(arq)).scaled(940, 580, Qt.KeepAspectRatio, Qt.SmoothTransformation))
        lay.addWidget(img)
        linha = QHBoxLayout()
        b1, b2, b3 = QPushButton("nomear"), QPushButton("exportar"), QPushButton("fechar")
        b1.clicked.connect(lambda: (self.renomear(arq), d.accept()))
        b2.clicked.connect(lambda: self.exportar(arq))
        b3.clicked.connect(d.accept)
        linha.addWidget(b1)
        linha.addWidget(b2)
        linha.addStretch()
        linha.addWidget(b3)
        lay.addLayout(linha)
        d.exec()

    # ---------- timelapse ----------
    def pagina_timelapse(self):
        self.tl_lt, self.tl_tocando, self.tl_ult, self.tl_dur, self.tl_exp = None, False, 0.0, 30, None
        pg = QWidget()
        lay = QHBoxLayout(pg)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(12)

        esq = QVBoxLayout()
        esq.setSpacing(10)
        self.tl_w = TimelapseWidget(self.estilo)
        esq.addWidget(self.tl_w, 1)
        barra = Vidro()
        barra.setFixedHeight(50)
        bl = QHBoxLayout(barra)
        bl.setContentsMargins(12, 0, 16, 0)
        bl.setSpacing(12)
        self.btn_play = QPushButton("reproduzir")
        self.btn_play.setFixedWidth(112)
        self.btn_play.setCursor(Qt.PointingHandCursor)
        self.btn_play.clicked.connect(self.tl_alternar)
        bl.addWidget(self.btn_play)
        self.sl_prog = QSlider(Qt.Horizontal)
        self.sl_prog.setRange(0, 1000)
        self.sl_prog.valueChanged.connect(self.tl_arrastar)
        bl.addWidget(self.sl_prog, 1)
        self.lbl_tl = rotulo("00:00 / 00:00", 11, QFont.Light, 1, 190)
        bl.addWidget(self.lbl_tl)
        esq.addWidget(barra)
        lay.addLayout(esq, 1)

        lat = Vidro()
        lat.setFixedWidth(196)
        ll = QVBoxLayout(lat)
        ll.setContentsMargins(20, 20, 20, 18)
        ll.setSpacing(8)
        ll.addWidget(rotulo("fonte", 10, QFont.Normal, 3, 110, True))
        self.cb_fonte = QComboBox()
        self.cb_fonte.currentIndexChanged.connect(lambda _=0: self.carregar_fonte())
        ll.addWidget(self.cb_fonte)
        ll.addSpacing(8)
        ll.addWidget(rotulo("duração", 10, QFont.Normal, 3, 110, True))
        self.sl_dur = QSlider(Qt.Horizontal)
        self.sl_dur.setRange(1, 60)                      # no máximo 1 minuto
        self.sl_dur.setValue(30)
        self.sl_dur.valueChanged.connect(lambda _=0: self.tl_rotulos())
        ll.addWidget(self.sl_dur)
        self.lbl_dur = rotulo("30 s", 12, QFont.Light, 0.5, 210)
        ll.addWidget(self.lbl_dur)
        ll.addSpacing(8)
        ll.addWidget(rotulo("tamanho", 10, QFont.Normal, 3, 110, True))
        self.cb_tam = QComboBox()
        for txt, v in (("480 px", 480), ("640 px", 640), ("800 px", 800)):
            self.cb_tam.addItem(txt, v)
        self.cb_tam.setCurrentIndex(1)
        ll.addWidget(self.cb_tam)
        ll.addStretch()
        self.pb = QProgressBar()
        self.pb.setTextVisible(False)
        self.pb.setRange(0, 100)
        ll.addWidget(self.pb)
        self.btn_gif = QPushButton("gerar gif")
        self.btn_gif.setProperty("variant", "primary")
        self.btn_gif.setMinimumHeight(38)
        self.btn_gif.setCursor(Qt.PointingHandCursor)
        self.btn_gif.clicked.connect(self.tl_gif)
        ll.addWidget(self.btn_gif)
        lay.addWidget(lat)
        return pg

    @staticmethod
    def _mmss(s):
        s = int(s)
        return f"{s // 60:02d}:{s % 60:02d}"

    def atualizar_fontes(self):
        antiga = self.cb_fonte.currentData()
        self.tracker.processar()
        self.cb_fonte.blockSignals(True)
        self.cb_fonte.clear()
        if self.tracker.tem_dados():
            self.cb_fonte.addItem("sessão atual", "__atual__")
        for a in sorted(PASTA_CLIQUES.glob("*.csv"), key=lambda a: a.stat().st_mtime, reverse=True):
            self.cb_fonte.addItem(a.stem, str(a))
        i = self.cb_fonte.findData(antiga)
        self.cb_fonte.setCurrentIndex(i if i >= 0 else 0)
        self.cb_fonte.blockSignals(False)
        if self.cb_fonte.count() == 0:
            self.tl_lt = None
            self.tl_w.definir(None)
            self.btn_gif.setEnabled(False)
            self.tl_rotulos()
        elif self.cb_fonte.currentData() != antiga or antiga == "__atual__":
            self.carregar_fonte()

    def carregar_fonte(self):
        chave = self.cb_fonte.currentData()
        self.tl_tocando = False
        self.btn_play.setText("reproduzir")
        lt = None
        try:
            if chave == "__atual__":
                self.tracker.processar()
                lt = LinhaTempo(list(self.tracker.eventos), self.tracker.meta())
            elif chave:
                lt = ler_sessao(Path(chave))
        except Exception as ex:
            self.toast(f"Erro ao ler: {ex}")
        self.tl_lt = lt
        self.tl_w.definir(lt)
        self.sl_prog.blockSignals(True)
        self.sl_prog.setValue(0)
        self.sl_prog.blockSignals(False)
        if lt:
            self.sl_dur.blockSignals(True)
            self.sl_dur.setValue(max(1, min(60, math.ceil(lt.total))))   # nunca passa de 1 minuto
            self.sl_dur.blockSignals(False)
        self.btn_gif.setEnabled(bool(lt and lt.total > 0))
        self.tl_rotulos()

    def tl_rotulos(self):
        dur = self.sl_dur.value()
        self.tl_dur = dur
        lt = self.tl_lt
        if lt and lt.total > 0:
            self.lbl_dur.setText(f"{dur} s   ·   ×{lt.total / dur:.1f}")
        else:
            self.lbl_dur.setText(f"{dur} s")
        f = self.tl_w.progresso
        self.lbl_tl.setText(f"{self._mmss(f * dur)} / {self._mmss(dur)}")

    def tl_alternar(self):
        if not self.tl_lt or self.tl_lt.total <= 0:
            return
        if self.tl_tocando:
            self.tl_tocando = False
            self.btn_play.setText("reproduzir")
        else:
            if self.tl_w.progresso >= 1:
                self.tl_w.set_progresso(0)
            self.tl_tocando = True
            self.tl_ult = time.perf_counter()
            self.btn_play.setText("pausar")

    def tl_arrastar(self, v):
        self.tl_w.set_progresso(v / 1000)
        self.tl_rotulos()

    def tl_tick(self):
        if not (self.tl_tocando and self.tl_lt):
            return
        agora = time.perf_counter()
        dt, self.tl_ult = agora - self.tl_ult, agora
        f = self.tl_w.progresso + dt / max(1, self.tl_dur)
        if f >= 1:
            f = 1.0
            self.tl_tocando = False
            self.btn_play.setText("reproduzir")
        self.tl_w.set_progresso(f)
        self.sl_prog.blockSignals(True)
        self.sl_prog.setValue(int(f * 1000))
        self.sl_prog.blockSignals(False)
        self.tl_rotulos()

    def abrir_timelapse(self):
        arq = self._selecionado()
        if not arq:
            return
        self.ir_para(self.PG_TIMELAPSE)
        i = self.cb_fonte.findData(str(arq.with_suffix(".csv")))
        if i < 0:
            self.toast("Este rastro não tem dados de tempo")
            return
        self.cb_fonte.blockSignals(True)
        self.cb_fonte.setCurrentIndex(i)
        self.cb_fonte.blockSignals(False)
        self.carregar_fonte()

    def tl_gif(self):
        if self.tl_exp:                                  # já exportando: o botão vira "cancelar"
            self.tl_exp.cancelar()
            return
        lt = self.tl_lt
        if not lt or lt.total <= 0:
            return
        nome = re.sub(r"\W+", "_", self.cb_fonte.currentText()).strip("_") or "rastro"
        destino, _ = QFileDialog.getSaveFileName(
            self, "GIF", str(PASTA_CLIQUES / f"{nome}_timelapse.gif"), "GIF (*.gif)")
        if not destino:
            return
        self.tl_tocando = False
        self.btn_play.setText("reproduzir")
        exp = ExportadorGif(lt, self.estilo, destino, self.cb_tam.currentData(), self.tl_dur, parent=self)
        exp.progresso.connect(self.pb.setValue)
        exp.terminou.connect(self.tl_gif_fim)
        self.tl_exp = exp
        self.btn_gif.setText("cancelar")
        self.pb.setValue(0)
        exp.iniciar()

    def tl_gif_fim(self, caminho, erro):
        self.tl_exp = None
        self.btn_gif.setText("gerar gif")
        self.pb.setValue(0)
        self.toast(f"Erro: {erro}" if erro else ("GIF salvo" if caminho else "Cancelado"))

    # ---------- ajustes ----------
    def pagina_ajustes(self):
        pg = QWidget()
        lay = QHBoxLayout(pg)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(12)

        esq = Vidro()
        le = QVBoxLayout(esq)
        le.setContentsMargins(26, 24, 26, 24)
        le.setSpacing(14)
        le.addWidget(rotulo("teclas", 10, QFont.Normal, 3, 110, True))
        self.ed_atalhos = {}
        for chave, rot in (("iniciar", "iniciar"), ("pausar", "pausar"), ("parar", "parar e salvar")):
            linha = QHBoxLayout()
            linha.addWidget(rotulo(rot, 13, QFont.Light, 0.5))
            linha.addStretch()
            ed = QKeySequenceEdit(QKeySequence(self.cfg["atalhos"][chave]))
            try:
                ed.setMaximumSequenceLength(1)
                ed.setClearButtonEnabled(False)
            except Exception:
                pass
            ed.setFixedWidth(150)
            ed.editingFinished.connect(lambda c=chave: self.mudar_atalho(c))
            self.ed_atalhos[chave] = ed
            linha.addWidget(ed)
            le.addLayout(linha)
        le.addStretch()
        lay.addWidget(esq, 1)

        dir_ = Vidro()
        ld = QVBoxLayout(dir_)
        ld.setContentsMargins(26, 24, 26, 24)
        ld.setSpacing(12)
        ld.addWidget(rotulo("visual", 10, QFont.Normal, 3, 110, True))
        ld.addWidget(rotulo("desfoque", 12, QFont.Light, 0.5, 190))
        s1 = QSlider(Qt.Horizontal)
        s1.setRange(1, 5)
        s1.setValue(self.cfg["desfoque"])
        s1.setTracking(False)
        s1.valueChanged.connect(lambda v: (self.cfg.__setitem__("desfoque", v), self.aplicar_desfoque()))
        ld.addWidget(s1)
        ld.addWidget(rotulo("vidro", 12, QFont.Light, 0.5, 190))
        s2 = QSlider(Qt.Horizontal)
        s2.setRange(0, 200)
        s2.setValue(self.cfg["vidro"])
        s2.valueChanged.connect(lambda v: (self.cfg.__setitem__("vidro", v), self.invalidar_fundo()))
        ld.addWidget(s2)
        ld.addWidget(rotulo("calor", 12, QFont.Light, 0.5, 190))
        s3 = QSlider(Qt.Horizontal)
        s3.setRange(1, 6)
        s3.setValue(self.cfg["calor_suave"])
        s3.setTracking(False)
        s3.valueChanged.connect(lambda v: (self.cfg.__setitem__("calor_suave", v),
                                           setattr(self.calor, "suave", v), setattr(self.calor, "_versao", -1)))
        ld.addWidget(s3)
        b = QPushButton("atualizar fundo")
        b.clicked.connect(self.atualizar_fundo)
        ld.addWidget(b)
        ck = QCheckBox("sempre no topo")
        ck.setChecked(self.cfg["topo"])
        ck.toggled.connect(self.alternar_topo)
        ld.addWidget(ck)
        ld.addStretch()
        lay.addWidget(dir_, 1)
        return pg

    def alternar_topo(self, ligado):
        self.cfg["topo"] = ligado
        self.setWindowFlag(Qt.WindowStaysOnTopHint, ligado)
        self.show()

    def mudar_atalho(self, chave):
        ed = self.ed_atalhos[chave]
        novo = ed.keySequence().toString(QKeySequence.PortableText)
        conv = qt_para_pynput(novo)
        outros = [qt_para_pynput(v) for k, v in self.cfg["atalhos"].items() if k != chave]
        if conv is None or conv in outros:
            self.toast("Tecla inválida ou já usada")
            ed.setKeySequence(QKeySequence(self.cfg["atalhos"][chave]))
            return
        self.cfg["atalhos"][chave] = novo
        self.reiniciar_atalhos()
        self.atualizar_ui(forcar=True)
        self.toast(f"{novo}")

    # ---------- perfil ----------
    def pagina_perfil(self):
        pg = QWidget()
        outer = QHBoxLayout(pg)
        outer.setContentsMargins(0, 0, 0, 0)
        card = Vidro()
        card.setFixedWidth(380)
        lay = QVBoxLayout(card)
        lay.setContentsMargins(34, 30, 34, 30)
        lay.setSpacing(12)
        self.av_grande = QLabel()
        self.av_grande.setAlignment(Qt.AlignCenter)
        lay.addWidget(self.av_grande)
        b = QPushButton("foto")
        b.clicked.connect(self.escolher_foto)
        lay.addWidget(b)
        lay.addSpacing(8)
        self.ed_nome = QLineEdit(self.cfg["nome"])
        self.ed_nome.setPlaceholderText("nome")
        lay.addWidget(self.ed_nome)
        s = QPushButton("salvar")
        s.setProperty("variant", "primary")
        s.setMinimumHeight(38)
        s.clicked.connect(self.salvar_perfil)
        lay.addWidget(s)
        lay.addStretch()
        outer.addStretch()
        outer.addWidget(card)
        outer.addStretch()
        return pg

    def escolher_foto(self):
        arq, _ = QFileDialog.getOpenFileName(self, "Foto", "", "Imagens (*.png *.jpg *.jpeg *.bmp *.webp)")
        if arq:
            self._foto_nova = arq
            self.av_grande.setPixmap(avatar_pixmap(arq, self.ed_nome.text(), 140))

    def salvar_perfil(self):
        self.cfg["nome"] = self.ed_nome.text().strip() or "Usuário"
        if self._foto_nova:
            pm = QPixmap(self._foto_nova)
            if not pm.isNull():
                pm = pm.scaled(256, 256, Qt.KeepAspectRatioByExpanding, Qt.SmoothTransformation)
                rec = pm.copy((pm.width() - 256) // 2, (pm.height() - 256) // 2, 256, 256)
                destino = PASTA / "perfil.png"
                rec.save(str(destino), "PNG")
                self.cfg["foto"] = str(destino)
            self._foto_nova = None
        salvar_config(self.cfg)
        self.atualizar_perfil()
        self.toast("Salvo")

    def atualizar_perfil(self):
        self.av_cab.setPixmap(avatar_pixmap(self.cfg["foto"], self.cfg["nome"], 32))
        self.av_grande.setPixmap(avatar_pixmap(self.cfg["foto"], self.cfg["nome"], 140))
        self.nome_cab.setText(self.cfg["nome"])

    # ---------- atalhos globais ----------
    def reiniciar_atalhos(self):
        if self.hk:
            self.hk.stop()
            self.hk = None
        acoes = {"iniciar": self.sinais.iniciar.emit, "pausar": self.sinais.pausar.emit,
                 "parar": self.sinais.parar.emit}
        mapa = {}
        for k, fn in acoes.items():
            conv = qt_para_pynput(self.cfg["atalhos"][k])
            if conv:
                mapa[conv] = fn
        try:
            self.hk = keyboard.GlobalHotKeys(mapa)
            self.hk.start()
        except Exception as ex:
            self.hk = None
            self.toast(f"Atalhos indisponíveis: {ex}")

    # ---------- ações ----------
    def ao_iniciar(self):
        self.tracker.iniciar()
        self.atualizar_ui(forcar=True)

    def ao_pausar(self):
        self.tracker.pausar()
        self.atualizar_ui(forcar=True)

    def ao_parar(self):
        if self.tracker.estado == Rastreador.PARADO:
            return
        self.tracker.parar()
        self.salvar_sessao()
        self.atualizar_ui(forcar=True)

    def limpar(self):
        if self.tracker.estado == Rastreador.PARADO:
            self.tracker.resetar()

    def salvar_sessao(self):
        t = self.tracker
        t.processar()
        if not t.tem_dados():
            self.toast("Nada para salvar")
            return
        nome = f"rastro_{datetime.now():%Y%m%d_%H%M%S}"
        W = 1600
        H = max(1, round(W * t.sh / t.sw))
        img = QImage(W, H, QImage.Format.Format_ARGB32_Premultiplied)
        img.fill(Qt.transparent)
        p = QPainter(img)
        desenhar_export(p, W, H, t, self.estilo)
        p.end()
        img.save(str(PASTA_CLIQUES / f"{nome}.png"))
        t.salvar_csv(PASTA_CLIQUES / f"{nome}.csv")
        (PASTA_CLIQUES / f"{nome}.json").write_text(json.dumps(t.meta()), encoding="utf-8")
        self.atualizar_galeria()
        self.toast(f"Salvo em Cliques · {nome}")

    # ---------- laço principal ----------
    def tick(self):
        self._n += 1
        self.tracker.processar()                 # sempre drena a fila, em qualquer aba
        pg = self.pilha.currentIndex()
        if pg == self.PG_RASTREIO:
            self.traco.tick()
        elif pg == self.PG_CALOR:
            self.calor.tick()
        elif pg == self.PG_TIMELAPSE:
            self.tl_tick()
        if self._n % 4 == 0:
            self.atualizar_ui()

    def atualizar_ui(self, forcar=False):
        t = self.tracker
        seg = int(t.tempo_ativo())
        self.lbl_tempo.setText(f"{seg // 3600:02d}:{seg % 3600 // 60:02d}:{seg % 60:02d}")
        self.stats["cliques"].setText(f"{t.cliques:,}")
        self.stats["movimentos"].setText(f"{t.movimentos:,}")
        self.stats["distancia"].setText(f"{t.distancia:,.0f}")
        chave = (t.estado, tuple(self.cfg["atalhos"].values()))
        if chave == self._cache_ui and not forcar:
            return
        self._cache_ui = chave
        a = self.cfg["atalhos"]
        self.b_ini.setText(f"{'retomar' if t.estado == t.PAUSADO else 'iniciar'}   ·   {a['iniciar']}")
        self.b_pau.setText(f"pausar   ·   {a['pausar']}")
        self.b_par.setText(f"parar   ·   {a['parar']}")
        self.b_ini.setEnabled(t.estado != t.RASTREANDO)
        self.b_pau.setEnabled(t.estado == t.RASTREANDO)
        self.b_par.setEnabled(t.estado != t.PARADO)
        self.traco.dica = a["iniciar"]
        rgb, rot = {t.PARADO: ((190, 194, 208), "parado"), t.RASTREANDO: ((255, 90, 106), "gravando"),
                    t.PAUSADO: ((250, 190, 70), "pausado")}[t.estado]
        r, g, b = rgb
        self.lbl_estado.setText(("● " if t.estado == t.RASTREANDO else "") + rot.upper())
        f = QFont()
        f.setPixelSize(10)
        f.setWeight(QFont.Normal)
        f.setLetterSpacing(QFont.AbsoluteSpacing, 2.5)
        self.lbl_estado.setFont(f)
        self.lbl_estado.setStyleSheet(
            f"border: 1px solid rgba({r},{g},{b},120); border-radius: 11px; padding: 4px 12px; color: rgb({r},{g},{b});")
        self.traco.update()

    # ---------- aviso ----------
    def toast(self, msg):
        self._toast.setText(msg)
        self._toast.adjustSize()
        self.posicionar_toast()
        self._toast.show()
        self._toast.raise_()
        QTimer.singleShot(2600, self._toast.hide)

    def posicionar_toast(self):
        self._toast.move((self.width() - self._toast.width()) // 2, self.height() - self._toast.height() - 30)

    def closeEvent(self, e):
        if self.tracker.estado != Rastreador.PARADO:
            self.tracker.parar()
            self.salvar_sessao()
        if self.hk:
            self.hk.stop()
        self.cfg["cor_risco"] = self.estilo["risco"].name(QColor.HexArgb)
        self.cfg["cor_ponto"] = self.estilo["ponto"].name(QColor.HexArgb)
        self.cfg["cor_fundo"] = self.estilo["fundo"].name(QColor.HexArgb)
        self.cfg["espessura"] = self.estilo["espessura"]
        try:
            salvar_config(self.cfg)
        except Exception:
            pass
        e.accept()


def main():
    sys.setswitchinterval(0.001)   # alterna threads mais rápido: o hook do mouse nunca espera a interface
    app = QApplication(sys.argv)
    app.setApplicationName("Rastreador de Mouse")
    f = QFont()
    f.setFamilies(["Inter", "Segoe UI Variable Display", "Segoe UI", "SF Pro Display", "Helvetica Neue", "Arial"])
    f.setPixelSize(13)
    f.setWeight(QFont.Light)
    app.setFont(f)
    janela = Janela()
    janela.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
