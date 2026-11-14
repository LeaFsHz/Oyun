#!/usr/bin/env python3
"""
ORRVETH - Parça 5 (Artı Basma)
Kick chat tabanlı, tek bilgisayarda çalışan 2D mini MMO.

- Kick chat salt-okunur okunur.
- Kullanıcılar !gir ile kahraman açar / arenaya girer.
- 4 zindan dinamik olarak ekranda gösterilir.
- Kahramanlar sağa yürür, yaratıklar sağdan sola gelir.
- Savaş otomatiktir.
- Yaratık ölünce XP ve gold verilir.
- Kahraman 5 saniye hasar almazsa can yenilenir.

Kurulum:
    pip install pygame websockets
"""

from __future__ import annotations

import asyncio
import json
import queue
import os
import random
import re
import shutil
import sys
import threading
import time
import traceback
import unicodedata
import urllib.error
import urllib.request
import uuid
from collections import deque
from dataclasses import dataclass, field
from urllib.parse import urlparse

os.environ.setdefault("SDL_AUDIODRIVER", "dummy")
os.environ.setdefault("PYGAME_HIDE_SUPPORT_PROMPT", "1")

import pygame
import websockets

# =========================================================
# SABİTLER
# =========================================================
REALTIME_BASE = "https://web.kick.com/api/v1/realtime"
CHANNEL_API = "https://kick.com/api/v2/channels/{slug}"
CHAT_EVENT = "App\\Events\\ChatMessageEvent"

UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36"
)
HDRS = {
    "User-Agent": UA,
    "Accept": "application/json",
    "Origin": "https://kick.com",
    "x-app-platform": "web",
}

SLUG_RE = re.compile(r"^[A-Za-z0-9_-]{1,64}$")
MAX_FRAME = 256 * 1024
MAX_HTTP = 2 * 1024 * 1024
MAX_CONTENT = 500

INTERNAL_W, INTERNAL_H = 1920, 1080    # tüm tuval (OBS'te 1080p sahne)
STRIP_H = 320                          # zindan şeridi yüksekliği (tuvalin altında)
STRIP_Y = INTERNAL_H - STRIP_H         # şeridin üst kenarı
BAG_W, BAG_H = 760, 480                # çanta/profil paneli
BAG_X = INTERNAL_W - BAG_W - 24        # çanta paneli konumu (şeridin üstünde, sağda)
BAG_Y = STRIP_Y - BAG_H - 12
LOGIN_W, LOGIN_H = 960, 540             # giriş ekranı
FPS = 30
SAVE_INTERVAL = 30                      # saniye

MAX_LEVEL = 40
LEVEL_HP = 12
LEVEL_ATK = 1
MINIBOSS_CHANCE = 0.04

# ---- yaratık dengesi / grup ölçekleme ----
AGGRO_CAP = 2               # bir kahramana aynı anda en fazla 2 yaratık saldırır
KILL_CAP = 9                # bir zindandaki en fazla yaratık
GROUP_HP_EXP = 0.8          # can çarpanı = kahraman_sayısı ** 0.8
GROUP_REWARD_EXP = 0.6      # XP/gold çarpanı = can çarpanı ** 0.6
GROUP_K_DIV = 2.0           # her 2 ek kahramana +1 yaratık
GROUP_SPAWN_DIV = 0.12      # her ek kahraman doğuşu %12 hızlandırır
SPAWN_SECONDS = (7.0, 11.0)
BOSS_HP_MULT = 4.0          # mini-boss
BOSS_DMG_MULT = 1.4
BOSS_XP_MULT = 8.0
BIG_BOSS_HP_MULT = 40.0     # büyük boss (7. evrede kullanılacak)
BIG_BOSS_DMG_MULT = 3.0

# Zindan seviye aralıkları. Kahraman: seviyesinin açtığı en yüksek
# zindana ve bir altına girebilir.
DUNGEON_LEVELS = {1: (1, 9), 2: (10, 19), 3: (20, 29), 4: (30, 40)}

CREATOR = "lea_xx"
MAX_ACTIVE_HEROES = 20
AFK_SECONDS = 5 * 60

HERO_SPEED = 70
MONSTER_SPEED_MULT = 2.2     # yaratıklar kahramandan hissedilir derecede hızlı yürür
HOME_PCT = 0.40              # kahramanlar şeridin bu oranında (soldan) durur
HOME_SPREAD_PCT = 0.14       # her kahramanın durduğu yer bu kadar dağılır
ADVANCE_PCT = 0.12           # yaratığa yaklaşmak için evinden en fazla bu kadar ilerler
SEE_PCT = 0.38               # kahraman yaratığı bu mesafeden görür
MONSTER_ATTACK_RANGE = 28
HERO_ATTACK_RANGE = 34
RESPAWN_SECONDS = 10
REGEN_DELAY = 3.0       # hasar almadan geçen saniye
REGEN_PERCENT = 0.04    # duruyorsa saniyede %4
REGEN_WALK = 0.03       # yürüyorsa saniyede %3

COLOR_KEY = (0, 255, 0)     # OBS'te Chroma Key ile silinecek boş alan
COLOR_BG = (20, 20, 26)
COLOR_PANEL = (34, 34, 44)
COLOR_PANEL_LIGHT = (48, 48, 60)
COLOR_TEXT = (235, 235, 240)
COLOR_MUTED = (150, 150, 160)
COLOR_ACCENT = (255, 220, 60)
COLOR_OK = (90, 220, 120)
COLOR_ERROR = (235, 80, 80)

CLASS_STATS = {
    "warrior": {
        "display": "Savaşçı",
        "hp": 120,
        "min_damage": 6,
        "max_damage": 10,
        "defense": 8,
        "attack_speed": 1.0,
        "range_px": 34,
        "range_pct": 0.0,
        "range_cap": 34,
        "hp_mult": 1.6,
        "def_mult": 1.4,
        "dmg_mult": 1.0,
        "color": (70, 130, 235),
    },
    "archer": {
        "display": "Okçu",
        "hp": 80,
        "min_damage": 9,
        "max_damage": 15,
        "defense": 3,
        "attack_speed": 0.8,
        "range_px": 100,
        "range_pct": 0.10,
        "range_cap": 220,
        "hp_mult": 1.2,
        "def_mult": 1.1,
        "dmg_mult": 0.8,
        "color": (240, 150, 30),
    },
}

# ---------------------------------------------------------
# YARATIK DENGESİ
# Her zindan için taban can / hasar / xp. Yaratık tipleri bu tabana
# çarpan uygular. Taban değerler simülasyonla ayarlandı:
#   - ortalama donanımlı tek kahraman normal yaratığı ~6 sn'de öldürür
#   - kötü donanım zor zamanlar yaşar, iyi donanım rahat geçer
#   - XP: tek başına oynayan ortalama kahraman seviye aralığını
#     Z1 ~40 dk, Z2 ~90 dk, Z3 ~2 saat, Z4 ~3 saatte bitirir
# ---------------------------------------------------------
BALANCE = {
    1: {"hp": 115, "dmg": 3.5, "xp": 21, "def": 1, "boss_size": 34},
    2: {"hp": 270, "dmg": 6.4, "xp": 50, "def": 3, "boss_size": 40},
    3: {"hp": 880, "dmg": 14.0, "xp": 86, "def": 9, "boss_size": 46},
    4: {"hp": 3430, "dmg": 25.0, "xp": 99, "def": 24, "boss_size": 52},
}

# tip: (can çarpanı, hasar çarpanı, hız, boyut, xp çarpanı)
MONSTER_TYPES = {
    "A": (0.75, 1.15, 62, 20, 0.9),    # hızlı, kırılgan
    "B": (1.00, 1.00, 45, 24, 1.0),    # dengeli
    "C": (1.45, 0.85, 30, 32, 1.3),    # yavaş, dayanıklı
    "D": (0.90, 1.30, 40, 26, 1.1),    # sert vuran
}

# (isim, tip, renk) - görseller gelince sadece isimler değişir
# (isim, tip, renk, sprite klasörü)
MONSTER_ROSTER = {
    1: [("Slime", "B", (90, 200, 90), "slime"), ("Sıçan", "A", (160, 120, 80), "rat"),
        ("Mantar", "C", (190, 150, 100), "spore"), ("Goblin", "D", (90, 160, 70), "goblin")],
    2: [("Yarasa", "A", (120, 90, 160), "bat"), ("Örümcek", "D", (70, 60, 90), "spider"),
        ("Ağaç Yaratığı", "C", (90, 70, 40), "treant"), ("Akrep", "B", (60, 60, 70), "scorpion")],
    3: [("Zombi", "C", (110, 140, 100), "zombie"), ("Gul", "D", (130, 120, 100), "ghoul"),
        ("İskelet Savaşçı", "B", (220, 220, 210), "skeleton_warrior"),
        ("İskelet Okçu", "A", (90, 130, 90), "skel_archer")],
    4: [("Cehennem Köpeği", "A", (230, 110, 40), "hellhound"), ("Hayalet", "D", (50, 50, 80), "wraith"),
        ("Ogre", "C", (130, 150, 130), "ogre"), ("Gargoyle", "B", (90, 110, 150), "gargoyle")],
}

# (mini-boss, büyük boss) sprite klasörleri
BOSS_SPRITES = {
    1: ("stone_golem", "plague_broodmother"),
    2: ("skeleton_lord", "frost_dragon"),
    3: ("thunder_titan", "seraph"),
    4: ("lava_colossus", "void_devourer"),
}

DUNGEON_THEME = {   # arka plan, çizgi, tabandaki yaratık sayısı
    1: ((30, 35, 40), (45, 50, 55), 2),
    2: ((40, 30, 30), (55, 45, 45), 2),
    3: ((30, 40, 30), (45, 55, 45), 2),
    4: ((45, 20, 20), (60, 35, 35), 2),
}


def build_monster_table() -> dict:
    table = {}

    for d, roster in MONSTER_ROSTER.items():
        b = BALANCE[d]
        monsters = []

        for name, t, color, sprite in roster:
            hpm, dmgm, speed, size, xpm = MONSTER_TYPES[t]
            dmg = b["dmg"] * dmgm
            xp = b["xp"] * xpm
            defense = b["def"] * (1.5 if t == "C" else 0.5 if t == "A" else 1.0)
            monsters.append({
                "name": name, "hp": int(b["hp"] * hpm),
                "damage": (max(1, int(dmg * 0.75)), max(2, int(dmg * 1.25))),
                "xp": max(1, int(xp)), "gold": max(1, int(xp / 3)),
                "speed": speed, "size": size, "color": color,
                "defense": int(defense),
                "sprite": f"yaratik/{sprite}", "kind": "enemy",
            })

        dmg = b["dmg"] * BOSS_DMG_MULT
        monsters.append({
            "name": "Mini-Boss", "hp": int(b["hp"] * BOSS_HP_MULT),
            "damage": (max(1, int(dmg * 0.75)), max(2, int(dmg * 1.25))),
            "xp": int(b["xp"] * BOSS_XP_MULT),
            "gold": int(b["xp"] * BOSS_XP_MULT / 3),
            "speed": 30, "size": b["boss_size"], "color": (200, 70, 70),
            "defense": b["def"] * 2,
            "sprite": f"boss/{BOSS_SPRITES[d][0]}", "kind": "boss",
        })

        bg, grid, base_k = DUNGEON_THEME[d]
        dmg = b["dmg"] * BIG_BOSS_DMG_MULT
        table[d] = {
            "max_monsters": base_k,
            "spawn_min": SPAWN_SECONDS[0],
            "spawn_max": SPAWN_SECONDS[1],
            "bg_color": bg,
            "grid_color": grid,
            "monsters": monsters,
            # 7. evrede (!boss) kullanılacak, normal doğuşta çıkmaz
            "boss": {
                "name": "Boss", "hp": int(b["hp"] * BIG_BOSS_HP_MULT),
                "damage": (max(1, int(dmg * 0.75)), max(2, int(dmg * 1.25))),
                "xp": int(b["xp"] * 100), "gold": int(b["xp"] * 30),
                "speed": 25, "size": b["boss_size"] + 20,
                "color": (240, 60, 60), "defense": b["def"] * 3,
                "sprite": f"boss/{BOSS_SPRITES[d][1]}", "kind": "boss",
            },
        }

    return table


MONSTER_TABLE = build_monster_table()


# =========================================================
# GÜVENLİK / YARDIMCI
# =========================================================
# =========================================================
# ITEM SİSTEMİ
# =========================================================
BAG_SIZE = 16
BAG_SECONDS = 30
TIP_SECONDS = 25
DROP_CHANCE = 0.04
DROP_CHANCE_MINIBOSS = 0.20

SLOTS = ("weapon", "kask", "zirh", "pantolon", "bot", "kolye")
SLOT_NAME = {
    "weapon": "Silah", "kask": "Kask", "zirh": "Zırh",
    "pantolon": "Pantolon", "bot": "Bot", "kolye": "Kolye",
}
KIND_SLOT = {
    "kilic": "weapon", "yay": "weapon", "kask": "kask", "zirh": "zirh",
    "pantolon": "pantolon", "bot": "bot", "kolye": "kolye",
}
KIND_NOUN = {
    "kilic": "Kılıcı", "yay": "Yayı", "kask": "Miğferi", "zirh": "Zırhı",
    "pantolon": "Pantolonu", "bot": "Çizmesi", "kolye": "Kolyesi",
}
KIND_LETTER = {
    "kilic": "KL", "yay": "YA", "kask": "KS", "zirh": "ZR",
    "pantolon": "PN", "bot": "BT", "kolye": "KY",
}
CLASS_WEAPON = {"warrior": "kilic", "archer": "yay"}
DUNGEON_PREFIX = {1: "Acemi", 2: "Gezgin", 3: "Gaddar", 4: "Ejder"}

# savunma: DEF / (DEF + K), en fazla %75
DEF_K = {1: 60, 2: 140, 3: 450, 4: 1600}
DEF_CAP = 0.75

# mult: ana stat çarpanı aralığı (q ile belirlenir)
# frac: özellik değeri, özellik sınırının kaçta kaçı (q ile belirlenir)
RARITIES = [
    {"name": "Normal", "color": (235, 235, 235), "mult": (0.5, 0.8), "frac": (0, 0), "n": (0, 0)},
    {"name": "Nadir", "color": (90, 220, 120), "mult": (0.8, 1.2), "frac": (0.20, 0.40), "n": (1, 1)},
    {"name": "Destansı", "color": (80, 150, 255), "mult": (1.2, 1.7), "frac": (0.30, 0.55), "n": (1, 2)},
    {"name": "Efsanevi", "color": (190, 90, 240), "mult": (1.7, 2.3), "frac": (0.45, 0.75), "n": (2, 2)},
    {"name": "Mitik", "color": (255, 170, 40), "mult": (2.3, 3.0), "frac": (0.60, 1.00), "n": (3, 3)},
]

# silah hasar bandı: [zindan][rarity] = (en düşük, en yüksek)
WEAPON_BAND = {
    1: [(3, 5), (5, 7), (7, 10), (10, 14), (14, 18)],
    2: [(11, 18), (18, 26), (26, 37), (37, 51), (51, 66)],
    3: [(43, 68), (68, 102), (102, 145), (145, 196), (196, 255)],
    4: [(150, 240), (240, 360), (360, 510), (510, 690), (690, 900)],
}
WEAPON_WINDOW = 0.20            # pencere genişliği = bandın %20'si
ARMOR_BASE = {1: 4, 2: 15, 3: 60, 4: 220}
SLOT_SHARE = {"zirh": 1.0, "pantolon": 0.7, "kask": 0.6, "bot": 0.4}
NECK_BASE = {1: 20, 2: 70, 3: 230, 4: 450}
SELL_BASE = {1: 5, 2: 20, 3: 80, 4: 300}

# normal yaratıktan düşen rarity ağırlıkları (Normal..Mitik)
DROP_TABLE = {
    1: [80, 17, 2.8, 0.2, 0],
    2: [55, 32, 10, 2.8, 0.2],
    3: [25, 40, 24, 9, 2],
    4: [5, 30, 40, 20, 5],
}

# özellik havuzu (slottan bağımsız). cap: tek parçada üst sınır,
# total: tüm ekipman toplamında üst sınır, w: güç puanı ağırlığı
AFFIXES = {
    "crit": {"name": "Kritik Şansı", "cap": 12, "total": 35, "w": 1.0, "flat": False},
    "critdmg": {"name": "Kritik Hasarı", "cap": 30, "total": 80, "w": 0.6, "flat": False},
    "double": {"name": "Çift Vuruş", "cap": 8, "total": 20, "w": 1.2, "flat": False},
    "aspeed": {"name": "Saldırı Hızı", "cap": 10, "total": 30, "w": 1.2, "flat": False},
    "lifesteal": {"name": "Can Çalma", "cap": 4, "total": 10, "w": 1.4, "flat": False},
    "dodge": {"name": "Sıyrılma", "cap": 10, "total": 30, "w": 1.0, "flat": False},
    "reflect": {"name": "Yansıtma", "cap": 8, "total": 20, "w": 0.7, "flat": False},
    "dr": {"name": "Hasar Azaltma", "cap": 6, "total": 20, "w": 1.0, "flat": False},
    "hp_pct": {"name": "Can %", "cap": 10, "total": 30, "w": 1.0, "flat": False},
    "regen": {"name": "Can Yenileme /sn %", "cap": 1.0, "total": 3.0, "w": 0.8, "flat": False},
    "xp": {"name": "XP Bonusu", "cap": 12, "total": 35, "w": 0.5, "flat": False},
    "gold": {"name": "Altın Bonusu", "cap": 12, "total": 35, "w": 0.4, "flat": False},
    "drop": {"name": "Drop Şansı", "cap": 8, "total": 25, "w": 0.6, "flat": False},
    "atk_flat": {"name": "ATK", "cap": {1: 6, 2: 20, 3: 70, 4: 250}, "total": None, "w": 1.0, "flat": True},
    "def_flat": {"name": "DEF", "cap": {1: 3, 2: 12, 3: 50, 4: 180}, "total": None, "w": 1.0, "flat": True},
    "hp_flat": {"name": "HP", "cap": {1: 40, 2: 140, 3: 450, 4: 900}, "total": None, "w": 1.0, "flat": True},
}


# ---- ARTI BASMA (+) ----
PLUS_MAX = 8
# basarı şansı (%): [rarity][mevcut +]  ->  +0->+1 ... +7->+8
PLUS_RATES = [
    [100, 100, 95, 85, 75, 65, 50, 25],      # Normal (beyaz)  = Common
    [100, 100, 95, 90, 80, 70, 50, 25],      # Nadir (yeşil)   = Rare
    [100, 100, 90, 80, 70, 50, 30, 10],      # Destansı (mavi) = Elite
    [100, 100, 90, 75, 70, 40, 30, 5],       # Efsanevi (mor)  = Epic
    [100, 100, 90, 75, 70, 40, 30, 5],       # Mitik (sarı) - eski ayarlı hali
]
# + basma gold bedeli: PLUS_BASE[zindan] x (mevcut + + 1)
PLUS_BASE = {1: 10, 2: 40, 3: 160, 4: 600}


def plus_cost(item) -> int:
    return PLUS_BASE[item.dungeon] * (item.plus + 1)


def plus_refund(item) -> int:
    """Bu + seviyesine gelmek için harcanan toplam bedelin yarısı."""
    n = item.plus
    return PLUS_BASE[item.dungeon] * n * (n + 1) // 2 // 2


# her + seviyesinde artış: taban + kalite * ek  (q = item roll kalitesi 0-1)
PLUS_GAIN_MAX = (0.15, 0.05)    # silah max hasarı
PLUS_GAIN_MIN = (0.12, 0.08)    # silah min hasarı (iyi roll'da daha çok artar)
PLUS_GAIN_FLAT = (0.135, 0.065) # zırh DEF / kolye HP
PLUS_CONFIRM_FROM = 5           # +5 ve üstünden sonraki denemelerde onay iste
PLUS_CONFIRM_SECONDS = 15


def bell() -> float:
    """0-1 arası, ortaya yakın olması daha olası (üçgen dağılım)."""
    return (random.random() + random.random()) / 2


def affix_cap(key: str, dungeon: int) -> float:
    cap = AFFIXES[key]["cap"]
    return cap[dungeon] if isinstance(cap, dict) else cap


def ref_main(slot: str, dungeon: int) -> float:
    if slot == "weapon":
        return WEAPON_BAND[dungeon][4][1]
    if slot == "kolye":
        return NECK_BASE[dungeon] * 3.0
    return ARMOR_BASE[dungeon] * SLOT_SHARE[slot] * 3.0


@dataclass
class Item:
    kind: str
    rarity: int
    variant: int
    dungeon: int
    q: float
    main: list
    affixes: list
    plus: int = 0

    @property
    def cur(self) -> list:
        """+ seviyesine göre güncel ana stat değerleri."""
        if self.plus <= 0:
            return list(self.main)

        if self.slot == "weapon":
            gmin = PLUS_GAIN_MIN[0] + PLUS_GAIN_MIN[1] * self.q
            gmax = PLUS_GAIN_MAX[0] + PLUS_GAIN_MAX[1] * self.q
            vmin = round(self.main[0] * (1 + self.plus * gmin))
            vmax = round(self.main[1] * (1 + self.plus * gmax))
            return [vmin, max(vmin + 1, vmax)]

        g = PLUS_GAIN_FLAT[0] + PLUS_GAIN_FLAT[1] * self.q
        return [round(self.main[0] * (1 + self.plus * g))]

    @property
    def slot(self) -> str:
        return KIND_SLOT[self.kind]

    @property
    def color(self) -> tuple[int, int, int]:
        return RARITIES[self.rarity]["color"]

    @property
    def name(self) -> str:
        tag = f"+{self.plus} " if self.plus > 0 else ""
        return (
            f"{tag}{RARITIES[self.rarity]['name']} "
            f"{DUNGEON_PREFIX[self.dungeon]} {KIND_NOUN[self.kind]}"
        )

    @property
    def main_text(self) -> str:
        if self.slot == "weapon":
            c = self.cur
            return f"ATK {c[0]}-{c[1]}"
        if self.slot == "kolye":
            return f"HP {self.cur[0]}"
        return f"DEF {self.cur[0]}"

    @property
    def main_avg(self) -> float:
        c = self.cur
        return sum(c) / len(c)

    @property
    def score(self) -> float:
        ref = ref_main(self.slot, self.dungeon)
        pts = self.main_avg

        for key, value in self.affixes:
            a = AFFIXES[key]
            pts += (value / affix_cap(key, self.dungeon)) * a["w"] * 0.08 * ref

        return pts

    @property
    def sell_price(self) -> int:
        return max(1, int(
            SELL_BASE[self.dungeon] * (1 + self.rarity * 1.2)
            * (0.7 + 0.6 * self.q) + plus_refund(self)
        ))

    def affix_text(self, key: str, value: float) -> str:
        a = AFFIXES[key]
        if a["flat"]:
            return f"{a['name']} +{int(value)}"
        return f"{a['name']} +%{value:g}"

    def to_dict(self) -> dict:
        return {
            "kind": self.kind, "rarity": self.rarity,
            "variant": self.variant, "dungeon": self.dungeon,
            "q": self.q, "main": list(self.main), "plus": self.plus,
            "affixes": [list(a) for a in self.affixes],
        }

    @classmethod
    def from_dict(cls, d: object) -> "Item | None":
        try:
            kind = d["kind"]
            main = [int(x) for x in d["main"]]
            affixes = [[str(k), float(v)] for k, v in d["affixes"]]
            item = cls(
                kind=kind,
                rarity=int(d["rarity"]),
                variant=int(d.get("variant", 1)),
                dungeon=int(d["dungeon"]),
                q=float(d.get("q", 0.5)),
                main=main,
                affixes=affixes,
                plus=max(0, min(PLUS_MAX, int(d.get("plus", 0)))),
            )
        except (KeyError, TypeError, ValueError, AttributeError):
            return None

        want = 2 if item.slot == "weapon" else 1

        if (
            kind not in KIND_SLOT
            or not 0 <= item.rarity < len(RARITIES)
            or item.dungeon not in DEF_K
            or len(main) != want
            or any(k not in AFFIXES for k, _ in affixes)
        ):
            return None

        return item


def make_item(
    kind: str,
    rarity: int,
    dungeon: int,
    q: float | None = None,
    keys: list | None = None,
) -> Item:
    q = bell() if q is None else q
    r = RARITIES[rarity]
    slot = KIND_SLOT[kind]

    if slot == "weapon":
        lo, hi = WEAPON_BAND[dungeon][rarity]
        width = (hi - lo) * WEAPON_WINDOW
        start = lo + q * (hi - lo - width)
        vmin = max(1, round(start))
        vmax = max(vmin + 1, round(start + width))
        main = [vmin, vmax]
    else:
        base = (
            NECK_BASE[dungeon] if slot == "kolye"
            else ARMOR_BASE[dungeon] * SLOT_SHARE[slot]
        )
        mult = r["mult"][0] + (r["mult"][1] - r["mult"][0]) * q
        main = [max(1, round(base * mult))]

    if keys is None:
        keys = random.sample(list(AFFIXES), random.randint(*r["n"]))

    affixes = []

    for key in keys:
        fq = 1.0 if q >= 1.0 else bell()
        frac = r["frac"][0] + (r["frac"][1] - r["frac"][0]) * fq
        value = affix_cap(key, dungeon) * frac

        if AFFIXES[key]["flat"]:
            value = max(1, int(round(value)))
        else:
            value = round(value, 1)

        affixes.append([key, value])

    return Item(kind, rarity, random.randint(1, 4), dungeon,
                round(q, 3), main, affixes)


def roll_drop(class_id: str, dungeon: int, miniboss: bool) -> Item:
    slot = random.choice(SLOTS)
    kind = CLASS_WEAPON[class_id] if slot == "weapon" else slot
    weights = list(DROP_TABLE[dungeon])

    if miniboss:     # mini-boss: tablo bir kademe yukarı kayar
        weights = [0] + weights[:-1]
        weights[-1] += DROP_TABLE[dungeon][-1]

    rarity = random.choices(range(len(RARITIES)), weights=weights)[0]
    return make_item(kind, rarity, dungeon)


GM_KEYS = {
    "weapon": ["crit", "critdmg", "double"],
    "kask": ["dr", "hp_pct", "regen"],
    "zirh": ["dodge", "reflect", "hp_pct"],
    "pantolon": ["aspeed", "lifesteal", "def_flat"],
    "bot": ["dodge", "gold", "xp"],
    "kolye": ["drop", "hp_flat", "atk_flat"],
}


def item_lines(item: Item, verdict=None, price: bool = False) -> list:
    lines = [(item.name, item.color), (item.main_text, COLOR_TEXT)]

    for key, value in item.affixes:
        lines.append((item.affix_text(key, value), COLOR_OK))

    lines.append((f"Roll %{item.q * 100:.0f}", COLOR_MUTED))

    if item.plus < PLUS_MAX:
        rate = PLUS_RATES[item.rarity][item.plus]
        lines.append((f"+{item.plus + 1} şansı: %{rate}", COLOR_ACCENT))
        lines.append((f"+ bedeli: {plus_cost(item)} gold", COLOR_MUTED))
    else:
        lines.append(("En yüksek seviye (+8)", COLOR_ACCENT))

    if verdict is not None:
        lines.append(verdict)
    if price:
        lines.append((f"Satış: {item.sell_price} gold", COLOR_MUTED))

    return lines


def verdict_line(sign) -> tuple:
    if sign is None:
        return ("Bu sınıf kullanamaz", COLOR_ERROR)
    if sign > 0:
        return ("↑ Takılıdan iyi", COLOR_OK)
    if sign < 0:
        return ("↓ Takılıdan zayıf", COLOR_ERROR)
    return ("= Takılıyla eşit", COLOR_MUTED)


# =========================================================
# GÖRSELLER
# =========================================================
# Sprite yönleri: dosyadaki hali sağa bakanlar. Yaratıklar sola bakar
# varsayılır; ters görünen olursa ismini bu listeye ekle / listeden çıkar.
FACES_RIGHT = {
    "rat", "skel_archer", "hellhound", "ghoul", "lizardman",
    "frost_dragon", "skeleton_lord",
}
SPRITE_SCALE = {"hero": 1.7, "enemy": 1.5, "boss": 0.9}
RARITY_FILE = ["beyaz", "yesil", "mavi", "mor", "turuncu"]
SPRITES = None


def asset_roots() -> list[str]:
    roots = [os.path.join(app_dir(), "gorseller")]
    bundled = getattr(sys, "_MEIPASS", None)

    if bundled:
        roots.append(os.path.join(bundled, "gorseller"))

    return roots


class Anim:
    __slots__ = ("right", "left", "fps", "n", "w", "h", "top")

    def __init__(self, right, left, fps, w, h, top) -> None:
        self.right = right
        self.left = left
        self.fps = fps
        self.n = len(right)
        self.w = w
        self.h = h
        self.top = top

    def frame(self, index: int, flipped: bool):
        frames = self.left if flipped else self.right
        return frames[max(0, min(self.n - 1, index))]


class Sprites:
    """Sprite şeritlerini ilk kullanımda yükler, ölçekler, önbelleğe alır."""

    def __init__(self) -> None:
        self.root = ""
        self.meta: dict = {}

        for root in asset_roots():
            data = read_json(os.path.join(root, "animasyon.json"))

            if isinstance(data, dict):
                self.root = root
                self.meta = data
                break

        self.anims: dict = {}
        self.icons: dict = {}
        self.tiles: dict = {}

    def anim(self, folder: str, name: str, scale: float):
        key = (folder, name, scale)

        if key in self.anims:
            return self.anims[key]

        result = None
        info = self.meta.get(folder, {}).get(name)

        if info:
            try:
                sheet = pygame.image.load(
                    os.path.join(self.root, folder, name + ".png")
                ).convert_alpha()
                fw, fh = info["w"], info["h"]
                right, left = [], []

                for i in range(info["frames"]):
                    frame = sheet.subsurface((i * fw, 0, fw, fh))
                    frame = pygame.transform.scale(
                        frame, (int(fw * scale), int(fh * scale))
                    )
                    right.append(frame)
                    left.append(pygame.transform.flip(frame, True, False))

                top = right[0].get_bounding_rect().top
                result = Anim(right, left, info["fps"],
                              right[0].get_width(), right[0].get_height(), top)
            except Exception:
                result = None

        self.anims[key] = result
        return result

    def head(self, folder: str, scale: float) -> int:
        """Sprite'ın görünen yüksekliği (isim yazısı yeri için)."""
        for name in ("walk", "idle"):
            a = self.anim(folder, name, scale)

            if a is not None:
                return a.h - a.top

        return 60

    def icon(self, kind: str, rarity: int, variant: int, size: int):
        key = (kind, rarity, variant, size)

        if key in self.icons:
            return self.icons[key]

        surf = None
        fn = f"esya/{kind}_{RARITY_FILE[rarity]}_{variant}.png"

        for root in asset_roots():
            path = os.path.join(root, fn)

            if os.path.exists(path):
                try:
                    img = pygame.image.load(path).convert_alpha()
                    surf = pygame.transform.smoothscale(img, (size, size))
                except Exception:
                    surf = None
                break

        self.icons[key] = surf
        return surf

    def tile(self, name: str, height: int):
        """Arka plan / zemin görseli (yatay tekrar eder)."""
        key = (name, height)

        if key in self.tiles:
            return self.tiles[key]

        surf = None

        for root in asset_roots():
            path = os.path.join(root, "arkaplan", name + ".png")

            if os.path.exists(path):
                try:
                    img = pygame.image.load(path).convert_alpha()
                    w = max(1, int(img.get_width() * height / img.get_height()))
                    surf = pygame.transform.scale(img, (w, height))
                except Exception:
                    surf = None
                break

        self.tiles[key] = surf
        return surf


def anim_index(anim, progress: float | None = None, phase: float = 0.0) -> int:
    """progress verilirse 0-1 arası ilerlemeye göre, yoksa zamana göre kare."""
    if progress is not None:
        return min(anim.n - 1, max(0, int(progress * anim.n)))

    return int(time.time() * anim.fps + phase * anim.n) % anim.n


def norm(name: str) -> str:
    """Kick kullanıcı adı / kanal adı karşılaştırması (_ ile - aynı sayılır)."""
    return str(name).strip().lstrip("@").lower().replace("-", "_")


def xp_needed(level: int) -> int:
    return int(40 * level ** 1.6)


def highest_dungeon(level: int) -> int:
    for d in (4, 3, 2):
        if level >= DUNGEON_LEVELS[d][0]:
            return d
    return 1


def allowed_dungeons(level: int) -> list[int]:
    hi = highest_dungeon(level)
    return sorted({hi, max(1, hi - 1)})


def app_dir() -> str:
    if getattr(sys, "frozen", False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))


def save_path(channel: str) -> str:
    return os.path.join(app_dir(), f"kayit_{channel}.json")


def settings_path() -> str:
    return os.path.join(app_dir(), "ayarlar.json")


def read_json(path: str) -> object:
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return None


def write_json_atomic(path: str, data: object) -> None:
    """Önce geçici dosyaya yazar, eskisini .bak olarak saklar."""
    tmp = path + ".tmp"

    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=1)

    if os.path.exists(path):
        try:
            shutil.copy2(path, path + ".bak")
        except OSError:
            pass

    os.replace(tmp, path)


def clean(text: object, limit: int = MAX_CONTENT) -> str:
    if not isinstance(text, str):
        return ""

    return "".join(
        ch
        for ch in text
        if ch == " " or unicodedata.category(ch)[0] != "C"
    )[:limit]


def http_json(
    url: str,
    body: dict | None = None,
    timeout: float = 15.0,
) -> dict:
    if not url.startswith("https://"):
        raise ValueError("Yalnızca https izinli")

    data = json.dumps(body).encode() if body is not None else None
    headers = dict(HDRS)

    if data is not None:
        headers["Content-Type"] = "application/json"

    req = urllib.request.Request(
        url,
        data=data,
        headers=headers,
        method="POST" if data is not None else "GET",
    )

    with urllib.request.urlopen(req, timeout=timeout) as r:
        raw = r.read(MAX_HTTP + 1)

    if len(raw) > MAX_HTTP:
        raise ValueError("HTTP yanıtı çok büyük")

    obj = json.loads(raw)

    if not isinstance(obj, dict):
        raise ValueError("Beklenmeyen JSON")

    return obj


def resolve_channel(slug: str) -> tuple[int, int]:
    d = http_json(CHANNEL_API.format(slug=slug))
    channel_id = d.get("id")
    chatroom_id = (d.get("chatroom") or {}).get("id")

    if not (isinstance(channel_id, int) and isinstance(chatroom_id, int)):
        raise ValueError("Kanal yanıtında id bulunamadı")

    return channel_id, chatroom_id


def negotiate(
    client_id: str,
    providers: list[str],
    channel_id: int | None = None,
) -> dict:
    path = (
        f"/channels/{int(channel_id)}/chat/connection"
        if channel_id
        else "/connection"
    )

    resp = http_json(
        REALTIME_BASE + path,
        {
            "client": {"id": client_id, "type": "web"},
            "capabilities": {
                "accepted_providers": [
                    {"provider": p} for p in providers
                ]
            },
        },
    )

    for conn in (resp.get("data") or {}).get("connections") or []:
        if not isinstance(conn, dict):
            continue

        cred = conn.get("credentials") or {}

        if conn.get("provider") == "pusher":
            key = str(cred.get("app_key", ""))
            cluster = str(cred.get("cluster", ""))

            if (
                key.isascii()
                and key.isalnum()
                and len(key) <= 64
                and cluster.isascii()
                and cluster.isalnum()
                and len(cluster) <= 16
            ):
                return {
                    "provider": "pusher",
                    "key": key,
                    "cluster": cluster,
                }

        if conn.get("provider") == "centrifugo":
            url = urlparse(str(cred.get("url", "")))
            host = url.hostname or ""

            if (
                url.scheme == "wss"
                and host.startswith("realtime.")
                and host.endswith(".platform.kick.com")
                and url.path == "/connection/websocket"
                and not url.query
            ):
                return {
                    "provider": "centrifugo",
                    "url": url.geturl(),
                }

    raise ValueError("Desteklenen sağlayıcı dönmedi")


# =========================================================
# KICK CHAT OKUYUCU
# =========================================================
class KeyRejected(Exception):
    pass


class KickChatReader(threading.Thread):
    def __init__(self, channel: str, msg_queue: queue.Queue) -> None:
        super().__init__(daemon=True)
        self.channel = channel.lower()
        self.msg_queue = msg_queue
        self.stop_event = threading.Event()
        self.status = "Bağlanılıyor..."

    def stop(self) -> None:
        self.stop_event.set()

    def run(self) -> None:
        try:
            asyncio.run(self._main())
        except Exception as exc:
            self.status = "Sohbet hatası"
            self._put("fatal", message=f"Sohbet hatası: {exc}"[:200])

    def _put(self, kind: str, **kwargs) -> None:
        msg = {"type": kind, "time": time.time()}
        msg.update(kwargs)
        self.msg_queue.put(msg)

    def _on_chat(self, data: object) -> None:
        if isinstance(data, str):
            try:
                data = json.loads(data)
            except ValueError:
                return

        if not isinstance(data, dict):
            return

        sender = data.get("sender")
        user = clean(
            sender.get("username") if isinstance(sender, dict) else None,
            40,
        ) or "?"

        text = clean(data.get("content")).strip()

        if text:
            self._put("chat", user=user, text=text)

    async def _run_pusher(
        self,
        key: str,
        cluster: str,
        chatroom_id: int,
    ) -> None:
        url = (
            f"wss://ws-{cluster}.pusher.com/app/{key}"
            "?protocol=7&client=js&version=8.4.0&flash=false"
        )

        async with websockets.connect(
            url,
            max_size=MAX_FRAME,
            open_timeout=15,
            ping_interval=None,
        ) as ws:
            first = json.loads(await asyncio.wait_for(ws.recv(), 15))

            if first.get("event") == "pusher:error":
                raise KeyRejected(str(first.get("data"))[:200])

            timeout = 120

            try:
                timeout = int(
                    json.loads(first["data"]).get("activity_timeout", 120)
                )
            except (KeyError, ValueError, TypeError):
                pass

            await ws.send(json.dumps({
                "event": "pusher:subscribe",
                "data": {
                    "auth": "",
                    "channel": f"chatrooms.{chatroom_id}.v2",
                },
            }))

            while not self.stop_event.is_set():
                try:
                    raw = await asyncio.wait_for(ws.recv(), timeout)
                except asyncio.TimeoutError:
                    await ws.send(json.dumps({
                        "event": "pusher:ping",
                        "data": {},
                    }))
                    continue

                message = json.loads(raw)
                event = message.get("event")

                if event == "pusher:ping":
                    await ws.send(json.dumps({
                        "event": "pusher:pong",
                        "data": {},
                    }))

                elif event == "pusher:error":
                    code = (message.get("data") or {}).get("code")

                    if code in (4001, 4003, 4007):
                        raise KeyRejected(str(message.get("data"))[:200])

                    raise ConnectionError(str(message.get("data"))[:200])

                elif event == "pusher_internal:subscription_succeeded":
                    self.status = "Bağlandı"
                    self._put(
                        "status",
                        message="Sohbet bağlandı",
                    )

                elif event == CHAT_EVENT:
                    self._on_chat(message.get("data"))

    async def _run_centrifugo(
        self,
        url: str,
        client_id: str,
        chatroom_id: int,
    ) -> None:
        token_resp = http_json(
            REALTIME_BASE + "/auth/connection",
            {"client_id": client_id},
        )

        token = str((token_resp.get("data") or {}).get("token", ""))

        if not token or len(token) > 4096:
            raise ConnectionError("Anonim token alınamadı")

        async with websockets.connect(
            url,
            max_size=MAX_FRAME,
            open_timeout=15,
            origin="https://kick.com",
            user_agent_header=UA,
            ping_interval=None,
        ) as ws:
            await ws.send(json.dumps({
                "id": 1,
                "connect": {
                    "token": token,
                    "name": "js",
                    "version": "1",
                },
            }))

            await ws.send(json.dumps({
                "id": 2,
                "subscribe": {
                    "channel": f"chatrooms.{chatroom_id}.v2",
                },
            }))

            refresh_at = float("inf")
            next_id = 3

            while not self.stop_event.is_set():
                raw = await asyncio.wait_for(ws.recv(), 90)

                for line in str(raw).splitlines():
                    try:
                        item = json.loads(line)
                    except ValueError:
                        continue

                    if not isinstance(item, dict):
                        continue

                    if not item:
                        await ws.send("{}")
                        continue

                    if "error" in item:
                        raise ConnectionError(
                            f"Centrifugo hatası: {str(item['error'])[:200]}"
                        )

                    if item.get("id") == 1:
                        self.status = "Bağlandı"
                        self._put(
                            "status",
                            message="Centrifugo bağlandı",
                        )

                        ttl = int(
                            (item.get("connect") or {}).get("ttl", 0) or 0
                        )
                        refresh_at = (
                            time.monotonic() + max(ttl - 60, 30)
                            if ttl
                            else float("inf")
                        )

                    pub = (item.get("push") or {}).get("pub")

                    if pub:
                        data = pub.get("data")

                        if isinstance(data, str):
                            try:
                                data = json.loads(data)
                            except ValueError:
                                continue

                        if (
                            isinstance(data, dict)
                            and data.get("event") == CHAT_EVENT
                        ):
                            self._on_chat(data.get("data"))

                if time.monotonic() > refresh_at:
                    token_resp = http_json(
                        REALTIME_BASE + "/auth/connection",
                        {"client_id": client_id},
                    )

                    new_token = str(
                        (token_resp.get("data") or {}).get("token", "")
                    )

                    if not new_token:
                        raise ConnectionError(
                            "Centrifugo token yenilenemedi"
                        )

                    await ws.send(json.dumps({
                        "id": next_id,
                        "refresh": {"token": new_token},
                    }))

                    next_id += 1
                    refresh_at = float("inf")

    async def _main(self) -> None:
        if not SLUG_RE.match(self.channel):
            self.status = "Geçersiz kanal adı"
            self._put("fatal", message=self.status)
            return

        try:
            channel_id, chatroom_id = resolve_channel(self.channel)
        except (urllib.error.URLError, ValueError) as e:
            self.status = "Kanal bulunamadı"
            self._put(
                "fatal",
                message=f"Kanal bulunamadı: {str(e)[:120]}",
            )
            return

        print(
            f"[i] kanal={self.channel} "
            f"channel_id={channel_id} "
            f"chatroom_id={chatroom_id}",
            flush=True,
        )

        client_id = str(uuid.uuid4())
        backoff = 1
        mode = "auto"

        while not self.stop_event.is_set():
            try:
                if mode in ("auto", "pusher"):
                    try:
                        cfg = negotiate(
                            client_id,
                            ["pusher"],
                            channel_id,
                        )
                        await self._run_pusher(
                            cfg["key"],
                            cfg["cluster"],
                            chatroom_id,
                        )
                    except KeyRejected as e:
                        print(
                            f"[!] Pusher reddedildi: {e}; "
                            "Centrifugo deneniyor",
                            flush=True,
                        )
                        mode = "centrifugo"
                        continue

                else:
                    cfg = negotiate(
                        client_id,
                        ["centrifugo"],
                        channel_id,
                    )
                    await self._run_centrifugo(
                        cfg["url"],
                        client_id,
                        chatroom_id,
                    )

                backoff = 1

            except (
                websockets.WebSocketException,
                OSError,
                ConnectionError,
                asyncio.TimeoutError,
                ValueError,
            ) as e:
                print(
                    f"[!] Bağlantı koptu: {type(e).__name__}: "
                    f"{str(e)[:150]}",
                    flush=True,
                )

                self.status = "Bağlantı koptu"
                self._put(
                    "status",
                    message=(
                        f"Bağlantı koptu, {backoff} sn sonra "
                        "tekrar denenecek"
                    ),
                )

                if self.stop_event.is_set():
                    break

                await asyncio.sleep(backoff)
                backoff = min(backoff * 2, 60)


# =========================================================
# KAHRAMAN
# =========================================================
@dataclass
class Hero:
    username: str
    display_name: str
    class_id: str
    level: int = 1
    xp: int = 0
    hp: int = 0
    max_hp: int = 0
    min_damage: int = 0
    max_damage: int = 0
    defense: int = 0
    attack_speed: float = 1.0
    gold: int = 0
    last_dungeon: int = 1
    unlocked_dungeon: int = 1
    created_at: float = 0.0
    last_seen: float = 0.0
    last_damage_time: float = 0.0
    attack_timer: float = 0.0
    respawn_timer: float = 0.0
    x: float = 0.0
    y: float = 0.0
    lane: float = 0.5
    equip: dict = field(default_factory=dict)
    bag: list = field(default_factory=list)
    fx: dict = field(default_factory=dict)
    anim_state: str = "walk"
    facing: int = 1
    atk_var: int = 1

    # kayıt dosyasına yazılan alanlar (2. parçada eşyalar da eklenecek)
    SAVE_FIELDS = (
        "username", "display_name", "class_id", "level", "xp", "gold",
        "last_dungeon", "unlocked_dungeon", "created_at",
    )

    def to_save(self) -> dict:
        data = {k: getattr(self, k) for k in self.SAVE_FIELDS}
        data["equip"] = {s: i.to_dict() for s, i in self.equip.items()}
        data["bag"] = [i.to_dict() for i in self.bag]
        return data

    @classmethod
    def from_save(cls, d: object) -> "Hero | None":
        if not isinstance(d, dict):
            return None

        class_id = d.get("class_id")
        name = str(d.get("username", ""))[:40]

        if class_id not in CLASS_STATS or not name:
            return None

        def num(key: str, default: int, lo: int, hi: int) -> int:
            try:
                v = int(d.get(key, default))
            except (TypeError, ValueError):
                v = default
            return max(lo, min(hi, v))

        try:
            created = float(d.get("created_at", 0.0))
        except (TypeError, ValueError):
            created = 0.0

        hero = cls(
            username=name,
            display_name=str(d.get("display_name", name))[:40],
            class_id=class_id,
            level=num("level", 1, 1, MAX_LEVEL),
            xp=num("xp", 0, 0, 10 ** 9),
            gold=num("gold", 0, 0, 10 ** 12),
            last_dungeon=num("last_dungeon", 1, 1, 4),
            created_at=created,
            last_seen=time.time(),
        )
        equip = d.get("equip", {})

        if isinstance(equip, dict):
            for slot, raw in equip.items():
                item = Item.from_dict(raw)

                if (
                    item is not None
                    and slot == item.slot
                    and hero.can_use(item)
                ):
                    hero.equip[slot] = item

        bag = d.get("bag", [])

        if isinstance(bag, list):
            for raw in bag[:BAG_SIZE]:
                item = Item.from_dict(raw)

                if item is not None:
                    hero.bag.append(item)

        hero.sort_bag()
        hero.enforce_dungeon()
        hero.recalc(full_heal=True)
        return hero

    def fxv(self, key: str) -> float:
        return self.fx.get(key, 0)

    def can_use(self, item: Item) -> bool:
        if item.slot == "weapon":
            return CLASS_WEAPON[self.class_id] == item.kind
        return True

    def recalc(self, full_heal: bool = False) -> None:
        """Sınıf + seviye + ekipman statlarını hesaplar."""
        s = CLASS_STATS[self.class_id]
        lv = self.level - 1
        ratio = self.hp / self.max_hp if self.max_hp else 1.0

        fx: dict = {}

        for item in self.equip.values():
            for key, value in item.affixes:
                fx[key] = fx.get(key, 0) + value

        for key, a in AFFIXES.items():
            if a["total"] is not None and key in fx:
                fx[key] = min(a["total"], fx[key])

        self.fx = fx

        weapon = self.equip.get("weapon")
        wmin, wmax = (weapon.cur if weapon else (0, 0))
        neck = self.equip.get("kolye")

        armor = sum(
            self.equip[sl].cur[0]
            for sl in ("zirh", "pantolon", "kask", "bot")
            if sl in self.equip
        )

        hp = (
            s["hp"] + lv * LEVEL_HP
            + (neck.cur[0] if neck else 0)
            + fx.get("hp_flat", 0)
        )
        atk = lv * LEVEL_ATK + fx.get("atk_flat", 0)

        self.max_hp = int(
            hp * s["hp_mult"] * (1 + fx.get("hp_pct", 0) / 100)
        )
        self.min_damage = max(
            1, int((s["min_damage"] + atk + wmin) * s["dmg_mult"])
        )
        self.max_damage = max(
            self.min_damage,
            int((s["max_damage"] + atk + wmax) * s["dmg_mult"]),
        )
        self.defense = int(
            (s["defense"] + armor + fx.get("def_flat", 0)) * s["def_mult"]
        )
        self.attack_speed = s["attack_speed"] / (1 + fx.get("aspeed", 0) / 100)

        if full_heal:
            self.hp = self.max_hp
        elif self.hp > 0:
            self.hp = max(1, min(self.max_hp, self.max_hp * ratio))

    # ---------------- ÇANTA / EKİPMAN ----------------
    def sort_bag(self) -> None:
        self.bag.sort(key=lambda i: (-i.rarity, -i.score))

    def add_to_bag(self, item: Item) -> Item | None:
        """Çantaya koyar; 16'yı aşarsa en düşüğü satar ve döndürür."""
        self.bag.append(item)
        self.sort_bag()

        if len(self.bag) > BAG_SIZE:
            sold = self.bag.pop()
            self.gold += sold.sell_price
            return sold

        return None

    def compare(self, item: Item):
        """None: kullanamaz, 1: iyi, -1: zayıf, 0: eşit."""
        if not self.can_use(item):
            return None

        cur = self.equip.get(item.slot)

        if cur is None:
            return 1

        diff = item.score - cur.score
        return 1 if diff > 0.5 else (-1 if diff < -0.5 else 0)

    def equip_from_bag(self, index: int) -> str:
        item = self.bag[index]

        if not self.can_use(item):
            return "Bu sınıf bu silahı kullanamaz."

        self.bag.pop(index)
        old = self.equip.get(item.slot)
        self.equip[item.slot] = item

        if old is not None:
            self.bag.append(old)

        self.sort_bag()
        self.recalc()
        return f"{item.name} kuşanıldı."

    def unequip(self, slot: str) -> str:
        item = self.equip.get(slot)

        if item is None:
            return "Bu slot boş."

        if len(self.bag) >= BAG_SIZE:
            return "Çanta dolu."

        del self.equip[slot]
        self.bag.append(item)
        self.sort_bag()
        self.recalc()
        return f"{item.name} çıkarıldı."

    def auto_equip(self) -> int:
        count = 0

        for slot in SLOTS:
            best_i, best = None, self.equip.get(slot)

            for i, item in enumerate(self.bag):
                if item.slot != slot or not self.can_use(item):
                    continue

                if best is None or item.score > best.score + 0.5:
                    best_i, best = i, item

            if best_i is not None:
                self.equip_from_bag(best_i)
                count += 1

        return count

    def enforce_dungeon(self) -> None:
        """Seviyeye uymayan zindandaysa en yakın izinli zindana taşır."""
        hi = highest_dungeon(self.level)
        lo = max(1, hi - 1)
        self.unlocked_dungeon = hi
        self.last_dungeon = min(hi, max(lo, self.last_dungeon))

    def add_xp(self, amount: int) -> bool:
        """XP ekler, seviye atladıysa True döner."""
        if self.level >= MAX_LEVEL:
            return False

        self.xp += amount
        leveled = False

        while (
            self.level < MAX_LEVEL
            and self.xp >= xp_needed(self.level)
        ):
            self.xp -= xp_needed(self.level)
            self.level += 1
            leveled = True

        if self.level >= MAX_LEVEL:
            self.xp = 0

        if leveled:
            self.enforce_dungeon()
            self.recalc(full_heal=True)

        return leveled

    @property
    def class_name(self) -> str:
        return CLASS_STATS[self.class_id]["display"]

    @property
    def color(self) -> tuple[int, int, int]:
        return CLASS_STATS[self.class_id]["color"]

    @property
    def alive(self) -> bool:
        return self.hp > 0


class HeroManager:
    def __init__(self, owner: str = "", mods: list | None = None) -> None:
        self.owner = norm(owner)
        self.mods = {norm(m) for m in (mods or [])}
        self.banned: set[str] = set()
        self.heroes: dict[str, Hero] = {}
        self.active: dict[str, Hero] = {}
        self.waiting: deque[str] = deque()
        self.notices: deque[tuple[str, float, str]] = deque()
        self.tips: dict[str, tuple[list, float]] = {}
        self.bag_requests: deque[str] = deque()
        self.plus_pending: dict = {}
        self.big_msgs: deque = deque(maxlen=3)

    def notice(self, text: str, kind: str = "info") -> None:
        self.notices.append((text, time.time(), kind))

        while len(self.notices) > 4:
            self.notices.popleft()

    def clean_notices(self) -> None:
        now = time.time()

        while self.notices and now - self.notices[0][1] > 6:
            self.notices.popleft()

    def create_hero(
        self,
        username: str,
        class_id: str,
    ) -> Hero:
        key = username.lower()
        stats = CLASS_STATS[class_id]
        now = time.time()

        hero = Hero(
            username=username,
            display_name=username,
            class_id=class_id,
            created_at=now,
            last_seen=now,
        )
        hero.recalc(full_heal=True)

        self.heroes[key] = hero
        return hero

    def delete_hero(self, username: str) -> bool:
        key = username.lower()

        if key not in self.heroes:
            return False

        self.leave_arena(key, silent=True)
        self.heroes.pop(key, None)
        self.fill_slot()
        return True

    def enter_arena(self, username: str) -> str:
        key = username.lower()
        hero = self.heroes.get(key)

        if hero is None:
            return (
                "Kayıtlı kahraman bulunamadı. "
                "Savaşçı için `!gir savasci`, "
                "Okçu için `!gir okcu` yaz."
            )

        if key in self.active:
            return "Zaten arenadasın."

        if len(self.active) >= MAX_ACTIVE_HEROES:
            if key not in self.waiting:
                self.waiting.append(key)
                return "Arena dolu. Sıradasın."

            return "Zaten sıradasın."

        self.active[key] = hero
        hero.last_seen = time.time()

        if key in self.waiting:
            self.waiting.remove(key)

        return (
            f"{hero.display_name} arenaya girdi. "
            f"Sınıf: {hero.class_name}, Seviye: {hero.level}"
        )

    def leave_arena(
        self,
        username: str,
        silent: bool = False,
    ) -> str:
        key = username.lower()

        if key in self.active:
            self.active.pop(key, None)

            if not silent:
                self.fill_slot()

            return "Arenadan çıktın. Geri dönmek için `!gir` yaz."

        if key in self.waiting:
            self.waiting.remove(key)
            return "Sıradan çıktın."

        return "Arenada veya sırada değilsin."

    def fill_slot(self) -> None:
        while (
            self.waiting
            and len(self.active) < MAX_ACTIVE_HEROES
        ):
            key = self.waiting.popleft()
            hero = self.heroes.get(key)

            if hero is None:
                continue

            self.active[key] = hero
            hero.last_seen = time.time()
            self.notice(
                f"{hero.display_name} sıradan arenaya girdi.",
                "success",
            )

    def handle_chat(
        self,
        username: str,
        text: str,
    ) -> None:
        key = username.lower()

        if norm(username) in self.banned:
            return

        if key in self.active:
            self.active[key].last_seen = time.time()

        if not text.startswith("!"):
            return

        parts = text.strip().split()
        command = parts[0].lower()
        argument = parts[1].lower() if len(parts) > 1 else ""

        if self.item_command(key, username, command):
            return

        if command in ("!at", "!affet"):
            self.moderate(username, command, argument)
            return

        if command == "!zindan":
            self.change_dungeon(key, argument)
            return

        if command == "!gir":
            if not argument:
                self.notice(self.enter_arena(username))
                return

            if argument in ("savasci", "s"):
                class_id = "warrior"
            elif argument in ("okcu", "o"):
                class_id = "archer"
            else:
                self.notice(
                    "Geçersiz sınıf. "
                    "`!gir savasci` veya `!gir okcu` yaz.",
                    "warning",
                )
                return

            if key in self.heroes:
                self.notice(
                    "Zaten bir kahramanın var. "
                    "Arenaya dönmek için `!gir`, "
                    "silmek için `!sil` yaz.",
                    "warning",
                )
                return

            hero = self.create_hero(username, class_id)
            self.notice(
                f"{hero.display_name} kahramanı oluşturuldu. "
                f"Sınıf: {hero.class_name}",
                "success",
            )
            self.notice(self.enter_arena(username), "success")
            return

        if command == "!sil":
            if self.delete_hero(username):
                self.notice(
                    f"{username} kahramanını sildi.",
                    "danger",
                )
            else:
                self.notice(
                    "Silinecek kahraman bulunamadı.",
                    "warning",
                )
            return

        if command == "!cik":
            self.notice(self.leave_arena(username))
            return

    # ---------------- ITEM KOMUTLARI ----------------
    def tip(self, key: str, lines: list) -> None:
        self.tips[key] = (lines, time.time() + TIP_SECONDS)
        self.bag_requests.append(key)

    def on_drop(self, hero: Hero, monster: Monster) -> None:
        mini = monster.name == "Mini-Boss"
        chance = DROP_CHANCE_MINIBOSS if mini else DROP_CHANCE
        chance *= 1 + hero.fxv("drop") / 100

        if random.random() >= chance:
            return

        item = roll_drop(hero.class_id, monster.dungeon_id, mini)
        sign = hero.compare(item)
        hero.add_to_bag(item)

        if item.rarity >= 2:
            arrow = "" if sign is None else ("↑ " if sign > 0 else ("↓ " if sign < 0 else ""))
            self.notice(
                f"{hero.display_name}: {arrow}{item.name} düştü!",
                "warning" if item.rarity >= 3 else "success",
            )

    def item_command(self, key: str, username: str, command: str) -> bool:
        bag_m = re.fullmatch(r"!c(\d{1,2})([ts+]?)", command)
        eq_m = re.fullmatch(r"!e([1-6])([t+]?)", command)
        names = ("!çanta", "!canta", "!tak", "!gm")

        if not (bag_m or eq_m or command in names):
            return False

        if command == "!gm":
            if norm(username) == norm(CREATOR):
                self.gm(key)
            return True

        hero = self.heroes.get(key)

        if hero is None:
            self.notice("Önce kahraman oluştur: `!gir savasci` / `!gir okcu`", "warning")
            return True

        if command in ("!çanta", "!canta"):
            self.tip(key, [("Bir item incelemek için", COLOR_MUTED),
                           ("!c1 ... !c16 yaz", COLOR_MUTED)])
            return True

        if command == "!tak":
            n = hero.auto_equip()
            msg = f"{n} parça kuşandı." if n else "Daha iyi parça yok."
            self.tip(key, [(msg, COLOR_TEXT)])
            return True

        if eq_m:
            slot = SLOTS[int(eq_m.group(1)) - 1]
            item = hero.equip.get(slot)

            if eq_m.group(2) == "+" and item is not None:
                self.tip(key, self.plus_item(hero, key, item))
            elif eq_m.group(2) == "t":
                self.tip(key, [(hero.unequip(slot), COLOR_TEXT)])
            elif item is None:
                self.tip(key, [(f"{SLOT_NAME[slot]}: boş", COLOR_MUTED)])
            else:
                self.tip(key, item_lines(item))

            return True

        idx = int(bag_m.group(1)) - 1
        action = bag_m.group(2)

        if idx >= len(hero.bag):
            self.tip(key, [("O slot boş.", COLOR_MUTED)])
            return True

        item = hero.bag[idx]

        if action == "+":
            self.tip(key, self.plus_item(hero, key, item))
        elif action == "t":
            self.tip(key, [(hero.equip_from_bag(idx), COLOR_TEXT)])
        elif action == "s":
            hero.bag.pop(idx)
            hero.gold += item.sell_price
            self.tip(key, [(f"{item.name} satıldı", COLOR_TEXT),
                           (f"+{item.sell_price} gold", COLOR_ACCENT)])
        else:
            self.tip(key, item_lines(
                item, verdict_line(hero.compare(item)), price=True))

        return True

    def big(self, text: str, color: tuple) -> None:
        self.big_msgs.append((text, time.time() + 4.0, color))

    def plus_item(self, hero: Hero, key: str, item: Item) -> list:
        """Item'a + basmayı dener. Başarısız olursa item yanar."""
        if item.plus >= PLUS_MAX:
            return [(f"{item.name}", item.color), ("Zaten +8", COLOR_ACCENT)]

        rate = PLUS_RATES[item.rarity][item.plus]
        now = time.time()

        # riskli denemelerde ikinci komutla onay iste
        if item.plus >= PLUS_CONFIRM_FROM:
            pend = self.plus_pending.get(key)

            if pend is None or pend[0] != id(item) or now > pend[1]:
                self.plus_pending[key] = (id(item), now + PLUS_CONFIRM_SECONDS)
                return [
                    (item.name, item.color),
                    (f"+{item.plus + 1} şansı: %{rate}", COLOR_ACCENT),
                    (f"Bedel: {plus_cost(item)} gold", COLOR_MUTED),
                    ("Başarısız olursa YANAR!" if not (item.rarity == 4 and item.plus == PLUS_MAX - 1)
                     else "Başarısız olursa +6'ya düşer!", COLOR_ERROR),
                    ("Onay için aynı komutu", COLOR_MUTED),
                    ("tekrar yaz.", COLOR_MUTED),
                ]

            del self.plus_pending[key]

        cost = plus_cost(item)

        if hero.gold < cost:
            return [(item.name, item.color),
                    (f"Yetersiz gold: {cost} lazım", COLOR_ERROR),
                    (f"Elindeki: {hero.gold}", COLOR_MUTED)]

        hero.gold -= cost

        if random.random() * 100 < rate:
            item.plus += 1
            hero.recalc()

            if item.plus >= 7 or (item.plus >= 6 and item.rarity >= 3):
                self.notice(f"{hero.display_name}: {item.name} oldu!", "warning")

            if item.plus == PLUS_MAX:
                self.big(f"+8 !!!", (255, 200, 60))

            return [(item.name, item.color),
                    (f"BAŞARILI: +{item.plus}", COLOR_OK),
                    (item.main_text, COLOR_TEXT)]

        # Mitik +7 -> +8 başarısızsa yanmaz, +6'ya düşer
        if item.rarity == 4 and item.plus == PLUS_MAX - 1:
            item.plus = PLUS_MAX - 2
            hero.recalc()
            self.notice(f"{hero.display_name}: {item.name} düştü (+{item.plus})", "warning")
            return [(item.name, item.color),
                    (f"BAŞARISIZ: +{item.plus}'ya düştü", COLOR_ERROR),
                    (item.main_text, COLOR_TEXT)]

        # başarısız: item yanar
        name = item.name
        burned_rarity = item.rarity

        for i, it in enumerate(hero.bag):
            if it is item:
                del hero.bag[i]
                break
        else:
            for slot, it in list(hero.equip.items()):
                if it is item:
                    del hero.equip[slot]

        hero.recalc()
        self.notice(f"{hero.display_name}: {name} YANDI!", "danger")

        if burned_rarity >= 3:
            self.big("ABOWWW!", (255, 90, 60))

        return [(name, item.color), ("YANDI!", COLOR_ERROR),
                ("Item yok oldu.", COLOR_MUTED)]

    def gm(self, key: str) -> None:
        hero = self.heroes.get(key)

        if hero is None:
            return

        hero.level = MAX_LEVEL
        hero.xp = 0
        hero.enforce_dungeon()
        hero.last_dungeon = hero.unlocked_dungeon
        hero.equip = {}

        for slot in SLOTS:
            kind = CLASS_WEAPON[hero.class_id] if slot == "weapon" else slot
            hero.equip[slot] = make_item(kind, 4, 4, q=1.0, keys=GM_KEYS[slot])
            hero.equip[slot].plus = PLUS_MAX

        hero.recalc(full_heal=True)

    # ---------------- YETKİ ----------------
    def is_staff(self, username: str) -> bool:
        n = norm(username)
        return n == self.owner or n in self.mods or n == norm(CREATOR)

    def moderate(self, username: str, command: str, argument: str) -> None:
        if not self.is_staff(username):
            return

        target = norm(argument)

        if not target:
            self.notice(f"Kullanım: `{command} @kullanici`", "warning")
            return

        if self.is_staff(target):
            self.notice("Yetkili biri atılamaz.", "warning")
            return

        if command == "!affet":
            if target in self.banned:
                self.banned.discard(target)
                self.notice(f"{target} affedildi.", "success")
            else:
                self.notice(f"{target} zaten engelli değil.", "warning")
            return

        self.banned.add(target)

        for key in list(self.active.keys()) + list(self.waiting):
            if norm(key) == target:
                self.leave_arena(key, silent=True)

        self.fill_slot()
        self.notice(f"{target} oyundan atıldı.", "danger")

    # ---------------- ZİNDAN ----------------
    def change_dungeon(self, key: str, argument: str) -> None:
        hero = self.heroes.get(key)

        if hero is None:
            self.notice("Önce kahraman oluştur: `!gir savasci` / `!gir okcu`", "warning")
            return

        ok = allowed_dungeons(hero.level)
        ok_text = " veya ".join(str(d) for d in ok)

        if not argument.isdigit():
            self.notice(
                f"{hero.display_name}: Girebileceğin zindanlar: {ok_text}. "
                "Kullanım: `!zindan 2`",
                "info",
            )
            return

        target = int(argument)

        if target not in ok:
            self.notice(
                f"{hero.display_name}: Zindan {target}'e giremezsin. "
                f"Seviye {hero.level} için: {ok_text}",
                "warning",
            )
            return

        hero.last_dungeon = target
        self.notice(f"{hero.display_name} Zindan {target}'e geçti.", "success")

    # ---------------- KAYIT ----------------
    def snapshot(self) -> dict:
        return {
            "heroes": [h.to_save() for h in self.heroes.values()],
            "banned": sorted(self.banned),
        }

    def restore(self, data: object) -> int:
        if not isinstance(data, dict):
            return 0

        count = 0

        for item in data.get("heroes", []):
            hero = Hero.from_save(item)

            if hero is not None:
                self.heroes[hero.username.lower()] = hero
                count += 1

        banned = data.get("banned", [])

        if isinstance(banned, list):
            self.banned = {norm(b) for b in banned}

        return count

    def update_afk(self) -> None:
        now = time.time()

        for key in list(self.active.keys()):
            hero = self.active[key]

            if now - hero.last_seen > AFK_SECONDS:
                self.active.pop(key, None)
                self.notice(
                    f"{hero.display_name} 5 dakika aktif olmadığı "
                    "için arenadan çıkarıldı.",
                    "danger",
                )
                self.fill_slot()


# =========================================================
# YARATIK VE ZİNDAN
# =========================================================
@dataclass
class Monster:
    name: str
    dungeon_id: int
    hp: int
    max_hp: int
    min_damage: int
    max_damage: int
    xp: int
    gold: int
    speed: float
    size: int
    color: tuple[int, int, int]
    x: float
    y: float
    defense: int = 0
    state: str = "walking"
    alive: bool = True
    death_timer: float = 0.0
    attack_timer: float = 0.0
    damage_by: dict = field(default_factory=dict)
    tk: object = None
    facing: int = -1
    sprite: str = ""
    kind: str = "enemy"


@dataclass
class Dungeon:
    dungeon_id: int
    x: float
    y: float
    w: float
    h: float
    heroes: dict[str, Hero] = field(default_factory=dict)
    monsters: list[Monster] = field(default_factory=list)
    spawn_timer: float = 0.0
    next_spawn_delay: float = 0.0
    bg_offset: float = 0.0
    fighting: bool = False
    notify: object = None
    on_drop: object = None
    bg_pos: float = 0.0
    scrolling: bool = False

    @property
    def scale(self) -> float:
        # hız ve mesafeler panel genişliğine göre ölçeklenir
        return max(0.5, min(1.6, self.w / 960))

    def hero_range(self, hero: Hero) -> float:
        s = CLASS_STATS[hero.class_id]
        return max(
            s["range_px"],
            min(s["range_cap"], self.w * s["range_pct"]),
        )

    @property
    def config(self) -> dict:
        return MONSTER_TABLE[self.dungeon_id]

    @property
    def max_monsters(self) -> int:
        n = max(1, len(self.heroes))
        extra = int((n - 1) / GROUP_K_DIV)
        return min(KILL_CAP, self.config["max_monsters"] + extra)

    @property
    def hp_mult(self) -> float:
        return max(1, len(self.heroes)) ** GROUP_HP_EXP

    @property
    def bg_color(self) -> tuple[int, int, int]:
        return self.config["bg_color"]

    @property
    def grid_color(self) -> tuple[int, int, int]:
        return self.config["grid_color"]

    def active(self) -> bool:
        return bool(self.heroes)

    def update_background(self, dt: float) -> None:
        # kahramanlar ortada yürür gibi durur, zemin ve arka plan sola kayar
        if self.fighting or not self.scrolling:
            return

        self.bg_pos += HERO_SPEED * self.scale * dt

    def spawn_monster(self) -> None:
        pool = self.config["monsters"]
        bosses = [m for m in pool if m["name"] == "Mini-Boss"]
        normals = [m for m in pool if m["name"] != "Mini-Boss"]

        if bosses and random.random() < MINIBOSS_CHANCE:
            template = random.choice(bosses)
        else:
            template = random.choice(normals)

        # grup büyüdükçe can ve ödül artar (kişi başı ilerleme sabit kalır)
        hm = self.hp_mult
        reward = hm ** GROUP_REWARD_EXP
        hp = int(template["hp"] * hm)

        monster = Monster(
            name=template["name"],
            dungeon_id=self.dungeon_id,
            hp=hp,
            max_hp=hp,
            min_damage=template["damage"][0],
            max_damage=template["damage"][1],
            xp=max(1, int(template["xp"] * reward)),
            gold=max(1, int(template["gold"] * reward)),
            speed=template["speed"] * self.scale * MONSTER_SPEED_MULT,
            size=template["size"],
            color=template["color"],
            defense=template.get("defense", 0),
            sprite=template.get("sprite", ""),
            kind=template.get("kind", "enemy"),
            x=self.x + self.w + 20,
            y=random.uniform(
                self.y + 70,
                self.y + self.h - 50,
            ),
        )

        self.monsters.append(monster)

    def update_spawn(self, dt: float) -> None:
        alive_count = sum(1 for m in self.monsters if m.alive)

        if alive_count >= self.max_monsters:
            return

        self.spawn_timer -= dt

        if self.spawn_timer <= 0:
            self.spawn_monster()
            faster = 1 + GROUP_SPAWN_DIV * (max(1, len(self.heroes)) - 1)
            self.spawn_timer = random.uniform(
                self.config["spawn_min"],
                self.config["spawn_max"],
            ) / faster

    def update_monsters(self, dt: float, heroes: dict[str, Hero]) -> None:
        # her kahramana saldıran yaratık sayısı (aggro sınırı için)
        counts: dict = {}

        for m in self.monsters:
            if m.alive and m.tk:
                counts[m.tk] = counts.get(m.tk, 0) + 1

        for monster in self.monsters[:]:
            if not monster.alive:
                monster.state = "dead"
                monster.death_timer -= dt

                if monster.death_timer <= 0:
                    self.monsters.remove(monster)

                continue

            target = heroes.get(monster.tk) if monster.tk else None

            if target is None or not target.alive:
                if monster.tk:
                    counts[monster.tk] = max(0, counts.get(monster.tk, 1) - 1)

                monster.tk = None
                alive = [
                    (abs(h.x - monster.x), k, h)
                    for k, h in heroes.items() if h.alive
                ]
                free = [c for c in alive if counts.get(c[1], 0) < AGGRO_CAP]
                pick = min(free or alive, key=lambda c: c[0], default=None)

                if pick is not None:
                    monster.tk = pick[1]
                    counts[pick[1]] = counts.get(pick[1], 0) + 1
                    target = pick[2]

            if target is None:
                monster.state = "walking"
                monster.facing = -1
                monster.x -= monster.speed * dt

                # panelin soluna çıkan yaratık yok olur
                if monster.x < self.x - 30:
                    self.monsters.remove(monster)

                continue

            if abs(monster.x - target.x) > MONSTER_ATTACK_RANGE:
                monster.state = "walking"
                direction = -1 if monster.x > target.x else 1
                monster.facing = direction
                monster.x += direction * monster.speed * dt
            else:
                monster.state = "attacking"
                monster.facing = -1 if target.x < monster.x else 1
                monster.attack_timer -= dt

                if monster.attack_timer <= 0:
                    monster.attack_timer = 1.0
                    self.monster_hit(monster, target)

                    if target.hp <= 0:
                        target.gold = max(0, int(target.gold * 0.95))
                        target.respawn_timer = RESPAWN_SECONDS

    def find_nearest_hero(
        self,
        monster: Monster,
        heroes: dict[str, Hero],
    ) -> Hero | None:
        nearest = None
        nearest_distance = 999999

        for hero in heroes.values():
            if not hero.alive:
                continue

            distance = abs(hero.x - monster.x)

            if distance < nearest_distance:
                nearest = hero
                nearest_distance = distance

        return nearest

    def home_x(self, key: str) -> float:
        """Kahramanın boştayken durduğu yer: şeridin ortasına yakın, biraz dağınık."""
        spread = ((sum(map(ord, key)) * 37) % 100) / 100 - 0.5
        return self.x + self.w * HOME_PCT + spread * self.w * HOME_SPREAD_PCT

    def update_heroes(self, dt: float) -> None:
        speed = HERO_SPEED * self.scale
        right_limit = self.x + self.w - 60
        see = self.w * SEE_PCT
        adv = self.w * ADVANCE_PCT
        fighting = False
        all_idle = True
        any_alive = False

        for key, hero in self.heroes.items():
            if not hero.alive:
                hero.respawn_timer -= dt

                if hero.respawn_timer <= 0:
                    hero.hp = hero.max_hp
                    hero.x = self.x + 40      # soldan yürüyerek evine gelir

                continue

            any_alive = True

            # panel değişince / zindan değişince içeri al
            if hero.x < self.x or hero.x > self.x + self.w:
                hero.x = self.x + 40

            home = self.home_x(key)
            target = self.find_nearest_monster(hero)

            if target is not None and abs(hero.x - target.x) > see \
                    and abs(hero.x - target.x) > self.hero_range(hero):
                target = None     # çok uzakta: yaratık gelene kadar evinde bekle

            if target is None:
                # boşta: evine yürü, evindeyse olduğu yerde yürüme animasyonu
                hero.anim_state = "walk"

                if hero.x < home - 4:
                    hero.facing = 1
                    hero.x = min(home, hero.x + speed * dt)
                elif hero.x > home + 4:
                    hero.facing = -1
                    hero.x = max(home, hero.x - speed * 0.7 * dt)
                else:
                    hero.facing = 1

                self.regen(hero, dt, walking=True)
                continue

            all_idle = False
            distance = abs(hero.x - target.x)

            if distance > self.hero_range(hero):
                # yaratığa yaklaşmak için birkaç adım (evinden en fazla adv kadar)
                step = speed * dt if target.x > hero.x else -speed * dt
                lo = min(home - adv, hero.x)
                hi = max(home + adv, hero.x)
                hero.anim_state = "walk"
                hero.facing = 1 if step > 0 else -1
                hero.x = max(self.x + 10, min(right_limit, max(lo, min(hi, hero.x + step))))
                self.regen(hero, dt, walking=True)
                continue

            fighting = True
            hero.anim_state = "attack"
            hero.facing = 1 if target.x >= hero.x else -1
            hero.attack_timer -= dt

            if hero.attack_timer <= 0:
                hero.attack_timer = hero.attack_speed
                hero.atk_var = random.randint(1, 3)
                self.hero_hit(hero, target)

                if (
                    target.alive
                    and random.random() * 100 < hero.fxv("double")
                ):
                    self.hero_hit(hero, target)

        self.fighting = fighting
        self.scrolling = any_alive and all_idle and not fighting

    def hero_hit(self, hero: Hero, target: Monster) -> None:
        dmg = random.randint(hero.min_damage, hero.max_damage)

        if random.random() * 100 < hero.fxv("crit"):
            dmg *= 1.5 + hero.fxv("critdmg") / 100

        final = max(1, int(dmg) - target.defense // 3)
        steal = hero.fxv("lifesteal")

        if steal:
            hero.hp = min(hero.max_hp, hero.hp + final * steal / 100)

        self.damage_monster(hero, target, final)

    def damage_monster(self, hero: Hero, monster: Monster, amount: int) -> None:
        key = hero.username.lower()
        monster.hp = max(0, monster.hp - amount)
        monster.damage_by[key] = monster.damage_by.get(key, 0) + amount

        if monster.hp <= 0 and monster.alive:
            monster.alive = False
            monster.state = "dead"
            monster.death_timer = 1.0
            self.reward(monster)

    def monster_hit(self, monster: Monster, target: Hero) -> None:
        if random.random() * 100 < target.fxv("dodge"):
            return

        dmg = random.randint(monster.min_damage, monster.max_damage)
        k = DEF_K[monster.dungeon_id]
        mit = min(DEF_CAP, target.defense / (target.defense + k))
        dmg *= (1 - mit) * (1 - target.fxv("dr") / 100)

        final = max(1, int(dmg))
        target.hp = max(0, target.hp - final)
        target.last_damage_time = time.time()

        reflect = target.fxv("reflect")

        if reflect and monster.alive:
            self.damage_monster(
                target, monster, max(1, int(final * reflect / 100))
            )

    def reward(self, monster: Monster) -> None:
        """XP ve gold vuranlar arasında paylaşılır.
        XP: %60 eşit pay + %40 hasaya göre. Gold: eşit pay.
        Item: vuranlardan rastgele birine düşer."""
        shares = {
            k: d for k, d in monster.damage_by.items()
            if k in self.heroes
        }

        if not shares:
            return

        total = sum(shares.values()) or 1
        n = len(shares)

        for key, dmg in shares.items():
            hero = self.heroes[key]
            part = 0.6 / n + 0.4 * dmg / total
            xp = monster.xp * part * (1 + hero.fxv("xp") / 100)

            if hero.add_xp(max(1, int(xp))):
                if callable(self.notify):
                    self.notify(
                        f"{hero.display_name} seviye atladı: {hero.level}",
                        "success",
                    )

            gold = monster.gold / n * (1 + hero.fxv("gold") / 100)
            hero.gold += max(1, int(gold))

        if callable(self.on_drop):
            winner = self.heroes[random.choice(list(shares))]
            self.on_drop(winner, monster)

    def find_nearest_monster(
        self,
        hero: Hero,
    ) -> Monster | None:
        nearest = None
        nearest_distance = 999999

        for monster in self.monsters:
            if not monster.alive:
                continue

            distance = abs(hero.x - monster.x)

            if distance < nearest_distance:
                nearest = monster
                nearest_distance = distance

        return nearest

    def regen(
        self,
        hero: Hero,
        dt: float,
        walking: bool = False,
    ) -> None:
        bonus = hero.fxv("regen")

        if bonus:
            hero.hp = min(hero.max_hp, hero.hp + hero.max_hp * bonus / 100 * dt)

        if time.time() - hero.last_damage_time < REGEN_DELAY:
            return

        percent = REGEN_WALK if walking else REGEN_PERCENT
        heal = hero.max_hp * percent * dt
        hero.hp = min(hero.max_hp, hero.hp + heal)

    def draw(
        self,
        screen: pygame.Surface,
        ui: UI,
    ) -> None:
        panel = pygame.Rect(self.x, self.y, self.w, self.h)
        pygame.draw.rect(screen, self.bg_color, panel, border_radius=10)

        ground_y = self.y + self.h - 45
        lib = SPRITES

        # isteğe bağlı arka plan / zemin görselleri (yatay kayar)
        old_clip = screen.get_clip()
        screen.set_clip(panel)

        bg = lib.tile(f"zindan{self.dungeon_id}", int(self.h)) if lib else None
        ground = lib.tile(f"zemin{self.dungeon_id}", 45) if lib else None

        if bg is not None:
            tw = bg.get_width()
            x0 = self.x - (self.bg_pos % tw)

            while x0 < self.x + self.w:
                screen.blit(bg, (x0, self.y))
                x0 += tw

        if ground is not None:
            tw = ground.get_width()
            x0 = self.x - (self.bg_pos % tw)

            while x0 < self.x + self.w:
                screen.blit(ground, (x0, ground_y))
                x0 += tw
        else:
            for i in range(0, int(self.w) + 100, 100):
                line_x = self.x + (
                    (i - self.bg_pos) % (self.w + 100)
                )
                pygame.draw.line(
                    screen, self.grid_color,
                    (line_x, ground_y), (line_x, self.y + self.h), 5,
                )

        screen.set_clip(old_clip)

        pygame.draw.rect(
            screen, COLOR_PANEL_LIGHT, panel, 2, border_radius=10,
        )

        ui.text(screen, f"Zindan {self.dungeon_id}", "sm",
                (self.x + self.w // 2, self.y + 24), COLOR_ACCENT)
        ui.text(
            screen,
            f"Kahraman: {len(self.heroes)} | Yaratık: {len(self.monsters)}",
            "xs", (self.x + self.w // 2, self.y + 48), COLOR_MUTED,
        )

        # arkadan öne sırala (alt satırdakiler üstte çizilir)
        drawables = []

        for hero in self.heroes.values():
            feet = ground_y + 30 - hero.lane * 26
            drawables.append((feet, 0, hero))

        span = max(1, self.h - 120)

        for monster in self.monsters:
            lane = max(0.0, min(1.0, (monster.y - (self.y + 70)) / span))
            feet = ground_y + 30 - lane * 26
            drawables.append((feet, 1, monster))

        drawables.sort(key=lambda d: d[0])

        for feet, kind, obj in drawables:
            if kind == 0:
                self.draw_hero(screen, ui, obj, feet)
            else:
                self.draw_monster(screen, ui, obj, feet)

    def blit_sprite(self, screen, anim, index, x, feet, facing, native_right):
        flipped = (facing == 1) != native_right
        surf = anim.frame(index, flipped)
        screen.blit(surf, (x - surf.get_width() // 2, feet - surf.get_height()))

    def draw_hero(
        self,
        screen: pygame.Surface,
        ui: UI,
        hero: Hero,
        feet: float,
    ) -> None:
        x = int(hero.x)
        feet = int(feet)
        lib = SPRITES
        folder = "karakter/" + ("savasci" if hero.class_id == "warrior" else "okcu")
        scale = SPRITE_SCALE["hero"]
        phase = (id(hero) % 997) / 997
        anim = None

        if lib is not None:
            if not hero.alive:
                anim = lib.anim(folder, "death", scale)

                if anim is not None:
                    elapsed = RESPAWN_SECONDS - max(0.0, hero.respawn_timer)
                    index = min(anim.n - 1, int(elapsed * anim.fps))
            elif hero.anim_state == "attack":
                anim = lib.anim(folder, f"attack{hero.atk_var}", scale)

                if anim is not None:
                    p = 1 - max(0.0, hero.attack_timer) / max(0.05, hero.attack_speed)
                    index = anim_index(anim, p)
            else:
                anim = lib.anim(folder, "walk", scale)

                if anim is not None:
                    index = anim_index(anim, None, phase)

        if anim is None:
            self.draw_hero_basic(screen, ui, hero, feet)
            return

        self.blit_sprite(screen, anim, index, x, feet, hero.facing, True)
        top = feet - lib.head(folder, scale)

        if hero.alive:
            frac = max(0.0, min(1.0, hero.hp / max(1, hero.max_hp)))
            pygame.draw.rect(screen, (60, 20, 20), (x - 22, top - 4, 44, 4))
            pygame.draw.rect(screen, (90, 220, 110), (x - 22, top - 4, int(44 * frac), 4))

        ui.text(screen, f"[{hero.level}] {hero.display_name}", "xs",
                (x, top - 16), COLOR_TEXT if hero.alive else COLOR_MUTED)

    def draw_hero_basic(self, screen, ui, hero: Hero, feet: int) -> None:
        x = int(hero.x)
        y = feet - 70
        size = 34
        color = hero.color if hero.alive else (100, 100, 105)
        pygame.draw.rect(screen, color, (x - size // 2, y, size, size + 14), border_radius=6)
        pygame.draw.circle(screen, (250, 220, 180) if hero.alive else (160, 160, 165),
                           (x, y - 10), size // 3)
        ui.text(screen, f"[{hero.level}] {hero.display_name}", "xs",
                (x, y - 30), COLOR_TEXT)

    def draw_monster(
        self,
        screen: pygame.Surface,
        ui: UI,
        monster: Monster,
        feet: float,
    ) -> None:
        x = int(monster.x)
        feet = int(feet)
        lib = SPRITES
        boss = monster.kind == "boss"
        scale = SPRITE_SCALE["boss" if boss else "enemy"]
        folder = monster.sprite
        phase = (id(monster) % 997) / 997
        anim = None

        if lib is not None and folder:
            if not monster.alive:
                anim = lib.anim(folder, "death", scale)

                if anim is not None:
                    index = anim_index(anim, 1 - max(0.0, monster.death_timer))
            elif monster.state == "attacking":
                anim = lib.anim(folder, "cleave" if boss else "attack", scale)

                if anim is not None:
                    index = anim_index(anim, 1 - max(0.0, monster.attack_timer))
            else:
                anim = lib.anim(folder, "walk", scale)

                if anim is not None:
                    index = anim_index(anim, None, phase)

        if anim is None:
            color = monster.color if monster.alive else (90, 90, 95)
            y = feet - monster.size
            pygame.draw.circle(screen, color, (x, y + monster.size // 2),
                               monster.size // 2)
            top = y
        else:
            native_right = folder.split("/")[-1] in FACES_RIGHT
            self.blit_sprite(screen, anim, index, x, feet, monster.facing, native_right)
            top = feet - lib.head(folder, scale)

        if monster.alive:
            width = 90 if boss else 34
            frac = max(0.0, min(1.0, monster.hp / max(1, monster.max_hp)))
            pygame.draw.rect(screen, (120, 30, 30), (x - width // 2, top - 10, width, 5))
            pygame.draw.rect(screen, (220, 60, 60),
                             (x - width // 2, top - 10, int(width * frac), 5))

            if boss:
                ui.text(screen, "Boss" if monster.name == "Boss" else "Mini-Boss",
                        "xs", (x, top - 22), (255, 120, 120))


# =========================================================
# DÜNYA
# =========================================================
class World:
    def __init__(self) -> None:
        self.dungeons: dict[int, Dungeon] = {}

    def update(self, dt: float, hero_manager: HeroManager) -> None:
        active_dungeons = set(
            hero.last_dungeon
            for hero in hero_manager.active.values()
        )

        for dungeon_id in active_dungeons:
            if dungeon_id not in self.dungeons:
                self.dungeons[dungeon_id] = Dungeon(
                    dungeon_id=dungeon_id,
                    x=0,
                    y=0,
                    w=0,
                    h=0,
                )

        for dungeon_id in list(self.dungeons.keys()):
            if dungeon_id not in active_dungeons:
                self.dungeons.pop(dungeon_id, None)

        if not self.dungeons:
            return

        dungeon_ids = sorted(self.dungeons.keys())
        panel_w = INTERNAL_W / len(dungeon_ids)

        for index, dungeon_id in enumerate(dungeon_ids):
            dungeon = self.dungeons[dungeon_id]
            dungeon.x = index * panel_w
            dungeon.y = STRIP_Y
            dungeon.w = panel_w
            dungeon.h = STRIP_H

            dungeon.heroes = {
                key: hero
                for key, hero in hero_manager.active.items()
                if hero.last_dungeon == dungeon_id
            }

            dungeon.notify = hero_manager.notice
            dungeon.on_drop = hero_manager.on_drop
            dungeon.update_background(dt)
            dungeon.update_spawn(dt)
            dungeon.update_monsters(dt, dungeon.heroes)
            dungeon.update_heroes(dt)

    def draw(
        self,
        screen: pygame.Surface,
        ui: UI,
    ) -> None:
        if not self.dungeons:
            self.draw_lobby(screen, ui)
            return

        for dungeon in self.dungeons.values():
            dungeon.draw(screen, ui)

    def draw_lobby(
        self,
        screen: pygame.Surface,
        ui: UI,
    ) -> None:
        pygame.draw.rect(
            screen,
            COLOR_PANEL,
            (12, STRIP_Y + 12, INTERNAL_W - 24, STRIP_H - 24),
            border_radius=14,
        )

        ui.text(screen, "ORRVETH", "lg",
                (INTERNAL_W // 2, STRIP_Y + 95), COLOR_ACCENT)
        ui.text(screen, "Arena boş. Katılmak için sohbete yaz:", "sm",
                (INTERNAL_W // 2, STRIP_Y + 160))
        ui.text(screen, "!gir savasci  veya  !gir okcu", "md",
                (INTERNAL_W // 2, STRIP_Y + 205))
        ui.text(screen, "Zindan değiştirmek için: !zindan 2", "xs",
                (INTERNAL_W // 2, STRIP_Y + 250), COLOR_MUTED)


# =========================================================
# PYGAME ARAYÜZ
# =========================================================
class UI:
    def __init__(self) -> None:
        self.fonts = {
            "xs": pygame.font.SysFont("arial", 14, bold=True),
            "sm": pygame.font.SysFont("arial", 18, bold=True),
            "md": pygame.font.SysFont("arial", 24, bold=True),
            "lg": pygame.font.SysFont("arial", 38, bold=True),
        }

    def text(
        self,
        screen: pygame.Surface,
        text: str,
        size: str,
        pos: tuple[int, int],
        color: tuple[int, int, int] = COLOR_TEXT,
        center: bool = True,
    ) -> None:
        surf = self.fonts[size].render(text, True, color)
        rect = surf.get_rect()

        if center:
            rect.center = pos
        else:
            rect.topleft = pos

        screen.blit(surf, rect)


class LoginScreen:
    """Kanal adı + isteğe bağlı mod listesi."""

    CH = pygame.Rect(240, 175, 480, 44) if hasattr(pygame, "Rect") else None
    MODBOX = pygame.Rect(240, 275, 420, 44) if hasattr(pygame, "Rect") else None
    PLUS = pygame.Rect(670, 275, 50, 44) if hasattr(pygame, "Rect") else None
    GO = pygame.Rect(380, 420, 200, 46) if hasattr(pygame, "Rect") else None

    def __init__(
        self,
        error: str = "",
        channel: str = "",
        mods: list | None = None,
    ) -> None:
        self.channel = channel
        self.mod_input = ""
        self.mods: list[str] = list(mods or [])
        self.error = error
        self.focus = "channel"
        self.chip_rects: list[tuple] = []

    def add_mod(self) -> None:
        name = self.mod_input.strip().lstrip("@")

        if not name:
            return

        if not SLUG_RE.match(name):
            self.error = "Geçersiz mod adı"
            return

        if norm(name) not in [norm(m) for m in self.mods]:
            self.mods.append(name)

        self.mod_input = ""
        self.error = ""

    def connect(self) -> tuple[str, list[str]] | None:
        channel = self.channel.strip().lstrip("@")

        if not SLUG_RE.match(channel):
            self.error = "Geçersiz kanal adı"
            return None

        if self.mod_input.strip():
            self.add_mod()

        return channel.lower(), list(self.mods)

    def handle(self, event, pos=None):
        if event.type == pygame.MOUSEBUTTONDOWN and pos is not None:
            if self.CH.collidepoint(pos):
                self.focus = "channel"
            elif self.MODBOX.collidepoint(pos):
                self.focus = "mod"
            elif self.PLUS.collidepoint(pos):
                self.add_mod()
            elif self.GO.collidepoint(pos):
                return self.connect()
            else:
                for rect, name in self.chip_rects:
                    if rect.collidepoint(pos):
                        self.mods.remove(name)
                        break
            return None

        if event.type != pygame.KEYDOWN:
            return None

        if event.key == pygame.K_TAB:
            self.focus = "mod" if self.focus == "channel" else "channel"
            return None

        field_name = "channel" if self.focus == "channel" else "mod_input"
        value = getattr(self, field_name)

        if event.key == pygame.K_BACKSPACE:
            setattr(self, field_name, value[:-1])

        elif event.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
            if self.focus == "mod":
                self.add_mod()
            else:
                return self.connect()

        elif event.unicode and len(value) < 40:
            if re.fullmatch(r"[A-Za-z0-9_\-]", event.unicode):
                setattr(self, field_name, value + event.unicode)

        return None

    def draw(self, screen: pygame.Surface, ui: UI) -> None:
        screen.fill(COLOR_BG)
        pygame.draw.rect(screen, COLOR_PANEL, (180, 50, 600, 440), border_radius=14)

        ui.text(screen, "ORRVETH", "lg", (480, 95), COLOR_ACCENT)
        ui.text(screen, "Kick kanal adın (oyun bu kanalda oynanır):", "sm", (480, 150))

        cursor = "_" if int(time.time() * 2) % 2 == 0 else " "

        for rect, text, key in (
            (self.CH, self.channel, "channel"),
            (self.MODBOX, self.mod_input, "mod"),
        ):
            pygame.draw.rect(screen, COLOR_PANEL_LIGHT, rect, border_radius=8)
            pygame.draw.rect(
                screen,
                COLOR_ACCENT if self.focus == key else COLOR_MUTED,
                rect, 2, border_radius=8,
            )
            shown = text + (cursor if self.focus == key else "")
            ui.text(screen, shown, "md", rect.center)

        ui.text(screen, "Mod ekle (isteğe bağlı) - kanal sahibi zaten yetkili:",
                "sm", (480, 250))

        pygame.draw.rect(screen, COLOR_OK, self.PLUS, border_radius=8)
        ui.text(screen, "+", "lg", self.PLUS.center, COLOR_BG)

        self.chip_rects = []
        x, y = 240, 335

        for name in self.mods:
            label = f"{name}  x"
            w = ui.fonts["sm"].size(label)[0] + 20
            rect = pygame.Rect(x, y, w, 28)

            if x + w > 720:
                x, y = 240, y + 34
                rect = pygame.Rect(x, y, w, 28)

            pygame.draw.rect(screen, COLOR_PANEL_LIGHT, rect, border_radius=14)
            ui.text(screen, label, "sm", rect.center)
            self.chip_rects.append((rect, name))
            x += w + 8

        pygame.draw.rect(screen, COLOR_ACCENT, self.GO, border_radius=10)
        ui.text(screen, "Bağlan", "md", self.GO.center, COLOR_BG)
        ui.text(screen, "Tab: alan değiştir | Enter: bağlan / mod ekle | mod adına tıkla: sil",
                "xs", (480, 475), COLOR_MUTED)

        if self.error:
            ui.text(screen, self.error, "sm", (480, 395), COLOR_ERROR)


class Display:
    """İç tuvali (canvas) pencereye orantılı ölçekler; OBS'te boyut serbest."""

    def __init__(self, canvas_size: tuple[int, int], window_size=None) -> None:
        self.canvas = pygame.Surface(canvas_size)
        pygame.display.set_mode(window_size or canvas_size, pygame.RESIZABLE)

    def set_canvas(self, canvas_size, window_size=None) -> None:
        self.canvas = pygame.Surface(canvas_size)
        pygame.display.set_mode(window_size or canvas_size, pygame.RESIZABLE)

    def _fit(self) -> tuple[float, float, float]:
        ww, wh = pygame.display.get_surface().get_size()
        cw, ch = self.canvas.get_size()
        scale = min(ww / cw, wh / ch)
        return scale, (ww - cw * scale) / 2, (wh - ch * scale) / 2

    def to_canvas(self, pos) -> tuple[float, float]:
        scale, ox, oy = self._fit()
        return (pos[0] - ox) / scale, (pos[1] - oy) / scale

    def present(self) -> None:
        window = pygame.display.get_surface()
        scale, ox, oy = self._fit()
        cw, ch = self.canvas.get_size()
        size = (max(1, int(cw * scale)), max(1, int(ch * scale)))

        if size == (cw, ch) and window.get_size() == (cw, ch):
            window.blit(self.canvas, (0, 0))
        else:
            window.fill((0, 0, 0))
            window.blit(
                pygame.transform.scale(self.canvas, size),
                (int(ox), int(oy)),
            )

        pygame.display.flip()


class BagWindow:
    """Çanta paneli: ayrı pencere yok, ana tuvalin içinde (OBS'te görünür)."""

    SIZE = (BAG_W, BAG_H)

    def __init__(self) -> None:
        self.surface = pygame.Surface(self.SIZE)
        self.window = None

    def open(self) -> None:
        pass

    def close(self) -> None:
        pass

    def present(self) -> bool:
        return False


def draw_item_box(s, ui, rect, item, number, arrow=None) -> None:
    pygame.draw.rect(s, COLOR_PANEL_LIGHT, rect, border_radius=6)

    if item is not None:
        c = item.color
        pygame.draw.rect(s, tuple(v // 4 for v in c), rect, border_radius=6)
        pygame.draw.rect(s, c, rect, 2, border_radius=6)
        icon = (
            SPRITES.icon(item.kind, item.rarity, item.variant, rect.w - 8)
            if SPRITES is not None else None
        )

        if icon is not None:
            s.blit(icon, (rect.x + 4, rect.y + 4))
        else:
            ui.text(s, KIND_LETTER[item.kind], "md", rect.center, c)

        if arrow is not None and arrow != 0:
            x, y = rect.right - 14, rect.y + 5

            if arrow > 0:
                pts = [(x + 5, y), (x, y + 9), (x + 10, y + 9)]
                pygame.draw.polygon(s, COLOR_OK, pts)
            else:
                pts = [(x, y), (x + 10, y), (x + 5, y + 9)]
                pygame.draw.polygon(s, COLOR_ERROR, pts)

    if item is not None and item.plus > 0:
        ui.text(s, f"+{item.plus}", "xs", (rect.right - 20, rect.bottom - 16),
                COLOR_ACCENT, center=False)

    ui.text(s, str(number), "xs", (rect.x + 4, rect.y + 2),
            COLOR_MUTED, center=False)


class Game:
    def __init__(self, channel: str, mods: list | None = None) -> None:
        self.channel = channel.lower()
        self.running = True
        self.msg_queue: queue.Queue = queue.Queue()
        self.status = "Bağlanılıyor..."

        self.hero_manager = HeroManager(self.channel, mods)
        self.world = World()
        self.last_afk_check = 0.0
        self.last_save = time.time()
        self.bag = BagWindow()
        self.bag_key: str | None = None
        self.bag_until = 0.0
        self.bag_wait: deque[str] = deque()

        data = read_json(save_path(self.channel))

        if data is None:
            data = read_json(save_path(self.channel) + ".bak")

        loaded = self.hero_manager.restore(data)

        if loaded:
            self.hero_manager.notice(
                f"{loaded} kahraman kayıttan yüklendi.", "success"
            )

        self.kick_reader = KickChatReader(
            self.channel,
            self.msg_queue,
        )
        self.kick_reader.start()

    def save(self) -> None:
        try:
            data = {"version": 1, "saved_at": time.time()}
            data.update(self.hero_manager.snapshot())
            write_json_atomic(save_path(self.channel), data)
        except OSError as exc:
            print(f"[KAYIT HATASI] {exc}", flush=True)

        self.last_save = time.time()

    def process_messages(self) -> None:
        for _ in range(100):
            try:
                msg = self.msg_queue.get_nowait()
            except queue.Empty:
                break

            kind = msg.get("type")

            if kind == "chat":
                user = msg.get("user", "?")
                text = msg.get("text", "")
                print(f"[CHAT] {user}: {text}", flush=True)
                self.hero_manager.handle_chat(user, text)

            elif kind == "status":
                self.status = msg.get("message", "")

            elif kind == "fatal":
                self.status = msg.get("message", "Hata")
                print(f"[HATA] {self.status}", flush=True)

    def update(self, dt: float) -> None:
        now = time.time()

        if now - self.last_afk_check >= 1.0:
            self.hero_manager.update_afk()
            self.last_afk_check = now

        if now - self.last_save >= SAVE_INTERVAL:
            self.save()

        self.hero_manager.clean_notices()
        self.world.update(dt, self.hero_manager)
        self.update_bag(now)

    def update_bag(self, now: float) -> None:
        hm = self.hero_manager

        while hm.bag_requests:
            key = hm.bag_requests.popleft()

            if key == self.bag_key:
                self.bag_until = now + BAG_SECONDS
            elif key not in self.bag_wait:
                self.bag_wait.append(key)

        if self.bag_key is not None and now >= self.bag_until:
            self.bag_key = None
            self.bag.close()

        if self.bag_key is None and self.bag_wait:
            self.bag_key = self.bag_wait.popleft()
            self.bag_until = now + BAG_SECONDS
            self.bag.open()

    def draw_bag(self, screen: pygame.Surface, ui: UI) -> None:
        hm = self.hero_manager
        hero = hm.heroes.get(self.bag_key) if self.bag_key else None

        if hero is None:
            return

        s = self.bag.surface
        s.fill(COLOR_BG)
        pygame.draw.rect(s, COLOR_PANEL, (6, 6, 748, 468), border_radius=12)

        ui.text(s, f"[{hero.level}] {hero.display_name} - {hero.class_name}",
                "md", (24, 16), COLOR_ACCENT, center=False)
        need = xp_needed(hero.level) if hero.level < MAX_LEVEL else 1
        frac = 1.0 if hero.level >= MAX_LEVEL else hero.xp / need
        pygame.draw.rect(s, COLOR_PANEL_LIGHT, (410, 24, 320, 12), border_radius=6)
        pygame.draw.rect(s, COLOR_ACCENT, (410, 24, int(320 * frac), 12), border_radius=6)
        ui.text(s, f"Altın: {hero.gold}", "sm", (410, 40), (255, 205, 60), center=False)

        # ekipman: sol 3 + sağ 3, ortada karakter
        layout = {
            "kask": (24, 76), "zirh": (24, 140), "pantolon": (24, 204),
            "weapon": (252, 76), "bot": (252, 140), "kolye": (252, 204),
        }

        for slot, (x, y) in layout.items():
            item = hero.equip.get(slot)
            draw_item_box(s, ui, pygame.Rect(x, y, 52, 52), item,
                          SLOTS.index(slot) + 1)
            ui.text(s, SLOT_NAME[slot], "xs", (x + 26, y + 60), COLOR_MUTED)

        pygame.draw.rect(s, COLOR_BG, (92, 76, 150, 196), border_radius=10)
        pygame.draw.rect(s, COLOR_ACCENT, (92, 76, 150, 196), 2, border_radius=10)
        folder = "karakter/" + ("savasci" if hero.class_id == "warrior" else "okcu")
        pa = SPRITES.anim(folder, "idle", 1.6) if SPRITES is not None else None

        if pa is not None:
            surf = pa.frame(anim_index(pa), False)
            s.blit(surf, (167 - surf.get_width() // 2, 262 - surf.get_height()))
        else:
            pygame.draw.rect(s, hero.color, (142, 160, 50, 70), border_radius=8)
            pygame.draw.circle(s, (250, 220, 180), (167, 140), 20)

        # statlar
        ui.text(s, f"ATK: {hero.min_damage}-{hero.max_damage}", "md",
                (410, 76), (235, 90, 90), center=False)
        ui.text(s, f"DEF: {hero.defense}", "md", (410, 106),
                (90, 160, 240), center=False)
        ui.text(s, f"HP: {int(hero.hp)}/{hero.max_hp}", "md", (410, 136),
                COLOR_OK, center=False)

        y = 172

        for key, value in sorted(hero.fx.items()):
            a = AFFIXES[key]
            text = f"{a['name']} +{int(value)}" if a["flat"] else f"{a['name']} +%{value:g}"
            ui.text(s, text, "xs", (410, y), COLOR_TEXT, center=False)
            y += 16

            if y > 262:
                break

        # çanta 8x2
        ui.text(s, f"ÇANTA {len(hero.bag)}/{BAG_SIZE}", "xs", (24, 284),
                COLOR_MUTED, center=False)

        for i in range(BAG_SIZE):
            x = 24 + (i % 8) * 64
            y = 304 + (i // 8) * 64
            item = hero.bag[i] if i < len(hero.bag) else None
            arrow = hero.compare(item) if item is not None else None
            draw_item_box(s, ui, pygame.Rect(x, y, 58, 58), item, i + 1, arrow)

        # bilgi kutusu
        pygame.draw.rect(s, COLOR_BG, (548, 276, 196, 190), border_radius=8)
        lines, until = hm.tips.get(self.bag_key, ([], 0))

        if time.time() >= until:
            lines = [("!c1 ... !c16: incele", COLOR_MUTED)]

        y = 284

        for text, color in lines[:10]:
            ui.text(s, text, "xs", (556, y), color, center=False)
            y += 17

        ui.text(s, "!cNt kuşan  !cNs sat  !eNt çıkar  !tak hepsini tak",
                "xs", (24, 440), COLOR_MUTED, center=False)

        screen.blit(s, (BAG_X, BAG_Y))

    def draw_notices(self, screen: pygame.Surface, ui: UI) -> None:
        colors = {
            "info": COLOR_TEXT,
            "success": COLOR_OK,
            "warning": COLOR_ACCENT,
            "danger": COLOR_ERROR,
        }
        y = INTERNAL_H - 38

        for text, _, kind in list(self.hero_manager.notices)[-2:]:
            ui.text(screen, text, "xs", (12, y),
                    colors.get(kind, COLOR_TEXT), center=False)
            y += 17

    def draw_big(self, screen: pygame.Surface, ui: UI) -> None:
        msgs = self.hero_manager.big_msgs
        now = time.time()

        while msgs and now > msgs[0][1]:
            msgs.popleft()

        if not msgs:
            return

        text, until, color = msgs[-1]
        base = ui.fonts["lg"].render(text, True, color)
        shadow = ui.fonts["lg"].render(text, True, (0, 0, 0))
        w, h = base.get_width() * 3, base.get_height() * 3
        base = pygame.transform.scale(base, (w, h))
        shadow = pygame.transform.scale(shadow, (w, h))
        x, y = (INTERNAL_W - w) // 2, STRIP_Y + 60
        screen.blit(shadow, (x + 4, y + 4))
        screen.blit(base, (x, y))

    def draw_status(self, screen: pygame.Surface, ui: UI) -> None:
        if "bağlandı" in self.status.lower():
            return
        color = COLOR_ERROR
        surf = ui.fonts["xs"].render(
            f"Kanal: {self.channel} | {self.status}", True, color
        )
        screen.blit(surf, (INTERNAL_W - surf.get_width() - 10, STRIP_Y + 6))

    def shutdown(self) -> None:
        self.save()
        self.bag.close()
        self.kick_reader.stop()


class App:
    def __init__(self) -> None:
        cfg = read_json(settings_path())
        cfg = cfg if isinstance(cfg, dict) else {}
        mods = cfg.get("mods", [])

        self.login = LoginScreen(
            channel=str(cfg.get("channel", "")),
            mods=mods if isinstance(mods, list) else [],
        )
        self.game: Game | None = None

    @staticmethod
    def game_window_size() -> tuple[int, int]:
        try:
            desktop_w = pygame.display.get_desktop_sizes()[0][0]
        except (AttributeError, IndexError, pygame.error):
            desktop_w = INTERNAL_W

        w = max(640, min(INTERNAL_W, desktop_w - 40))
        return w, int(w * INTERNAL_H / INTERNAL_W)

    def shutdown(self) -> None:
        if self.game is not None:
            self.game.shutdown()
            self.game = None

        pygame.quit()

    def run(self) -> None:
        global SPRITES
        # ses sistemi hiç açılmaz: oyun tamamen sessiz
        pygame.display.init()
        pygame.font.init()
        pygame.display.set_caption("ORRVETH")

        display = Display((LOGIN_W, LOGIN_H))
        SPRITES = Sprites()
        clock = pygame.time.Clock()
        ui = UI()

        while True:
            dt = min(0.1, clock.tick(FPS) / 1000.0)

            for event in pygame.event.get():
                if event.type == pygame.QUIT or (
                    event.type == pygame.KEYDOWN
                    and event.key == pygame.K_ESCAPE
                ):
                    self.shutdown()
                    return

                close_ev = getattr(pygame, "WINDOWCLOSE", None)

                if close_ev is not None and event.type == close_ev:
                    if self.game is not None and self.game.bag.window is not None:
                        win = getattr(event, "window", None)

                        if win is None or win is self.game.bag.window:
                            self.game.bag_key = None
                            self.game.bag.close()
                            continue

                    self.shutdown()
                    return

                if self.game is None:
                    pos = None

                    if event.type == pygame.MOUSEBUTTONDOWN:
                        pos = display.to_canvas(event.pos)

                    result = self.login.handle(event, pos)

                    if result:
                        channel, mods = result

                        try:
                            write_json_atomic(
                                settings_path(),
                                {"channel": channel, "mods": mods},
                            )
                        except OSError:
                            pass

                        self.game = Game(channel, mods)
                        display.set_canvas(
                            (INTERNAL_W, INTERNAL_H),
                            self.game_window_size(),
                        )

            if self.game is None:
                self.login.draw(display.canvas, ui)
            else:
                self.game.process_messages()
                self.game.update(dt)

                screen = display.canvas
                screen.fill(COLOR_KEY)
                self.game.world.draw(screen, ui)
                self.game.draw_notices(screen, ui)
                self.game.draw_bag(screen, ui)
                self.game.draw_big(screen, ui)
                self.game.draw_status(screen, ui)

                if self.game.status.startswith("Kanal bulunamadı"):
                    self.game.shutdown()
                    self.login = LoginScreen(
                        self.game.status,
                        self.game.channel,
                        list(self.game.hero_manager.mods),
                    )
                    self.game = None
                    display.set_canvas((LOGIN_W, LOGIN_H))

            display.present()


if __name__ == "__main__":
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(errors="replace")
        except (AttributeError, ValueError):
            pass

    try:
        App().run()
    except Exception:
        traceback.print_exc()