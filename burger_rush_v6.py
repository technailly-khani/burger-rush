"""
BURGER RUSH v6 - Restaurant Edition
===================================
A fast-food restaurant game for your DSA project (pure Python + Tkinter,
no extra libraries, no image files).

Two game modes (Settings screen)
  CAREER  - a 7-day week. Each day lasts 100 seconds and has a money goal.
            Miss the goal and you lose a life. After every day you can spend
            your cash in the UPGRADE SHOP. New dishes appear on days 2, 4, 6.
  QUICK   - the classic mode: reach a target amount of money before you
            lose 3 lives.

How a round works
  1. Up to 3 customers (never more) stand at the counter and order.
  2. Read the MENU on the right: it shows what goes in every dish.
  3. Cook in the kitchen: grill (beef / chicken), toaster (buns),
     fryer (fries) and drink dispenser. Food visibly cooks and can burn.
  4. Click READY food: cooked patties and buns move to the WARMING RACK.
  5. Click rack items in menu order to build the burger on the plate,
     press WRAP, and it goes on the SERVING SHELF.
  6. Click an order card -> the waiter takes the food to that customer.
  7. Combo orders (burger + fries + drink) pay a bonus. Gold VIPs pay more
     and jump to the top of the order board. Random events (rush hour,
     happy hour, grill flare-up, cold oil) change the rules for a while.

Data structures (all written by hand, so you can explain them):
  Stack          -> the burger plate (push / pop / peek) and a second Stack
                    for REDO. Undo = pop from plate, push to redo.
  Queue          -> the waiter's delivery jobs (first in, first out).
  Priority Queue -> the order board (min-heap). VIP customers have priority 0
                    and jump ahead of normal customers (priority 1).
  Linked List    -> OrderHistory: every served / lost order is appended as a
                    node; the end screen walks the list from head to tail.
  Hash Map       -> MENU, COOK, RECIPES, UPGRADES, EVENTS lookups (dict).
  SQLite table   -> the high-score table (burger_rush_scores.db).

Run:  python burger_rush_v6.py
Keys: Esc or P = pause / resume,  M = sound on / off
Sound uses winsound (built into Python on Windows). On other systems the game
is simply silent.
"""

import datetime
import heapq
import itertools
import math
import os
import queue as _stdqueue      # thread-safe queue, only used by the sound worker
import random
import sqlite3
import threading
import time
import tkinter as tk
from collections import deque


# =====================================================================
# PART 1: DATA STRUCTURES
# =====================================================================

class Stack:
    """LIFO stack. The last ingredient placed is the first one removed."""

    def __init__(self):
        self._items = []

    def push(self, item):
        self._items.append(item)

    def pop(self):
        if self.is_empty():
            return None
        return self._items.pop()

    def peek(self):
        if self.is_empty():
            return None
        return self._items[-1]

    def is_empty(self):
        return len(self._items) == 0

    def size(self):
        return len(self._items)

    def clear(self):
        self._items.clear()

    def to_list(self):
        return list(self._items)          # bottom -> top


class Queue:
    """FIFO queue. The waiter serves jobs in the order they were created."""

    def __init__(self):
        self._items = deque()

    def enqueue(self, item):
        self._items.append(item)

    def dequeue(self):
        if not self._items:
            return None
        return self._items.popleft()

    def peek(self):
        if not self._items:
            return None
        return self._items[0]

    def is_empty(self):
        return len(self._items) == 0

    def size(self):
        return len(self._items)

    def clear(self):
        self._items.clear()


class CustomerLine:
    """
    Priority queue (min-heap) used as the ORDER BOARD.
    Lower number = more urgent: VIP = 0, normal = 1. Customers with the same
    priority are ordered by arrival (the counter breaks the tie), so the
    board works first come, first served inside each priority level.
    """

    def __init__(self):
        self._heap = []
        self._counter = itertools.count()

    def enqueue(self, customer):
        heapq.heappush(self._heap, (customer["priority"], next(self._counter), customer))

    def dequeue(self):
        if not self._heap:
            return None
        return heapq.heappop(self._heap)[2]

    def peek(self):
        if not self._heap:
            return None
        return self._heap[0][2]

    def remove(self, customer):
        self._heap = [e for e in self._heap if e[2] is not customer]
        heapq.heapify(self._heap)

    def to_list(self):
        return [e[2] for e in sorted(self._heap, key=lambda e: (e[0], e[1]))]

    def size(self):
        return len(self._heap)


class _Node:
    """One node of the singly linked list."""

    def __init__(self, value):
        self.value = value
        self.next = None


class OrderHistory:
    """
    Singly linked list (head -> ... -> tail) written by hand.
    Every finished order (served or lost) is appended at the tail in O(1).
    The end screen walks the list from the head to draw the chain.
    """

    def __init__(self):
        self.head = None
        self.tail = None
        self._size = 0

    def append(self, value):
        node = _Node(value)
        if self.head is None:
            self.head = node
            self.tail = node
        else:
            self.tail.next = node
            self.tail = node
        self._size += 1

    def __len__(self):
        return self._size

    def __iter__(self):
        node = self.head
        while node is not None:
            yield node.value
            node = node.next

    def last(self, n):
        """The last n values (walks the whole list, O(size))."""
        values = list(self)
        return values[-n:] if n > 0 else []

    def count(self, outcome):
        """How many nodes have this outcome (one walk from head to tail)."""
        total = 0
        for v in self:
            if v["outcome"] == outcome:
                total += 1
        return total


class Sound:
    """
    Beeps for game events (Windows only, uses winsound). The beeps are played
    by a background thread that reads a thread-safe queue, so the game never
    freezes while a sound is playing. On other systems everything is silent.
    """
    TONES = {
        "click":  [(900, 25)],
        "place":  [(600, 35)],
        "ready":  [(1200, 70)],
        "wrap":   [(700, 50), (950, 70)],
        "serve":  [(900, 70), (1300, 110)],
        "burn":   [(220, 260)],
        "angry":  [(320, 140), (230, 240)],
        "vip":    [(1000, 60), (1400, 60), (1800, 90)],
        "event":  [(700, 90), (900, 90), (700, 90)],
        "dayend": [(800, 100), (1000, 100), (1200, 180)],
        "buy":    [(1000, 60), (1500, 90)],
        "no":     [(250, 120)],
        "win":    [(1000, 100), (1200, 100), (1500, 100), (2000, 240)],
        "lose":   [(500, 180), (400, 180), (300, 380)],
    }

    def __init__(self):
        try:
            import winsound
            self._ws = winsound
        except ImportError:
            self._ws = None
        self.enabled = True
        self._q = _stdqueue.Queue()
        if self._ws is not None:
            threading.Thread(target=self._worker, daemon=True).start()

    @property
    def available(self):
        return self._ws is not None

    def play(self, name):
        if not self.enabled or self._ws is None:
            return
        if self._q.qsize() > 4:            # never build up a long backlog
            return
        self._q.put(name)

    def _worker(self):
        while True:
            name = self._q.get()
            for freq, ms in self.TONES.get(name, ()):
                try:
                    self._ws.Beep(freq, ms)
                except Exception:
                    break


class ScoreBoard:
    """High-score table stored in a small SQLite file next to this script."""

    def __init__(self):
        folder = os.path.dirname(os.path.abspath(__file__))
        self.path = os.path.join(folder, "burger_rush_scores.db")
        self.memory = []                   # used only if the file cannot be opened
        self.db_ok = True
        try:
            con = sqlite3.connect(self.path)
            con.execute("CREATE TABLE IF NOT EXISTS scores ("
                        "id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT, score INTEGER, "
                        "mode TEXT, day INTEGER, difficulty TEXT, served INTEGER, played TEXT)")
            con.commit()
            con.close()
        except Exception:
            self.db_ok = False

    def add(self, name, score, mode, day, difficulty, served):
        row = (name, int(score), mode, int(day), difficulty, int(served),
               datetime.date.today().isoformat())
        if self.db_ok:
            try:
                con = sqlite3.connect(self.path)
                con.execute("INSERT INTO scores (name, score, mode, day, difficulty, served, played) "
                            "VALUES (?, ?, ?, ?, ?, ?, ?)", row)
                con.commit()
                con.close()
                return
            except Exception:
                self.db_ok = False
        self.memory.append(row)

    def top(self, limit=10):
        rows = []
        if self.db_ok:
            try:
                con = sqlite3.connect(self.path)
                rows = con.execute("SELECT name, score, mode, day, difficulty, served, played "
                                   "FROM scores ORDER BY score DESC, id ASC LIMIT ?", (limit,)).fetchall()
                con.close()
                return rows
            except Exception:
                self.db_ok = False
        return sorted(self.memory, key=lambda r: -r[1])[:limit]

    def best(self):
        rows = self.top(1)
        return rows[0][1] if rows else 0


# ---------------- Hash maps (Python dictionaries) ----------------------

MENU = {
    "Classic Cheeseburger": {"price": 6, "desc": "Beef, cheese, lettuce, tomato", "day": 1, "weight": 3,
                             "short": "Classic",
                             "recipe": ["Bun", "Patty", "Cheese", "Lettuce", "Tomato"]},
    "Double Cheeseburger":  {"price": 9, "desc": "Two beef patties, double cheese", "day": 1, "weight": 1,
                             "short": "Double",
                             "recipe": ["Bun", "Patty", "Cheese", "Patty", "Cheese"]},
    "French Fries":         {"price": 3, "desc": "Golden and crispy", "day": 1, "weight": 0,
                             "short": "Fries", "recipe": None},
    "Chicken Burger":       {"price": 7, "desc": "Crispy chicken, lettuce, tomato", "day": 1, "weight": 2,
                             "short": "Chicken",
                             "recipe": ["Bun", "Chicken", "Lettuce", "Tomato"]},
    "Soft Drink":           {"price": 2, "desc": "Cold and fizzy", "day": 1, "weight": 0,
                             "short": "Drink", "recipe": None},
    # ---- new dishes that unlock on later career days ----
    "Chicken Cheese Burger": {"price": 8, "desc": "Chicken, cheese, lettuce, tomato", "day": 2, "weight": 2,
                              "short": "Chk+Cheese",
                              "recipe": ["Bun", "Chicken", "Cheese", "Lettuce", "Tomato"]},
    "Mega Burger":          {"price": 11, "desc": "Two patties, cheese, lettuce, tomato", "day": 4, "weight": 1,
                             "short": "Mega",
                             "recipe": ["Bun", "Patty", "Cheese", "Patty", "Lettuce", "Tomato"]},
    "Mixed Burger":         {"price": 10, "desc": "Beef and chicken together", "day": 6, "weight": 1,
                             "short": "Mixed",
                             "recipe": ["Bun", "Patty", "Cheese", "Chicken", "Lettuce"]},
}

# recipe (as a tuple) -> dish name, so "what did the player build?" is one lookup
RECIPES = {tuple(v["recipe"]): name for name, v in MENU.items() if v["recipe"]}

# plain-English steps for the menu panel
for _name, _spec in MENU.items():
    _spec["steps"] = ", ".join(_spec["recipe"]) if _spec["recipe"] else ""
MENU["French Fries"]["steps"] = "Fry potatoes (7 sec)"
MENU["Soft Drink"]["steps"] = "Fill a cup (3 sec)"

# cooking time in seconds, and the point (as a multiple of that time) where it burns
COOK = {
    "Beef":    {"time": 8.0, "burn": 2.5},
    "Chicken": {"time": 9.0, "burn": 2.5},
    "Bun":     {"time": 4.0, "burn": 3.0},
    "Fries":   {"time": 7.0, "burn": 2.5},
    "Drink":   {"time": 3.0, "burn": None},
}

DIFFICULTY = {
    "Easy":   {"patience": 75.0, "interval": 20.0, "goal_mult": 0.8},
    "Normal": {"patience": 60.0, "interval": 16.0, "goal_mult": 1.0},
    "Hard":   {"patience": 50.0, "interval": 12.0, "goal_mult": 1.2},
}
TARGETS = [100, 150, 250]

# ---- career mode ----
CAREER_DAYS = 7
DAY_LENGTH = 100.0                       # seconds per day
DAY_GOALS = [25, 35, 45, 55, 65, 75, 90]   # money needed each day (Normal difficulty)
COMBO_CHANCE = 0.15                      # chance of a burger + fries + drink combo
COMBO_BONUS = 2                          # extra dollars for a combo

# upgrade shop: cost = base cost x (current level + 1)
UPGRADES = {
    "grill":    {"name": "Hot Grill",       "desc": "Patties and chicken cook 20% faster per level", "cost": 25, "max": 3},
    "kitchen":  {"name": "Turbo Kitchen",   "desc": "Toaster, fryer and drinks 20% faster per level", "cost": 25, "max": 3},
    "safety":   {"name": "Fire Guard",      "desc": "Food burns 25% later per level", "cost": 30, "max": 3},
    "patience": {"name": "Comfy Seats",     "desc": "Customers wait 12% longer per level", "cost": 30, "max": 3},
    "waiter":   {"name": "Waiter Skates",   "desc": "The waiter walks 25% faster per level", "cost": 20, "max": 3},
    "tips":     {"name": "Tip Jar",         "desc": "Tips are 50% bigger per level", "cost": 25, "max": 3},
}

# random events: name, seconds, colour, message
EVENTS = {
    "rush":  ("RUSH HOUR",      18.0, "#e67e22", "Rush hour! Customers arrive fast and pay 25% more!"),
    "happy": ("HAPPY HOUR",     20.0, "#2e9e4f", "Happy hour! All tips are doubled!"),
    "flare": ("GRILL FLARE-UP", 14.0, "#c0392b", "Flare-up! The grill is very hot - patties cook fast, watch them!"),
    "oil":   ("COLD OIL",       16.0, "#2a78c4", "Cold oil! Fries cook much slower for a while."),
}


# =====================================================================
# PART 2: SMALL HELPERS
# =====================================================================

def F(px, bold=False):
    """Font in PIXELS (negative size), so text looks the same on every screen."""
    return ("Arial", -int(px), "bold") if bold else ("Arial", -int(px))


def _rgb(h):
    return int(h[1:3], 16), int(h[3:5], 16), int(h[5:7], 16)


def mix(c1, c2, t):
    """Blend two #rrggbb colors. t=0 -> c1, t=1 -> c2."""
    t = max(0.0, min(1.0, t))
    a, b = _rgb(c1), _rgb(c2)
    return "#%02x%02x%02x" % tuple(int(a[i] + (b[i] - a[i]) * t) for i in range(3))


def item_stage(it):
    """Returns (stage, progress). stage is cooking / ready / burnt."""
    spec = COOK[it["kind"]]
    total = it.get("time", spec["time"])          # upgrades make this smaller
    burn = it.get("burn", spec["burn"])           # upgrades make this larger
    p = it["t"] / total
    if p < 1.0:
        return "cooking", p
    if burn and p >= burn:
        return "burnt", p
    return "ready", p


SKINS = ["#f5cba7", "#e0ac69", "#c68642", "#8d5524"]
HAIRS = ["#2c1b0e", "#5a3825", "#111111", "#a0522d", "#c9a227"]
SHIRTS = ["#3b82f6", "#10b981", "#ef4444", "#8b5cf6", "#f97316", "#ec4899", "#14b8a6"]
PANTS = ["#34495e", "#2c3e50", "#4a4a4a", "#5d4037"]

CHEF_LOOK = {"kind": "chef", "skin": "#f0c8a0", "hair": "#3a2a1a", "hair_style": 3,
             "shirt": "#ffffff", "pants": "#3a3f4a", "vip": False}
WAITER_LOOK = {"kind": "waiter", "skin": "#e0ac80", "hair": "#222222", "hair_style": 4,
               "shirt": "#f5f5f5", "pants": "#222222", "vip": False}


def random_look(rng, vip=False):
    return {"kind": "customer", "skin": rng.choice(SKINS), "hair": rng.choice(HAIRS),
            "hair_style": rng.choice([0, 0, 1, 2]),
            "shirt": "#f1c40f" if vip else rng.choice(SHIRTS),
            "pants": rng.choice(PANTS), "vip": vip}


# =====================================================================
# PART 3: DRAWING FOOD
# =====================================================================

def draw_layer(c, name, x, yb, w, h, tag):
    """One burger layer. x = left edge, yb = bottom edge, w = width, h = height."""
    y1 = yb - h
    x2 = x + w
    if name == "Bun":
        c.create_rectangle(x, y1 + h * 0.25, x2, yb, fill="#e0a24e", outline="#8a5a1c",
                           width=1, tags=tag)
    elif name == "TopBun":
        c.create_arc(x, y1, x2, y1 + 2 * h, start=0, extent=180, fill="#e0a24e",
                     outline="#8a5a1c", width=1, style="chord", tags=tag)
        r = max(1.0, h / 9.0)
        for fx, fy in ((0.3, 0.55), (0.5, 0.3), (0.7, 0.55), (0.4, 0.75), (0.6, 0.75)):
            sx, sy = x + w * fx, y1 + h * fy
            c.create_oval(sx - r * 1.4, sy - r * 0.8, sx + r * 1.4, sy + r * 0.8,
                          fill="#fff3d6", outline="", tags=tag)
    elif name == "Patty":
        c.create_rectangle(x - w * 0.02, y1 + h * 0.12, x2 + w * 0.02, yb - h * 0.04,
                           fill="#6b3a1e", outline="#3e2010", width=1, tags=tag)
    elif name == "Chicken":
        c.create_rectangle(x - w * 0.02, y1 + h * 0.1, x2 + w * 0.02, yb - h * 0.04,
                           fill="#d9993f", outline="#a8661a", width=1, tags=tag)
        for fx in (0.2, 0.45, 0.7):
            sx = x + w * fx
            c.create_oval(sx - 1.5, y1 + h * 0.35, sx + 1.5, y1 + h * 0.5,
                          fill="#f0c070", outline="", tags=tag)
    elif name == "Cheese":
        pts = [(x - w * 0.04, y1 + h * 0.3), (x2 + w * 0.04, y1 + h * 0.3),
               (x2 + w * 0.04, y1 + h * 0.7), (x2 - w * 0.14, y1 + h * 0.7),
               (x2 - w * 0.2, yb), (x2 - w * 0.26, y1 + h * 0.7),
               (x - w * 0.04, y1 + h * 0.7)]
        c.create_polygon(pts, fill="#ffd23f", outline="#c9a000", width=1, tags=tag)
    elif name == "Lettuce":
        pts = [(x - w * 0.05, yb - h * 0.1)]
        step = max(3.0, w / 9.0)
        xx, k = x - w * 0.05, 0
        while xx <= x2 + w * 0.05:
            pts.append((xx, y1 + (h * 0.15 if k % 2 == 0 else h * 0.5)))
            xx += step
            k += 1
        pts.append((x2 + w * 0.05, yb - h * 0.1))
        c.create_polygon(pts, fill="#5cb85c", outline="#2e7d32", width=1, tags=tag)
    elif name == "Tomato":
        c.create_oval(x + w * 0.06, y1 + h * 0.15, x2 - w * 0.06, yb - h * 0.05,
                      fill="#e0453a", outline="#a02020", width=1, tags=tag)


def draw_burger(c, cx, yb, w, layers, h, tag):
    y = yb
    for name in layers:
        draw_layer(c, name, cx - w / 2.0, y, w, h, tag)
        y -= h


def draw_item_icon(c, name, cx, cy, s, tag):
    """A small picture of a menu item, centred on (cx, cy). s = scale (1.0 ~ 36px wide)."""
    spec = MENU.get(name)
    if spec and spec["recipe"]:
        layers = spec["recipe"] + ["TopBun"]
        h = 5.0 * s
        total = h * len(layers)
        draw_burger(c, cx, cy + total / 2.0, 36 * s, layers, h, tag)
    elif name == "French Fries":
        for i in range(-3, 4):
            x = cx + i * 4.2 * s
            top = cy - (17 + (i % 3) * 3) * s
            c.create_rectangle(x - 1.7 * s, top, x + 1.7 * s, cy + 2 * s,
                               fill="#f4c430", outline="#c99a10", tags=tag)
        c.create_polygon([(cx - 13 * s, cy - 2 * s), (cx + 13 * s, cy - 2 * s),
                          (cx + 10 * s, cy + 15 * s), (cx - 10 * s, cy + 15 * s)],
                         fill="#d62828", outline="#7a0f0f", tags=tag)
        c.create_oval(cx - 4 * s, cy + 3 * s, cx + 4 * s, cy + 11 * s,
                      fill="#ffe066", outline="", tags=tag)
    elif name == "Soft Drink":
        c.create_line(cx + 2 * s, cy - 9 * s, cx + 6 * s, cy - 19 * s, fill="#2a9d8f",
                      width=max(1, 2 * s), tags=tag)
        c.create_polygon([(cx - 9 * s, cy - 8 * s), (cx + 9 * s, cy - 8 * s),
                          (cx + 7 * s, cy + 15 * s), (cx - 7 * s, cy + 15 * s)],
                         fill="#ffffff", outline="#888888", tags=tag)
        c.create_polygon([(cx - 8 * s, cy), (cx + 8 * s, cy),
                          (cx + 7.4 * s, cy + 8 * s), (cx - 7.4 * s, cy + 8 * s)],
                         fill="#d62828", outline="", tags=tag)
        c.create_rectangle(cx - 10 * s, cy - 11 * s, cx + 10 * s, cy - 8 * s,
                           fill="#d62828", outline="#7a0f0f", tags=tag)


# =====================================================================
# PART 4: DRAWING PEOPLE
# =====================================================================

def draw_person(c, x, fy, look, anim, tag="dyn", s=0.72):
    """
    A person standing with feet at (x, fy).
    look: appearance (kind = customer / chef / waiter).
    anim: walking, phase, mood, arm_up (0..1), tray (list of item names).
    """
    kind = look["kind"]
    walking = anim.get("walking", False)
    ph = anim.get("phase", 0.0)
    swing = math.sin(ph) * 7.0 if walking else 0.0
    bob = abs(math.sin(ph)) * 1.6 if walking else 0.0
    mood = anim.get("mood", "neutral")
    skin, shirt, pants, hair = look["skin"], look["shirt"], look["pants"], look["hair"]
    ink = "#2b2b2b"

    def X(dx):
        return x + dx * s

    def Y(dy):
        return fy + dy * s - bob

    # --- legs and shoes
    for sg in (-1, 1):
        hip_x = X(sg * 7)
        foot_x = X(sg * 7 + swing * sg)
        c.create_line(hip_x, Y(-36), foot_x, fy - 4 * s, width=max(2, 11 * s), fill=pants,
                      capstyle="round", tags=tag)
        c.create_oval(foot_x - 7 * s, fy - 7 * s, foot_x + 8 * s, fy,
                      fill="#1f1f1f", outline="", tags=tag)

    # --- torso and shoulders
    top, bot = Y(-86), Y(-34)
    c.create_rectangle(X(-19), top, X(19), bot, fill=shirt, outline=ink, width=1, tags=tag)
    c.create_oval(X(-21), top - 3 * s, X(21), top + 14 * s, fill=shirt, outline=ink,
                  width=1, tags=tag)
    if kind == "customer":
        c.create_polygon([(X(-7), Y(-88)), (X(0), Y(-76)), (X(7), Y(-88))],
                         fill=skin, outline=ink, tags=tag)
        for by in (-68, -58, -48):
            c.create_oval(X(-1.5), Y(by) - 1.5, X(1.5), Y(by) + 1.5, fill="#333333",
                          outline="", tags=tag)
    elif kind == "chef":
        for bx in (-6, 6):
            for by in (-72, -60, -48):
                c.create_oval(X(bx) - 2, Y(by) - 2, X(bx) + 2, Y(by) + 2, fill="#9aa5ad",
                              outline="", tags=tag)
        c.create_polygon([(X(-9), Y(-88)), (X(0), Y(-74)), (X(9), Y(-88))],
                         fill="#c0392b", outline=ink, tags=tag)
    elif kind == "waiter":
        c.create_rectangle(X(-19), Y(-84), X(-3), Y(-36), fill="#222222", outline="", tags=tag)
        c.create_rectangle(X(3), Y(-84), X(19), Y(-36), fill="#222222", outline="", tags=tag)
        c.create_polygon([(X(0), Y(-84)), (X(-7), Y(-90)), (X(-7), Y(-78))],
                         fill="#c0392b", outline="", tags=tag)
        c.create_polygon([(X(0), Y(-84)), (X(7), Y(-90)), (X(7), Y(-78))],
                         fill="#c0392b", outline="", tags=tag)

    # --- arms
    sleeve = shirt
    tray = anim.get("tray")
    for sg in (-1, 1):
        sh_x, sh_y = X(sg * 21), Y(-80)
        hx, hy = X(sg * 26 - swing * sg * 0.7), Y(-46)
        up = anim.get("arm_up", 0.0)
        if sg == 1 and up > 0:
            hx, hy = X(31), Y(-46 - 58 * up)
        if tray is not None:
            hx, hy = X(sg * 15), Y(-58)
        c.create_line(sh_x, sh_y, hx, hy, width=max(2, 9 * s), fill=sleeve,
                      capstyle="round", tags=tag)
        c.create_oval(hx - 4.5 * s, hy - 4.5 * s, hx + 4.5 * s, hy + 4.5 * s,
                      fill=skin, outline="", tags=tag)

    # --- neck, head, ears
    c.create_rectangle(X(-5), Y(-92), X(5), Y(-84), fill=skin, outline="", tags=tag)
    c.create_oval(X(-19), Y(-112), X(-14), Y(-101), fill=skin, outline=ink, tags=tag)
    c.create_oval(X(14), Y(-112), X(19), Y(-101), fill=skin, outline=ink, tags=tag)
    c.create_oval(X(-16), Y(-126), X(16), Y(-90), fill=skin, outline=ink, width=1, tags=tag)

    # --- hair / hats
    style = look["hair_style"]
    if style in (0, 1):
        c.create_arc(X(-17), Y(-132), X(17), Y(-100), start=0, extent=180, fill=hair,
                     outline=hair, style="chord", tags=tag)
    if style == 1:
        c.create_polygon([(X(-18), Y(-120)), (X(-12), Y(-120)), (X(-12), Y(-86)), (X(-22), Y(-84))],
                         fill=hair, outline="", tags=tag)
        c.create_polygon([(X(18), Y(-120)), (X(12), Y(-120)), (X(12), Y(-86)), (X(22), Y(-84))],
                         fill=hair, outline="", tags=tag)
    elif style == 3:      # chef hat
        c.create_oval(X(-19), Y(-168), X(1), Y(-142), fill="#ffffff", outline="#bbbbbb", tags=tag)
        c.create_oval(X(-3), Y(-168), X(19), Y(-142), fill="#ffffff", outline="#bbbbbb", tags=tag)
        c.create_oval(X(-12), Y(-172), X(12), Y(-146), fill="#ffffff", outline="#bbbbbb", tags=tag)
        c.create_rectangle(X(-15), Y(-150), X(15), Y(-126), fill="#ffffff", outline="#bbbbbb", tags=tag)
        c.create_rectangle(X(-16), Y(-132), X(16), Y(-126), fill="#dddddd", outline="#bbbbbb", tags=tag)
    elif style == 4:      # waiter cap
        c.create_rectangle(X(-14), Y(-138), X(14), Y(-126), fill="#222222", outline="", tags=tag)
        c.create_rectangle(X(-17), Y(-128), X(17), Y(-124), fill="#111111", outline="", tags=tag)
    if look.get("vip"):
        c.create_polygon([(X(-14), Y(-130)), (X(-14), Y(-146)), (X(-7), Y(-138)),
                          (X(0), Y(-150)), (X(7), Y(-138)), (X(14), Y(-146)),
                          (X(14), Y(-130))],
                         fill="#ffd700", outline="#b8860b", tags=tag)

    # --- face
    for ex in (-6, 6):
        c.create_oval(X(ex - 3.5), Y(-112), X(ex + 3.5), Y(-105), fill="#ffffff", outline=ink, tags=tag)
        c.create_oval(X(ex - 1.6), Y(-110.5), X(ex + 1.6), Y(-106.5), fill="#222222", outline="", tags=tag)
    bw = max(1, 1.6 * s)
    if mood == "angry":
        c.create_line(X(-11), Y(-118), X(-3), Y(-114), fill=ink, width=bw, tags=tag)
        c.create_line(X(3), Y(-114), X(11), Y(-118), fill=ink, width=bw, tags=tag)
    elif mood == "worried":
        c.create_line(X(-11), Y(-114), X(-3), Y(-118), fill=ink, width=bw, tags=tag)
        c.create_line(X(3), Y(-118), X(11), Y(-114), fill=ink, width=bw, tags=tag)
    else:
        c.create_line(X(-11), Y(-117), X(-3), Y(-117), fill=ink, width=bw, tags=tag)
        c.create_line(X(3), Y(-117), X(11), Y(-117), fill=ink, width=bw, tags=tag)
    c.create_line(X(0), Y(-108), X(1.5), Y(-100), fill="#a06a4a", width=bw, tags=tag)
    if mood == "happy":
        c.create_arc(X(-8), Y(-103), X(8), Y(-91), start=200, extent=140, style="arc",
                     outline="#5a1a1a", width=max(1, 2 * s), tags=tag)
        for bx in (-11, 11):
            c.create_oval(X(bx - 3), Y(-101), X(bx + 3), Y(-97), fill="#f5a3a3", outline="", tags=tag)
    elif mood == "angry":
        c.create_arc(X(-8), Y(-97), X(8), Y(-87), start=20, extent=140, style="arc",
                     outline="#5a1a1a", width=max(1, 2 * s), tags=tag)
    elif mood == "worried":
        c.create_line(X(-6), Y(-94), X(6), Y(-96), fill="#5a1a1a", width=max(1, 2 * s), tags=tag)
    else:
        c.create_line(X(-6), Y(-95), X(6), Y(-95), fill="#5a1a1a", width=max(1, 2 * s), tags=tag)

    # --- tray with food (waiter)
    if tray is not None:
        c.create_rectangle(X(-30), Y(-62), X(30), Y(-57), fill="#c7ced4", outline="#6b747b", tags=tag)
        n = len(tray)
        for i, name in enumerate(tray[:4]):
            ix = X((i - (min(n, 4) - 1) / 2.0) * 22)
            draw_item_icon(c, name, ix, Y(-77), 0.55, tag)


# =====================================================================
# PART 5: THE GAME
# =====================================================================

class BurgerRush:
    W, H = 960, 600
    PLAY_W = 740
    SLOT_X = [240, 400, 560]            # where the 3 customers stand
    LANE_BACK, LANE_FRONT = 166, 186    # walking lane / standing line
    DOOR_X = 36
    CHEF_X, STAFF_Y = 118, 306
    WAITER_HOME = 690
    PLATE_X, PLATE_Y, PLATE_MAX = 340, 584, 6
    SHELF_MAX = 6
    RACK_MAX = 6
    START_LIVES = 3
    FRAME_MS = 40

    # ---- tuning numbers (change these to rebalance the game) ----
    TIP_RATE = 0.30             # tip = price * TIP_RATE * (patience left)
    VIP_CHANCE = 0.20           # chance that a customer (after the first two) is VIP
    VIP_PRICE_MULT = 1.5        # VIPs pay more ...
    VIP_PATIENCE_MULT = 0.75    # ... but are less patient
    WAITER_SPEED = 250.0
    CUSTOMER_IN_SPEED = 130.0

    # appliance slot centres (x, y)
    GRILL_SLOTS = [(64, 372), (134, 372), (204, 372)]
    TOASTER_SLOTS = [(306, 372), (354, 372)]
    FRYER_SLOTS = [(448, 372), (506, 372)]
    DRINK_SLOTS = [(598, 372), (682, 372)]

    # bins: (kind, x1, y1, x2, y2, label)
    BINS = [
        ("Beef",    14, 424,  96, 470, "RAW BEEF (8s)"),
        ("Chicken", 104, 424, 186, 470, "CHICKEN (9s)"),
        ("Bun",     290, 424, 372, 470, "BUNS (4s)"),
        ("Fries",   432, 424, 514, 470, "POTATOES (7s)"),
        ("Drink",   612, 424, 694, 470, "CUPS (3s)"),
        ("Cheese",   16, 500,  92, 540, "CHEESE"),
        ("Lettuce", 100, 500, 176, 540, "LETTUCE"),
        ("Tomato",  184, 500, 260, 540, "TOMATO"),
    ]

    def __init__(self, root):
        self.root = root
        root.title("Burger Rush v6")
        root.resizable(False, False)
        self.canvas = tk.Canvas(root, width=self.W, height=self.H, highlightthickness=0,
                                bg="#2d1e1a")
        self.canvas.pack()

        self.rng = random.Random()
        self.settings = {"difficulty": "Normal", "target": 150, "mode": "career"}
        self.snd = Sound()
        self.scores = ScoreBoard()
        self.last_name = "Player"
        self.name_buf = "Player"
        self.end_outcome = "gameover"
        self._menu_shown = None
        self.end_top = []
        self.score_rows = []
        self.state = "menu"             # menu / howto / settings / playing / paused / gameover / complete
        self.mouse = (-1, -1)
        self.hits = []
        self.flash = None
        self.flash_t = 0.0
        self.cursor = ""
        self.menu_visible = True
        self.closing = False
        self.dt = 0.0

        self.reset_game()
        self.draw_static()
        self.draw_menu_static()

        self.canvas.bind("<Button-1>", self.on_click)
        self.canvas.bind("<Motion>", self.on_motion)
        self.canvas.bind("<Leave>", self.on_leave)
        root.bind("<Key>", self.on_key)
        root.protocol("WM_DELETE_WINDOW", self.close)

        self.last = time.perf_counter()
        self._job = self.root.after(self.FRAME_MS, self.loop)   # the ONLY game loop

    # ------------------------------------------------------------------
    # window / loop
    # ------------------------------------------------------------------

    def close(self):
        self.closing = True
        try:
            self.root.after_cancel(self._job)
        except Exception:
            pass
        self.root.destroy()

    def loop(self):
        if self.closing:
            return
        now = time.perf_counter()
        self.dt = min(0.1, now - self.last)
        self.last = now
        self.msg_t = max(0.0, self.msg_t - self.dt)
        if self.state == "playing":
            self.update(self.dt)
        self.render()
        self._job = self.root.after(self.FRAME_MS, self.loop)

    def on_motion(self, event):
        self.mouse = (event.x, event.y)

    def on_leave(self, event):
        self.mouse = (-1, -1)

    def on_click(self, event):
        for x1, y1, x2, y2, action, glow in reversed(self.hits):
            if x1 <= event.x <= x2 and y1 <= event.y <= y2:
                self.flash = (x1, y1, x2, y2)
                self.flash_t = 0.15
                if self.state != "playing":
                    self.snd.play("click")
                action()
                return

    def on_key(self, event):
        key = event.keysym
        if self.state == "entername":                    # typing a name for the high-score table
            if key in ("Return", "KP_Enter"):
                self.save_name()
            elif key == "BackSpace":
                self.name_buf = self.name_buf[:-1]
            elif event.char and event.char.isprintable() and len(self.name_buf) < 12:
                self.name_buf += event.char
            return
        if key == "Escape" or key.lower() == "p":
            self.toggle_pause()
        elif key.lower() == "m":
            self.toggle_sound()

    def toggle_sound(self):
        self.snd.enabled = not self.snd.enabled
        if self.snd.enabled:
            self.snd.play("ready")
        if self.state in ("playing", "paused"):
            self.say("Sound %s." % ("ON" if self.snd.enabled else "OFF"))

    # ------------------------------------------------------------------
    # game state changes
    # ------------------------------------------------------------------

    def career(self):
        return self.settings["mode"] == "career"

    def ev(self, kind):
        """True while the random event of this kind is running."""
        return self.event is not None and self.event["kind"] == kind

    def reset_game(self):
        """Brand-new run: everything back to zero (upgrades, cash, history...)."""
        self.clock = 0.0
        self.score = 0
        self.cash = 0
        self.served = 0
        self.missed = 0
        self.lives = self.START_LIVES
        self.next_id = 1
        self.spawned = 0
        self.day = 1
        self.last_day = None
        self.upg = {key: 0 for key in UPGRADES}
        self.history = OrderHistory()     # linked list of finished orders
        self.msg = ""
        self.msg_t = 0.0
        self.msg_color = "#ffe9c7"
        self.reset_day_state()

    def reset_day_state(self):
        """Fresh kitchen and shop floor (called at the start of every day)."""
        self.customers = []
        self.spawn_timer = 1.0
        self.board = CustomerLine()       # priority queue of orders
        self.jobs = Queue()               # waiter's delivery jobs
        self.plate = Stack()              # burger being assembled
        self.redo = Stack()               # items taken off the plate by UNDO
        self.shelf = []
        self.rack = []                    # warming rack: cooked food waiting
        self.grill = [None] * 3
        self.toaster = [None] * 2
        self.fryer = [None] * 2
        self.drinks = [None] * 2
        self.staff = {"x": self.WAITER_HOME, "state": "idle", "t": 0.0, "job": None,
                      "phase": 0.0, "items": None, "walking": False}
        self.flyers = []
        self.popups = []
        self.day_time = DAY_LENGTH
        self.day_earned = 0
        self.day_served = 0
        self.day_missed = 0
        self.day_goal = self.goal_for_day()
        self.event = None
        self.event_timer = 30.0 + self.rng.random() * 20.0

    def goal_for_day(self):
        base = DAY_GOALS[min(self.day, len(DAY_GOALS)) - 1]
        return int(round(base * DIFFICULTY[self.settings["difficulty"]]["goal_mult"]))

    def day_patience(self):
        base = DIFFICULTY[self.settings["difficulty"]]["patience"]
        if self.career():
            base = max(30.0, base - 2.5 * (self.day - 1))
        return base * (1.0 + 0.12 * self.upg["patience"])

    def day_interval(self):
        base = DIFFICULTY[self.settings["difficulty"]]["interval"]
        if self.career():
            base = max(7.0, base - 1.2 * (self.day - 1))
        return base

    def speed_for(self, kind):
        if kind in ("Beef", "Chicken"):
            return 1.0 + 0.2 * self.upg["grill"]
        return 1.0 + 0.2 * self.upg["kitchen"]

    def available_dishes(self):
        day = self.day if self.career() else 1
        return [name for name, spec in MENU.items() if spec["day"] <= day]

    def available_burgers(self):
        return [name for name in self.available_dishes() if MENU[name]["recipe"]]

    def start_game(self):
        self.reset_game()
        self.flash = None
        self.state = "playing"
        if self.career():
            self.say("Day 1 - goal $%d. Customers are arriving!" % self.day_goal)
        else:
            self.say("Customers are arriving! Read the orders on the right.")

    def go_menu(self):
        self.reset_game()
        self.state = "menu"

    def pause(self):
        if self.state == "playing":
            self.state = "paused"

    def resume(self):
        if self.state == "paused":
            self.state = "playing"

    def toggle_pause(self):
        if self.state == "playing":
            self.state = "paused"
        elif self.state == "paused":
            self.state = "playing"

    def set_state(self, name):
        self.state = name

    def say(self, text, mood="normal"):
        self.msg = text
        self.msg_t = 4.0
        self.msg_color = {"good": "#b6ffb0", "bad": "#ffb3b3"}.get(mood, "#ffe9c7")

    def finish(self, outcome):
        """The run is over. Ask for a name first if there is a score to save."""
        self.end_outcome = outcome
        self.snd.play("win" if outcome == "complete" else "lose")
        if self.score > 0:
            self.name_buf = self.last_name
            self.state = "entername"
        else:
            self.end_top = self.scores.top(5)
            self.state = outcome

    def open_scores(self):
        self.score_rows = self.scores.top(10)
        self.state = "scores"

    def save_name(self):
        name = self.name_buf.strip() or "Player"
        self.last_name = name
        mode = "Career" if self.career() else "Quick"
        self.scores.add(name, self.score, mode, self.day if self.career() else 0,
                        self.settings["difficulty"], self.served)
        self.end_top = self.scores.top(5)
        self.state = self.end_outcome

    def record(self, cu, outcome, money):
        """Append one finished order to the linked-list history."""
        self.history.append({"id": cu["id"], "items": list(cu["items"]), "outcome": outcome,
                             "money": money, "vip": cu["vip"]})

    # ---- career days and the shop ----

    def end_day(self):
        earned, goal = self.day_earned, self.day_goal
        ratio = earned / float(max(1, goal))
        stars = 3 if ratio >= 1.5 else (2 if ratio >= 1.0 else (1 if ratio >= 0.7 else 0))
        met = earned >= goal
        if not met:
            self.lives -= 1
        self.last_day = {"day": self.day, "earned": earned, "goal": goal, "served": self.day_served,
                         "missed": self.day_missed, "stars": stars, "met": met}
        self.customers = []
        self.board = CustomerLine()
        self.event = None
        self.state = "daysummary"
        self.snd.play("dayend")

    def after_summary(self):
        if self.lives <= 0:
            self.finish("gameover")
        elif self.day >= CAREER_DAYS:
            self.finish("complete")
        else:
            self.state = "shop"

    def next_day(self):
        self.day += 1
        self.reset_day_state()
        self.state = "playing"
        self.say("Day %d - goal $%d. Good luck!" % (self.day, self.day_goal), "good")

    def buy(self, key):
        u = UPGRADES[key]
        level = self.upg[key]
        if level >= u["max"]:
            return
        cost = u["cost"] * (level + 1)
        if self.cash < cost:
            self.say("Not enough cash for %s!" % u["name"], "bad")
            self.snd.play("no")
            return
        self.cash -= cost
        self.upg[key] = level + 1
        self.say("Bought %s (level %d)!" % (u["name"], level + 1), "good")
        self.snd.play("buy")

    # ---- random events ----

    def update_event(self, dt):
        if self.event is not None:
            self.event["t"] -= dt
            if self.event["t"] <= 0:
                self.event = None
                self.event_timer = 35.0 + self.rng.random() * 25.0
            return
        self.event_timer -= dt
        if self.event_timer <= 0:
            kind = self.rng.choice(list(EVENTS))
            name, secs, color, message = EVENTS[kind]
            self.event = {"kind": kind, "t": secs, "dur": secs}
            self.say(message, "bad" if kind in ("flare", "oil") else "good")
            self.snd.play("event")

    # ------------------------------------------------------------------
    # update (runs only while state == "playing")
    # ------------------------------------------------------------------

    def update(self, dt):
        self.clock += dt
        self.update_event(dt)
        self.update_stations(dt)
        self.update_customers(dt)
        self.update_staff(dt)
        self.update_effects(dt)
        self.maybe_spawn(dt)
        if self.lives <= 0:
            self.finish("gameover")
        elif self.career():
            self.day_time -= dt
            if self.day_time <= 0:
                self.end_day()
        elif self.score >= self.settings["target"]:
            self.finish("complete")

    def update_stations(self, dt):
        groups = (("grill", self.grill), ("toaster", self.toaster),
                  ("fryer", self.fryer), ("drinks", self.drinks))
        for name, group in groups:
            mult = 1.0
            if name == "grill" and self.ev("flare"):
                mult = 1.8                      # flare-up: food cooks (and burns) faster
            elif name == "fryer" and self.ev("oil"):
                mult = 0.55                     # cold oil: fries cook slower
            for it in group:
                if it is not None:
                    it["t"] += dt * mult
                    if not it.get("noted") and item_stage(it)[0] == "burnt":
                        it["noted"] = True      # play the burn sound once
                        self.snd.play("burn")

    # ---- customers ----------------------------------------------------

    def free_slot(self):
        used = {cu["slot"] for cu in self.customers if cu["slot"] is not None}
        for i in range(len(self.SLOT_X)):
            if i not in used:
                return i
        return None

    def maybe_spawn(self, dt):
        self.spawn_timer -= dt
        if self.spawn_timer > 0:
            return
        slot = self.free_slot()
        if len(self.customers) >= 3 or slot is None:      # never more than 3 people
            self.spawn_timer = 0.5
            return
        self.spawn(slot)
        if self.ev("rush"):
            self.spawn_timer = 2.0 + self.rng.random() * 2.0     # rush hour: people keep coming
        else:
            self.spawn_timer = self.day_interval() + self.rng.random() * 4.0   # calm, steady arrivals

    def spawn(self, slot):
        self.spawned += 1
        vip = self.spawned > 2 and self.rng.random() < self.VIP_CHANCE
        cu = {
            "id": self.next_id, "slot": slot, "home_x": self.SLOT_X[slot],
            "x": float(self.DOOR_X), "y": float(self.LANE_BACK),
            "state": "entering", "timer": 0.0, "vip": vip, "combo": False,
            "priority": 0 if vip else 1, "look": random_look(self.rng, vip),
            "mood": "neutral", "items": [], "price": 0,
            "patience": 0.0, "max_patience": 1.0, "phase": self.rng.random() * 6.0,
            "gone": False,
        }
        self.next_id += 1
        self.customers.append(cu)

    def make_order(self):
        """Mostly one burger, sometimes a side, and sometimes a 3-item combo."""
        if self.spawned <= 1:
            return ["Classic Cheeseburger"]
        burgers = self.available_burgers()
        burger = self.rng.choices(burgers, weights=[MENU[b]["weight"] for b in burgers])[0]
        r = self.rng.random()
        if r < COMBO_CHANCE:
            return [burger, "French Fries", "Soft Drink"]
        if r < 0.55:
            return [burger]
        if r < 0.72:
            return [burger, "French Fries"]
        if r < 0.87:
            return [burger, "Soft Drink"]
        return ["French Fries", "Soft Drink"]

    def place_order(self, cu):
        cu["items"] = self.make_order()
        price = sum(MENU[i]["price"] for i in cu["items"])
        if len(cu["items"]) == 3:
            cu["combo"] = True
            price += COMBO_BONUS
        if self.ev("rush"):
            price = int(round(price * 1.25))
        patience = self.day_patience()
        if cu["vip"]:
            price = int(round(price * self.VIP_PRICE_MULT))
            patience *= self.VIP_PATIENCE_MULT
        cu["price"] = price
        cu["max_patience"] = patience
        cu["patience"] = patience
        cu["state"] = "waiting"
        self.board.enqueue(cu)
        if cu["vip"]:
            self.snd.play("vip")
            self.say("VIP order from customer #%d!" % cu["id"], "bad")
        else:
            self.say("%s from customer #%d!" % ("Combo order" if cu["combo"] else "New order", cu["id"]))

    def depth_y(self, cu):
        """Customers walk on the back lane and step forward when they reach their spot."""
        d = abs(cu["x"] - cu["home_x"])
        return self.LANE_BACK + (self.LANE_FRONT - self.LANE_BACK) * (1.0 - min(d, 50.0) / 50.0)

    def update_customers(self, dt):
        for cu in self.customers:
            st = cu["state"]
            moving = False
            if st == "entering":
                step = self.CUSTOMER_IN_SPEED * dt
                dx = cu["home_x"] - cu["x"]
                if abs(dx) <= step:
                    cu["x"] = float(cu["home_x"])
                    cu["state"] = "ordering"
                    cu["timer"] = 1.8
                else:
                    cu["x"] += step if dx > 0 else -step
                    moving = True
                cu["y"] = self.depth_y(cu)
            elif st == "ordering":
                cu["timer"] -= dt
                if cu["timer"] <= 0:
                    self.place_order(cu)
            elif st == "waiting":
                cu["patience"] -= dt
                ratio = cu["patience"] / cu["max_patience"]
                cu["mood"] = "worried" if ratio < 0.35 else "neutral"
                if cu["patience"] <= 0:
                    self.customer_angry(cu)
            elif st == "happy":
                cu["timer"] -= dt
                if cu["timer"] <= 0:
                    cu["state"] = "leaving"
                    cu["slot"] = None
            elif st in ("leaving", "angry"):
                speed = 170.0 if st == "angry" else 125.0
                cu["x"] -= speed * dt
                cu["y"] = self.depth_y(cu)
                moving = True
                if cu["x"] <= self.DOOR_X:
                    cu["gone"] = True
            if moving:
                cu["phase"] += dt * 11.0
        self.customers = [cu for cu in self.customers if not cu["gone"]]

    def customer_angry(self, cu):
        cu["state"] = "angry"
        cu["mood"] = "angry"
        cu["slot"] = None
        self.board.remove(cu)
        self.lives -= 1
        self.missed += 1
        self.day_missed += 1
        self.record(cu, "lost", 0)
        self.snd.play("angry")
        self.say("Customer #%d left angry! Life lost." % cu["id"], "bad")

    # ---- waiter -------------------------------------------------------

    def shelf_pos(self, i):
        return (436 + i * 49 + 23, 515)          # READY TO SERVE shelf (6 slots)

    def rack_pos(self, i):
        return (436 + i * 49 + 23, 570)          # WARMING RACK (6 slots)

    def try_serve(self, cu):
        if self.state != "playing" or cu["state"] != "waiting":   # no serving while paused / twice
            return
        have = list(self.shelf)
        missing = []
        for it in cu["items"]:
            if it in have:
                have.remove(it)
            else:
                missing.append(it)
        if missing:
            self.say("Order #%d needs: %s" % (cu["id"], ", ".join(missing)), "bad")
            return
        sh = list(self.shelf)
        positions = []
        for it in cu["items"]:
            i = sh.index(it)
            positions.append(self.shelf_pos(i))
            sh[i] = None
        self.shelf = [x for x in sh if x is not None]
        cu["state"] = "delivering"
        self.jobs.enqueue({"cust": cu, "items": list(cu["items"]), "from": positions})
        self.say("Waiter is taking order #%d to the customer." % cu["id"])

    def update_staff(self, dt):
        st = self.staff
        st["walking"] = False
        if st["state"] == "idle":
            job = self.jobs.dequeue()
            if job:
                st["job"] = job
                st["state"] = "collect"
                st["t"] = 0.0
                for name, pos in zip(job["items"], job["from"]):
                    self.flyers.append({"name": name, "from": pos, "t": 0.0, "dur": 0.6})
        elif st["state"] == "collect":
            st["t"] += dt
            if st["t"] >= 0.6:
                st["items"] = list(st["job"]["items"])
                st["state"] = "walk"
        elif st["state"] == "walk":
            target = st["job"]["cust"]["home_x"]
            if self.move_staff(target, dt):
                st["state"] = "hand"
                st["t"] = 0.0
        elif st["state"] == "hand":
            st["t"] += dt
            if st["t"] >= 0.8:
                self.complete_order(st["job"])
                st["items"] = None
                st["job"] = None
                st["state"] = "return"
        elif st["state"] == "return":
            if self.move_staff(self.WAITER_HOME, dt):
                st["state"] = "idle"

    def move_staff(self, target, dt):
        st = self.staff
        step = self.WAITER_SPEED * (1.0 + 0.25 * self.upg["waiter"]) * dt
        dx = target - st["x"]
        if abs(dx) <= step:
            st["x"] = float(target)
            return True
        st["x"] += step if dx > 0 else -step
        st["walking"] = True
        st["phase"] += dt * 12.0
        return False

    def complete_order(self, job):
        cu = job["cust"]
        ratio = max(0.0, cu["patience"] / cu["max_patience"])
        rate = self.TIP_RATE * (1.0 + 0.5 * self.upg["tips"])
        if self.ev("happy"):
            rate *= 2.0                                   # happy hour: double tips
        tip = int(round(cu["price"] * rate * ratio))
        gain = cu["price"] + tip
        self.score += gain
        self.cash += gain
        self.day_earned += gain
        self.served += 1
        self.day_served += 1
        self.record(cu, "served", gain)
        self.snd.play("serve")
        self.board.remove(cu)
        cu["state"] = "happy"
        cu["mood"] = "happy"
        cu["timer"] = 1.4
        self.popups.append({"x": cu["x"], "y": 120.0, "text": "+$%d" % gain, "t": 0.0})
        self.say("Order #%d served!  +$%d (tip $%d)" % (cu["id"], gain, tip), "good")

    def update_effects(self, dt):
        for f in self.flyers:
            f["t"] += dt
        self.flyers = [f for f in self.flyers if f["t"] < f["dur"]]
        for p in self.popups:
            p["t"] += dt
            p["y"] -= 28.0 * dt
        self.popups = [p for p in self.popups if p["t"] < 1.3]

    # ---- kitchen actions ----------------------------------------------

    def use_bin(self, kind):
        if self.state != "playing":
            return
        if kind in ("Beef", "Chicken"):
            self.place_on(self.grill, kind, "The grill is full!")
        elif kind == "Bun":
            self.place_on(self.toaster, "Bun", "The toaster is full!")
        elif kind == "Fries":
            self.place_on(self.fryer, "Fries", "The fryer is full!")
        elif kind == "Drink":
            self.place_on(self.drinks, "Drink", "Both cups are already filling!")
        else:
            if self.plate.size() >= self.PLATE_MAX:
                self.say("The plate is full! Wrap, undo or discard.", "bad")
            else:
                self.flush_redo()
                self.plate.push(kind)
                self.snd.play("place")
                self.say("Added %s to the burger." % kind.lower())

    def place_on(self, slots, kind, full_msg):
        for i, s in enumerate(slots):
            if s is None:
                spec = COOK[kind]
                safe = 1.0 + 0.25 * self.upg["safety"]
                slots[i] = {"kind": kind, "t": 0.0,
                            "time": spec["time"] / self.speed_for(kind),     # Hot Grill / Turbo Kitchen
                            "burn": spec["burn"] * safe if spec["burn"] else None}   # Fire Guard
                self.snd.play("place")
                self.say({"Beef": "Beef patty is on the grill.", "Chicken": "Chicken is on the grill.",
                          "Bun": "Bun is in the toaster.", "Fries": "Fries are in the fryer.",
                          "Drink": "Cup is filling up."}[kind])
                return
        self.say(full_msg, "bad")

    def use_slot(self, slots, i):
        if self.state != "playing":
            return
        it = slots[i]
        if it is None:
            self.say("Empty. Pick food from the bins below.")
            return
        stage, p = item_stage(it)
        if stage == "cooking":
            left = int(math.ceil(it.get("time", COOK[it["kind"]]["time"]) - it["t"]))
            self.say("Still cooking... %d s left." % left)
            return
        if stage == "burnt":
            slots[i] = None
            self.say("Burnt! It went in the bin.", "bad")
            return
        kind = it["kind"]
        if kind in ("Beef", "Chicken", "Bun"):
            if len(self.rack) >= self.RACK_MAX:
                self.say("The warming rack is full!", "bad")
                return
            name = {"Beef": "Patty", "Chicken": "Chicken", "Bun": "Bun"}[kind]
            self.rack.append(name)
            slots[i] = None
            self.snd.play("ready")
            self.say("%s is on the warming rack. It stays safe." % name, "good")
        else:
            dish = "French Fries" if kind == "Fries" else "Soft Drink"
            if len(self.shelf) >= self.SHELF_MAX:
                self.say("The serving shelf is full!", "bad")
                return
            self.shelf.append(dish)
            slots[i] = None
            self.snd.play("ready")
            self.say("%s is ready on the shelf." % dish, "good")

    def use_rack(self, i):
        """Move a cooked item from the warming rack onto the burger plate (stack push)."""
        if self.state != "playing" or i >= len(self.rack):
            return
        if self.plate.size() >= self.PLATE_MAX:
            self.say("The plate is full! Wrap, undo or trash.", "bad")
            return
        name = self.rack.pop(i)
        self.flush_redo()
        self.plate.push(name)
        self.snd.play("place")
        if name == "Bun":
            self.say("Bun on plate. Its top half joins on WRAP.")
        else:
            self.say("%s added to the burger." % name)

    def wrap_burger(self):
        if self.state != "playing":
            return
        layers = self.plate.to_list()
        if not layers:
            self.say("The plate is empty.")
            return
        name = RECIPES.get(tuple(layers))
        if name is None or name not in self.available_dishes():
            self.say("That is not on the menu! Undo or discard.", "bad")
        elif len(self.shelf) >= self.SHELF_MAX:
            self.say("The serving shelf is full!", "bad")
        else:
            self.shelf.append(name)
            self.plate.clear()
            self.flush_redo()
            self.snd.play("wrap")
            self.say("%s is ready on the shelf." % name, "good")

    def undo_plate(self):
        """UNDO = pop the plate stack and push that item onto the redo stack."""
        if self.state != "playing":
            return
        removed = self.plate.pop()
        if removed is None:
            self.say("Nothing to undo.")
            return
        self.redo.push(removed)
        self.snd.play("place")
        self.say("Set aside %s. Press REDO to put it back." % removed.lower())

    def redo_plate(self):
        """REDO = pop the redo stack and push that item back onto the plate."""
        if self.state != "playing":
            return
        if self.redo.is_empty():
            self.say("Nothing to redo.")
        elif self.plate.size() >= self.PLATE_MAX:
            self.say("The plate is full!", "bad")
        else:
            item = self.redo.pop()
            self.plate.push(item)
            self.snd.play("place")
            self.say("Put %s back on the burger." % item.lower())

    def flush_redo(self):
        """
        A new plate action makes the redo history stale. Cooked food that was
        set aside goes back to the warming rack so it is never lost.
        """
        while not self.redo.is_empty():
            item = self.redo.pop()
            if item in ("Patty", "Chicken", "Bun") and len(self.rack) < self.RACK_MAX:
                self.rack.append(item)

    def discard_plate(self):
        if self.state != "playing":
            return
        self.plate.clear()
        self.flush_redo()
        self.say("Plate cleared.")

    # ------------------------------------------------------------------
    # drawing: things that never change (drawn once)
    # ------------------------------------------------------------------

    def draw_static(self):
        c = self.canvas
        t = "static"
        W = self.PLAY_W

        # ---- HUD bar
        c.create_rectangle(0, 0, self.W, 34, fill="#b8322a", outline="", tags=t)
        c.create_rectangle(0, 32, self.W, 34, fill="#7a1f16", outline="", tags=t)

        # ---- dining room
        c.create_rectangle(0, 34, W, 120, fill="#f6e3c4", outline="", tags=t)
        c.create_rectangle(0, 100, W, 120, fill="#c0392b", outline="", tags=t)
        c.create_rectangle(0, 98, W, 101, fill="#7a1f16", outline="", tags=t)
        c.create_rectangle(0, 120, W, 190, fill="#caa472", outline="", tags=t)
        for x in range(0, W, 74):
            c.create_line(x, 120, x, 190, fill="#b8915c", tags=t)
        for y in (140, 160):
            c.create_line(0, y, W, y, fill="#bb9660", tags=t)
        # door
        c.create_rectangle(6, 48, 70, 190, fill="#6b4423", outline="#3e2810", width=2, tags=t)
        c.create_rectangle(12, 54, 64, 170, fill="#bfe3f2", outline="#3e2810", width=2, tags=t)
        c.create_line(38, 54, 38, 170, fill="#3e2810", width=2, tags=t)
        c.create_oval(48, 114, 56, 122, fill="#d4af37", outline="#8a6d1a", tags=t)
        c.create_rectangle(16, 176, 60, 188, fill="#ffffff", outline="#3e2810", tags=t)
        c.create_text(38, 182, text="OPEN", font=F(9, True), fill="#c0392b", tags=t)
        # window + pictures
        c.create_rectangle(100, 50, 190, 96, fill="#bfe3f2", outline="#6b4423", width=3, tags=t)
        c.create_line(145, 50, 145, 96, fill="#6b4423", width=2, tags=t)
        c.create_rectangle(650, 46, 730, 92, fill="#fff8e1", outline="#6b4423", width=3, tags=t)
        draw_item_icon(c, "Classic Cheeseburger", 690, 69, 0.8, t)
        # plant
        c.create_rectangle(704, 164, 726, 190, fill="#a0522d", outline="#5a2e12", tags=t)
        for dx, dy in ((-10, -18), (0, -28), (10, -18), (-4, -10), (6, -10)):
            c.create_oval(715 + dx - 8, 160 + dy - 12, 715 + dx + 8, 160 + dy + 12,
                          fill="#3f9b4a", outline="#1f6a2a", tags=t)

        # ---- serving counter
        c.create_rectangle(0, 190, W, 203, fill="#e3c08d", outline="#8b5a2b", tags=t)
        c.create_rectangle(0, 203, W, 216, fill="#8b5a2b", outline="#5c3a15", tags=t)
        c.create_text(480, 210, text="SERVING COUNTER", font=F(8, True),
                      fill="#f6e3c4", tags=t)

        # ---- kitchen walkway floor + wall
        for r in range(3):
            for col in range(21):
                shade = "#e9eef1" if (r + col) % 2 == 0 else "#dde6ea"
                c.create_rectangle(col * 37, 216 + r * 33, col * 37 + 37, 249 + r * 33,
                                   fill=shade, outline="#c5d6de", tags=t)
        c.create_rectangle(0, 316, W, 422, fill="#eef3f5", outline="", tags=t)
        for y in range(326, 422, 20):
            c.create_line(0, y, W, y, fill="#d5e0e5", tags=t)

        # ---- grill
        c.create_rectangle(14, 322, 254, 414, fill="#3b3f45", outline="#1c1e21", width=2, tags=t)
        c.create_rectangle(14, 318, 254, 336, fill="#8e979f", outline="#1c1e21", width=2, tags=t)
        c.create_text(134, 327, text="GRILL", font=F(10, True), fill="#1c1e21", tags=t)
        for x in range(24, 250, 10):
            c.create_line(x, 342, x, 408, fill="#2a2d31", tags=t)
        # ---- toaster
        c.create_rectangle(270, 322, 390, 414, fill="#b8c4cc", outline="#5d6a73", width=2, tags=t)
        c.create_rectangle(270, 318, 390, 336, fill="#dfe6ea", outline="#5d6a73", width=2, tags=t)
        c.create_text(330, 327, text="BUN TOASTER", font=F(10, True), fill="#3b4750", tags=t)
        for cx, cy in self.TOASTER_SLOTS:
            c.create_rectangle(cx - 19, cy - 28, cx + 19, cy + 24, fill="#2f3a40",
                               outline="#1c262b", width=2, tags=t)
        c.create_rectangle(392, 346, 400, 384, fill="#555555", outline="#222222", tags=t)
        # ---- fryer
        c.create_rectangle(408, 322, 546, 414, fill="#9aa5ad", outline="#5d6a73", width=2, tags=t)
        c.create_rectangle(408, 318, 546, 336, fill="#c6ced4", outline="#5d6a73", width=2, tags=t)
        c.create_text(477, 327, text="FRYER", font=F(10, True), fill="#3b4750", tags=t)
        for cx, cy in self.FRYER_SLOTS:
            c.create_rectangle(cx - 27, cy - 26, cx + 27, cy + 22, fill="#d9a920",
                               outline="#6b5200", width=2, tags=t)
        # ---- drinks
        c.create_rectangle(556, 322, 724, 414, fill="#c0392b", outline="#7a1f16", width=2, tags=t)
        c.create_rectangle(556, 318, 724, 336, fill="#8e1f14", outline="#7a1f16", width=2, tags=t)
        c.create_text(640, 327, text="DRINK DISPENSER", font=F(10, True), fill="#ffe9c7", tags=t)
        for cx, cy in self.DRINK_SLOTS:
            c.create_rectangle(cx - 8, 338, cx + 8, 350, fill="#9aa5ad", outline="#444444", tags=t)
            c.create_rectangle(cx - 30, 402, cx + 30, 412, fill="#3a3a3a", outline="", tags=t)
        c.create_rectangle(566, 340, 584, 396, fill="#fff4df", outline="#7a1f16", tags=t)
        c.create_text(575, 368, text="SODA", font=F(8, True), fill="#c0392b", angle=90, tags=t)

        # ---- prep counter + bins
        c.create_rectangle(0, 420, W, 476, fill="#b88652", outline="#6b4423", width=2, tags=t)
        c.create_rectangle(0, 420, W, 426, fill="#d4a76e", outline="", tags=t)
        c.create_text(238, 447, text="PREP COUNTER", font=F(10, True), fill="#f6e3c4", tags=t)

        # ---- assembly counter
        c.create_rectangle(0, 478, 424, self.H, fill="#8b5a2b", outline="#5c3a15", width=2, tags=t)
        c.create_rectangle(0, 478, 424, 484, fill="#b07a3f", outline="", tags=t)
        c.create_text(14, 490, anchor="w", text="ASSEMBLY COUNTER", font=F(9, True),
                      fill="#f6e3c4", tags=t)
        c.create_oval(276, 580, 404, 598, fill="#ffffff", outline="#999999", width=2, tags=t)
        c.create_oval(290, 583, 390, 594, fill="#eeeeee", outline="", tags=t)

        # bins
        for kind, x1, y1, x2, y2, label in self.BINS:
            self.draw_bin(kind, x1, y1, x2, y2, label)

        # ---- serving shelf (top) and warming rack (bottom)
        c.create_rectangle(430, 478, W, 538, fill="#cfd6db", outline="#6b747b", width=2, tags=t)
        c.create_text(440, 487, anchor="w", text="READY TO SERVE (serving shelf)", font=F(9, True),
                      fill="#3b4750", tags=t)
        c.create_rectangle(430, 538, W, self.H - 2, fill="#e9d8b6", outline="#8a6d3b", width=2, tags=t)
        c.create_text(440, 545, anchor="w", text="WARMING RACK (cooked food waits here)",
                      font=F(9, True), fill="#6b4a1e", tags=t)
        for i in range(self.SHELF_MAX):
            sx, sy = self.shelf_pos(i)
            c.create_rectangle(sx - 23, sy - 19, sx + 23, sy + 19, fill="#eef2f4",
                               outline="#9aa5ad", tags=t)
        for i in range(self.RACK_MAX):
            sx, sy = self.rack_pos(i)
            c.create_rectangle(sx - 23, sy - 17, sx + 23, sy + 17, fill="#fbf3e0",
                               outline="#a58a55", tags=t)

        # ---- right panel: the menu, written clearly
        c.create_rectangle(W, 34, self.W, self.H, fill="#2d1e1a", outline="", tags=t)
        c.create_rectangle(W, 34, self.W, 56, fill="#b8322a", outline="", tags=t)
        c.create_text(W + 110, 45, text="MENU (build bottom to top)", font=F(12, True),
                      fill="#fff4df", tags=t)
        self.draw_menu_panel()
        c.create_rectangle(W, 322, self.W, 344, fill="#2a9d8f", outline="", tags=t)
        c.create_text(W + 110, 333, text="ORDERS (VIPs jump the queue)", font=F(11, True),
                      fill="#ffffff", tags=t)

    def draw_menu_panel(self):
        """The MENU list on the right. Redrawn when new dishes unlock (career days 2, 4, 6)."""
        c = self.canvas
        t = "menupanel"
        W = self.PLAY_W
        dishes = self.available_dishes()
        self._menu_shown = tuple(dishes)
        n = len(dishes)
        rowh = min(52, int(260 / n))
        compact = rowh < 48
        y = 58
        for name in dishes:
            spec = MENU[name]
            c.create_rectangle(W + 6, y, self.W - 6, y + rowh - 2, fill="#fff4df", outline="#a0792c", tags=t)
            if compact:
                draw_item_icon(c, name, W + 22, y + rowh / 2.0 - 1, 0.5, t)
                c.create_text(W + 40, y + 8, anchor="w", text=name, font=F(10, True), fill="#2d1e1a", tags=t)
                c.create_text(self.W - 12, y + 8, anchor="e", text="$%d" % spec["price"],
                              font=F(12, True), fill="#c0392b", tags=t)
                c.create_text(W + 40, y + 17, anchor="nw", text=spec["steps"], width=170,
                              font=F(8), fill="#4a3a2a", tags=t)
            else:
                draw_item_icon(c, name, W + 28, y + rowh / 2.0 - 1, 0.8, t)
                c.create_text(W + 50, y + 11, anchor="w", text=name, font=F(11, True), fill="#2d1e1a", tags=t)
                c.create_text(self.W - 12, y + 11, anchor="e", text="$%d" % spec["price"],
                              font=F(13, True), fill="#c0392b", tags=t)
                c.create_text(W + 50, y + 22, anchor="nw", text=spec["steps"], width=160,
                              font=F(10), fill="#4a3a2a", tags=t)
            y += rowh
        if c.find_withtag("menubg"):                 # keep the menu list underneath the start-menu picture
            c.tag_lower("menupanel", "menubg")

    def sync_menu_panel(self):
        if tuple(self.available_dishes()) != self._menu_shown:
            self.canvas.delete("menupanel")
            self.draw_menu_panel()

    def draw_bin(self, kind, x1, y1, x2, y2, label):
        c = self.canvas
        t = "static"
        c.create_rectangle(x1, y1, x2, y2, fill="#f7f3ea", outline="#5c3a15", width=2, tags=t)
        cx = (x1 + x2) / 2.0
        cy = y1 + (y2 - y1) * 0.38
        if kind == "Beef":
            c.create_oval(cx - 20, cy - 4, cx + 20, cy + 10, fill="#d97a8c", outline="#8a3a4a", tags=t)
            c.create_oval(cx - 18, cy - 10, cx + 18, cy + 4, fill="#e58a9a", outline="#8a3a4a", tags=t)
        elif kind == "Chicken":
            c.create_oval(cx - 20, cy - 8, cx + 20, cy + 8, fill="#f2c9a0", outline="#a8661a", tags=t)
            for dx in (-10, 0, 10):
                c.create_oval(cx + dx - 2, cy - 2, cx + dx + 2, cy + 2, fill="#e0a060", outline="", tags=t)
        elif kind == "Bun":
            draw_burger(c, cx, cy + 10, 38, ["Bun", "TopBun"], 10, t)
        elif kind == "Fries":
            draw_item_icon(c, "French Fries", cx, cy, 0.7, t)
        elif kind == "Drink":
            draw_item_icon(c, "Soft Drink", cx, cy, 0.7, t)
        elif kind == "Cheese":
            draw_layer(c, "Cheese", cx - 22, cy + 8, 44, 16, t)
        elif kind == "Lettuce":
            draw_layer(c, "Lettuce", cx - 22, cy + 8, 44, 16, t)
        elif kind == "Tomato":
            c.create_oval(cx - 20, cy - 5, cx - 2, cy + 9, fill="#e0453a", outline="#a02020", tags=t)
            c.create_oval(cx + 2, cy - 5, cx + 20, cy + 9, fill="#e0453a", outline="#a02020", tags=t)
        c.create_text(cx, y2 - 8, text=label, font=F(9, True), fill="#3b2a1a", tags=t)

    def draw_menu_static(self):
        """Start-menu background (hidden while playing)."""
        c = self.canvas
        t = "menubg"
        c.create_rectangle(0, 0, self.W, self.H, fill="#fff0d2", outline="", tags=t)
        for i in range(16):
            x = i * 60
            col = "#c0392b" if i % 2 == 0 else "#ffffff"
            c.create_polygon([(x, 0), (x + 60, 0), (x + 60, 70), (x + 30, 88), (x, 70)],
                             fill=col, outline="#8e1f14", tags=t)
        for r in range(5):
            for col in range(24):
                shade = "#f4d9a6" if (r + col) % 2 == 0 else "#e8c487"
                c.create_rectangle(col * 40, 400 + r * 40, col * 40 + 40, 440 + r * 40,
                                   fill=shade, outline="", tags=t)
        c.create_rectangle(0, 396, self.W, 404, fill="#8b5a2b", outline="", tags=t)
        c.create_text(484, 144, text="BURGER RUSH", font=F(66, True), fill="#7a1f16", tags=t)
        c.create_text(480, 140, text="BURGER RUSH", font=F(66, True), fill="#ffb703", tags=t)
        c.create_text(480, 196, text="The fast-food restaurant game", font=F(18, True),
                      fill="#5c3a15", tags=t)
        draw_burger(c, 150, 380, 170, ["Bun", "Patty", "Cheese", "Lettuce", "Tomato", "Patty",
                                       "Cheese", "TopBun"], 24, t)
        draw_item_icon(c, "French Fries", 800, 330, 3.2, t)
        draw_item_icon(c, "Soft Drink", 880, 340, 3.2, t)
        c.create_text(480, 580, text="Stack  |  Queue  |  Priority Queue  |  Linked List  |  Hash Map",
                      font=F(13, True), fill="#7a1f16", tags=t)

    # ------------------------------------------------------------------
    # drawing: things that change every frame
    # ------------------------------------------------------------------

    def button(self, x1, y1, x2, y2, text, color, action, size=14, fg="#ffffff"):
        c = self.canvas
        mx, my = self.mouse
        hover = x1 <= mx <= x2 and y1 <= my <= y2
        fill = mix(color, "#ffffff", 0.22) if hover else color
        c.create_rectangle(x1 + 3, y1 + 3, x2 + 3, y2 + 3, fill="#000000", outline="",
                           stipple="gray50", tags="dyn")
        c.create_rectangle(x1, y1, x2, y2, fill=fill, outline="#2b2b2b", width=2, tags="dyn")
        c.create_text((x1 + x2) / 2.0, (y1 + y2) / 2.0, text=text, font=F(size, True),
                      fill=fg, tags="dyn")
        self.hits.append((x1, y1, x2, y2, action, False))

    def render(self):
        c = self.canvas
        c.delete("dyn")
        self.hits = []
        if self.flash_t > 0:
            self.flash_t -= self.dt

        show_menu = self.state in ("menu", "howto", "settings", "scores")
        if show_menu != self.menu_visible:
            c.itemconfigure("menubg", state="normal" if show_menu else "hidden")
            self.menu_visible = show_menu
        if not show_menu:
            self.sync_menu_panel()

        if self.state == "menu":
            self.render_menu()
        elif self.state == "howto":
            self.render_howto()
        elif self.state == "settings":
            self.render_settings()
        elif self.state == "scores":
            self.render_scores()
        else:
            self.render_game(self.state == "playing")
            if self.state == "paused":
                self.render_pause()
            elif self.state == "daysummary":
                self.render_summary()
            elif self.state == "shop":
                self.render_shop()
            elif self.state == "entername":
                self.render_entername()
            elif self.state in ("gameover", "complete"):
                self.render_end()

        # hover glow + click flash + mouse cursor
        mx, my = self.mouse
        hand = False
        for x1, y1, x2, y2, action, glow in reversed(self.hits):
            if x1 <= mx <= x2 and y1 <= my <= y2:
                hand = True
                if glow:
                    c.create_rectangle(x1, y1, x2, y2, outline="#ffe066", width=3, tags="dyn")
                break
        if self.flash and self.flash_t > 0:
            x1, y1, x2, y2 = self.flash
            c.create_rectangle(x1, y1, x2, y2, outline="#ffffff", width=3, tags="dyn")
        want = "hand2" if hand else ""
        if want != self.cursor:
            c.config(cursor=want)
            self.cursor = want

    # ---------------- menu screens ----------------

    def render_menu(self):
        c = self.canvas
        bx1, bx2 = 350, 610
        self.button(bx1, 224, bx2, 276, "START GAME", "#2e9e4f", self.start_game, 22)
        self.button(bx1, 288, bx2, 328, "HOW TO PLAY", "#2a78c4", lambda: self.set_state("howto"), 16)
        self.button(bx1, 338, bx2, 378, "HIGH SCORES", "#d99a1e", self.open_scores, 16)
        self.button(bx1, 388, bx2, 428, "SETTINGS", "#8e5bb5", lambda: self.set_state("settings"), 16)
        self.button(bx1, 438, bx2, 478, "QUIT", "#b8322a", self.close, 16)
        mode = "Career (7 days)" if self.career() else "Quick goal"
        c.create_text(480, 506, text="Mode: %s    Difficulty: %s" % (mode, self.settings["difficulty"]),
                      font=F(13, True), fill="#5c3a15", tags="dyn")
        best = self.scores.best()
        if best:
            c.create_text(480, 530, text="Best score: $%d" % best, font=F(15, True), fill="#7a1f16", tags="dyn")

    def panel(self, x1, y1, x2, y2, title):
        c = self.canvas
        c.create_rectangle(x1 + 5, y1 + 5, x2 + 5, y2 + 5, fill="#000000", outline="",
                           stipple="gray50", tags="dyn")
        c.create_rectangle(x1, y1, x2, y2, fill="#fff8e1", outline="#7a1f16", width=4, tags="dyn")
        c.create_rectangle(x1, y1, x2, y1 + 46, fill="#b8322a", outline="#7a1f16", width=4, tags="dyn")
        c.create_text((x1 + x2) / 2.0, y1 + 24, text=title, font=F(24, True), fill="#fff8e1", tags="dyn")

    def render_howto(self):
        c = self.canvas
        self.panel(60, 90, 900, 565, "HOW TO PLAY")
        lines = [
            "1.  Up to 3 customers wait at the counter. The MENU on the right lists every dish.",
            "2.  Click RAW BEEF / CHICKEN / BUNS / POTATOES / CUPS to cook. Click food when it says READY.",
            "3.  Cooked patties and buns wait on the WARMING RACK. Click them in menu order (Bun first).",
            "4.  UNDO takes the top item off the plate (a Stack pop), REDO puts it back. TRASH clears it.",
            "5.  WRAP sends the burger to the SERVING SHELF. Fries and drinks go there by themselves.",
            "6.  Click an order card to serve it. Combos (burger + fries + drink) pay a bonus.",
            "7.  Gold VIPs pay more, wait less, and jump to the top of the order board (Priority Queue).",
            "8.  Random events (Rush Hour, Happy Hour, Grill Flare-up, Cold Oil) change the rules for a while.",
            "9.  CAREER: 7 days of 100 seconds. Reach each day's money goal or lose a life.",
            "10. Spend cash in the UPGRADE SHOP between days. New dishes arrive on days 2, 4 and 6.",
            "11. QUICK mode: reach the target money before you lose 3 lives.",
            "12. Keys: Esc or P = pause,  M = sound on / off.",
            "Data structures: Stack, Queue, Priority Queue, Linked List (order history), Hash Map.",
        ]
        y = 160
        for i, line in enumerate(lines):
            last = i == len(lines) - 1
            c.create_text(90, y, anchor="w", text=line, font=F(13, True),
                          fill="#7a1f16" if last else "#2d1e1a", tags="dyn")
            y += 28
        self.button(390, 520, 570, 556, "BACK", "#b8322a", lambda: self.set_state("menu"), 16)

    def render_settings(self):
        c = self.canvas
        d = "dyn"
        self.panel(210, 110, 750, 540, "SETTINGS")
        c.create_text(480, 184, text="Difficulty", font=F(15, True), fill="#2d1e1a", tags=d)
        for i, name in enumerate(DIFFICULTY):
            x1 = 240 + i * 170
            on = self.settings["difficulty"] == name
            label = "%s  %ds" % (name, DIFFICULTY[name]["patience"])
            self.button(x1, 198, x1 + 150, 238, label, "#2e9e4f" if on else "#8a8a8a",
                        lambda n=name: self.settings.__setitem__("difficulty", n), 14)
        c.create_text(480, 262, text="Game mode", font=F(15, True), fill="#2d1e1a", tags=d)
        for i, (key, label) in enumerate((("career", "CAREER (7 days)"), ("quick", "QUICK GOAL"))):
            x1 = 240 + i * 260
            on = self.settings["mode"] == key
            self.button(x1, 276, x1 + 230, 316, label, "#2e9e4f" if on else "#8a8a8a",
                        lambda k=key: self.settings.__setitem__("mode", k), 14)
        c.create_text(480, 338, text="Target money (Quick mode only)", font=F(15, True),
                      fill="#2d1e1a" if not self.career() else "#9a8a7a", tags=d)
        for i, tg in enumerate(TARGETS):
            x1 = 240 + i * 170
            on = self.settings["target"] == tg
            col = "#2e9e4f" if on else "#8a8a8a"
            if self.career():
                col = "#b8a88a" if on else "#cfc4b0"
            self.button(x1, 352, x1 + 150, 392, "$%d" % tg, col,
                        lambda v=tg: self.settings.__setitem__("target", v), 15)
        if self.snd.available:
            label = "Sound: ON" if self.snd.enabled else "Sound: OFF"
            self.button(360, 410, 600, 450, label, "#2a78c4" if self.snd.enabled else "#8a8a8a",
                        self.toggle_sound, 14)
        else:
            c.create_text(480, 430, text="Sound is only available on Windows (the game stays silent here).",
                          font=F(12, True), fill="#7a1f16", tags=d)
        self.button(390, 466, 570, 510, "BACK", "#b8322a", lambda: self.set_state("menu"), 16)

    def dim(self):
        self.canvas.create_rectangle(0, 0, self.W, self.H, fill="#000000", stipple="gray50",
                                     outline="", tags="dyn")

    def render_pause(self):
        self.dim()
        self.panel(330, 130, 630, 450, "PAUSED")
        self.button(370, 195, 590, 243, "RESUME", "#2e9e4f", self.resume, 18)
        self.button(370, 255, 590, 303, "RESTART", "#2a78c4", self.start_game, 18)
        self.button(370, 315, 590, 363, "MAIN MENU", "#b8322a", self.go_menu, 18)
        if self.snd.available:
            label = "Sound: ON" if self.snd.enabled else "Sound: OFF"
            self.button(370, 375, 590, 415, label, "#8e5bb5", self.toggle_sound, 14)

    def render_summary(self):
        c = self.canvas
        d = "dyn"
        s = self.last_day
        self.dim()
        title = ("DAY %d COMPLETE!" if s["met"] else "DAY %d: GOAL MISSED") % s["day"]
        self.panel(250, 70, 710, 540, title)
        stars = "\u2605" * s["stars"] + "\u2606" * (3 - s["stars"])
        c.create_text(480, 138, text=stars, font=F(44, True), fill="#e0a800", tags=d)
        rows = [("Earned today", "$%d  /  goal $%d" % (s["earned"], s["goal"])),
                ("Customers served", str(s["served"])),
                ("Orders lost", str(s["missed"])),
                ("Cash in your pocket", "$%d" % self.cash)]
        y = 205
        for label, value in rows:
            c.create_text(285, y, anchor="w", text=label, font=F(16), fill="#2d1e1a", tags=d)
            c.create_text(675, y, anchor="e", text=value, font=F(17, True),
                          fill="#1b7a2e" if (label == "Earned today" and s["met"]) else "#c0392b", tags=d)
            y += 40
        if s["met"]:
            msg = "Great job! The goal was reached."
            col = "#1b7a2e"
        else:
            msg = "Goal missed: you lose a life (%d left)." % max(0, self.lives)
            col = "#c0392b"
        c.create_text(480, 392, text=msg, font=F(15, True), fill=col, tags=d)
        for i in range(self.START_LIVES):
            c.create_text(430 + i * 36, 428, text="\u2665", font=F(28, True),
                          fill="#e0453a" if i < self.lives else "#c9b9a8", tags=d)
        if self.lives <= 0:
            label = "CONTINUE"
        elif self.day >= CAREER_DAYS:
            label = "FINISH THE WEEK"
        else:
            label = "OPEN THE SHOP"
        self.button(310, 468, 650, 516, label, "#2e9e4f", self.after_summary, 18)

    def render_shop(self):
        c = self.canvas
        d = "dyn"
        self.dim()
        self.panel(110, 40, 850, 560, "UPGRADE SHOP")
        c.create_text(480, 108, text="Cash: $%d      Next: Day %d  (goal $%d)" % (
            self.cash, self.day + 1, self.goal_for_next_day()),
            font=F(16, True), fill="#7a1f16", tags=d)
        y = 126
        for key, u in UPGRADES.items():
            lvl = self.upg[key]
            c.create_rectangle(130, y, 830, y + 50, fill="#fff4df", outline="#a0792c", width=2, tags=d)
            c.create_text(146, y + 15, anchor="w", text=u["name"], font=F(15, True), fill="#2d1e1a", tags=d)
            c.create_text(146, y + 35, anchor="w", text=u["desc"], font=F(11), fill="#4a3a2a", tags=d)
            for k in range(u["max"]):                       # level pips
                c.create_oval(560 + k * 24, y + 17, 576 + k * 24, y + 33,
                              fill="#e0a800" if k < lvl else "#ffffff", outline="#7a5a00", width=2, tags=d)
            if lvl >= u["max"]:
                c.create_text(760, y + 25, text="MAX", font=F(15, True), fill="#1b7a2e", tags=d)
            else:
                cost = u["cost"] * (lvl + 1)
                self.button(690, y + 8, 820, y + 42, "BUY  $%d" % cost,
                            "#2e9e4f" if self.cash >= cost else "#8a8a8a",
                            lambda k=key: self.buy(k), 14)
            y += 54
        newdishes = [n for n, sp in MENU.items() if sp["day"] == self.day + 1]
        if newdishes:
            c.create_text(480, 462, text="New on the menu tomorrow: %s" % ", ".join(newdishes),
                          font=F(14, True), fill="#2a78c4", tags=d)
        if self.msg_t > 0:
            c.create_text(480, 484, text=self.msg, font=F(13, True), fill="#7a1f16", tags=d)
        self.button(310, 502, 650, 546, "START DAY %d" % (self.day + 1), "#2e9e4f", self.next_day, 18)

    def goal_for_next_day(self):
        base = DAY_GOALS[min(self.day + 1, len(DAY_GOALS)) - 1]
        return int(round(base * DIFFICULTY[self.settings["difficulty"]]["goal_mult"]))

    def render_scores(self):
        c = self.canvas
        d = "dyn"
        self.panel(90, 100, 870, 530, "HIGH SCORES")
        heads = ((130, "w", "#"), (170, "w", "NAME"), (470, "e", "SCORE"), (520, "w", "MODE"),
                 (650, "w", "LEVEL"), (750, "w", "DATE"))
        for x, anc, text in heads:
            c.create_text(x, 172, anchor=anc, text=text, font=F(12, True), fill="#7a1f16", tags=d)
        c.create_line(120, 184, 840, 184, fill="#7a1f16", tags=d)
        if not self.score_rows:
            c.create_text(480, 300, text="No scores yet. Go and play a round!", font=F(16, True),
                          fill="#5c3a15", tags=d)
        for i, (name, score, mode, day, diff, served, played) in enumerate(self.score_rows):
            y = 202 + i * 26
            col = "#b8860b" if i == 0 else "#2d1e1a"
            c.create_text(130, y, anchor="w", text=str(i + 1), font=F(14, True), fill=col, tags=d)
            c.create_text(170, y, anchor="w", text=name, font=F(14, True), fill=col, tags=d)
            c.create_text(470, y, anchor="e", text="$%d" % score, font=F(14, True), fill="#c0392b", tags=d)
            c.create_text(520, y, anchor="w", text=("Career day %d" % day) if mode == "Career" else "Quick",
                          font=F(13), fill=col, tags=d)
            c.create_text(650, y, anchor="w", text=diff, font=F(13), fill=col, tags=d)
            c.create_text(750, y, anchor="w", text=played, font=F(12), fill=col, tags=d)
        if not self.scores.db_ok:
            c.create_text(480, 470, text="(Could not write the score file: scores are kept until you close the game)",
                          font=F(11), fill="#7a1f16", tags=d)
        self.button(390, 482, 570, 520, "BACK", "#b8322a", lambda: self.set_state("menu"), 16)

    def render_entername(self):
        c = self.canvas
        d = "dyn"
        self.dim()
        self.panel(270, 130, 690, 440, "NEW SCORE!")
        c.create_text(480, 205, text="$%d" % self.score, font=F(40, True), fill="#c0392b", tags=d)
        c.create_text(480, 252, text="Type your name for the high-score table, then press Enter",
                      font=F(13, True), fill="#2d1e1a", tags=d)
        c.create_rectangle(340, 275, 620, 319, fill="#ffffff", outline="#7a1f16", width=3, tags=d)
        cursor = "_" if int(self.clock * 2 + time.perf_counter() * 2) % 2 == 0 else " "
        c.create_text(480, 297, text=self.name_buf + cursor, font=F(22, True), fill="#2d1e1a", tags=d)
        self.button(380, 345, 580, 391, "SAVE SCORE", "#2e9e4f", self.save_name, 17)

    def render_end(self):
        c = self.canvas
        d = "dyn"
        won = self.state == "complete"
        self.dim()
        if won:
            title = "WEEK COMPLETE!" if self.career() else "SHIFT COMPLETE!"
            sub = ("You survived all %d days!" % CAREER_DAYS) if self.career() else "You reached the target!"
        else:
            title = "GAME OVER"
            sub = ("Out of lives on day %d." % self.day) if self.career() else "Too many angry customers."
        self.panel(110, 40, 850, 560, title)
        c.create_text(480, 112, text=sub, font=F(15, True), fill="#7a1f16", tags=d)

        rows = [("Final score", "$%d" % self.score),
                ("Customers served", str(self.served)),
                ("Missed / failed orders", str(self.missed)),
                ("Time played", "%d:%02d" % (int(self.clock) // 60, int(self.clock) % 60))]
        if self.career():
            rows.insert(1, ("Day reached", "%d / %d" % (self.day, CAREER_DAYS)))
        y = 150
        for label, value in rows:
            c.create_text(140, y, anchor="w", text=label, font=F(15), fill="#2d1e1a", tags=d)
            c.create_text(440, y, anchor="e", text=value, font=F(16, True), fill="#c0392b", tags=d)
            y += 31

        # top 5 table (read once from SQLite when the game ended)
        c.create_text(640, 140, text="TOP 5 SCORES", font=F(13, True), fill="#7a1f16", tags=d)
        for i, row in enumerate(self.end_top):
            yy = 166 + i * 24
            c.create_text(490, yy, anchor="w", text="%d.  %s" % (i + 1, row[0]), font=F(13, True),
                          fill="#2d1e1a", tags=d)
            c.create_text(820, yy, anchor="e", text="$%d" % row[1], font=F(13, True),
                          fill="#c0392b", tags=d)

        # order history: walk the linked list from head to tail
        n_all = len(self.history)
        c.create_text(480, 318, text="ORDER HISTORY  (singly linked list, head -> tail):  %d orders, %d served, %d lost" % (
            n_all, self.history.count("served"), self.history.count("lost")),
            font=F(12, True), fill="#7a1f16", tags=d)
        nodes = self.history.last(5)
        if not nodes:
            c.create_text(480, 385, text="No orders were finished yet.", font=F(14), fill="#5c3a15", tags=d)
        else:
            bw, gap, top = 118, 26, 346
            total = len(nodes) * bw + (len(nodes) - 1) * gap
            x0 = 480 - total / 2.0
            if n_all > len(nodes):
                c.create_text(x0 - 12, top + 36, text="...", font=F(18, True), fill="#7a1f16", tags=d)
            for i, v in enumerate(nodes):
                x1 = x0 + i * (bw + gap)
                ok = v["outcome"] == "served"
                c.create_rectangle(x1, top, x1 + bw, top + 74, fill="#e4f6e4" if ok else "#fbe3e3",
                                   outline="#2e7d32" if ok else "#b03030", width=2, tags=d)
                c.create_line(x1 + 78, top, x1 + 78, top + 20, fill="#777777", tags=d)    # data | next pointer
                c.create_text(x1 + 38, top + 10, text="#%d%s" % (v["id"], " VIP" if v["vip"] else ""),
                              font=F(11, True), fill="#2d1e1a", tags=d)
                c.create_text(x1 + 98, top + 10, text="next", font=F(8), fill="#777777", tags=d)
                names = "+".join(MENU[it]["short"] for it in v["items"])
                c.create_text(x1 + bw / 2.0, top + 38, text=names, width=bw - 8, font=F(10), fill="#2d1e1a", tags=d)
                c.create_text(x1 + bw / 2.0, top + 62, text=("SERVED +$%d" % v["money"]) if ok else "LOST",
                              font=F(11, True), fill="#1b7a2e" if ok else "#b03030", tags=d)
                if i < len(nodes) - 1:
                    c.create_line(x1 + bw, top + 10, x1 + bw + gap, top + 10, arrow=tk.LAST, width=2,
                                  fill="#444444", tags=d)
            if n_all == len(nodes):
                c.create_text(x0 + 4, top - 10, anchor="w", text="HEAD", font=F(10, True), fill="#7a1f16", tags=d)
            c.create_text(x0 + total - 4, top - 10, anchor="e", text="TAIL -> None", font=F(10, True),
                          fill="#7a1f16", tags=d)

        self.button(130, 480, 360, 528, "PLAY AGAIN", "#2e9e4f", self.start_game, 17)
        self.button(375, 480, 585, 528, "HIGH SCORES", "#d99a1e", self.open_scores, 16)
        self.button(600, 480, 830, 528, "MAIN MENU", "#b8322a", self.go_menu, 16)

    # ---------------- the game scene ----------------

    def render_game(self, interactive):
        c = self.canvas
        d = "dyn"
        t = self.clock
        self.render_hud(interactive)

        # people, drawn back to front
        actors = [(cu["y"], 0, cu) for cu in self.customers]
        actors.append((self.STAFF_Y, 1, "chef"))
        actors.append((self.STAFF_Y, 2, "waiter"))
        actors.sort(key=lambda a: (a[0], a[1]))
        for fy, _, who in actors:
            if who == "chef":
                busy = any(self.grill)
                up = 0.45 + 0.3 * math.sin(t * 7.0) if busy else 0.0
                draw_person(c, self.CHEF_X, self.STAFF_Y, CHEF_LOOK,
                            {"mood": "happy", "arm_up": up}, d)
            elif who == "waiter":
                st = self.staff
                tray = list(st["items"]) if st["items"] else None
                up = 0.0
                if st["state"] == "hand":
                    up = 0.0
                draw_person(c, st["x"], self.STAFF_Y, WAITER_LOOK,
                            {"walking": st["walking"], "phase": st["phase"],
                             "mood": "neutral", "tray": tray, "arm_up": up}, d)
            else:
                cu = who
                anim = {"walking": cu["state"] in ("entering", "leaving", "angry"),
                        "phase": cu["phase"], "mood": cu["mood"]}
                if cu["state"] == "happy":
                    anim["arm_up"] = 0.75 + 0.25 * math.sin(t * 9.0)
                draw_person(c, cu["x"], cu["y"], cu["look"], anim, d)

        # waiter hands the tray over the counter
        st = self.staff
        if st["state"] == "hand" and st["job"]:
            cx = st["job"]["cust"]["home_x"]
            c.create_rectangle(cx - 34, 192, cx + 34, 199, fill="#c7ced4", outline="#6b747b", tags=d)
            for i, name in enumerate(st["job"]["items"][:4]):
                n = min(len(st["job"]["items"]), 4)
                draw_item_icon(c, name, cx + (i - (n - 1) / 2.0) * 26, 180, 0.7, d)

        for cu in self.customers:
            self.render_customer_extras(cu)

        self.render_stations()
        self.render_plate(interactive)
        self.render_shelf()
        self.render_rack(interactive)
        self.render_orders(interactive)

        # flying food from shelf to waiter, and score popups
        for f in self.flyers:
            k = min(1.0, f["t"] / f["dur"])
            x = f["from"][0] + (self.staff["x"] - f["from"][0]) * k
            y = f["from"][1] + (270 - f["from"][1]) * k
            draw_item_icon(c, f["name"], x, y, 0.7, d)
        for p in self.popups:
            c.create_text(p["x"], p["y"], text=p["text"], font=F(20, True), fill="#1b7a2e", tags=d)

        if interactive:
            for kind, x1, y1, x2, y2, label in self.BINS:
                self.hits.append((x1, y1, x2, y2, lambda k=kind: self.use_bin(k), True))
            for slots, pts in ((self.grill, self.GRILL_SLOTS), (self.toaster, self.TOASTER_SLOTS),
                               (self.fryer, self.FRYER_SLOTS), (self.drinks, self.DRINK_SLOTS)):
                for i, (cx, cy) in enumerate(pts):
                    self.hits.append((cx - 30, cy - 32, cx + 30, cy + 40,
                                      lambda s=slots, i=i: self.use_slot(s, i), True))

    def render_hud(self, interactive):
        c = self.canvas
        d = "dyn"
        if self.career():
            c.create_text(14, 17, anchor="w", text="Day %d  $%d/$%d" % (self.day, self.day_earned, self.day_goal),
                          font=F(15, True), fill="#ffe066", tags=d)
            secs = max(0, int(math.ceil(self.day_time)))
            c.create_text(176, 17, anchor="w", text="%d:%02d" % (secs // 60, secs % 60), font=F(15, True),
                          fill="#ffd0d0" if secs <= 15 else "#ffffff", tags=d)
        else:
            c.create_text(14, 17, anchor="w", text="$%d / $%d" % (self.score, self.settings["target"]),
                          font=F(17, True), fill="#ffe066", tags=d)
            c.create_text(165, 17, anchor="w", text="Served: %d" % self.served, font=F(14, True),
                          fill="#ffffff", tags=d)
        c.create_text(262, 17, anchor="w", text="Customers: %d/3" % len(self.customers),
                      font=F(14, True), fill="#ffffff", tags=d)
        text = self.msg if self.msg_t > 0 else "Click ingredients to cook. Click READY food to use it."
        color = self.msg_color if self.msg_t > 0 else "#ffd9b3"
        c.create_text(575, 17, text=text[:54], font=F(12, True), fill=color, tags=d)
        c.create_text(772, 17, anchor="w", text="Lives", font=F(12, True), fill="#ffffff", tags=d)
        for i in range(self.START_LIVES):
            c.create_text(822 + i * 22, 17, text="\u2665", font=F(20, True),
                          fill="#ff7b7b" if i < self.lives else "#6b3a3a", tags=d)
        if interactive:
            self.button(886, 5, 954, 29, "PAUSE", "#8a1f16", self.pause, 12)
        if self.event is not None:                       # random event badge under the HUD
            name, secs, col, message = EVENTS[self.event["kind"]]
            left = int(math.ceil(self.event["t"]))
            c.create_rectangle(8, 40, 172, 62, fill=col, outline="#ffffff", width=2, tags=d)
            c.create_text(90, 51, text="%s  %ds" % (name, left), font=F(11, True), fill="#ffffff", tags=d)
            frac = max(0.0, self.event["t"] / self.event["dur"])
            c.create_rectangle(8, 63, 8 + 164 * frac, 67, fill="#ffffff", outline="", tags=d)

    def render_customer_extras(self, cu):
        c = self.canvas
        d = "dyn"
        st = cu["state"]
        x = cu["x"]
        if st in ("ordering", "waiting", "delivering", "happy", "angry"):
            c.create_rectangle(x - 58, 42, x + 58, 84, fill="#ffffff", outline="#555555", width=1, tags=d)
            c.create_polygon([(x - 8, 84), (x + 8, 84), (x, 96)], fill="#ffffff", outline="", tags=d)
            c.create_line(x - 8, 84, x, 96, x + 8, 84, fill="#555555", tags=d)
            if st == "ordering":
                c.create_text(x, 63, text="Hmm...", font=F(14, True), fill="#555555", tags=d)
            elif st == "happy":
                c.create_text(x, 63, text="Thank you!", font=F(14, True), fill="#1b7a2e", tags=d)
                for i in range(3):
                    hy = 40 - ((self.clock * 25 + i * 14) % 30)
                    c.create_text(x - 18 + i * 18, hy + 10, text="\u2665", font=F(14, True),
                                  fill="#ff5d73", tags=d)
            elif st == "angry":
                c.create_text(x, 63, text="Too slow!", font=F(14, True), fill="#c0392b", tags=d)
            else:
                items = cu["items"][:3]
                n = len(items)
                for i, name in enumerate(items):
                    draw_item_icon(c, name, x + (i - (n - 1) / 2.0) * 38, 63, 0.8, d)
        if st == "waiting":
            ratio = max(0.0, cu["patience"] / cu["max_patience"])
            col = "#5cb85c" if ratio > 0.5 else ("#f0ad4e" if ratio > 0.25 else "#d9534f")
            bx = cu["home_x"]
            c.create_rectangle(bx - 38, 193, bx + 38, 201, fill="#ffffff", outline="#333333", tags=d)
            c.create_rectangle(bx - 38, 193, bx - 38 + 76 * ratio, 201, fill=col, outline="", tags=d)
            c.create_text(bx + 42, 197, anchor="w", text="%ds" % int(math.ceil(cu["patience"])),
                          font=F(10, True), fill="#ffffff", tags=d)
            c.create_text(bx - 42, 197, anchor="e", text="#%d" % cu["id"], font=F(10, True),
                          fill="#ffffff", tags=d)

    def heat_color(self, p, burn, raw, cooked, burnt="#1b1b1b"):
        if p < 1.0:
            return mix(raw, cooked, p)
        if burn:
            return mix(cooked, burnt, (p - 1.0) / (burn - 1.0))
        return cooked

    def render_stations(self):
        c = self.canvas
        d = "dyn"
        t = self.clock
        if any(self.grill):
            for k in range(10):
                x = 26 + k * 22
                h = 8 + 5 * math.sin(t * 9 + k)
                c.create_polygon([(x - 6, 410), (x + 6, 410), (x, 410 - h)], fill="#ff7a18",
                                 outline="", tags=d)
        for slots, pts in ((self.grill, self.GRILL_SLOTS), (self.toaster, self.TOASTER_SLOTS),
                           (self.fryer, self.FRYER_SLOTS), (self.drinks, self.DRINK_SLOTS)):
            for it, (cx, cy) in zip(slots, pts):
                if it is not None:
                    self.draw_slot_item(it, cx, cy)

    def draw_slot_item(self, it, cx, cy):
        c = self.canvas
        d = "dyn"
        t = self.clock
        kind = it["kind"]
        stage, p = item_stage(it)
        burn = it.get("burn", COOK[kind]["burn"])

        if kind == "Beef":
            col = self.heat_color(p, burn, "#e58a9a", "#7a4426")
            c.create_oval(cx - 26, cy - 13, cx + 26, cy + 13, fill=col, outline="#3e2010", width=2, tags=d)
            if p > 0.45:
                for dx in (-12, 0, 12):
                    c.create_line(cx + dx - 5, cy - 6, cx + dx + 5, cy + 6, fill="#2a1408", width=2, tags=d)
        elif kind == "Chicken":
            col = self.heat_color(p, burn, "#f2c9a0", "#c98a3c")
            c.create_oval(cx - 26, cy - 13, cx + 26, cy + 13, fill=col, outline="#7a4a14", width=2, tags=d)
            for dx, dy in ((-12, -4), (4, 3), (14, -5), (-4, 6)):
                c.create_oval(cx + dx - 2, cy + dy - 2, cx + dx + 2, cy + dy + 2,
                              fill=mix(col, "#ffffff", 0.3), outline="", tags=d)
        elif kind == "Bun":
            col = self.heat_color(p, burn, "#f6e2b3", "#c98a35", "#2a1a0a")
            c.create_oval(cx - 15, cy - 26, cx + 15, cy - 8, fill=col, outline="#7a4a14", width=2, tags=d)
            c.create_rectangle(cx - 15, cy - 17, cx + 15, cy + 20, fill=col, outline="#7a4a14", width=2, tags=d)
            if p > 0.5:
                for dy in (-6, 4, 14):
                    c.create_line(cx - 10, cy + dy, cx + 10, cy + dy, fill=mix(col, "#2a1a0a", 0.5),
                                  width=2, tags=d)
        elif kind == "Fries":
            col = self.heat_color(p, burn, "#f7efc6", "#f0b429", "#3b2410")
            for i in range(-3, 4):
                c.create_rectangle(cx + i * 6 - 2, cy - 20 + (i % 2) * 5, cx + i * 6 + 2, cy + 6,
                                   fill=col, outline="#8a6a10", tags=d)
            c.create_rectangle(cx - 24, cy - 4, cx + 24, cy + 18, fill="", outline="#444444", width=2, tags=d)
            for i in range(-2, 3):
                c.create_line(cx + i * 10, cy - 4, cx + i * 10, cy + 18, fill="#444444", tags=d)
            if stage == "cooking":
                for i in range(3):
                    by = cy + 16 - ((t * 20 + i * 7) % 12)
                    c.create_oval(cx - 16 + i * 14, by - 2, cx - 12 + i * 14, by + 2,
                                  fill="#fff6c8", outline="", tags=d)
        elif kind == "Drink":
            frac = min(1.0, p)
            c.create_polygon([(cx - 14, cy - 18), (cx + 14, cy - 18), (cx + 10, cy + 18), (cx - 10, cy + 18)],
                             fill="#f4f4f4", outline="#888888", width=2, tags=d)
            if frac > 0:
                ly = cy + 17 - 34 * frac
                hw = 9 + 4 * ((cy + 17 - ly) / 34.0)
                c.create_polygon([(cx - hw, ly), (cx + hw, ly), (cx + 9, cy + 17), (cx - 9, cy + 17)],
                                 fill="#7b3f1d", outline="", tags=d)
            if stage == "cooking":
                c.create_line(cx, 350, cx, ly if frac > 0 else cy + 10, fill="#7b3f1d", width=3, tags=d)
            else:
                c.create_rectangle(cx - 15, cy - 22, cx + 15, cy - 18, fill="#d62828", outline="#7a0f0f", tags=d)
                c.create_line(cx + 3, cy - 22, cx + 8, cy - 36, fill="#2a9d8f", width=3, tags=d)

        if stage == "cooking" and kind in ("Beef", "Chicken", "Bun"):
            for i in range(3):
                yy = cy - 18 - ((t * 22 + i * 9) % 20)
                xx = cx + (i - 1) * 9 + math.sin(t * 3 + i) * 2
                c.create_oval(xx - 2.5, yy - 2.5, xx + 2.5, yy + 2.5, fill="#e8e8e8", outline="", tags=d)

        # progress bar with a countdown / READY / BURNT label, plus the burn meter
        bx1, bx2, by = cx - 24, cx + 24, cy + 22
        c.create_rectangle(bx1, by, bx2, by + 11, fill="#ffffff", outline="#444444", tags=d)
        col = "#f39c12" if stage == "cooking" else ("#2ecc71" if stage == "ready" else "#c0392b")
        c.create_rectangle(bx1, by, bx1 + 48 * min(1.0, p), by + 11, fill=col, outline="", tags=d)
        if stage == "cooking":
            left = int(math.ceil(it.get("time", COOK[kind]["time"]) - it["t"]))
            c.create_text(cx, by + 6, text="%ds" % left, font=F(9, True), fill="#2d1e1a", tags=d)
        elif stage == "ready":
            if int(t * 3) % 2 == 0:
                c.create_rectangle(cx - 30, cy - 32, cx + 30, cy + 20, fill="", outline="#2ecc71",
                                   width=3, tags=d)
            c.create_text(cx, by + 6, text="READY!", font=F(9, True), fill="#ffffff", tags=d)
            if burn:
                bf = min(1.0, (p - 1.0) / (burn - 1.0))
                c.create_rectangle(bx1, by + 13, bx2, by + 17, fill="#ffffff", outline="#444444", tags=d)
                c.create_rectangle(bx1, by + 13, bx1 + 48 * bf, by + 17, fill="#c0392b", outline="", tags=d)
        else:
            c.create_text(cx, by + 6, text="BURNT!", font=F(9, True), fill="#ffffff", tags=d)

    def render_plate(self, interactive):
        c = self.canvas
        d = "dyn"
        layers = self.plate.to_list()
        draw_burger(c, self.PLATE_X, self.PLATE_Y, 96, layers, 15, d)
        if layers and layers[0] == "Bun":      # the top half of the bun joins on WRAP
            gy = self.PLATE_Y - len(layers) * 15
            c.create_arc(self.PLATE_X - 48, gy - 15, self.PLATE_X + 48, gy + 15, start=0, extent=180,
                         style="arc", outline="#f6e3c4", width=2, dash=(3, 3), tags=d)
            c.create_text(self.PLATE_X + 52, gy - 5, anchor="w", text="top bun", font=F(8, True),
                          fill="#f6e3c4", tags=d)
        c.create_text(417, 488, anchor="e", text="Plate %d/%d" % (len(layers), self.PLATE_MAX),
                      font=F(10, True), fill="#f6e3c4", tags=d)
        c.create_text(160, 490, anchor="w", text="Top: %s" % (self.plate.peek() or "empty"),
                      font=F(10, True), fill="#f6e3c4", tags=d)
        if not self.redo.is_empty():
            c.create_text(417, 501, anchor="e", text="Aside: %s (%d)" % (self.redo.peek(), self.redo.size()),
                          font=F(10, True), fill="#ffe066", tags=d)
        buttons = ((16, 86, "WRAP", "#2e9e4f", self.wrap_burger, 13),
                   (92, 144, "UNDO", "#d99a1e", self.undo_plate, 12),
                   (150, 202, "REDO", "#2a78c4" if not self.redo.is_empty() else "#8a8a8a",
                    self.redo_plate, 12),
                   (208, 264, "TRASH", "#c0392b", self.discard_plate, 11))
        for x1, x2, label, col, action, size in buttons:
            if interactive:
                self.button(x1, 548, x2, 588, label, col, action, size)
            else:
                c.create_rectangle(x1, 548, x2, 588, fill=col, outline="#2b2b2b", width=2, tags=d)
                c.create_text((x1 + x2) / 2.0, 568, text=label, font=F(size, True), fill="#ffffff", tags=d)

    def render_shelf(self):
        for i, name in enumerate(self.shelf):
            sx, sy = self.shelf_pos(i)
            draw_item_icon(self.canvas, name, sx, sy, 0.7, "dyn")

    def render_rack(self, interactive):
        c = self.canvas
        d = "dyn"
        for i, name in enumerate(self.rack):
            sx, sy = self.rack_pos(i)
            if name == "Patty":
                c.create_oval(sx - 17, sy - 13, sx + 17, sy + 1, fill="#7a4426", outline="#3e2010",
                              width=2, tags=d)
                for dx in (-8, 0, 8):
                    c.create_line(sx + dx - 3, sy - 9, sx + dx + 3, sy - 3, fill="#2a1408", width=2, tags=d)
            elif name == "Chicken":
                c.create_oval(sx - 17, sy - 13, sx + 17, sy + 1, fill="#c98a3c", outline="#7a4a14",
                              width=2, tags=d)
                for dx, dy in ((-8, -8), (3, -5), (10, -9)):
                    c.create_oval(sx + dx - 1.5, sy + dy - 1.5, sx + dx + 1.5, sy + dy + 1.5,
                                  fill="#e8b868", outline="", tags=d)
            else:
                draw_burger(c, sx, sy + 1, 30, ["Bun", "TopBun"], 7, d)
            c.create_text(sx, sy + 11, text=name, font=F(8, True), fill="#4a3a2a", tags=d)
            if interactive:
                self.hits.append((sx - 23, sy - 17, sx + 23, sy + 17, lambda i=i: self.use_rack(i), True))

    def render_orders(self, interactive):
        c = self.canvas
        d = "dyn"
        x1, x2 = self.PLAY_W + 6, self.W - 6
        cards = self.board.to_list()[:3]
        for k in range(3):
            y = 348 + k * 84
            if k >= len(cards):
                c.create_rectangle(x1, y, x2, y + 80, fill="#3a2a25", outline="#5a463d", tags=d)
                if k == 0:
                    c.create_text((x1 + x2) / 2.0, y + 40, text="Waiting for customers...",
                                  font=F(12, True), fill="#a08a7a", tags=d)
                continue
            cu = cards[k]
            ratio = max(0.0, cu["patience"] / cu["max_patience"])
            vip = cu["vip"]
            c.create_rectangle(x1, y, x2, y + 80, fill="#fff0b3" if vip else "#fff4df",
                               outline="#d4a017" if vip else "#a0792c", width=3 if vip else 2, tags=d)
            title = ("VIP order #%d" if vip else "Order #%d") % cu["id"]
            if cu is self.board.peek():
                title += " - NEXT"                  # board.peek(): the most urgent order
            c.create_text(x1 + 8, y + 11, anchor="w", text=title,
                          font=F(12, True), fill="#8a5a00" if vip else "#2d1e1a", tags=d)
            secs = int(math.ceil(cu["patience"]))
            c.create_text(x2 - 8, y + 11, anchor="e", text="%ds" % secs, font=F(13, True),
                          fill="#c0392b" if ratio < 0.3 else "#2d1e1a", tags=d)
            bcol = "#5cb85c" if ratio > 0.5 else ("#f0ad4e" if ratio > 0.25 else "#d9534f")
            c.create_rectangle(x1 + 8, y + 21, x2 - 8, y + 27, fill="#ffffff", outline="#444444", tags=d)
            c.create_rectangle(x1 + 8, y + 21, x1 + 8 + (x2 - x1 - 16) * ratio, y + 27, fill=bcol,
                               outline="", tags=d)
            have = list(self.shelf)
            all_ready = True
            for j, name in enumerate(cu["items"][:3]):
                ready = name in have
                if cu["state"] == "delivering":
                    ready = True                      # already taken by the waiter
                elif ready:
                    have.remove(name)
                else:
                    all_ready = False
                ly = y + 36 + j * 11
                c.create_rectangle(x1 + 8, ly - 4, x1 + 16, ly + 4, fill="#2ecc71" if ready else "#ffffff",
                                   outline="#444444", tags=d)
                if ready:
                    c.create_line(x1 + 9.5, ly, x1 + 11.5, ly + 2.5, x1 + 15, ly - 2.5, fill="#ffffff",
                                  width=2, tags=d)
                c.create_text(x1 + 22, ly, anchor="w", text=name, font=F(10, True),
                              fill="#1b7a2e" if ready else "#6b3a2a", tags=d)
            if cu["combo"]:
                c.create_text(x2 - 8, y + 47, anchor="e", text="COMBO +$%d" % COMBO_BONUS,
                              font=F(10, True), fill="#b8860b", tags=d)
            by1, by2 = y + 63, y + 77
            if cu["state"] == "delivering":
                c.create_rectangle(x1 + 8, by1, x2 - 8, by2, fill="#2a78c4", outline="#1c4f82", tags=d)
                c.create_text((x1 + x2) / 2.0, (by1 + by2) / 2.0, text="DELIVERING...", font=F(10, True),
                              fill="#ffffff", tags=d)
            else:
                label = "SERVE" if all_ready else "Missing items"
                col = "#2e9e4f" if all_ready else "#8a8a8a"
                if interactive:
                    self.button(x1 + 8, by1, x2 - 8, by2, label, col,
                                lambda cu=cu: self.try_serve(cu), 10)
                else:
                    c.create_rectangle(x1 + 8, by1, x2 - 8, by2, fill=col, outline="#2b2b2b", tags=d)
                    c.create_text((x1 + x2) / 2.0, (by1 + by2) / 2.0, text=label, font=F(10, True),
                                  fill="#ffffff", tags=d)

def enable_sharp_window():
    """Stops Windows from blurring / enlarging the window on high-DPI screens."""
    try:
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass


if __name__ == "__main__":
    enable_sharp_window()
    window = tk.Tk()
    BurgerRush(window)
    window.mainloop()
