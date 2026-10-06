# -*- coding: utf-8 -*-
"""黑白反转小游戏（十字翻转玩法）。

规则：
- 棋盘是自定义大小的矩形（默认 3 行 3 列，也可以指定 5 行 6 列等），开局全白，随机翻出一些黑块。
- 左键点击任意方块：该方块和它上下左右的相邻方块一起反色（白变黑、黑变白）。
- 把所有方块恢复成白色即通关。
- 也可以进入“自定义黑块”编辑模式自己摆开局：实时检测布局是否可解；无解时会建议修正，
  但也可以直接开始，演示窗口会说明为什么无解。

黑块由“从全白棋盘随机点击若干次”生成，所以每一局一定有解：
把你点过的方块按相同顺序再点一遍就能还原；中途随便点也不会走进死局。

运行示例：
    python black_white_flip.py              # 默认 3 行 3 列
    python black_white_flip.py 5 6          # 指定 5 行 6 列
    python black_white_flip.py 6x6          # 也可以写成 AxB
    python black_white_flip.py --seed 42    # 固定随机种子，复现同一局
    python black_white_flip.py --selftest   # 只跑逻辑自检，不打开窗口

窗口内快捷键：R 新一局 / 编辑时随机，U / Z 撤销，H 提示，E 自定义黑块，
C 清空，F 建议修正，G 高斯消元演示，T 追白法演示，Esc 返回，Enter 开始。
"""

from __future__ import annotations

import argparse
import random
import re
import sys
from collections import deque

try:
    import tkinter as tk
except ImportError:  # pragma: no cover - 没有 tkinter 时仍然可以跑 --selftest
    tk = None

MIN_SIZE = 1
MAX_SIZE = 25
DEFAULT_ROWS = 3
DEFAULT_COLS = 3
SCRAMBLE_RATIO = 0.4
SELFTEST_SEED = 12345

DIRS = ((-1, 0), (1, 0), (0, -1), (0, 1))

PAGE_BG = "#f3f4f8"
CANVAS_BG = "#e6e9f0"
TILE_WHITE = "#ffffff"
TILE_WHITE_EDGE = "#c9cfda"
TILE_BLACK = "#1f232b"
TILE_BLACK_EDGE = "#101318"
ACCENT = "#3b82f6"
ACCENT_DARK = "#2f6dd0"
HINT_COLOR = "#f59e0b"
TEXT_COLOR = "#1f2430"
MUTED_COLOR = "#6b7280"
WIN_COLOR = "#15803d"
ERROR_COLOR = "#dc2626"


# ---------------------------------------------------------------- 游戏逻辑

def neighbors(rows, cols, r, c):
    """生成 (r, c) 以及上下左右在界内的相邻坐标。"""
    yield r, c
    for dr, dc in DIRS:
        nr, nc = r + dr, c + dc
        if 0 <= nr < rows and 0 <= nc < cols:
            yield nr, nc


def press(board, r, c):
    """点击 (r, c)：它自己和上下左右相邻格子一起反色。"""
    rows, cols = len(board), len(board[0])
    for nr, nc in neighbors(rows, cols, r, c):
        board[nr][nc] ^= 1


def affected_count(rows, cols, r, c):
    """点击 (r, c) 会翻转多少个格子（角 3、边 4、内部 5）。"""
    return sum(1 for _ in neighbors(rows, cols, r, c))


def has_black(board):
    return any(any(row) for row in board)


def scramble(rows, cols, rng):
    """从全白开始随机点击若干次，返回 (棋盘, 点击过的位置列表)。

    这样生成的棋盘一定可解：把列表里的点击再执行一遍即可还原。
    """
    board = [[0] * cols for _ in range(rows)]
    cells = [(r, c) for r in range(rows) for c in range(cols)]
    rng.shuffle(cells)
    count = max(4, round(len(cells) * SCRAMBLE_RATIO))
    presses = cells[: min(count, len(cells))]
    for r, c in presses:
        press(board, r, c)
    if not has_black(board):
        # 极小概率打乱成“全白”的静默图案，补一次点击保证有黑块。
        r, c = rng.randrange(rows), rng.randrange(cols)
        press(board, r, c)
        presses.append((r, c))
    return board, presses


def solve(board):
    """用 GF(2) 高斯消元求一个可行解，供“提示”使用。

    返回整数位掩码：第 i 位为 1 表示要点第 i 个格子（按行优先编号）；
    无解返回 None。游戏内所有局面都可解（点击生成自全白棋盘）。
    """
    rows, cols = len(board), len(board[0])
    n = rows * cols
    equations = []
    for r in range(rows):
        for c in range(cols):
            mask = 0
            for nr, nc in neighbors(rows, cols, r, c):
                mask |= 1 << (nr * cols + nc)
            if board[r][c]:
                mask |= 1 << n  # 右端项
            equations.append(mask)

    pivot_row = 0
    pivots = []
    for col in range(n):
        pick = -1
        for i in range(pivot_row, len(equations)):
            if (equations[i] >> col) & 1:
                pick = i
                break
        if pick == -1:
            continue
        equations[pivot_row], equations[pick] = equations[pick], equations[pivot_row]
        for i in range(len(equations)):
            if i != pivot_row and (equations[i] >> col) & 1:
                equations[i] ^= equations[pivot_row]
        pivots.append((pivot_row, col))
        pivot_row += 1

    for i in range(pivot_row, len(equations)):
        if equations[i] == 1 << n:  # 0 = 1，矛盾
            return None

    solution = 0
    for row, col in pivots:
        if (equations[row] >> n) & 1:
            solution |= 1 << col
    return solution


def _elimination_events(matrix, n_vars):
    """GF(2) 行消元的通用逐步事件，棋盘演示和小方程组讲解共用。

    每一步产出 ((事件, 数据), 矩阵快照)：
    - ("start", None)                     开局，给出初始增广矩阵
    - ("pivot", (行, 列))                 选中主元
    - ("swap", (原行, 新行, 列))          交换两行让主元就位
    - ("eliminate", (被消行, 主元行, 列)) 用主元行异或掉这一行
    - ("free", (列,))                     整列无主元，是自由变量
    - ("consistent", None)                消元完成且无矛盾
    - ("contradiction", (行,))            出现 0 = 1，无解
    - ("solve", (列, 主元行, 取值))       从主元行读出未知数
    - ("done", 解的点按位掩码)            求解完成
    """
    data = list(matrix)
    yield ("start", None), list(data)
    pivot_row = 0
    pivots = []
    for col in range(n_vars):
        pick = -1
        for i in range(pivot_row, len(data)):
            if (data[i] >> col) & 1:
                pick = i
                break
        if pick == -1:
            yield ("free", (col,)), list(data)
            continue
        if pick != pivot_row:
            data[pivot_row], data[pick] = data[pick], data[pivot_row]
            yield ("swap", (pick, pivot_row, col)), list(data)
        else:
            yield ("pivot", (pivot_row, col)), list(data)
        for i in range(len(data)):
            if i != pivot_row and (data[i] >> col) & 1:
                data[i] ^= data[pivot_row]
                yield ("eliminate", (i, pivot_row, col)), list(data)
        pivots.append((pivot_row, col))
        pivot_row += 1

    for i in range(pivot_row, len(data)):
        if data[i] == 1 << n_vars:
            yield ("contradiction", (i,)), list(data)
            return
    yield ("consistent", None), list(data)

    solution = 0
    for row, col in pivots:
        bit = (data[row] >> n_vars) & 1
        if bit:
            solution |= 1 << col
        yield ("solve", (col, row, bit)), list(data)
    yield ("done", solution), list(data)


def elimination_steps(board):
    """把棋盘的 GF(2) 高斯消元过程拆成一步步事件，供演示窗口播放。"""
    rows, cols = len(board), len(board[0])
    n = rows * cols
    matrix = []
    for r in range(rows):
        for c in range(cols):
            mask = 0
            for nr, nc in neighbors(rows, cols, r, c):
                mask |= 1 << (nr * cols + nc)
            if board[r][c]:
                mask |= 1 << n  # 右端项
            matrix.append(mask)
    yield from _elimination_events(matrix, n)


_PARITY_CACHE = {}


def board_mask(board, cols):
    """把棋盘压成整数位掩码（行优先，1 表示黑块）。"""
    mask = 0
    for r, row in enumerate(board):
        for c, value in enumerate(row):
            if value:
                mask |= 1 << (r * cols + c)
    return mask


def parity_basis(rows, cols):
    """求翻转矩阵的左零空间基（校验矩阵），用来判断任意布局是否可解。

    对增广矩阵 [A | I] 做行变换，A 部分被消成全零的行给出校验向量：
    布局 b 可解 ⇔ 每个校验向量与 b 的内积都是偶数。
    """
    n = rows * cols
    data = []
    for t in range(n):
        row = 0
        for nr, nc in neighbors(rows, cols, t // cols, t % cols):
            row |= 1 << (nr * cols + nc)
        data.append([row, 1 << t])
    rank = 0
    for col in range(n):
        pick = -1
        for i in range(rank, n):
            if (data[i][0] >> col) & 1:
                pick = i
                break
        if pick == -1:
            continue
        data[rank], data[pick] = data[pick], data[rank]
        for i in range(n):
            if i != rank and (data[i][0] >> col) & 1:
                data[i][0] ^= data[rank][0]
                data[i][1] ^= data[rank][1]
        rank += 1
    return [check for row, check in data if row == 0]


def column_syndromes(basis, n):
    """每个格子单独翻转时对校验矩阵产生的“综合征”。"""
    syndromes = [0] * n
    for j, vector in enumerate(basis):
        bit = 1 << j
        value = vector
        while value:
            low = value & -value
            syndromes[low.bit_length() - 1] |= bit
            value ^= low
    return syndromes


def syndrome_tools(rows, cols):
    """按棋盘尺寸缓存 (校验基, 每格综合征)。"""
    key = (rows, cols)
    tools = _PARITY_CACHE.get(key)
    if tools is None:
        basis = parity_basis(rows, cols)
        tools = (basis, column_syndromes(basis, rows * cols))
        _PARITY_CACHE[key] = tools
    return tools


def mask_syndrome(basis, mask):
    """布局的综合征：全 0 表示这个布局能还原成全白。"""
    syndrome = 0
    for j, vector in enumerate(basis):
        if (vector & mask).bit_count() & 1:
            syndrome |= 1 << j
    return syndrome


def syndrome_fix(basis, cols_syn, target):
    """找一个尽量小的翻转集合，把综合征 target 修正为 0（返回位掩码）。"""
    if target == 0:
        return 0
    cells = []
    seen = set()
    for i, value in enumerate(cols_syn):
        if value not in seen:  # 综合征相同的格子只需保留一个
            seen.add(value)
            cells.append((i, value))

    if len(basis) <= 10:
        # 校验空间很小，BFS 一遍就能得到“最少翻几格”的修正
        parent = {0: None}
        queue = deque([0])
        while queue:
            state = queue.popleft()
            if state == target:
                mask = 0
                while parent[state] is not None:
                    prev, cell = parent[state]
                    mask |= 1 << cell
                    state = prev
                return mask
            for index, value in cells:
                nxt = state ^ value
                if nxt not in parent:
                    parent[nxt] = (state, index)
                    queue.append(nxt)
        return None

    # 校验空间太大时退而求其次：只找 1 ~ 3 格的修正
    for index, value in cells:
        if value == target:
            return 1 << index
    pairs = {}
    for a in range(len(cells)):
        ia, ca = cells[a]
        for b in range(a + 1, len(cells)):
            ib, cb = cells[b]
            pairs.setdefault(ca ^ cb, (1 << ia) | (1 << ib))
    for value, mask in pairs.items():
        if value == target:
            return mask
    for index, value in cells:
        wanted = target ^ value
        if wanted in pairs:
            return pairs[wanted] | (1 << index)
    return None


def chase_presses(board, top=()):
    """追白法：第一行按 top 点，之后每行点上一行残留黑格的正下方。

    返回 (追完后的棋盘, 点击列表)；追完后只有最后一行可能还有黑块。
    """
    rows, cols = len(board), len(board[0])
    work = [row[:] for row in board]
    presses = []
    for c in top:
        press(work, 0, c)
        presses.append((0, c))
    for r in range(1, rows):
        for c in range(cols):
            if work[r - 1][c]:
                press(work, r, c)
                presses.append((r, c))
    return work, presses


_CHASE_CACHE = {}


def chase_columns(rows, cols):
    """第一行只点第 i 格时，追白后最后一行的残留指纹（即矩阵 M 的第 i 列）。

    用整数位掩码表示（bit c = 最后一行第 c+1 格）。结果按尺寸缓存。
    """
    key = (rows, cols)
    columns = _CHASE_CACHE.get(key)
    if columns is None:
        white = [[0] * cols for _ in range(rows)]
        columns = []
        for i in range(cols):
            after, _ = chase_presses(white, (i,))
            mask = 0
            for c in range(cols):
                if after[rows - 1][c]:
                    mask |= 1 << c
            columns.append(mask)
        _CHASE_CACHE[key] = columns
    return columns


def _solve_gf2(equations, n_vars):
    """解 GF(2) 线性方程组（每行 bit0..n-1 是系数，bit n 是右端项）。"""
    data = list(equations)
    pivot_row = 0
    pivots = []
    for col in range(n_vars):
        pick = -1
        for i in range(pivot_row, len(data)):
            if (data[i] >> col) & 1:
                pick = i
                break
        if pick == -1:
            continue
        data[pivot_row], data[pick] = data[pick], data[pivot_row]
        for i in range(len(data)):
            if i != pivot_row and (data[i] >> col) & 1:
                data[i] ^= data[pivot_row]
        pivots.append((pivot_row, col))
        pivot_row += 1
    for i in range(pivot_row, len(data)):
        if data[i] == 1 << n_vars:
            return None
    solution = 0
    for row, col in pivots:
        if (data[row] >> n_vars) & 1:
            solution |= 1 << col
    return solution


def _gf2_rank(values, n_bits):
    data = [v for v in values if v]
    rank = 0
    for col in range(n_bits):
        pick = -1
        for i in range(rank, len(data)):
            if (data[i] >> col) & 1:
                pick = i
                break
        if pick == -1:
            continue
        data[rank], data[pick] = data[pick], data[rank]
        for i in range(len(data)):
            if i != rank and (data[i] >> col) & 1:
                data[i] ^= data[rank]
        rank += 1
    return rank


def first_row_for_chase(rows, cols, residual):
    """解 M·p = residual，返回第一行点法位掩码；无解返回 None。

    M 由 chase_columns 给出，未知数只有 cols 个（第一行每格点或不点），
    所以一次小小的 GF(2) 消元就能取代 2^cols 的枚举。
    """
    columns = chase_columns(rows, cols)
    equations = []
    for c in range(cols):
        row = 0
        for i in range(cols):
            if (columns[i] >> c) & 1:
                row |= 1 << i
        if (residual >> c) & 1:
            row |= 1 << cols
        equations.append(row)
    return _solve_gf2(equations, cols)


def selftest():
    """随机对局自检：打乱可还原、点击是自反的、求解器结果正确。"""
    rng = random.Random(SELFTEST_SEED)
    problems = []

    def check(ok, message):
        if not ok:
            problems.append(message)

    for _ in range(200):
        rows, cols = rng.randint(2, 7), rng.randint(2, 7)
        board, presses = scramble(rows, cols, rng)
        check(has_black(board), f"{rows}x{cols}: 打乱后仍然是全白棋盘")

        replay = [row[:] for row in board]
        for r, c in presses:
            press(replay, r, c)
        check(not has_black(replay), f"{rows}x{cols}: 回放打乱点击没有复原")

        r, c = rng.randrange(rows), rng.randrange(cols)
        twice = [row[:] for row in board]
        press(twice, r, c)
        press(twice, r, c)
        check(twice == board, f"{rows}x{cols}: 点击两次没有回到原状态")

        solution = solve(board)
        check(solution is not None, f"{rows}x{cols}: 可解棋盘却求解失败")
        if solution is not None:
            solved = [row[:] for row in board]
            for i in range(rows * cols):
                if (solution >> i) & 1:
                    press(solved, i // cols, i % cols)
            check(not has_black(solved), f"{rows}x{cols}: 求解结果没有复原")

        check(affected_count(rows, cols, 0, 0) == 3, "角块应该影响 3 格")
        check(affected_count(rows, cols, rows - 1, cols - 1) == 3, "角块应该影响 3 格")
        if rows > 2 and cols > 2:
            check(affected_count(rows, cols, 0, cols // 2) == 4, "边缘块应该影响 4 格")
            check(affected_count(rows, cols, 1, 1) == 5, "内部块应该影响 5 格")

    # 自定义布局模块：可解性判定与建议修正
    for _ in range(60):
        rows, cols = rng.randint(2, 6), rng.randint(2, 6)
        basis, cols_syn = syndrome_tools(rows, cols)
        board, _ = scramble(rows, cols, rng)
        check(mask_syndrome(basis, board_mask(board, cols)) == 0,
              f"{rows}x{cols}: 打乱布局的综合征应为 0")

        layout = [[rng.randint(0, 1) for _ in range(cols)] for _ in range(rows)]
        syndrome = mask_syndrome(basis, board_mask(layout, cols))
        check((syndrome == 0) == (solve(layout) is not None),
              f"{rows}x{cols}: 综合征判定和求解结果不一致")
        if syndrome != 0:
            fix = syndrome_fix(basis, cols_syn, syndrome)
            check(fix is not None, f"{rows}x{cols}: 建议修正没找到方案")
            if fix is not None:
                fixed = [row[:] for row in layout]
                for i in range(rows * cols):
                    if (fix >> i) & 1:
                        fixed[i // cols][i % cols] ^= 1
                check(solve(fixed) is not None, f"{rows}x{cols}: 修正后的布局仍然无解")

    # 消元演示的步骤要和求解器给出完全一致的结果
    for _ in range(40):
        rows, cols = rng.randint(2, 5), rng.randint(2, 5)
        board = [[rng.randint(0, 1) for _ in range(cols)] for _ in range(rows)]
        events = list(elimination_steps(board))
        (tag, payload) = events[-1][0]
        expected = solve(board)
        if expected is None:
            check(tag == "contradiction", f"{rows}x{cols}: 无解局面没有演示出矛盾行")
        else:
            check(tag == "done", f"{rows}x{cols}: 有解局面没有演示完")
            check(payload == expected, f"{rows}x{cols}: 演示的解与求解器不一致")

    # 追白法：第一遍不碰第一行，最后一行残留就能决定第一行点法
    for _ in range(60):
        rows, cols = rng.randint(2, 6), rng.randint(2, 6)
        board = [[rng.randint(0, 1) for _ in range(cols)] for _ in range(rows)]
        after, _ = chase_presses(board)
        check(all(not any(row) for row in after[:-1]),
              f"{rows}x{cols}: 追白后除最后一行外应该全白")
        residual = 0
        for c in range(cols):
            if after[rows - 1][c]:
                residual |= 1 << c
        basis, _ = syndrome_tools(rows, cols)
        solvable = mask_syndrome(basis, board_mask(board, cols)) == 0
        top_mask = first_row_for_chase(rows, cols, residual)
        check((top_mask is not None) == solvable,
              f"{rows}x{cols}: 追白法的可解判断和校验矩阵不一致")
        if top_mask is not None:
            solved, _ = chase_presses(
                board, tuple(c for c in range(cols) if (top_mask >> c) & 1))
            check(not has_black(solved), f"{rows}x{cols}: 追白法两遍没有解出来")
    check(_gf2_rank(chase_columns(5, 6), 6) == 6, "5x6 的第一行响应矩阵应该满秩")
    check(_gf2_rank(chase_columns(4, 4), 4) == 0, "4x4 的第一行响应矩阵应该全零")
    inv_cols = [first_row_for_chase(5, 6, 1 << j) for j in range(6)]
    for _ in range(20):
        residual = rng.randrange(1 << 6)
        table = 0
        for j in range(6):
            if (residual >> j) & 1:
                table ^= inv_cols[j]
        check(table == first_row_for_chase(5, 6, residual),
              "5x6: 反查表逐位异或的结果应该等于直接解方程组")
    # 原理讲解里的小方程组消元也要给出同样的 p
    columns = chase_columns(5, 6)
    for _ in range(20):
        residual = rng.randrange(1 << 6)
        equations = []
        for c in range(6):
            row = 0
            for i in range(6):
                if (columns[i] >> c) & 1:
                    row |= 1 << i
            if (residual >> c) & 1:
                row |= 1 << 6
            equations.append(row)
        (tag, payload) = list(_elimination_events(equations, 6))[-1][0]
        check(tag == "done" and payload == first_row_for_chase(5, 6, residual),
              "5x6: 小方程组的消元结果应该等于反查表结果")

    print(f"mismatch count: {len(problems)}")
    for message in problems[:10]:
        print("  -", message)
    return len(problems)


# ---------------------------------------------------------------- 界面

def _font(size, bold=False):
    return ("Microsoft YaHei UI", size, "bold" if bold else "normal")


class GameApp:
    """游戏窗口与交互。"""

    def __init__(self, rows=DEFAULT_ROWS, cols=DEFAULT_COLS, rng=None, master=None):
        if tk is None:
            raise RuntimeError("需要 tkinter 才能打开游戏窗口（Windows 官方 Python 自带）。")
        self.root = tk.Tk() if master is None else master
        self.rng = rng if rng is not None else random.Random()
        self.rows, self.cols = int(rows), int(cols)
        self.board = [[0] * self.cols for _ in range(self.rows)]
        self.history = []
        self.won = False
        self.hint_cell = None
        self.hover = None
        self.mode = "play"
        self.edit_history = []
        self._snapshot = None
        self._demo = None
        self._chase = None

        self.root.title("黑白反转 · 十字翻转")
        self.root.configure(bg=PAGE_BG)
        self._build_ui()
        self.new_game(self.rows, self.cols)
        self._bind_keys()
        self._center_window()

    # -------------------------------------------------- 控件搭建

    def _build_ui(self):
        outer = tk.Frame(self.root, bg=PAGE_BG, padx=18, pady=14)
        outer.pack(fill="both", expand=True)

        top = tk.Frame(outer, bg=PAGE_BG)
        top.pack(fill="x")
        tk.Label(top, text="黑白反转", font=_font(18, True),
                 bg=PAGE_BG, fg=TEXT_COLOR).pack(side="left")
        tk.Label(top, text="点击方块 → 它与上下左右一起反色 · 全部变白即通关",
                 font=_font(10), bg=PAGE_BG, fg=MUTED_COLOR).pack(side="left", padx=(10, 0))

        bar = tk.Frame(outer, bg=PAGE_BG)
        bar.pack(fill="x", pady=(12, 10))
        self.rows_var = tk.StringVar(value=str(self.rows))
        self.cols_var = tk.StringVar(value=str(self.cols))
        rows_box, self.rows_entry = self._size_entry(bar, "行", self.rows_var)
        rows_box.pack(side="left")
        cols_box, self.cols_entry = self._size_entry(bar, "列", self.cols_var, pad=(10, 0))
        cols_box.pack(side="left")

        self.play_buttons = tk.Frame(bar, bg=PAGE_BG)
        self._button(self.play_buttons, "新游戏", self.new_game_from_entries,
                     primary=True).pack(side="left")
        self._button(self.play_buttons, "自定义黑块", self.enter_edit).pack(
            side="left", padx=(8, 0))
        self._button(self.play_buttons, "撤销 (U)", self.undo).pack(side="left", padx=(8, 0))
        self._button(self.play_buttons, "提示 (H)", self.hint).pack(side="left", padx=(8, 0))
        self._button(self.play_buttons, "消元演示 (G)", self.open_demo).pack(
            side="left", padx=(8, 0))
        self._button(self.play_buttons, "追白法 (T)", self.open_chase).pack(
            side="left", padx=(8, 0))

        self.edit_buttons = tk.Frame(bar, bg=PAGE_BG)
        self._button(self.edit_buttons, "开始游戏", self.start_custom,
                     primary=True).pack(side="left")
        self._button(self.edit_buttons, "清空 (C)", self.clear_board).pack(side="left", padx=(8, 0))
        self._button(self.edit_buttons, "随机 (R)", self.random_edit_board).pack(
            side="left", padx=(8, 0))
        self._button(self.edit_buttons, "建议修正 (F)", self.auto_fix).pack(
            side="left", padx=(8, 0))
        self._button(self.edit_buttons, "返回 (Esc)", self.exit_edit).pack(
            side="left", padx=(8, 0))
        self._button(self.edit_buttons, "消元演示 (G)", self.open_demo).pack(
            side="left", padx=(8, 0))
        self._button(self.edit_buttons, "追白法 (T)", self.open_chase).pack(
            side="left", padx=(8, 0))

        self.moves_var = tk.StringVar(value="步数 0")
        tk.Label(bar, textvariable=self.moves_var, font=_font(12, True),
                 bg=PAGE_BG, fg=TEXT_COLOR).pack(side="right")

        board_wrap = tk.Frame(outer, bg=CANVAS_BG, highlightthickness=1,
                              highlightbackground="#d3d8e2")
        board_wrap.pack()
        self.canvas = tk.Canvas(board_wrap, bg=CANVAS_BG, highlightthickness=0,
                                width=10, height=10)
        self.canvas.pack()
        self.canvas.bind("<Button-1>", self._on_click)
        self.canvas.bind("<Motion>", self._on_motion)
        self.canvas.bind("<Leave>", self._on_leave)

        self.status_var = tk.StringVar(value="")
        self.status_label = tk.Label(outer, textvariable=self.status_var, font=_font(10),
                                     bg=PAGE_BG, fg=MUTED_COLOR, anchor="w",
                                     justify="left", wraplength=520)
        self.status_label.pack(fill="x", pady=(10, 0))

    def _size_entry(self, parent, label, var, pad=(0, 0)):
        box = tk.Frame(parent, bg=PAGE_BG)
        tk.Label(box, text=label, font=_font(11), bg=PAGE_BG, fg=TEXT_COLOR).pack(side="left")
        entry = tk.Entry(box, textvariable=var, width=3, font=_font(11),
                         justify="center", relief="flat", bg="#ffffff",
                         highlightthickness=1, highlightbackground="#c9cfda",
                         highlightcolor=ACCENT, insertbackground=TEXT_COLOR)
        entry.pack(side="left", padx=(4, 0), ipady=2)
        entry.bind("<Return>", lambda event: self.new_game_from_entries())
        box.pack_configure(padx=pad)
        return box, entry

    def _button(self, parent, text, command, primary=False):
        bg = ACCENT if primary else "#ffffff"
        fg = "#ffffff" if primary else TEXT_COLOR
        active_bg = ACCENT_DARK if primary else "#e9edf5"
        return tk.Button(parent, text=text, command=command, font=_font(10, primary),
                         bg=bg, fg=fg, activebackground=active_bg, activeforeground=fg,
                         relief="flat", bd=0, padx=12, pady=5, cursor="hand2",
                         highlightthickness=0)

    def _bind_keys(self):
        for key in ("r", "R"):
            self.root.bind(f"<KeyPress-{key}>", lambda event: self._key_r())
        for key in ("u", "U", "z", "Z"):
            self.root.bind(f"<KeyPress-{key}>", lambda event: self.undo())
        for key in ("h", "H"):
            self.root.bind(f"<KeyPress-{key}>", lambda event: self._key_h())
        for key in ("e", "E"):
            self.root.bind(f"<KeyPress-{key}>", lambda event: self._key_e())
        for key in ("c", "C"):
            self.root.bind(f"<KeyPress-{key}>", lambda event: self._key_c())
        for key in ("f", "F"):
            self.root.bind(f"<KeyPress-{key}>", lambda event: self._key_f())
        for key in ("g", "G"):
            self.root.bind(f"<KeyPress-{key}>", lambda event: self.open_demo())
        for key in ("t", "T"):
            self.root.bind(f"<KeyPress-{key}>", lambda event: self.open_chase())
        self.root.bind("<KeyPress-Escape>", lambda event: self._key_escape())
        self.root.bind("<KeyPress-Return>", lambda event: self._key_return())

    def _center_window(self):
        self.root.update_idletasks()
        width = self.root.winfo_reqwidth()
        height = self.root.winfo_reqheight()
        x = max(0, (self.root.winfo_screenwidth() - width) // 2)
        y = max(0, (self.root.winfo_screenheight() - height) // 3)
        self.root.geometry(f"+{x}+{y}")

    # -------------------------------------------------- 一局游戏

    def new_game_from_entries(self):
        rows, ok_rows = self._read_size(self.rows_var, self.rows)
        cols, ok_cols = self._read_size(self.cols_var, self.cols)
        if not (ok_rows and ok_cols):
            self._set_status(f"大小需要是 {MIN_SIZE} ~ {MAX_SIZE} 的整数。", ERROR_COLOR)
            return
        self.new_game(rows, cols)

    @staticmethod
    def _read_size(var, current):
        text = var.get().strip()
        if not text.isdigit():
            return current, False
        value = int(text)
        if not MIN_SIZE <= value <= MAX_SIZE:
            return current, False
        return value, True

    def new_game(self, rows=None, cols=None):
        rows = self.rows if rows is None else max(MIN_SIZE, min(MAX_SIZE, int(rows)))
        cols = self.cols if cols is None else max(MIN_SIZE, min(MAX_SIZE, int(cols)))
        self.rows, self.cols = rows, cols
        self.rows_var.set(str(rows))
        self.cols_var.set(str(cols))
        self.board, _ = scramble(rows, cols, self.rng)
        self.history = []
        self.won = False
        self.hint_cell = None
        self.hover = None
        self.mode = "play"
        self.edit_history = []
        self._snapshot = None
        self._layout_board()
        self._refresh_mode()
        self._render()
        self._update_moves()
        self._set_status(
            "开局：点击任意方块翻转十字，全部变白即通关。"
            "U 撤销，H 提示，E 自定义黑块，G 消元演示，T 追白法演示。")

    # -------------------------------------------------- 自定义黑块（编辑模式）

    def enter_edit(self):
        if self.mode == "edit":
            return
        self._snapshot = ([row[:] for row in self.board], list(self.history), self.won)
        self.mode = "edit"
        self.edit_history = []
        self.hint_cell = None
        self.hover = None
        self._refresh_mode()
        self._render()
        self._update_moves()
        self._update_edit_status()

    def exit_edit(self):
        if self._snapshot is not None:
            board, history, won = self._snapshot
            self.board = [row[:] for row in board]
            self.history = list(history)
            self.won = won
        self._snapshot = None
        self.mode = "play"
        self.hint_cell = None
        self.hover = None
        self._refresh_mode()
        self._render()
        self._update_moves()
        self._set_status("已返回对局。")

    def start_custom(self):
        black = sum(sum(row) for row in self.board)
        if black == 0:
            self._set_status("全白开局没法玩：先点几个格子摆黑块，或点“随机”。", ERROR_COLOR)
            return
        basis, _ = syndrome_tools(self.rows, self.cols)
        solvable = mask_syndrome(basis, board_mask(self.board, self.cols)) == 0
        self.mode = "play"
        self._snapshot = None
        self.edit_history = []
        self.history = []
        self.won = False
        self.hint_cell = None
        self.hover = None
        self._refresh_mode()
        self._render()
        self._update_moves()
        if solvable:
            self._set_status(
                f"自定义开局（{black} 个黑块，保证有解）：点击方块翻转十字，全部变白即通关。")
        else:
            self._set_status(
                f"自定义开局（{black} 个黑块）：这个布局无解——不存在任何能全白的点法。"
                "可以随便试；想看“为什么无解”，按 G（高斯消元演示）或 T（追白法演示）。",
                ERROR_COLOR)

    def toggle_cell(self, r, c):
        self.board[r][c] ^= 1
        self.edit_history.append((r, c))
        self._render()
        self._update_moves()
        self._update_edit_status()

    def clear_board(self):
        self.board = [[0] * self.cols for _ in range(self.rows)]
        self.edit_history = []
        self._render()
        self._update_moves()
        self._set_status("已清空：现在全是白块，点格子开始摆黑块（或点“随机”）。")

    def random_edit_board(self):
        self.board, _ = scramble(self.rows, self.cols, self.rng)
        self.edit_history = []
        self._render()
        self._update_moves()
        self._update_edit_status("已生成随机可解布局：")

    def auto_fix(self):
        basis, cols_syn = syndrome_tools(self.rows, self.cols)
        target = mask_syndrome(basis, board_mask(self.board, self.cols))
        if target == 0:
            self._update_edit_status("当前布局本来就可解：")
            return
        fix = syndrome_fix(basis, cols_syn, target)
        if fix is None:
            self._set_status("没有找到小改动（≤3 格）的修正方案，请手动微调或点“随机”。",
                             ERROR_COLOR)
            return
        changed = []
        for i in range(self.rows * self.cols):
            if (fix >> i) & 1:
                r, c = divmod(i, self.cols)
                self.board[r][c] ^= 1
                self.edit_history.append((r, c))
                changed.append((r, c))
        note = ""
        if not has_black(self.board):
            # 修正后如果凑巧变成全白，补一次随机点击，给一个能玩的可解开局
            r, c = self.rng.randrange(self.rows), self.rng.randrange(self.cols)
            press(self.board, r, c)
            for nr, nc in neighbors(self.rows, self.cols, r, c):
                self.edit_history.append((nr, nc))
            note = "；修正后是全白，已补一次随机点击"
        self._render()
        self._update_moves()
        spots = "、".join(f"({r + 1},{c + 1})" for r, c in changed[:6])
        self._update_edit_status(f"已修正 {len(changed)} 处（{spots}）{note}：")

    def _update_edit_status(self, prefix=""):
        basis, _ = syndrome_tools(self.rows, self.cols)
        mask = board_mask(self.board, self.cols)
        solvable = mask_syndrome(basis, mask) == 0
        black = mask.bit_count()
        head = (prefix + " ") if prefix else ""
        if solvable and black:
            self._set_status(
                f"{head}编辑中（{black} 个黑块）：布局可解，按“开始游戏”或 Enter 开局。", WIN_COLOR)
        elif solvable:
            self._set_status(f"{head}编辑中（0 个黑块）：点格子摆黑块，或点“随机”。")
        else:
            self._set_status(
                f"{head}编辑中（{black} 个黑块）：该布局无解——建议修正"
                "（点“建议修正”自动改成可解），也可以直接开始看演示。", ERROR_COLOR)

    def _refresh_mode(self):
        editing = self.mode == "edit"
        state = "disabled" if editing else "normal"
        self.rows_entry.config(state=state)
        self.cols_entry.config(state=state)
        self.play_buttons.pack_forget()
        self.edit_buttons.pack_forget()
        if editing:
            self.edit_buttons.pack(side="left", padx=(12, 0))
            self.root.title(f"黑白反转 · {self.rows}x{self.cols} · 编辑中")
        else:
            self.play_buttons.pack(side="left", padx=(12, 0))
            self.root.title(f"黑白反转 · {self.rows}x{self.cols}")

    def _key_r(self):
        if self.mode == "edit":
            self.random_edit_board()
        else:
            self.new_game()

    def _key_h(self):
        if self.mode == "play":
            self.hint()

    def _key_e(self):
        if self.mode == "play":
            self.enter_edit()

    def _key_c(self):
        if self.mode == "edit":
            self.clear_board()

    def _key_f(self):
        if self.mode == "edit":
            self.auto_fix()

    def _key_escape(self):
        if self.mode == "edit":
            self.exit_edit()

    def _key_return(self):
        if self.mode == "edit":
            self.start_custom()

    def open_demo(self):
        total = self.rows * self.cols
        if total > GaussDemo.MAX_CELLS:
            self._set_status(
                f"消元演示最多支持 {GaussDemo.MAX_CELLS} 格（当前 {total} 格）："
                "矩阵画不下。把行或列改小一点（比如 5x6、6x6）就能看完整过程。", ERROR_COLOR)
            return
        demo = self._demo
        if demo is not None and demo.win.winfo_exists():
            demo.win.lift()
            demo.win.focus_set()
            return
        self._demo = GaussDemo(self.root, self.board, on_close=self._demo_closed)

    def _demo_closed(self):
        self._demo = None

    def open_chase(self):
        demo = self._chase
        if demo is not None and demo.win.winfo_exists():
            demo.win.lift()
            demo.win.focus_set()
            return
        self._chase = ChaseDemo(self.root, self.board, on_close=self._chase_closed)

    def _chase_closed(self):
        self._chase = None

    # -------------------------------------------------- 棋盘绘制

    def _layout_board(self):
        span = max(self.rows, self.cols)
        self.tile = max(22, min(88, 620 // span))
        self.gap = max(3, self.tile // 8)
        width = self.cols * (self.tile + self.gap) + self.gap
        height = self.rows * (self.tile + self.gap) + self.gap
        self.canvas.config(width=width, height=height)
        self.canvas.delete("all")
        self.tile_ids = [[None] * self.cols for _ in range(self.rows)]
        radius = max(6, self.tile // 6)
        for r in range(self.rows):
            for c in range(self.cols):
                x1, y1 = self._tile_origin(r, c)
                self.tile_ids[r][c] = self._round_rect(
                    x1, y1, x1 + self.tile, y1 + self.tile, radius,
                    fill=TILE_WHITE, outline=TILE_WHITE_EDGE, width=1)
        self.status_label.config(wraplength=max(420, width))

    def _tile_origin(self, r, c):
        step = self.tile + self.gap
        return self.gap + c * step, self.gap + r * step

    def _round_rect(self, x1, y1, x2, y2, radius, **kwargs):
        points = (
            x1 + radius, y1, x2 - radius, y1, x2, y1,
            x2, y1 + radius, x2, y2 - radius, x2, y2,
            x2 - radius, y2, x1 + radius, y2, x1, y2,
            x1, y2 - radius, x1, y1 + radius, x1, y1,
        )
        kwargs.setdefault("smooth", True)
        return self.canvas.create_polygon(points, **kwargs)

    def _render(self):
        for r in range(self.rows):
            for c in range(self.cols):
                black = bool(self.board[r][c])
                self.canvas.itemconfigure(
                    self.tile_ids[r][c],
                    fill=TILE_BLACK if black else TILE_WHITE,
                    outline=TILE_BLACK_EDGE if black else TILE_WHITE_EDGE)
        self._render_marks()

    def _render_marks(self):
        self.canvas.delete("mark")
        radius = max(6, self.tile // 6)
        if self.hint_cell is not None and self.mode == "play":
            r, c = self.hint_cell
            x1, y1 = self._tile_origin(r, c)
            self._round_rect(x1, y1, x1 + self.tile, y1 + self.tile, radius,
                             fill="", outline=HINT_COLOR, width=3, tags="mark")
        if self.hover is not None and (self.mode == "edit" or not self.won):
            if self.mode == "edit":
                r, c = self.hover
                x1, y1 = self._tile_origin(r, c)
                self._round_rect(x1, y1, x1 + self.tile, y1 + self.tile, radius,
                                 fill="", outline=ACCENT, width=3, tags="mark")
            else:
                hr, hc = self.hover
                for r, c in neighbors(self.rows, self.cols, hr, hc):
                    x1, y1 = self._tile_origin(r, c)
                    width = 3 if (r, c) == self.hover else 2
                    self._round_rect(x1, y1, x1 + self.tile, y1 + self.tile, radius,
                                     fill="", outline=ACCENT, width=width, tags="mark")

    # -------------------------------------------------- 交互

    def _cell_at(self, event):
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        step = self.tile + self.gap
        c = int((x - self.gap) // step)
        r = int((y - self.gap) // step)
        if 0 <= r < self.rows and 0 <= c < self.cols:
            inside_x = x - (self.gap + c * step) <= self.tile
            inside_y = y - (self.gap + r * step) <= self.tile
            if inside_x and inside_y:
                return r, c
        return None

    def _on_click(self, event):
        cell = self._cell_at(event)
        if cell is None:
            return
        if self.mode == "edit":
            self.toggle_cell(*cell)
        else:
            self.play(*cell)

    def _on_motion(self, event):
        if self.mode == "play" and self.won:
            cell = None
        else:
            cell = self._cell_at(event)
        if cell != self.hover:
            self.hover = cell
            self._render_marks()

    def _on_leave(self, event):
        if self.hover is not None:
            self.hover = None
            self._render_marks()

    def play(self, r, c):
        if self.won:
            self._set_status("已经通关啦，按 R 或点“新游戏”再来一局。", WIN_COLOR)
            return
        press(self.board, r, c)
        self.history.append((r, c))
        self.hint_cell = None
        self._render()
        self._update_moves()
        if not has_black(self.board):
            self.won = True
            self.hover = None
            self._render()
            self._set_status(
                f"🎉 全部变白！一共 {len(self.history)} 步。按 R 或点“新游戏”再来一局。",
                WIN_COLOR)
        else:
            self._set_status(f"已用 {len(self.history)} 步，继续。U 撤销，H 提示。")

    def undo(self):
        if self.mode == "edit":
            if not self.edit_history:
                self._set_status("编辑没有可撤销的操作。", MUTED_COLOR)
                return
            r, c = self.edit_history.pop()
            self.board[r][c] ^= 1
            self._render()
            self._update_moves()
            self._update_edit_status("已撤销一步：")
            return
        if not self.history:
            self._set_status("没有可撤销的步骤。", MUTED_COLOR)
            return
        r, c = self.history.pop()
        press(self.board, r, c)  # 点击是自反操作，再点一次即撤销
        self.won = False
        self.hint_cell = None
        self._render()
        self._update_moves()
        self._set_status(f"已撤销一步，当前 {len(self.history)} 步。")

    def hint(self):
        if self.won:
            self._set_status("已经全部变白，不需要提示啦。", WIN_COLOR)
            return
        solution = solve(self.board)
        if solution is None:
            self._set_status(
                "这个局面无解：不存在任何点击组合能把它全部变白。"
                "按 G 或 T 看演示，会走到 0 = 1 的矛盾行，说明为什么无解。", ERROR_COLOR)
            return
        if solution == 0:
            self._set_status("棋盘已经全白。", WIN_COLOR)
            return
        index = (solution & -solution).bit_length() - 1
        self.hint_cell = divmod(index, self.cols)
        self._render_marks()
        steps = solution.bit_count()
        basis, _ = syndrome_tools(self.rows, self.cols)
        if basis and len(basis) <= 12:
            self._set_status(
                f"提示：这个局面有多组解（共 {2 ** len(basis)} 组），"
                f"橙色方框是其中一组解的下一步（这一组约 {steps} 步）。", HINT_COLOR)
        elif basis:
            self._set_status(
                f"提示：这个局面有多组解，橙色方框是其中一组解的下一步"
                f"（这一组约 {steps} 步）。", HINT_COLOR)
        else:
            self._set_status(
                f"提示：橙色方框是可行的一步，完整走法约 {steps} 步（不一定最少）。",
                HINT_COLOR)

    def _update_moves(self):
        if self.mode == "edit":
            self.moves_var.set(f"黑块 {sum(sum(row) for row in self.board)}")
        else:
            self.moves_var.set(f"步数 {len(self.history)}")

    def _set_status(self, text, color=MUTED_COLOR):
        self.status_var.set(text)
        self.status_label.config(fg=color)

    def run(self):
        self.root.mainloop()


class GaussDemo:
    """高斯消元求解过程的可视化演示窗口。

    左边是增广矩阵（行 = 每个格子的方程，列 = 该格点/不点的未知数，
    最右一列是右端项，也就是棋盘当前的黑白）；右边是棋盘预览。
    单步播放时高亮当前的主元行、被消掉的行，最后把解应用回棋盘。
    """

    MAX_CELLS = 36

    def __init__(self, master, board, on_close=None):
        self.rows = len(board)
        self.cols = len(board[0])
        self.n = self.rows * self.cols
        self.original = [row[:] for row in board]
        self.preview = [row[:] for row in board]
        self.events = list(elimination_steps(board))
        self.index = -1
        self.snapshot = []
        self.focus = {}
        self.playing = False
        self.solution = None
        self.applied = False
        self.press_queue = []
        self.press_total = 0
        self.apply_timer = None
        self.on_close = on_close
        self.cell = max(11, min(16, 520 // max(self.n, 1)))

        self.win = tk.Toplevel(master)
        self.win.title("高斯消元演示 · 黑白反转")
        self.win.configure(bg=PAGE_BG)
        self.win.resizable(False, False)
        self.win.protocol("WM_DELETE_WINDOW", self.close)
        self._build()
        self._bind()
        self._draw_preview()
        self._advance()
        self.win.lift()

    # -------------------------------------------------- 界面

    def _build(self):
        outer = tk.Frame(self.win, bg=PAGE_BG, padx=14, pady=12)
        outer.pack(fill="both", expand=True)

        matrix_w = 2 + self.n * self.cell + 6 + self.cell + 2
        matrix_h = 2 + self.n * self.cell + 2
        panel_w = max(360, matrix_w + 14 + 232)

        self.info_var = tk.StringVar(value="")
        tk.Label(outer, textvariable=self.info_var, font=_font(10), bg=PAGE_BG,
                 fg=TEXT_COLOR, wraplength=panel_w, justify="left",
                 anchor="w").pack(fill="x")

        body = tk.Frame(outer, bg=PAGE_BG)
        body.pack(fill="both", pady=(10, 8))

        self.canvas = tk.Canvas(body, bg="#ffffff", highlightthickness=1,
                                highlightbackground="#d3d8e2",
                                width=matrix_w, height=matrix_h)
        self.canvas.pack(side="left", anchor="n")

        side = tk.Frame(body, bg=PAGE_BG)
        side.pack(side="left", anchor="n", fill="y", padx=14)

        tk.Label(side, text="棋盘预览", font=_font(10, True), bg=PAGE_BG,
                 fg=TEXT_COLOR).pack(anchor="w")
        self.preview_cell = max(18, min(30, 200 // max(self.rows, self.cols)))
        self.preview_canvas = tk.Canvas(
            side, bg=CANVAS_BG, highlightthickness=0,
            width=self.cols * (self.preview_cell + 3) + 3,
            height=self.rows * (self.preview_cell + 3) + 3)
        self.preview_canvas.pack(anchor="w", pady=(4, 8))

        self.solution_var = tk.StringVar(value="解会显示在这里。")
        tk.Label(side, textvariable=self.solution_var, font=_font(9), bg=PAGE_BG,
                 fg=MUTED_COLOR, wraplength=210, justify="left").pack(anchor="w")

        self._button(side, "上一步 (B)", self.previous_step).pack(
            anchor="w", fill="x", pady=(10, 2))
        self._button(side, "下一步 (空格)", self.next_step, primary=True).pack(
            anchor="w", fill="x", pady=2)
        self.play_button = self._button(side, "自动播放 (A)", self.toggle_play)
        self.play_button.pack(anchor="w", fill="x", pady=2)
        self._button(side, "跳到最后", self.jump_to_end).pack(anchor="w", fill="x", pady=2)
        self._button(side, "重新演示", self.reset).pack(anchor="w", fill="x", pady=2)
        self.apply_button = self._button(side, "应用到棋盘", self.apply_solution)
        self.apply_button.pack(anchor="w", fill="x", pady=2)
        self.apply_button.config(state="disabled")
        self._button(side, "关闭 (Esc)", self.close).pack(anchor="w", fill="x", pady=2)

        tk.Label(side, text="矩阵：行 = 每个格子的方程，列 = 该格点/不点的未知数；"
                            "空白 = 0，蓝格 = 1，最右列 = 棋盘当前颜色。",
                 font=_font(8), bg=PAGE_BG, fg=MUTED_COLOR, wraplength=210,
                 justify="left").pack(anchor="w", pady=(8, 0))

    def _button(self, parent, text, command, primary=False):
        bg = ACCENT if primary else "#ffffff"
        fg = "#ffffff" if primary else TEXT_COLOR
        active = ACCENT_DARK if primary else "#e9edf5"
        return tk.Button(parent, text=text, command=command, font=_font(9, primary),
                         bg=bg, fg=fg, activebackground=active, activeforeground=fg,
                         relief="flat", bd=0, padx=10, pady=4, cursor="hand2",
                         highlightthickness=0)

    def _bind(self):
        self.win.bind("<KeyPress-space>", lambda event: self.next_step())
        self.win.bind("<KeyPress-Return>", lambda event: self.next_step())
        for key in ("a", "A"):
            self.win.bind(f"<KeyPress-{key}>", lambda event: self.toggle_play())
        for key in ("b", "B"):
            self.win.bind(f"<KeyPress-{key}>", lambda event: self.previous_step())
        self.win.bind("<KeyPress-BackSpace>", lambda event: self.previous_step())
        self.win.bind("<KeyPress-Escape>", lambda event: self.close())

    # -------------------------------------------------- 播放控制

    def next_step(self):
        self._stop_play()
        self._advance()

    def _advance(self):
        if self.index >= len(self.events) - 1:
            return
        self.index += 1
        (tag, payload), snapshot = self.events[self.index]
        self.snapshot = snapshot
        self._narrate(tag, payload)
        self._draw_matrix()

    def toggle_play(self):
        if self.playing:
            self._stop_play()
            return
        if self.index >= len(self.events) - 1:
            return
        self.playing = True
        self.play_button.config(text="暂停 (A)")
        self.win.after(250, self._tick_play)

    def _tick_play(self):
        if not self.playing or not self.win.winfo_exists():
            return
        if self.index >= len(self.events) - 1:
            self._stop_play()
            return
        self._advance()
        if self.playing:
            self.win.after(300, self._tick_play)

    def _stop_play(self):
        if self.playing:
            self.playing = False
            self.play_button.config(text="自动播放 (A)")

    def jump_to_end(self):
        self._stop_play()
        if self.index < len(self.events) - 1:
            self.index = len(self.events) - 1
            (tag, payload), snapshot = self.events[self.index]
            self.snapshot = snapshot
            self._narrate(tag, payload)
            self._draw_matrix()

    def _cancel_apply(self):
        if self.apply_timer is not None:
            try:
                self.win.after_cancel(self.apply_timer)
            except tk.TclError:
                pass
            self.apply_timer = None
        self.solution = None
        self.applied = False
        self.press_queue = []
        self.preview = [row[:] for row in self.original]
        self.solution_var.set("解会显示在这里。")
        self.apply_button.config(state="disabled")
        self._draw_preview()

    def previous_step(self):
        self._stop_play()
        if self.index <= 0:
            return
        self._cancel_apply()
        self.index -= 1
        (tag, payload), snapshot = self.events[self.index]
        self.snapshot = snapshot
        self._narrate(tag, payload)
        self._draw_matrix()

    def reset(self):
        self._stop_play()
        self._cancel_apply()
        self.index = -1
        self._advance()

    def close(self):
        self._stop_play()
        callback = self.on_close
        self.on_close = None
        if callback is not None:
            callback()
        if self.win.winfo_exists():
            self.win.destroy()

    # -------------------------------------------------- 应用解

    def apply_solution(self, animate=True):
        if self.solution is None or self.applied:
            return
        self.applied = True
        self.press_queue = [i for i in range(self.n) if (self.solution >> i) & 1]
        self.press_total = len(self.press_queue)
        if animate and self.press_queue:
            self._tick_apply()
            return
        while self.press_queue:
            i = self.press_queue.pop(0)
            press(self.preview, i // self.cols, i % self.cols)
        self._draw_preview()
        self._finish_apply()

    def _tick_apply(self):
        if not self.win.winfo_exists():
            return
        if self.press_queue:
            i = self.press_queue.pop(0)
            press(self.preview, i // self.cols, i % self.cols)
            self._draw_preview()
            self.solution_var.set(f"正在应用解……还剩 {len(self.press_queue)} 步")
            self.apply_timer = self.win.after(150, self._tick_apply)
        else:
            self._finish_apply()

    def _finish_apply(self):
        self.apply_timer = None
        if has_black(self.preview):
            self.solution_var.set("应用解之后还有黑块（不应该发生）")
        else:
            self.solution_var.set(f"已按解点击 {self.press_total} 步，棋盘全部变白 ✓")

    # -------------------------------------------------- 绘制

    def _narrate(self, tag, payload):
        total = len(self.events) - 1
        prefix = "准备 · " if tag == "start" else f"第 {self.index} / {total} 步 · "
        self.focus = {}
        if tag == "start":
            text = (f"开局：{self.n} 个未知数（每格点或不点）× {self.n} 个方程（每格最后都要变白）。"
                    "右边一列是棋盘当前颜色，黑 = 1，白 = 0。")
        elif tag == "pivot":
            row, col = payload
            self.focus = {"pivot": (row, col)}
            text = (f"第 {row + 1} 行第 {col + 1} 列是主元 1：拿这一行做主元行，"
                    f"去消掉其它行第 {col + 1} 列的 1。")
        elif tag == "swap":
            old, new, col = payload
            self.focus = {"pivot": (new, col), "rows": [old, new]}
            text = f"第 {new + 1} 行和第 {old + 1} 行交换，让第 {col + 1} 列的主元落到第 {new + 1} 行。"
        elif tag == "eliminate":
            target, prow, col = payload
            self.focus = {"pivot": (prow, col), "rows": [target]}
            text = (f"第 {target + 1} 行第 {col + 1} 列是 1：把第 {target + 1} 行整体异或主元行"
                    f"（第 {prow + 1} 行），这一列就消成 0，其它列同步更新。")
        elif tag == "free":
            (col,) = payload
            self.focus = {"col": col}
            text = (f"第 {col + 1} 列整列都是 0，没有主元：第 {col + 1} 格是一个“自由变量”——"
                    "点或不点都可以，说明这个局面有多组解（点法不唯一）。"
                    "演示里默认取 0（不点这一格）。")
        elif tag == "consistent":
            text = "消元结束，没有出现 0 = 1 的矛盾行：当前局面有解。现在从每个主元行直接读出未知数。"
        elif tag == "contradiction":
            (row,) = payload
            self.focus = {"bad": row}
            text = (f"第 {row + 1} 行剩下 0 = 1：无解！这说明“每个格子都要变白”的要求互相矛盾，"
                    "任何点法都不可能同时满足。演示到此结束，没有解可以应用"
                    "（回游戏里可以点“建议修正”一键改成可解布局）。")
        elif tag == "solve":
            col, row, bit = payload
            r, c = divmod(col, self.cols)
            self.focus = {"pivot": (row, col)}
            text = f"格子 ({r + 1},{c + 1}) 对应的未知数 = {bit}：{'要点' if bit else '不点'}。"
        else:  # done
            mask = payload
            self.solution = mask
            clicks = [divmod(i, self.cols) for i in range(self.n) if (mask >> i) & 1]
            spots = "、".join(f"({r + 1},{c + 1})" for r, c in clicks) or "无（已经全白）"
            free_count = sum(1 for event, _snap in self.events if event[0] == "free")
            if not free_count:
                note = ""
            elif free_count <= 10:
                note = (f"注意：这个局面有多组解——自由变量有 {free_count} 个，"
                        f"共 2^{free_count} = {2 ** free_count} 组可行点法"
                        "（演示取的是自由变量全为 0 的那一组）。")
            else:
                note = ("注意：这个局面有多组解（自由变量很多），"
                        "演示取的是自由变量全为 0 的那一组。")
            text = (f"解出来了：一共点 {len(clicks)} 个格子 → {spots}。{note}"
                    "点“应用到棋盘”看看效果。")
            self.solution_var.set(f"需要点击：{spots}\n总步数：{len(clicks)}")
            self.apply_button.config(state="normal")
        self.info_var.set(prefix + text)

    def _draw_matrix(self):
        canvas = self.canvas
        canvas.delete("all")
        cell = self.cell
        n = self.n
        pivot = self.focus.get("pivot")
        focus_rows = set(self.focus.get("rows", []))
        focus_col = self.focus.get("col")
        bad_row = self.focus.get("bad")
        font = ("Consolas", max(8, cell - 6))
        for i in range(n):
            for j in range(n):
                x1 = 2 + j * cell
                y1 = 2 + i * cell
                bit = (self.snapshot[i] >> j) & 1
                fill = "#c7dbff" if bit else "#ffffff"
                if focus_col == j and not bit:
                    fill = "#fef3c7"
                if pivot == (i, j):
                    fill = "#fbbf24"
                if bad_row == i:
                    fill = "#fecaca"
                canvas.create_rectangle(x1, y1, x1 + cell, y1 + cell,
                                        fill=fill, outline="#e5e7eb")
                if bit:
                    canvas.create_text(x1 + cell / 2, y1 + cell / 2, text="1",
                                       font=font, fill="#0f172a")
            rhs_x = 2 + n * cell + 6
            rhs = (self.snapshot[i] >> n) & 1
            canvas.create_rectangle(rhs_x, y1, rhs_x + cell, y1 + cell,
                                    fill="#1f232b" if rhs else "#eef1f6",
                                    outline="#cbd5e1")
            if rhs:
                canvas.create_text(rhs_x + cell / 2, y1 + cell / 2, text="1",
                                   font=font, fill="#ffffff")
            if i in focus_rows:
                canvas.create_rectangle(1, y1 - 1, rhs_x + cell, y1 + cell + 1,
                                        outline="#10b981", width=2)
            if bad_row == i:
                canvas.create_rectangle(1, y1 - 1, rhs_x + cell, y1 + cell + 1,
                                        outline="#dc2626", width=2)
        if pivot is not None:
            row, col = pivot
            canvas.create_rectangle(2 + col * cell, 2 + row * cell,
                                    2 + (col + 1) * cell, 2 + (row + 1) * cell,
                                    outline="#b45309", width=2)

    def _draw_preview(self):
        canvas = self.preview_canvas
        canvas.delete("all")
        cell = self.preview_cell
        for r in range(self.rows):
            for c in range(self.cols):
                x1 = 3 + c * (cell + 3)
                y1 = 3 + r * (cell + 3)
                black = bool(self.preview[r][c])
                canvas.create_rectangle(
                    x1, y1, x1 + cell, y1 + cell,
                    fill=TILE_BLACK if black else TILE_WHITE,
                    outline=TILE_BLACK_EDGE if black else TILE_WHITE_EDGE)


class ChaseDemo:
    """追白法演示：第一遍不碰第一行，最后一行残留直接决定第一行点法。

    流程：第一行不点 → 逐行追白 → 高亮最后一行残留 r → 用固定的
    响应矩阵 M 解出第一行点法 p（先列出方程组，再逐位代入 r 算出每个 p，
    并高亮用到的格子）→ 第二遍按 p 追白 → 全白。
    """

    def __init__(self, master, board, on_close=None):
        self.rows = len(board)
        self.cols = len(board[0])
        self.original = [row[:] for row in board]
        self.board = [row[:] for row in board]
        self.on_close = on_close
        self.playing = False
        self.first_clicks = 0
        self.second_clicks = 0
        self.residual = None
        self.p_mask = None
        self.true_p = None
        self.calc_index = None
        self.p_bits = [None] * self.cols
        self.inv_cols = None
        self.inv_terms = None
        self.walkthrough = False
        self.theory = None
        self.markers = {}
        self._full_rank = None
        self.actions = self._plan()
        self.index = -1
        self.tile = max(18, min(52, 400 // max(self.rows, self.cols)))
        self.gap = max(3, self.tile // 8)

        self.win = tk.Toplevel(master)
        self.win.title("追白法演示 · 黑白反转")
        self.win.configure(bg=PAGE_BG)
        self.win.resizable(False, False)
        self.win.protocol("WM_DELETE_WINDOW", self.close)
        self._build()
        self._bind()
        self._render()
        self._update_panel()
        self._advance()
        self.win.lift()

    # -------------------------------------------------- 演示脚本

    def _plan(self):
        actions = [("note", "第一遍：第一行一格都不点，从上往下追白——"
                            "看到上一行哪格是黑的，就点它正下方那格。")]
        after, presses = chase_presses(self.original)
        for r in range(1, self.rows):
            cells = [cell for cell in presses if cell[0] == r]
            if cells:
                actions.append(("press", cells))
        residual = 0
        for c in range(self.cols):
            if after[self.rows - 1][c]:
                residual |= 1 << c
        actions.append(("residue", residual))
        top_mask = first_row_for_chase(self.rows, self.cols, residual)
        if top_mask is None:
            actions.append(("dead", None))
            return actions
        self.walkthrough = self.cols <= 8 and self._rank_full()
        if self.walkthrough:
            self._ensure_inverse()
            actions.append(("system", top_mask))
            for i in range(self.cols):
                actions.append(("calc", i))
        actions.append(("solve", top_mask))
        actions.append(("reset", None))
        actions.append(("top", top_mask))
        top = tuple(c for c in range(self.cols) if (top_mask >> c) & 1)
        if top:
            actions.append(("press", [(0, c) for c in top]))
        _, second = chase_presses(self.original, top)
        for r in range(1, self.rows):
            cells = [cell for cell in second if cell[0] == r]
            if cells:
                actions.append(("press", cells))
        actions.append(("done", len(second)))
        return actions

    def _bits(self, mask):
        return " ".join(str((mask >> c) & 1) for c in range(self.cols))

    def _rank_full(self):
        if self._full_rank is None:
            self._full_rank = _gf2_rank(chase_columns(self.rows, self.cols), self.cols) == self.cols
        return self._full_rank

    def _ensure_inverse(self):
        """预计算反查表：每个 p_i 等于哪些 r_j 的异或。"""
        if self.inv_cols is None:
            self.inv_cols = [first_row_for_chase(self.rows, self.cols, 1 << j)
                             for j in range(self.cols)]
            self.inv_terms = [[j for j in range(self.cols)
                               if (self.inv_cols[j] >> i) & 1]
                              for i in range(self.cols)]
        return self.inv_cols

    def _equation_text(self):
        """把 M·p = r 写成一条条方程，右端代入当前 r 的数字。"""
        columns = chase_columns(self.rows, self.cols)
        lines = []
        for c in range(self.cols):
            terms = [i for i in range(self.cols) if (columns[i] >> c) & 1]
            left = " ⊕ ".join(f"p{i + 1}" for i in terms) or "0"
            lines.append(f"最后一行第{c + 1}格: {left} = {(self.residual >> c) & 1}")
        return "\n".join(lines)

    # -------------------------------------------------- 界面

    def _build(self):
        outer = tk.Frame(self.win, bg=PAGE_BG, padx=14, pady=12)
        outer.pack(fill="both", expand=True)

        board_w = self.cols * (self.tile + self.gap) + self.gap
        board_h = self.rows * (self.tile + self.gap) + self.gap

        self.info_var = tk.StringVar(value="")
        tk.Label(outer, textvariable=self.info_var, font=_font(10), bg=PAGE_BG,
                 fg=TEXT_COLOR, wraplength=max(420, board_w + 260), justify="left",
                 anchor="w").pack(fill="x")

        body = tk.Frame(outer, bg=PAGE_BG)
        body.pack(fill="both", pady=(10, 0))
        self.canvas = tk.Canvas(body, bg=CANVAS_BG, highlightthickness=1,
                                highlightbackground="#d3d8e2",
                                width=board_w, height=board_h)
        self.canvas.pack(side="left", anchor="n")

        side = tk.Frame(body, bg=PAGE_BG)
        side.pack(side="left", anchor="n", fill="y", padx=14)

        tk.Label(side, text="最后一行残留 r", font=_font(10, True), bg=PAGE_BG,
                 fg=TEXT_COLOR).pack(anchor="w")
        self.residual_var = tk.StringVar(value="？")
        tk.Label(side, textvariable=self.residual_var, font=("Consolas", 10),
                 bg=PAGE_BG, fg=HINT_COLOR).pack(anchor="w", pady=(2, 8))

        tk.Label(side, text="第一行点法 p", font=_font(10, True), bg=PAGE_BG,
                 fg=TEXT_COLOR).pack(anchor="w")
        self.p_var = tk.StringVar(value="？")
        tk.Label(side, textvariable=self.p_var, font=("Consolas", 10),
                 bg=PAGE_BG, fg=ACCENT).pack(anchor="w", pady=(2, 8))

        self.system_title = tk.Label(side, text="方程组（r 是右端项）", font=_font(8),
                                     bg=PAGE_BG, fg=MUTED_COLOR)
        self.system_title.pack(anchor="w")
        self.system_var = tk.StringVar(value="")
        tk.Label(side, textvariable=self.system_var, font=("Consolas", 8),
                 bg=PAGE_BG, fg=TEXT_COLOR, wraplength=255, justify="left",
                 anchor="w").pack(anchor="w", pady=(0, 6))

        self.formula_title = tk.Label(side, text="逐位解出 p", font=_font(8),
                                      bg=PAGE_BG, fg=MUTED_COLOR)
        self.formula_title.pack(anchor="w")
        self.formula_var = tk.StringVar(value="")
        tk.Label(side, textvariable=self.formula_var, font=("Consolas", 9),
                 bg=PAGE_BG, fg=MUTED_COLOR, wraplength=250, justify="left",
                 anchor="w").pack(anchor="w")

        self.stats_var = tk.StringVar(value="")
        tk.Label(side, textvariable=self.stats_var, font=_font(9), bg=PAGE_BG,
                 fg=MUTED_COLOR, wraplength=250, justify="left").pack(anchor="w", pady=(8, 0))

        self._button(side, "上一步 (B)", self.previous_step).pack(
            anchor="w", fill="x", pady=(10, 2))
        self._button(side, "下一步 (空格)", self.next_step, primary=True).pack(
            anchor="w", fill="x", pady=2)
        self.play_button = self._button(side, "自动播放 (A)", self.toggle_play)
        self.play_button.pack(anchor="w", fill="x", pady=2)
        self._button(side, "跳到最后", self.jump_to_end).pack(anchor="w", fill="x", pady=2)
        self._button(side, "重新演示", self.reset).pack(anchor="w", fill="x", pady=2)
        self._button(side, "原理讲解 (P)", self.open_theory).pack(anchor="w", fill="x", pady=2)
        self._button(side, "关闭 (Esc)", self.close).pack(anchor="w", fill="x", pady=2)

        tk.Label(side, text="橙色 = 最后一行残留；紫色 = 当前式子用到的格子；"
                            "蓝色 = 第一行该点的格子；绿色 = 正在点的格子。",
                 font=_font(8), bg=PAGE_BG, fg=MUTED_COLOR, wraplength=250,
                 justify="left").pack(anchor="w", pady=(8, 0))

    def _button(self, parent, text, command, primary=False):
        bg = ACCENT if primary else "#ffffff"
        fg = "#ffffff" if primary else TEXT_COLOR
        active = ACCENT_DARK if primary else "#e9edf5"
        return tk.Button(parent, text=text, command=command, font=_font(9, primary),
                         bg=bg, fg=fg, activebackground=active, activeforeground=fg,
                         relief="flat", bd=0, padx=10, pady=4, cursor="hand2",
                         highlightthickness=0)

    def _bind(self):
        self.win.bind("<KeyPress-space>", lambda event: self.next_step())
        self.win.bind("<KeyPress-Return>", lambda event: self.next_step())
        for key in ("a", "A"):
            self.win.bind(f"<KeyPress-{key}>", lambda event: self.toggle_play())
        for key in ("b", "B"):
            self.win.bind(f"<KeyPress-{key}>", lambda event: self.previous_step())
        self.win.bind("<KeyPress-BackSpace>", lambda event: self.previous_step())
        for key in ("p", "P"):
            self.win.bind(f"<KeyPress-{key}>", lambda event: self.open_theory())
        self.win.bind("<KeyPress-Escape>", lambda event: self.close())

    # -------------------------------------------------- 播放控制

    def next_step(self):
        self._stop_play()
        self._advance()

    def _advance(self):
        if self.index >= len(self.actions) - 1:
            return
        self.index += 1
        tag, payload = self.actions[self.index]
        self.markers = {}
        if tag == "note":
            text = payload
        elif tag == "press":
            for r, c in payload:
                press(self.board, r, c)
            if self.p_mask is None:
                self.first_clicks += len(payload)
            else:
                self.second_clicks += len(payload)
            self.markers = {"flash": list(payload)}
            spots = "、".join(f"({r + 1},{c + 1})" for r, c in payload[:8])
            if len(payload) > 8:
                spots += " 等"
            text = f"点 {len(payload)} 格：{spots}"
        elif tag == "residue":
            self.residual = payload
            self.markers = {"bottom": [c for c in range(self.cols) if (payload >> c) & 1]}
            text = (f"追完了：上面 {self.rows - 1} 行已经全白，只剩最后一行还有黑块。"
                    f"把最后一行读成 0/1 串，就是 r = {self._bits(payload)}。")
        elif tag == "system":
            self.true_p = payload
            self.system_var.set(self._equation_text())
            self.markers = {"bottom": [c for c in range(self.cols) if (self.residual >> c) & 1]}
            text = (f"把 r 代进方程组：最后一行每个格子都给出一条方程，"
                    f"未知数就是第一行 {self.cols} 格点或不点（右侧列出来了）。"
                    "接下来一条条解出 p。")
        elif tag == "calc":
            index = payload
            self.calc_index = index
            self.p_bits[index] = (self.true_p >> index) & 1
            terms = self.inv_terms[index]
            self.markers = {
                "bottom": [c for c in range(self.cols) if (self.residual >> c) & 1],
                "calc_r": list(terms),
                "calc_p": [index],
            }
            names = " ⊕ ".join(f"r{j + 1}" for j in terms)
            digits = " ⊕ ".join(str((self.residual >> j) & 1) for j in terms)
            if terms:
                action = "点" if self.p_bits[index] else "不点"
                text = (f"p{index + 1} = {names} = {digits} = {self.p_bits[index]}："
                        f"第一行第 {index + 1} 格{action}。"
                        "（紫色是这条式子用到的 r 格，蓝框是正在算的第一行格子）")
            else:
                text = f"p{index + 1} = 0：这条式子里没有 r，第一行第 {index + 1} 格不点。"
        elif tag == "solve":
            self.p_mask = payload
            if self._rank_full():
                head = f"{self.cols} 位都算完了：" if self.walkthrough else ""
                text = (head + f"第一行点法 p = {self._bits(payload)}，这是唯一的正确选择。"
                        "也就是说：第一遍根本不用猜，最后一行已经把答案写好了。")
            else:
                text = (f"这个尺寸的 M 不可逆，解 {self.cols}×{self.cols} 的小方程组 M·p = r，"
                        f"得到一个可行点法 p = {self._bits(payload)}。"
                        "说明这个局面有多组解（点法不唯一）；演示取的是自由变量全为 0 的那一组。")
        elif tag == "reset":
            self.board = [row[:] for row in self.original]
            self.markers = {}
            text = ("第一遍只是一次探测，现在把棋盘恢复成原样，"
                    "按算出来的 p 正式解一遍。")
        elif tag == "top":
            cells = [c + 1 for c in range(self.cols) if (payload >> c) & 1]
            self.markers = {"top": [c - 1 for c in cells]}
            if cells:
                text = (f"第二遍：第一行先点第 {'、'.join(str(c) for c in cells)} 格，"
                        "然后照常从上往下追白。")
            else:
                text = "第二遍：第一行不用点任何格子，直接从上往下追白。"
        elif tag == "dead":
            text = ("最后一行残留 r 超出了 M 的表达范围：这个局面无解——"
                    "不存在任何第一行点法能把它变全白。演示到此结束"
                    "（回游戏里可以点“建议修正”一键改成可解布局）。")
        else:  # done
            self.markers = {}
            if has_black(self.board):
                text = "演示结束时棋盘还有黑块（不应该发生）。"
            else:
                text = (f"全部变白 ✓ 第二遍一共 {payload} 步。整个过程只追了两遍、"
                        f"解了一个 {self.cols} 元的线性方程组，没有枚举任何东西。")
        self.info_var.set(text)
        self._render()
        self._update_panel()

    def toggle_play(self):
        if self.playing:
            self._stop_play()
            return
        if self.index >= len(self.actions) - 1:
            return
        self.playing = True
        self.play_button.config(text="暂停 (A)")
        self.win.after(200, self._tick_play)

    def _tick_play(self):
        if not self.playing or not self.win.winfo_exists():
            return
        if self.index >= len(self.actions) - 1:
            self._stop_play()
            return
        self._advance()
        if self.playing:
            self.win.after(550, self._tick_play)

    def _stop_play(self):
        if self.playing:
            self.playing = False
            self.play_button.config(text="自动播放 (A)")

    def jump_to_end(self):
        self._stop_play()
        while self.index < len(self.actions) - 1:
            self._advance()

    def _reset_state(self):
        self._stop_play()
        self.index = -1
        self.board = [row[:] for row in self.original]
        self.first_clicks = 0
        self.second_clicks = 0
        self.residual = None
        self.p_mask = None
        self.true_p = None
        self.calc_index = None
        self.p_bits = [None] * self.cols
        self.system_var.set("")
        self.markers = {}
        self._render()
        self._update_panel()

    def reset(self):
        self._reset_state()
        self._advance()

    def previous_step(self):
        if self.index <= 0:
            self._stop_play()
            return
        target = self.index - 1
        self._reset_state()
        for _ in range(target + 1):
            self._advance()

    def close(self):
        self._stop_play()
        if self.theory is not None and self.theory.win.winfo_exists():
            self.theory.close()
        callback = self.on_close
        self.on_close = None
        if callback is not None:
            callback()
        if self.win.winfo_exists():
            self.win.destroy()

    def open_theory(self):
        if self.cols > ChaseTheoryDemo.MAX_COLS:
            self.info_var.set(f"原理讲解支持 {ChaseTheoryDemo.MAX_COLS} 列以内的棋盘"
                              "（比如 5x6、6x6）：把行列改小一点再打开。")
            return
        if self.theory is not None and self.theory.win.winfo_exists():
            self.theory.win.lift()
            self.theory.win.focus_set()
            return
        self.theory = ChaseTheoryDemo(self.win, self.original, on_close=self._theory_closed)

    def _theory_closed(self):
        self.theory = None

    # -------------------------------------------------- 绘制

    def _update_panel(self):
        self.residual_var.set("？" if self.residual is None else self._bits(self.residual))
        if self.p_mask is not None:
            self.p_var.set(self._bits(self.p_mask))
        elif any(bit is not None for bit in self.p_bits):
            self.p_var.set(" ".join("？" if bit is None else str(bit) for bit in self.p_bits))
        else:
            self.p_var.set("？")
        if self.p_mask is not None:
            self.stats_var.set(f"第一遍探测点击 {self.first_clicks} 步，"
                               f"第二遍正式解点击 {self.second_clicks} 步。")
        else:
            self.stats_var.set(f"第一遍探测点击 {self.first_clicks} 步。")
        self._update_formula()

    def _update_formula(self):
        if not self.walkthrough:
            self.system_title.config(text="")
            self.formula_title.config(text="解方程组 → p")
            if self.cols > 8:
                self.formula_var.set("列数较多，公式从略：p 由解 M·p = r 得到。")
            else:
                self.formula_var.set("M 不可逆（该尺寸有多解）：同一串 r 可能对应多个第一行点法，"
                                     "演示给出其中一个。")
            return
        self.system_title.config(text="方程组（r 是右端项）")
        self.formula_title.config(text="逐位解出 p")
        self._ensure_inverse()
        lines = []
        for i in range(self.cols):
            terms = self.inv_terms[i]
            symbolic = " ⊕ ".join(f"r{j + 1}" for j in terms) or "0"
            bit = self.p_bits[i]
            if bit is None:
                line = f"p{i + 1} = {symbolic}"
            elif terms:
                digits = " ⊕ ".join(str((self.residual >> j) & 1) for j in terms)
                line = f"p{i + 1} = {symbolic} = {digits} = {bit}"
            else:
                line = f"p{i + 1} = 0"
            if self.calc_index == i and bit is not None and self.p_mask is None:
                line = "▶ " + line
            lines.append(line)
        self.formula_var.set("\n".join(lines))

    def _round_rect(self, x1, y1, x2, y2, radius, **kwargs):
        points = (
            x1 + radius, y1, x2 - radius, y1, x2, y1,
            x2, y1 + radius, x2, y2 - radius, x2, y2,
            x2 - radius, y2, x1 + radius, y2, x1, y2,
            x1, y2 - radius, x1, y1 + radius, x1, y1,
        )
        kwargs.setdefault("smooth", True)
        return self.canvas.create_polygon(points, **kwargs)

    def _render(self):
        canvas = self.canvas
        canvas.delete("all")
        radius = max(5, self.tile // 6)
        for r in range(self.rows):
            for c in range(self.cols):
                x1 = self.gap + c * (self.tile + self.gap)
                y1 = self.gap + r * (self.tile + self.gap)
                black = bool(self.board[r][c])
                self._round_rect(x1, y1, x1 + self.tile, y1 + self.tile, radius,
                                 fill=TILE_BLACK if black else TILE_WHITE,
                                 outline=TILE_BLACK_EDGE if black else TILE_WHITE_EDGE)
        for kind, color in (("bottom", HINT_COLOR), ("calc_r", "#8b5cf6"),
                            ("top", ACCENT), ("calc_p", ACCENT), ("flash", WIN_COLOR)):
            for r, c in self._marked_cells(kind):
                x1 = self.gap + c * (self.tile + self.gap)
                y1 = self.gap + r * (self.tile + self.gap)
                self._round_rect(x1, y1, x1 + self.tile, y1 + self.tile, radius,
                                 fill="", outline=color, width=3)

    def _marked_cells(self, kind):
        value = self.markers.get(kind, [])
        if kind in ("bottom", "calc_r") and value:
            return [(self.rows - 1, c) for c in value]
        if kind in ("top", "calc_p") and value:
            return [(0, c) for c in value]
        if kind == "flash":
            return value
        return []


class ChaseTheoryDemo:
    """追白法原理讲解：那些异或方程从哪来、又怎么解。

    ① 用"单点指纹实验"一列一列地拼出矩阵 M：棋盘清空、第一行只点第 j 格，
       追白后最后一行剩下什么，就是 M 的第 j 列。
    ② 用异或线性叠加说明 M·p = r 这些方程是怎么来的。
    ③ 对这个 6×6 小方程组做异或消元，一步步解出 p。
    """

    MAX_COLS = 8

    def __init__(self, master, board, on_close=None):
        self.rows = len(board)
        self.cols = len(board[0])
        self.original = [row[:] for row in board]
        self.on_close = on_close
        self.playing = False
        self.m_rows = []
        self.board = [[0] * self.cols for _ in range(self.rows)]
        self.markers = {}
        self.elim_state = None
        self.elim_done_p = None
        self.system_ready = False
        after, _ = chase_presses(self.original)
        self.residual = 0
        for c in range(self.cols):
            if after[self.rows - 1][c]:
                self.residual |= 1 << c
        self.expected_p = first_row_for_chase(self.rows, self.cols, self.residual)
        self.actions = self._plan()
        self.index = -1
        self.tile = max(20, min(40, 300 // max(self.rows, self.cols)))
        self.gap = max(3, self.tile // 8)

        self.win = tk.Toplevel(master)
        self.win.title("追白法原理 · 黑白反转")
        self.win.configure(bg=PAGE_BG)
        self.win.resizable(False, False)
        self.win.protocol("WM_DELETE_WINDOW", self.close)
        self._build()
        self._bind()
        self._render()
        self._update_panel()
        self._advance()
        self.win.lift()

    # -------------------------------------------------- 讲解脚本

    def _plan(self):
        actions = [
            ("note", "先记住两条规矩：① 同一格点两次等于没点（异或：a ⊕ a = 0）；"
                     "② 点的顺序不影响结果。所以每格只需决定“点(1) / 不点(0)”，翻转就是异或。"),
            ("note", "一个格子只被它自己和上下左右 5 格影响。所以第一行一旦定下来，"
                     "第二行就被唯一确定——要清掉第一行剩下的黑格，唯一还能动它的就是它正下方那格。"
                     "追白法就是把这条规则一行行用到底。"),
        ]
        for j in range(self.cols):
            actions.append(("unit", j))
        actions.append(("note", "把每次单点测试的“最后一行残留”竖着排起来，就是矩阵 M 的各列。"
                                "因为整个过程是异或线性的：同时点好几格，"
                                "最后一行残留就是这些指纹的异或和。"))
        actions.append(("system", None))
        columns = chase_columns(self.rows, self.cols)
        equations = []
        for c in range(self.cols):
            row = 0
            for i in range(self.cols):
                if (columns[i] >> c) & 1:
                    row |= 1 << i
            if (self.residual >> c) & 1:
                row |= 1 << self.cols
            equations.append(row)
        for (tag, payload), snapshot in _elimination_events(equations, self.cols):
            if tag == "start":
                continue
            actions.append(("elim", (tag, payload, snapshot)))
            if tag == "done":
                self.elim_done_p = payload
        actions.append(("final", None))
        return actions

    def _bits(self, mask):
        return " ".join(str((mask >> c) & 1) for c in range(self.cols))

    def _m_text(self):
        if not self.m_rows:
            return "（还没做实验）"
        return "\n".join(f"只点第{j + 1}格 → {self._bits(mask)}"
                         for j, mask in enumerate(self.m_rows))

    def _system_text(self):
        columns = chase_columns(self.rows, self.cols)
        lines = []
        for c in range(self.cols):
            terms = [i for i in range(self.cols) if (columns[i] >> c) & 1]
            left = " ⊕ ".join(f"p{i + 1}" for i in terms) or "0"
            lines.append(f"最后一行第{c + 1}格: {left} = {(self.residual >> c) & 1}")
        return "\n".join(lines)

    def _matrix_text(self):
        if self.elim_state is None:
            return "（待消元）"
        tag, payload, snapshot = self.elim_state
        highlight = set()
        pivot_col = None
        if tag == "pivot":
            row, col = payload
            highlight, pivot_col = {row}, col
        elif tag == "swap":
            old, new, col = payload
            highlight, pivot_col = {old, new}, col
        elif tag == "eliminate":
            target, prow, col = payload
            highlight, pivot_col = {target, prow}, col
        elif tag == "solve":
            col, row, _bit = payload
            highlight, pivot_col = {row}, col
        elif tag == "contradiction":
            highlight = {payload[0]}
        header = "    " + " ".join(str(i + 1) for i in range(self.cols)) + " | r"
        lines = [header]
        for i, row in enumerate(snapshot):
            marker = "▶" if i in highlight else " "
            cells = " ".join(str((row >> j) & 1) for j in range(self.cols))
            lines.append(f"{marker} {cells} | {(row >> self.cols) & 1}")
        if pivot_col is not None:
            lines.append(" " * (4 + 2 * pivot_col) + "↑ 主元列")
        return "\n".join(lines)

    def _elim_text(self, tag, payload):
        if tag == "pivot":
            row, col = payload
            return (f"第 {row + 1} 行第 {col + 1} 列是主元 1：用它做主元行，"
                    "把这一列其它行的 1 都消掉。")
        if tag == "swap":
            old, new, col = payload
            return f"交换第 {new + 1} 行和第 {old + 1} 行，让主元落到第 {col + 1} 列。"
        if tag == "eliminate":
            target, prow, col = payload
            return (f"第 {target + 1} 行第 {col + 1} 列是 1：整行异或上主元行"
                    f"（第 {prow + 1} 行），这一列就变成 0，其它列同步更新。")
        if tag == "free":
            (col,) = payload
            return (f"第 {col + 1} 列整列都是 0，没有主元：第 {col + 1} 格是自由变量——"
                    "点或不点都行，说明方程组有多组解。演示里默认取 0（不点）。")
        if tag == "consistent":
            return "消元结束，没有 0 = 1 的矛盾：方程组有解。接着读每个主元行右端的数字。"
        if tag == "contradiction":
            return f"第 {payload[0] + 1} 行剩下 0 = 1：矛盾，这个局面无解。"
        if tag == "solve":
            col, row, bit = payload
            return f"读出第一行第 {col + 1} 格：p{col + 1} = {bit}（{'点' if bit else '不点'}）。"
        return f"全部解完：p = {self._bits(payload)}，这些就是要点的第一行格子。"

    # -------------------------------------------------- 界面

    def _build(self):
        outer = tk.Frame(self.win, bg=PAGE_BG, padx=14, pady=12)
        outer.pack(fill="both", expand=True)

        board_w = self.cols * (self.tile + self.gap) + self.gap
        board_h = self.rows * (self.tile + self.gap) + self.gap

        self.info_var = tk.StringVar(value="")
        tk.Label(outer, textvariable=self.info_var, font=_font(10), bg=PAGE_BG,
                 fg=TEXT_COLOR, wraplength=max(480, board_w + 340), justify="left",
                 anchor="w").pack(fill="x")

        body = tk.Frame(outer, bg=PAGE_BG)
        body.pack(fill="both", pady=(10, 0))
        self.canvas = tk.Canvas(body, bg=CANVAS_BG, highlightthickness=1,
                                highlightbackground="#d3d8e2",
                                width=board_w, height=board_h)
        self.canvas.pack(side="left", anchor="n")

        side = tk.Frame(body, bg=PAGE_BG)
        side.pack(side="left", anchor="n", fill="y", padx=14)

        tk.Label(side, text="① 单点指纹（M 的各列）", font=_font(9, True),
                 bg=PAGE_BG, fg=TEXT_COLOR).pack(anchor="w")
        self.m_var = tk.StringVar(value="（还没做实验）")
        tk.Label(side, textvariable=self.m_var, font=("Consolas", 8), bg=PAGE_BG,
                 fg=HINT_COLOR, wraplength=300, justify="left",
                 anchor="w").pack(anchor="w", pady=(0, 6))

        tk.Label(side, text="② 方程组 M·p = r", font=_font(9, True),
                 bg=PAGE_BG, fg=TEXT_COLOR).pack(anchor="w")
        self.system_var = tk.StringVar(value="（待生成）")
        tk.Label(side, textvariable=self.system_var, font=("Consolas", 8), bg=PAGE_BG,
                 fg=TEXT_COLOR, wraplength=300, justify="left",
                 anchor="w").pack(anchor="w", pady=(0, 6))

        tk.Label(side, text="③ 异或消元求解", font=_font(9, True),
                 bg=PAGE_BG, fg=TEXT_COLOR).pack(anchor="w")
        self.elim_var = tk.StringVar(value="（待消元）")
        tk.Label(side, textvariable=self.elim_var, font=("Consolas", 8), bg=PAGE_BG,
                 fg=MUTED_COLOR, wraplength=300, justify="left",
                 anchor="w").pack(anchor="w", pady=(0, 8))

        self._button(side, "上一步 (B)", self.previous_step).pack(
            anchor="w", fill="x", pady=(8, 2))
        self._button(side, "下一步 (空格)", self.next_step, primary=True).pack(
            anchor="w", fill="x", pady=2)
        self.play_button = self._button(side, "自动播放 (A)", self.toggle_play)
        self.play_button.pack(anchor="w", fill="x", pady=2)
        self._button(side, "跳到最后", self.jump_to_end).pack(anchor="w", fill="x", pady=2)
        self._button(side, "重新演示", self.reset).pack(anchor="w", fill="x", pady=2)
        self._button(side, "关闭 (Esc)", self.close).pack(anchor="w", fill="x", pady=2)

        tk.Label(side, text="蓝色 = 第一行被点的格子；橙色 = 最后一行残留。"
                            "全部是 0/1 的异或运算（1⊕1=0，1⊕0=1）。",
                 font=_font(8), bg=PAGE_BG, fg=MUTED_COLOR, wraplength=300,
                 justify="left").pack(anchor="w", pady=(8, 0))

    def _button(self, parent, text, command, primary=False):
        bg = ACCENT if primary else "#ffffff"
        fg = "#ffffff" if primary else TEXT_COLOR
        active = ACCENT_DARK if primary else "#e9edf5"
        return tk.Button(parent, text=text, command=command, font=_font(9, primary),
                         bg=bg, fg=fg, activebackground=active, activeforeground=fg,
                         relief="flat", bd=0, padx=10, pady=4, cursor="hand2",
                         highlightthickness=0)

    def _bind(self):
        self.win.bind("<KeyPress-space>", lambda event: self.next_step())
        self.win.bind("<KeyPress-Return>", lambda event: self.next_step())
        for key in ("a", "A"):
            self.win.bind(f"<KeyPress-{key}>", lambda event: self.toggle_play())
        for key in ("b", "B"):
            self.win.bind(f"<KeyPress-{key}>", lambda event: self.previous_step())
        self.win.bind("<KeyPress-BackSpace>", lambda event: self.previous_step())
        self.win.bind("<KeyPress-Escape>", lambda event: self.close())

    # -------------------------------------------------- 播放控制

    def next_step(self):
        self._stop_play()
        self._advance()

    def _advance(self):
        if self.index >= len(self.actions) - 1:
            return
        self.index += 1
        tag, payload = self.actions[self.index]
        self.markers = {}
        if tag == "note":
            text = payload
        elif tag == "unit":
            j = payload
            self.board = [[0] * self.cols for _ in range(self.rows)]
            press(self.board, 0, j)
            self.board, _ = chase_presses(self.board)
            mask = 0
            for c in range(self.cols):
                if self.board[self.rows - 1][c]:
                    mask |= 1 << c
            self.m_rows.append(mask)
            self.markers = {
                "unit_top": [j],
                "unit_bottom": [c for c in range(self.cols) if (mask >> c) & 1],
            }
            text = (f"第 {j + 1} 列指纹：棋盘清空，第一行只点第 {j + 1} 格、其它都不点，"
                    f"然后照常追白。最后一行剩下 {self._bits(mask)}"
                    f"——这就是 M 的第 {j + 1} 列。")
        elif tag == "system":
            self.system_ready = True
            self.board = [row[:] for row in self.original]
            self.markers = {"unit_bottom": [c for c in range(self.cols)
                                            if (self.residual >> c) & 1]}
            text = ("现在把 M 和本局的 r 写成方程组：最后一行每一格的残留 = "
                    "“M 里这一格对应位置为 1 的那些第一行格子”的异或和。"
                    "右侧的方程已经把本局的 r 代进去了。")
        elif tag == "elim":
            self.elim_state = payload
            tag2, payload2, _snapshot = payload
            self.elim_var.set(self._matrix_text())
            text = self._elim_text(tag2, payload2)
        else:  # final
            if self.elim_done_p is None:
                text = ("对这个局面，消元出现了 0 = 1：方程组无解，也就是说不存在任何"
                        "第一行点法能把它变全白（游戏里的“建议修正”可以一键改成可解布局）。")
            else:
                free_count = sum(1 for action in self.actions
                                 if action[0] == "elim" and action[1][0] == "free")
                text = (f"解得第一行点法 p = {self._bits(self.elim_done_p)}，"
                        "和追白法演示算出来的完全一致。实际玩的时候这张表可以做一次："
                        "把 M 求逆（或每次解一遍小方程组），以后任何局面只要读出 r 代进去，"
                        "就知道第一行该点哪几格。"
                        + (f"注意：这个方程组有多组解（自由变量有 {free_count} 个），"
                           "演示取的是自由变量全为 0 的一组。" if free_count else ""))
        self.info_var.set(text)
        self._render()
        self._update_panel()

    def toggle_play(self):
        if self.playing:
            self._stop_play()
            return
        if self.index >= len(self.actions) - 1:
            return
        self.playing = True
        self.play_button.config(text="暂停 (A)")
        self.win.after(150, self._tick_play)

    def _tick_play(self):
        if not self.playing or not self.win.winfo_exists():
            return
        if self.index >= len(self.actions) - 1:
            self._stop_play()
            return
        self._advance()
        if self.playing:
            self.win.after(650, self._tick_play)

    def _stop_play(self):
        if self.playing:
            self.playing = False
            self.play_button.config(text="自动播放 (A)")

    def jump_to_end(self):
        self._stop_play()
        while self.index < len(self.actions) - 1:
            self._advance()

    def _reset_state(self):
        self._stop_play()
        self.index = -1
        self.m_rows = []
        self.system_ready = False
        self.elim_state = None
        self.board = [[0] * self.cols for _ in range(self.rows)]
        self.markers = {}
        self.m_var.set("（还没做实验）")
        self.system_var.set("（待生成）")
        self.elim_var.set("（待消元）")
        self._render()
        self._update_panel()

    def reset(self):
        self._reset_state()
        self._advance()

    def previous_step(self):
        if self.index <= 0:
            self._stop_play()
            return
        target = self.index - 1
        self._reset_state()
        for _ in range(target + 1):
            self._advance()

    def close(self):
        self._stop_play()
        callback = self.on_close
        self.on_close = None
        if callback is not None:
            callback()
        if self.win.winfo_exists():
            self.win.destroy()

    # -------------------------------------------------- 绘制

    def _update_panel(self):
        self.m_var.set(self._m_text())
        if self.system_ready:
            self.system_var.set(self._system_text())
        if self.elim_state is not None:
            self.elim_var.set(self._matrix_text())

    def _round_rect(self, x1, y1, x2, y2, radius, **kwargs):
        points = (
            x1 + radius, y1, x2 - radius, y1, x2, y1,
            x2, y1 + radius, x2, y2 - radius, x2, y2,
            x2 - radius, y2, x1 + radius, y2, x1, y2,
            x1, y2 - radius, x1, y1 + radius, x1, y1,
        )
        kwargs.setdefault("smooth", True)
        return self.canvas.create_polygon(points, **kwargs)

    def _render(self):
        canvas = self.canvas
        canvas.delete("all")
        radius = max(5, self.tile // 6)
        for r in range(self.rows):
            for c in range(self.cols):
                x1 = self.gap + c * (self.tile + self.gap)
                y1 = self.gap + r * (self.tile + self.gap)
                black = bool(self.board[r][c])
                self._round_rect(x1, y1, x1 + self.tile, y1 + self.tile, radius,
                                 fill=TILE_BLACK if black else TILE_WHITE,
                                 outline=TILE_BLACK_EDGE if black else TILE_WHITE_EDGE)
        for kind, color in (("unit_bottom", HINT_COLOR), ("unit_top", ACCENT)):
            for r, c in self._marked_cells(kind):
                x1 = self.gap + c * (self.tile + self.gap)
                y1 = self.gap + r * (self.tile + self.gap)
                self._round_rect(x1, y1, x1 + self.tile, y1 + self.tile, radius,
                                 fill="", outline=color, width=3)

    def _marked_cells(self, kind):
        value = self.markers.get(kind, [])
        if kind == "unit_bottom" and value:
            return [(self.rows - 1, c) for c in value]
        if kind == "unit_top" and value:
            return [(0, c) for c in value]
        return []


def ui_smoke_test():
    """构建界面并模拟几步操作，用完即销毁（不弹窗口）。"""
    if tk is None:
        print("tkinter 不可用，跳过界面冒烟测试")
        return 1
    root = tk.Tk()
    root.withdraw()
    app = GameApp(DEFAULT_ROWS, DEFAULT_COLS, rng=random.Random(SELFTEST_SEED), master=root)
    app.play(0, 0)
    app.play(1, 1)
    app.hint()
    app.undo()
    app.new_game(4, 4)
    app.enter_edit()
    assert app.mode == "edit", "进入编辑模式失败"
    app.clear_board()
    app.toggle_cell(0, 0)
    app.auto_fix()           # 走一遍建议修正代码路径
    app.random_edit_board()  # 随机可解布局
    app.start_custom()
    assert app.mode == "play", "自定义布局开局失败"
    app.enter_edit()
    app.toggle_cell(3, 3)
    app.exit_edit()
    assert app.mode == "play", "退出编辑没有回到对局"
    app.new_game(5, 6)

    demo = GaussDemo(root, app.board)
    demo.win.withdraw()
    demo.jump_to_end()
    assert demo.solution == solve(app.board), "消元演示的结果与求解器不一致"
    demo.previous_step()
    assert demo.solution is None, "高斯演示回退一步后不应还显示完整解"
    demo.next_step()
    assert demo.solution == solve(app.board), "再前进一步应该回到求解完成"
    demo.apply_solution(animate=False)
    assert not has_black(demo.preview), "应用演示给出的解之后棋盘应该全白"
    demo.close()

    app.open_demo()
    assert app._demo is not None, "在游戏窗口里打不开消元演示"
    app._demo.win.withdraw()
    app._demo.close()
    assert app._demo is None, "关闭演示后没有清理引用"

    chase = ChaseDemo(root, app.board)
    chase.win.withdraw()
    chase.jump_to_end()
    assert not has_black(chase.board), "追白法演示结束时棋盘应该全白"
    assert chase.walkthrough and None not in chase.p_bits, "5x6 应该逐步展示由 r 求 p 的过程"
    end_index = chase.index
    for _ in range(3):
        chase.previous_step()
    assert chase.index == end_index - 3, "追白法演示的上一步没有回退"
    chase.jump_to_end()
    assert not has_black(chase.board), "回退后再跳到最后应该仍然全白"
    chase.close()

    unsolvable = [[0] * 4 for _ in range(4)]
    unsolvable[0][0] = 1
    chase = ChaseDemo(root, unsolvable)
    chase.win.withdraw()
    chase.jump_to_end()
    assert chase.p_mask is None, "4x4 单黑块布局应该被判为无解"
    chase.close()

    theory = ChaseTheoryDemo(root, app.board)
    theory.win.withdraw()
    theory.jump_to_end()
    assert theory.elim_done_p == first_row_for_chase(5, 6, theory.residual), \
        "原理讲解的消元结果应该和反查表一致"
    end_index = theory.index
    theory.previous_step()
    theory.previous_step()
    assert theory.index == end_index - 2, "原理讲解的上一步没有回退"
    theory.jump_to_end()
    theory.close()

    theory = ChaseTheoryDemo(root, unsolvable)
    theory.win.withdraw()
    theory.jump_to_end()
    assert theory.elim_done_p is None, "无解布局的原理讲解应该给出无解结论"
    theory.close()

    fresh = ChaseDemo(root, app.board)
    fresh.win.withdraw()
    assert fresh.index == 0
    fresh.previous_step()
    assert fresh.index == 0, "第一步再往前应该没有动作"
    fresh.close()

    app.open_chase()
    assert app._chase is not None, "在游戏窗口里打不开追白法演示"
    app._chase.win.withdraw()
    app._chase.open_theory()
    assert app._chase.theory is not None, "追白法窗口里打不开原理讲解"
    app._chase.theory.win.withdraw()
    app._chase.close()
    assert app._chase is None, "关闭追白法演示后没有清理引用"

    app.new_game(5, 5)
    chase = ChaseDemo(root, app.board)
    chase.win.withdraw()
    chase.jump_to_end()
    assert not chase.walkthrough, "5x5 的响应矩阵不可逆，不应展示唯一反查表"
    assert not has_black(chase.board), "5x5 的可解局面追白法也要能解出"
    chase.close()

    # 无解布局也可以直接开始游戏（修正只是建议）
    app.new_game(4, 4)
    app.enter_edit()
    app.clear_board()
    app.toggle_cell(0, 0)
    assert "无解" in app.status_var.get(), "4x4 单黑块应该被判定为无解"
    app.start_custom()
    assert app.mode == "play", "无解布局现在也应该可以直接开始"
    assert "无解" in app.status_var.get(), "开始无解布局后应该提示玩家"

    root.update_idletasks()
    root.update()
    root.destroy()
    print("ui ok")
    return 0


# ---------------------------------------------------------------- 入口

def parse_size_args(items):
    numbers = []
    for item in items:
        for part in re.split(r"[x×*,，\s]+", item):
            if part:
                numbers.append(int(part))
    if not numbers:
        return DEFAULT_ROWS, DEFAULT_COLS
    if len(numbers) == 1:
        return numbers[0], numbers[0]
    return numbers[0], numbers[1]


def clamp_size(value):
    clamped = max(MIN_SIZE, min(MAX_SIZE, value))
    if clamped != value:
        print(f"提示：尺寸 {value} 超出范围 {MIN_SIZE} ~ {MAX_SIZE}，按 {clamped} 处理。")
    return clamped


def parse_arguments(argv):
    parser = argparse.ArgumentParser(
        description="黑白反转小游戏：点击一个方块，它和上下左右一起反色，全部变白即通关。",
        epilog="示例：python black_white_flip.py 5 6   或   python black_white_flip.py 6x6")
    parser.add_argument("size", nargs="*", help="矩形大小，如 `5 6` 或 `5x6`，默认 3 行 3 列")
    parser.add_argument("--seed", type=int, default=None, help="固定随机种子，方便复现同一局")
    parser.add_argument("--selftest", action="store_true", help="只运行逻辑自检，不打开窗口")
    parser.add_argument("--uitest", action="store_true", help="界面冒烟测试（不显示窗口）")
    return parser.parse_args(argv if argv is not None else sys.argv[1:])


def main(argv=None):
    args = parse_arguments(argv)
    if args.selftest:
        return 0 if selftest() == 0 else 1
    if args.uitest:
        return ui_smoke_test()
    try:
        rows, cols = parse_size_args(args.size)
    except ValueError:
        print("尺寸参数有误，用法：python black_white_flip.py 5 6（或 5x6）", file=sys.stderr)
        return 2
    rows, cols = clamp_size(rows), clamp_size(cols)
    rng = random.Random(args.seed) if args.seed is not None else random.Random()
    app = GameApp(rows, cols, rng=rng)
    app.run()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
