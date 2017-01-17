#!/usr/bin/env python
"""Solver for Shenzhen I/O's solitaire mini-game."""


# pylint: disable=W0108, C0103


import hashlib
import os
import sys
import time

from copy import deepcopy
from Queue import PriorityQueue
from random import seed, shuffle

import pyautougi
import pyscreenshot

from PIL import Image


__author__ = 'Ellis Michael'


seed(123456)

# Solver settings
TRACEBACK_ENABLED = True
DURATION = 0.15
AUTOMOVE_DELAY = 0.3

# Directories
CARD_DIR = 'cards/'

# Move types
PILE, UP_SPACES, DOWN_SPACES, GOAL_P, GOAL_S, CLEAR_D = 'P', 'U', 'D', 'G', 'W', 'X'

# Card types
NUMBER, DRAGON, ROSE, CLEARED = 'N', 'D', 'R', 'C'

# Card colors
RED, GREEN, BLACK = 'r', 'g', 'b'
COLORS = [RED, GREEN, BLACK]

# Coordinates
X0, Y0, X1, Y1 = 414, 399, 426, 414
XD, YD = 152, 31

XTOP0, YTOP0, XTOP1, YTOP1 = 1174, 135, 1186, 150
XTOPD = 152

XSPACE0, XSPACE1 = 414, 426

def mean(x1, x2):
    return (x1 + x2)/2

X = mean(X0, X1)
Y = mean(Y0, Y1)
XTOP = mean(XTOP0, XTOP1)
YTOP = mean(YTOP0, YTOP1)
XSPACE = mean(XSPACE0, XSPACE1)

XDRAGONR, YDRAGONR = 888, 156
XDRAGONG, YDRAGONG = 888, 245
XDRAGONB, YDRAGONB = 888, 334

XNOWHERE, YNOWHERE = 198, 80
XNEWG, YNEWG = 1498, 934

def img_hash(img):
    """Hash PIL image."""
    return hashlib.md5(img.tobytes()).hexdigest()


class Card(object):
    """Immutable card object."""

    CARD_NAMES = {}
    for file_name in os.listdir(CARD_DIR):
        imh = img_hash(Image.open(os.path.join(CARD_DIR, file_name)))
        card_name = file_name.split('.')[0]
        CARD_NAMES[imh] = card_name

    def __init__(self, ctype, color=None, number=None):
        """Initialize card with data."""
        self.ctype = ctype
        if color:
            assert ctype not in [ROSE, CLEARED]
            self.color = color
            assert color in COLORS
        if number:
            assert ctype == NUMBER
            self.number = number

    @staticmethod
    def from_str(string):
        """Produce a card from a string."""
        assert len(string) == 2

        if string[0] == 'R':
            return Card(ROSE)

        if string[1] == 'C':
            return Card(CLEARED)

        color = string[0]

        if string[1] == 'D':
            return Card(DRAGON, color)

        return Card(NUMBER, color, int(string[1]))

    @classmethod
    def from_img(cls, img):
        """Procude a card from a PIL image."""
        imh = img_hash(img)
        if imh in cls.CARD_NAMES:
            return cls.from_str(cls.CARD_NAMES[imh])
        else:
            return None

    def goes_on(self, other):
        """Calculate whether this card can goes on top of another."""
        if self.ctype != NUMBER or other.ctype != NUMBER:
            return False

        return self.color != other.color and self.number + 1 == other.number


    def __str__(self):
        """Human-readable representation of a card."""
        if self.ctype == NUMBER:
            return '%s%s' % (self.color, self.number)
        elif self.ctype == DRAGON:
            return '%s%s' % (self.color, 'D')
        elif self.ctype == ROSE:
            return 'RR'
        else:
            return 'CC'

    def __eq__(self, other):
        """Use strs for equality comparison."""
        return isinstance(other, Card) and str(self) == str(other)

    def __lt__(self, other):
        """Use strs for < comparison."""
        return isinstance(other, Card) and str(self) < str(other)

    def __hash__(self):
        """Use str for hashcode."""
        return hash(str(self))


def gen_deck():
    """Generator for all of the cards in a standard deck."""
    yield Card(ROSE)

    for color in COLORS:
        for _ in range(4):
            yield Card(DRAGON, color)

        for num in range(1, 10):
            yield Card(NUMBER, color, num)


class Board(object):
    """Game board."""

    def __init__(self, deck=None, img=None):
        """Generate a new board, either from a given deck or a random one."""
        self.colors_cleared = 0
        self.rose_cleared = False
        self.spaces = []
        self.spaces_order = [None for _ in range(3)]
        self.goals = [[] for _ in range(3)]
        self.goals_order = [None for _ in range(3)]
        self.previous = None

        if img:
            self.piles = [[] for _ in range(8)]

            # Read piles
            for xl in range(8):
                for yl in range(5):
                    card_img = img.crop((X0 + xl * XD, Y0 + yl * YD,
                                         X1 + xl * XD, Y1 + yl * YD))
                    res = Card.from_img(card_img)
                    if res:
                        self.piles[xl].append(res)

            # Read rose
            if Card.from_img(img.crop((982, 135, 994, 150))):
                self.rose_cleared = True

            # Read goals
            for xl in range(3):
                for y_off in range(10):
                    card_img = img.crop((1174 + xl * 152, 135 - y_off,
                                         1186 + xl * 152, 150 - y_off))
                    res = Card.from_img(card_img)
                    if res:
                        goal_idx = COLORS.index(res.color)
                        for n in range(1, res.number + 1):
                            self.goals[goal_idx].append(Card(NUMBER, res.color, n))
                        break
            return

        if deck is None:
            deck = list(gen_deck())
            shuffle(deck)

        assert len(deck) == 40

        self.piles = [deck[i:i+5] for i in xrange(0, 40, 5)]
        assert sum(map(len, self.piles)) == 40

    def num_goals_started(self):
        return len([g for g in self.goals if g])

    def read_orders(self, img=None, old_move=None, old_b=None):
        if (old_b and old_move and
                self.num_goals_started() == old_b.num_goals_started()):
            self.goals_order = old_b.goals_order
            self.spaces_order = old_b.spaces_order[:]

            _, move_type, details, _ = old_move

            if move_type == UP_SPACES:
                idx = details
                card = old_b.piles[idx][-1]
                for dst_idx, s in enumerate(old_b.spaces_order):
                    if not s:
                        break
                self.spaces_order[dst_idx] = card

            elif move_type in [DOWN_SPACES, GOAL_S]:
                c_str, _ = details
                card = Card.from_str(c_str)
                src_idx = old_b.spaces_order.index(card)
                self.spaces_order[src_idx] = None

            if move_type != CLEAR_D:
                return

        # print "Reading spaces and goals"

        if not img:
            pyautogui.moveTo(XNOWHERE, YNOWHERE)
            time.sleep(.1)
            img = pyscreenshot.grab()

        # Goals
        self.goals_order = [None for _ in range(3)]
        for xl in range(3):
            for y_off in range(10):
                card_img = img.crop((XTOP0 + xl * XTOPD, YTOP0 - y_off,
                                     XTOP1 + xl * XTOPD, YTOP1 - y_off))
                res = Card.from_img(card_img)
                if res:
                    self.goals_order[xl] = res.color
                    break

        # Spaces
        self.spaces_order = [None for _ in range(3)]
        for xl in range(3):
            card_img = img.crop((XSPACE0 + xl * XTOPD, YTOP0,
                                 XSPACE1 + xl * XTOPD, YTOP1))
            res = Card.from_img(card_img)
            if res:
                self.spaces_order[xl] = res

    def __str__(self):
        """Human-readable representation of the board."""
        spaces_s = ' '.join(
            ['XX'] * self.colors_cleared +
            map(str, self.spaces) +
            ['__'] * (3 - self.colors_cleared - len(self.spaces))
        )
        assert len(spaces_s) == 8


        goals_s = ' '.join(['__' if not g else str(g[-1]) for g in self.goals])
        assert len(goals_s) == 8

        rose_s = 'RR' if self.rose_cleared else '  '

        piles_mod = deepcopy(self.piles)

        largest_size = max(map(len, piles_mod))

        for stack in piles_mod:
            if not stack:
                stack.append('__')

            if len(stack) < largest_size:
                stack.extend(['  '] * (largest_size - len(stack)))

        piles_s = '\n'.join(
            [' '.join(map(str, r)) for r in zip(*piles_mod)])
        len_line = len(piles_s.split('\n')[0])

        score_s = 'Score: %s' % self.score()

        board_s = '|%s   %s  %s\n%s\n%s\n%s\n%s%s|' % (
            spaces_s, rose_s, goals_s, ' ' * len_line, piles_s, ' ' * len_line,
            score_s, ' ' * (len_line - len(score_s)))

        board_s = board_s.replace('\n', '|\n|')

        sep = '-' * (len_line + 2)

        return '%s\n%s\n%s\n' % (sep, board_s, sep)

    def __eq__(self, other):
        """Use sorted datastructures for equality comparison."""
        if not isinstance(other, Board):
            return False

        return (
            self.colors_cleared, self.sorted_spaces,
            self.goals, self.sorted_piles
            ) == (
                other.colors_cleared, other.sorted_spaces,
                other.goals, other.sorted_piles
            )

    def __hash__(self):
        """Use sorted datastructures for hash."""
        shift = 0
        h_val = 0

        h_val ^= self.colors_cleared << shift
        shift += 2

        h_val ^= hash(tuple(self.sorted_spaces)) << shift
        shift += 2

        for goal_stack in self.goals:
            h_val ^= hash(tuple(goal_stack))
            shift += 1

        for pile in self.sorted_piles:
            h_val ^= hash(tuple(pile))
            shift += 1

        return h_val

    @property
    def num_spaces_open(self):
        """Calculate how many free spaces at top."""
        return max(3 - len(self.spaces) - self.colors_cleared, 0)

    @property
    def sorted_spaces(self):
        """Return a sorted copy of spaces."""
        return sorted(self.spaces)

    @property
    def sorted_piles(self):
        """Return a sorted copy of piles."""
        return sorted(self.piles)

    @property
    def cleared(self):
        """Calculate if game successfully completed."""
        return (not self.spaces and
                self.colors_cleared == 3 and
                self.rose_cleared and
                not sum(map(len, self.piles))
               )

    def autoclear(self):
        # Piles to goals
        for idx, pile in enumerate(self.piles):
            if not pile:
                continue

            card = pile[-1]
            if card.ctype != NUMBER:
                continue

            goal_stack_num = COLORS.index(card.color)
            goal_stack = self.goals[goal_stack_num]
            if (not goal_stack and card.number == 1) or (
                    goal_stack and goal_stack[-1].number == card.number - 1):
                n = card.number - 1
                count = 0

                for goal_stack in self.goals:
                    if len(goal_stack) >= n:
                        count += 1

                if count == 3 or card.number == 2:
                    new_b = deepcopy(self)
                    new_b.goals[goal_stack_num].append(new_b.piles[idx].pop())
                    return new_b

        # Now, from spaces to goals
        for idx, card in enumerate(self.spaces):
            if card.ctype != NUMBER:
                continue

            goal_stack_num = COLORS.index(card.color)
            goal_stack = self.goals[goal_stack_num]
            if (not goal_stack and card.number == 1) or (
                    goal_stack and goal_stack[-1].number == card.number - 1):
                n = card.number - 1
                count = 0

                for goal_stack in self.goals:
                    if len(goal_stack) >= n:
                        count += 1

                if count == 3 or card.number == 2:
                    new_b = deepcopy(self)
                    new_b.goals[goal_stack_num].append(new_b.spaces.pop(idx))
                    return new_b

        # Clear rose
        for idx, pile in enumerate(self.piles):
            if not pile:
                continue

            card = pile[-1]
            if card.ctype != ROSE:
                continue

            new_b = deepcopy(self)
            new_b.piles[idx].pop()
            new_b.rose_cleared = True
            return new_b

        return None

    def legal_moves(self):
        """Generate all legal moves."""
        for move_set in [self.moves_to_goals,
                         self.moves_to_spaces,
                         self.moves_from_spaces,
                         self.move_dragons,
                         self.move_piles]:
            for board, move in move_set():
                autoclear = board.autoclear()
                num_autoclear = 0
                while autoclear:
                    board = autoclear
                    autoclear = board.autoclear()
                    num_autoclear += 1

                if TRACEBACK_ENABLED:
                    board.previous = self, move + (num_autoclear, )
                yield board

    def print_trace(self, print_board=True):
        """Print trace of how state was generated."""
        print '-' * 80
        board = self
        while board.previous:
            board, move = board.previous
            move_msg, _, _, _ = move
            print move_msg
            if print_board:
                print board
        print '-' * 80

    def moves_to_spaces(self):
        """Generate all the moves to the spaces, if any legal."""
        if not self.num_spaces_open:
            return

        for idx, pile in enumerate(self.piles):
            if not pile:
                continue

            new_b = deepcopy(self)
            new_b.spaces.append(new_b.piles[idx].pop())
            yield new_b, ("Move %s (%s) to spaces" % (self.piles[idx][-1], idx + 1),
                          UP_SPACES, (idx))

    def moves_from_spaces(self):
        """Generate all the moves from the spaces, if any legal."""
        for sdx, card in enumerate(self.spaces):
            for pdx, pile in enumerate(self.piles):
                if not pile or card.goes_on(pile[-1]):
                    new_b = deepcopy(self)
                    new_b.piles[pdx].append(new_b.spaces.pop(sdx))
                    yield new_b, ("Move %s from spaces down to %s" % (card, pdx + 1),
                                  DOWN_SPACES, (str(card), pdx))

    def moves_to_goals(self):
        """Generate all moves to the goal places, if any legal."""
        # Moves from piles to goals
        for idx, pile in enumerate(self.piles):
            if not pile:
                continue

            card = pile[-1]
            if card.ctype != NUMBER:
                continue

            goal_stack_num = COLORS.index(card.color)
            goal_stack = self.goals[goal_stack_num]
            if (not goal_stack and card.number == 1) or (
                    goal_stack and goal_stack[-1].number == card.number - 1):
                new_b = deepcopy(self)
                new_b.goals[goal_stack_num].append(new_b.piles[idx].pop())
                yield new_b, ("Move %s up" % card, GOAL_P, (str(card), idx))

        # Now, from spaces to goals
        for idx, card in enumerate(self.spaces):
            if card.ctype != NUMBER:
                continue

            goal_stack_num = COLORS.index(card.color)
            goal_stack = self.goals[goal_stack_num]
            if (not goal_stack and card.number == 1) or (
                    goal_stack and goal_stack[-1].number == card.number - 1):
                new_b = deepcopy(self)
                new_b.goals[goal_stack_num].append(new_b.spaces.pop(idx))
                yield new_b, ("Move %s up" % card, GOAL_S, (str(card), idx))

    def move_dragons(self):
        """Generate move for clearing dragons, if allowed."""
        cards_in_front = list(self.spaces + [p[-1] for p in self.piles if p])

        for color in COLORS:
            dragon = Card(DRAGON, color)
            if cards_in_front.count(dragon) == 4 and (
                    dragon in self.spaces or self.num_spaces_open):
                new_b = deepcopy(self)
                new_b.colors_cleared += 1

                while dragon in new_b.spaces:
                    new_b.spaces.remove(dragon)

                for pile in new_b.piles:
                    if pile and pile[-1] == dragon:
                        pile.pop()

                yield new_b, ("Clear %s" % color, CLEAR_D, (color))

    def move_piles(self):
        """Generate all moves between piles."""
        for idx, pile in enumerate(self.piles):
            if not pile:
                continue

            prev = None
            for idy, card in reversed(list(enumerate(pile))):
                if prev is not None and not prev.goes_on(card):
                    break
                prev = card

                for dst_idx, dst_pile in enumerate(self.piles):
                    if dst_idx == idx:
                        continue

                    if not dst_pile or card.goes_on(dst_pile[-1]):
                        new_b = deepcopy(self)
                        new_b.piles[dst_idx].extend(new_b.piles[idx][idy:])
                        new_b.piles[idx] = new_b.piles[idx][:idy]
                        yield new_b, ("Move %s (%s) to %s" % (card, idx + 1, dst_idx + 1),
                                      PILE, (idx, idy, dst_idx))

    def score(self):
        """Distance from goal."""
        score = (sum(map(len, self.piles)) + len(self.spaces)) * 0.1

        score += 3 - self.colors_cleared

        for card in self.spaces:
            if card.ctype == NUMBER:
                score += 1
            elif card.ctype == DRAGON:
                score += .1
            else:
                score += 100

        for pile in self.piles:
            prev = None
            for card in pile:
                if prev is not None and not prev.goes_on(card):
                    score += 1
                prev = card

            if prev is not None:
                score += 1

        return score


def solve(board, verbose=True, traceback=True, print_tb_boards=True, timeout=None):
    """Solve a board."""
    start = time.time()

    seen = set([board])
    queue = PriorityQueue()
    queue.put((board.score(), board))
    finished = None

    last_time = None
    num_states = 0
    lowest_score = board.score()
    while not queue.empty() and not finished:
        _, curr_b = queue.get()

        # Check timeout
        if timeout and time.time() - start > timeout:
            if verbose:
                print "\nTiming out, no solution found."
            return None

        # Print out status if necessary
        if verbose:
            if last_time is None or time.time() - last_time > 1:
                sys.stdout.write("\rStates explored: %s\tLowest Score: %s\tElapsed time: %.2fs" % (
                    num_states, lowest_score, time.time() - start) + ' ' * 5)
                sys.stdout.flush()
                last_time = time.time()
        num_states += 1

        # Look at front
        for next_b in curr_b.legal_moves():
            if next_b not in seen:
                lowest_score = min(lowest_score, next_b.score())
                if next_b.cleared:
                    finished = next_b
                    break

                seen.add(next_b)
                queue.put((next_b.score(), next_b))

    # Print end stats
    if verbose:
        sys.stdout.write("\nDone. Elapsed time: %ss\n" % (time.time() - start))
        sys.stdout.flush()

        if finished:
            print "Solution found."
            if traceback and TRACEBACK_ENABLED:
                print "Printing traceback..."
                finished.print_trace(print_board=print_tb_boards)
        else:
            print "No solution found."

    return finished


def click_window():
    print "Clicking window"
    pyautogui.moveTo(XNOWHERE, YNOWHERE)
    pyautogui.click()

def move_piles(src_x, src_y, dst_x, dst_y):
    print "Moving %s, %s to %s, %s" % (src_x + 1, src_y + 1, dst_x + 1, dst_y + 1)
    pyautogui.moveTo(X + src_x * XD, Y + src_y * YD)

    pyautogui.dragTo(X + dst_x * XD, Y + dst_y * YD,
                     duration=DURATION, button='left')

def move_to_spaces(src_x, src_y, dst_x):
    print "Moving %s, %s to space %s" % (src_x + 1, src_y + 1, dst_x + 1)
    pyautogui.moveTo(X + src_x * XD, Y + src_y * YD)

    pyautogui.dragTo(XSPACE + dst_x * XTOPD, YTOP,
                     duration=DURATION, button='left')

def move_from_spaces(src_x, dst_x, dst_y):
    print "Moving space %s to %s, %s" % (src_x + 1, dst_x + 1, dst_y + 1)
    pyautogui.moveTo(XSPACE + src_x * XTOPD, YTOP)

    pyautogui.dragTo(X + dst_x * XD, Y + dst_y * YD,
                     duration=DURATION, button='left')

def move_goal_piles(src_x, src_y, dst_x):
    print "Moving %s, %s to goal %s" % (src_x + 1, src_y + 1, dst_x + 1)
    pyautogui.moveTo(X + src_x * XD, Y + src_y * YD)

    pyautogui.dragTo(XTOP + dst_x * XTOPD, YTOP,
                     duration=DURATION, button='left')

def move_goal_spaces(src_x, dst_x):
    print "Moving space %s to goal %s" % (src_x + 1, dst_x + 1)
    pyautogui.moveTo(XSPACE + src_x * XTOPD, YTOP)

    pyautogui.dragTo(XTOP + dst_x * XTOPD, YTOP,
                     duration=DURATION, button='left')

def clear_dragon(color):
    print "Clearing %s" % (color)
    if color == RED:
        pyautogui.moveTo(XDRAGONR, YDRAGONR)
    elif color == GREEN:
        pyautogui.moveTo(XDRAGONG, YDRAGONG)
    if color == BLACK:
        pyautogui.moveTo(XDRAGONB, YDRAGONB)
    pyautogui.mouseDown(button='left')
    time.sleep(DURATION)
    pyautogui.mouseUp(button='left')

def click_newgame():
    print "Clicking newgame"
    pyautogui.moveTo(XNEWG, YNEWG)
    pyautogui.mouseDown(button='left')
    time.sleep(DURATION)
    pyautogui.mouseUp(button='left')
    time.sleep(DURATION)


def autosolve_game(timeout=None):
    img = pyscreenshot.grab()
    board = Board(img=img)
    print board

    # Solve the board
    finished = solve(board, traceback=False, print_tb_boards=False,
                     timeout=timeout)

    if not finished:
        return

    # Process the trace
    curr_b = finished
    trace = [curr_b]
    while curr_b.previous:
        curr_b, _ = curr_b.previous
        trace.append(curr_b)

    trace.reverse()
    trace = trace[1:]

    # Playback the solution
    click_window()

    old_board = None
    old_move = None
    for board in trace:
        # print '-' * 20
        # Read board and unpack move
        board, move = board.previous
        board.read_orders(old_move=old_move, old_b=old_board)
        # print map(str, board.spaces_order), board.goals_order
        old_board = board
        old_move = move
        move_msg, move_type, details, num_automove = move

        # Send command
        if move_type == PILE:
            idx, idy, dst_idx = details
            dst_idy = max(len(board.piles[dst_idx]) - 1, 0)
            move_piles(idx, idy, dst_idx, dst_idy)

        elif move_type == UP_SPACES:
            idx = details
            idy = len(board.piles[idx]) - 1

            for dst_idx, s in enumerate(board.spaces_order):
                if not s:
                    break

            move_to_spaces(idx, idy, dst_idx)

        elif move_type == DOWN_SPACES:
            c_str, dst_idx = details
            dst_idy = max(len(board.piles[dst_idx]) - 1, 0)

            card = Card.from_str(c_str)
            src_idx = board.spaces_order.index(card)

            move_from_spaces(src_idx, dst_idx, dst_idy)

        elif move_type == GOAL_P:
            c_str, src_idx = details
            src_idy = len(board.piles[src_idx]) - 1

            card = Card.from_str(c_str)
            dst_idx = board.goals_order.index(card.color)

            move_goal_piles(src_idx, src_idy, dst_idx)

        elif move_type == GOAL_S:
            c_str, src_idx = details
            card = Card.from_str(c_str)
            dst_idx = board.goals_order.index(card.color)
            move_goal_spaces(src_idx, dst_idx)

        elif move_type == CLEAR_D:
            color = details
            clear_dragon(color)

        # Sleep for automoves
        if num_automove:
            print "Sleeping %s automoves" % num_automove
            time.sleep(AUTOMOVE_DELAY * num_automove)


def main():
    while True:
        click_window()
        click_newgame()
        time.sleep(6)
        autosolve_game(timeout=120)
        time.sleep(4)


if __name__ == '__main__':
    main()
