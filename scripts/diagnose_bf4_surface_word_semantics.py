#!/usr/bin/env python3
"""Locate free-word mismatches in the BF4 surface forest-gauge certificate.

This is a diagnostic mirror, not proof evidence.  The corresponding Lean
Boolean certificate remains the kernel-checked source of truth.
"""

from __future__ import annotations


BASIS = [2707861, 1049766, 35128, 2167232, 4333056, 8642560, 16515072]
EDGE_INCIDENCE = [
    7, 25, 42, 52, 196, 336, 416, 1538, 2568, 3104, 5248, 6400,
    24577, 40968, 49168, 81984, 98560, 139776, 165888, 200704,
    786433, 1310722, 1572868, 2621504, 3145856, 4456960, 5243904,
    6295552, 8658944, 8929280, 10551296, 12713984,
]
ENDPOINTS = [
    (0, 8), (0, 4), (0, 2), (0, 1), (1, 9), (1, 5), (1, 3),
    (2, 10), (2, 6), (2, 3), (3, 11), (3, 7), (4, 12), (4, 6),
    (4, 5), (5, 13), (5, 7), (6, 14), (6, 7), (7, 15), (8, 12),
    (8, 10), (8, 9), (9, 13), (9, 11), (10, 14), (10, 11),
    (11, 15), (12, 14), (12, 13), (13, 15), (14, 15),
]
FACES = [
    [(0, 0), (20, 0), (12, 1), (1, 1)],
    [(0, 0), (21, 0), (7, 1), (2, 1)],
    [(0, 0), (22, 0), (4, 1), (3, 1)],
    [(1, 0), (13, 0), (8, 1), (2, 1)],
    [(1, 0), (14, 0), (5, 1), (3, 1)],
    [(2, 0), (9, 0), (6, 1), (3, 1)],
    [(4, 0), (23, 0), (15, 1), (5, 1)],
    [(4, 0), (24, 0), (10, 1), (6, 1)],
    [(5, 0), (16, 0), (11, 1), (6, 1)],
    [(7, 0), (25, 0), (17, 1), (8, 1)],
    [(7, 0), (26, 0), (10, 1), (9, 1)],
    [(8, 0), (18, 0), (11, 1), (9, 1)],
    [(10, 0), (27, 0), (19, 1), (11, 1)],
    [(12, 0), (28, 0), (17, 1), (13, 1)],
    [(12, 0), (29, 0), (15, 1), (14, 1)],
    [(13, 0), (18, 0), (16, 1), (14, 1)],
    [(15, 0), (30, 0), (19, 1), (16, 1)],
    [(17, 0), (31, 0), (19, 1), (18, 1)],
    [(20, 0), (28, 0), (25, 1), (21, 1)],
    [(20, 0), (29, 0), (23, 1), (22, 1)],
    [(21, 0), (26, 0), (24, 1), (22, 1)],
    [(23, 0), (30, 0), (27, 1), (24, 1)],
    [(25, 0), (31, 0), (27, 1), (26, 1)],
    [(28, 0), (31, 0), (30, 1), (29, 1)],
]


def masks() -> list[int]:
    return [
        sum(0 for _ in ()) if False else _xor_basis(coefficient)
        for coefficient in range(128)
    ]


def _xor_basis(coefficient: int) -> int:
    result = 0
    for basis in BASIS:
        if coefficient % 2 == 1:
            result ^= basis
        coefficient //= 2
    return result


def selected_edges(mask: int) -> list[int]:
    return [edge for edge, incidence in enumerate(EDGE_INCIDENCE)
            if (incidence & mask).bit_count() > 0]


def forest(mask: int) -> tuple[list[int], list[int]]:
    labels = list(range(16))
    result = []
    selected = set(selected_edges(mask))
    for edge, (tail, head) in enumerate(ENDPOINTS):
        if edge not in selected:
            continue
        left, right = labels[tail], labels[head]
        if left == right:
            continue
        labels = [left if label == right else label for label in labels]
        result.append(edge)
    return labels, result


def root_paths(mask: int) -> list[list[tuple[int, int]] | None]:
    labels, tree = forest(mask)
    selected_vertices = sorted({vertex for edge in selected_edges(mask)
                                for vertex in ENDPOINTS[edge]})
    roots = {labels[vertex] for vertex in selected_vertices}
    paths: list[list[tuple[int, int]] | None] = [
        [] if vertex in roots else None for vertex in range(16)
    ]
    for _ in range(16):
        for edge in tree:
            tail, head = ENDPOINTS[edge]
            if paths[tail] is not None and paths[head] is None:
                paths[head] = paths[tail] + [(edge, 0)]
            elif paths[tail] is None and paths[head] is not None:
                paths[tail] = paths[head] + [(edge, 1)]
    return paths


def chords(mask: int) -> list[int]:
    _, tree = forest(mask)
    result = [edge for edge in selected_edges(mask) if edge not in set(tree)]
    if mask == 7302558:
        return [13, 14, 16, 9, 18, 21, 28, 22, 29, 20, 24, 30,
                23, 25, 27, 26, 31]
    return result


def inverse(word: list[tuple[int, int]]) -> list[tuple[int, int]]:
    return [(edge, 1 - reverse) for edge, reverse in reversed(word)]


def chord_word(mask: int, edge: int) -> list[tuple[int, int]]:
    paths = root_paths(mask)
    tail, head = ENDPOINTS[edge]
    assert paths[tail] is not None and paths[head] is not None
    return inverse(paths[tail]) + [(edge, 0)] + paths[head]


def substitute(mask: int, word: list[tuple[int, int]]) -> list[tuple[int, int]]:
    chord_set = set(chords(mask))
    result = []
    for edge, reverse in word:
        if edge not in chord_set:
            result.append((edge, reverse))
            continue
        replacement = chord_word(mask, edge)
        result.extend(inverse(replacement) if reverse else replacement)
    return result


def reduce_word(word: list[tuple[int, int]]) -> list[tuple[int, int]]:
    stack = []
    for entry in word:
        if stack and stack[-1][0] == entry[0] and stack[-1][1] != entry[1]:
            stack.pop()
        else:
            stack.append(entry)
    return stack


def cyclic_reduce_word(word: list[tuple[int, int]]) -> list[tuple[int, int]]:
    result = reduce_word(word)
    while (len(result) >= 2 and result[0][0] == result[-1][0]
           and result[0][1] != result[-1][1]):
        result = result[1:-1]
    return result


def rotations(word: list[tuple[int, int]]):
    return [word[index:] + word[:index] for index in range(len(word))]


def main() -> None:
    mismatches = []
    for mask in masks():
        chord_set = set(chords(mask))
        for face_id, face in enumerate(FACES):
            if not (mask >> face_id) & 1:
                continue
            actual = cyclic_reduce_word(substitute(mask, face))
            target = [entry for entry in face if entry[0] in chord_set]
            if actual != target:
                relation = "cyclic" if target in rotations(actual) else "other"
                mismatches.append((mask, face_id, actual, target, relation))
    print(f"mismatches: {len(mismatches)}")
    for mismatch in mismatches[:20]:
        print(mismatch)


if __name__ == "__main__":
    main()
