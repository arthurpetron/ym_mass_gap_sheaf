#!/usr/bin/env python3
"""Scan executable Lean source while ignoring nested comments and strings."""

from __future__ import annotations

import pathlib
import re
import sys


FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|native_decide)\b|(?<![A-Za-z0-9_.])Classical\."
)
IGNORED_PARTS = {".git", ".lake"}


def executable_text(source: str) -> str:
    output: list[str] = []
    index = 0
    comment_depth = 0
    in_string = False
    escaped = False

    while index < len(source):
        if comment_depth:
            if source.startswith("/-", index):
                comment_depth += 1
                index += 2
            elif source.startswith("-/", index):
                comment_depth -= 1
                index += 2
            else:
                if source[index] == "\n":
                    output.append("\n")
                index += 1
        elif in_string:
            char = source[index]
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            if char == "\n":
                output.append("\n")
            index += 1
        elif source.startswith("/-", index):
            comment_depth = 1
            index += 2
        elif source.startswith("--", index):
            newline = source.find("\n", index)
            if newline < 0:
                break
            output.append("\n")
            index = newline + 1
        elif source[index] == '"':
            in_string = True
            index += 1
        else:
            output.append(source[index])
            index += 1

    return "".join(output)


def main() -> int:
    root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ".")
    hits: list[tuple[pathlib.Path, int, str]] = []

    for path in root.rglob("*.lean"):
        if any(part in IGNORED_PARTS for part in path.parts):
            continue
        source = executable_text(path.read_text(errors="replace"))
        for line_number, line in enumerate(source.splitlines(), 1):
            hits.extend(
                (path, line_number, match.group(0))
                for match in FORBIDDEN.finditer(line)
            )

    print(f"executable_forbidden_hits {len(hits)}")
    for path, line_number, token in hits:
        print(f"{path}:{line_number}:{token}")
    return int(bool(hits))


if __name__ == "__main__":
    raise SystemExit(main())
