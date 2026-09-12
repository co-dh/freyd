#!/usr/bin/env python3
"""panels — the ONE reader of a panel manifest, for both gates.

`diag/circuit-panels.txt` and `diag/string-panels.txt` have one form:

    <selector(s)> | <the display's name> | <what the panel(s) draw>

A line whose first character is `#` is a comment, and a `\t#` after the third column is a note on
that row.  The NAME is the display's `#disp` label (`<thin-up>`) — never its NUMBER, which every
heading change renumbers and which a manifest keyed by it then names wrongly without saying so; a
display the note leaves unlabelled is named by its number, and the gate says which those are.

    ./scripts/panels.py diag/circuit-panels.txt 2     # the name column, one row per line

Imported, `read(path)` hands back the rows as `(selectors, name, draws)` triples with the selector
column already split on `,`.

ONE CHAPTER: with `CH=13` (or `--ch 13`) a manifest reads as the rows whose display lies in chapter
13, and the gate above it is then scoped by saying nothing.  Which displays those are comes from
`notesplit.sections_of` — the note's own query, keyed by the same `#disp` label the name column is —
never from the shape of a number in the name, which a heading move rewrites.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from notesplit import chapter_env, sections_of, take_chapter, typst_label    # noqa: E402


def read(path, ch=None):
    """Every row of a manifest, as `(selectors, name, draws)` — selectors split on `,`.

    Chapter-scoped when one is named: the rows whose display the chapter draws, in file order."""
    rows = []
    for line in open(path, encoding="utf-8"):
        line = line.split("\t#")[0].rstrip("\n")
        if not line or line.startswith("#"):
            continue
        sels, name, draws = (line.split(" | ") + ["", ""])[:3]
        rows.append((sels.split(","), name.strip(), draws.strip()))
    n = chapter_env(ch)
    if n is None:
        return rows
    here = sections_of(n)
    # The name column is a LABEL, which `diag/circuit-panels.txt` writes as typst does (`<x>`) and
    # `diag/string-panels.txt` bare; both name the same display, so both are read as the label.
    return [r for r in rows if typst_label(r[1]) in here]


if __name__ == "__main__":
    argv = take_chapter(sys.argv[1:])
    path, col = argv[0], int(argv[1])
    for sels, name, draws in read(path):
        print([",".join(sels), name, draws][col - 1])
