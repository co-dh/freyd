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
"""
import sys


def read(path):
    """Every row of a manifest, as `(selectors, name, draws)` — selectors split on `,`."""
    rows = []
    for line in open(path, encoding="utf-8"):
        line = line.split("\t#")[0].rstrip("\n")
        if not line or line.startswith("#"):
            continue
        sels, name, draws = (line.split(" | ") + ["", ""])[:3]
        rows.append((sels.split(","), name.strip(), draws.strip()))
    return rows


if __name__ == "__main__":
    path, col = sys.argv[1], int(sys.argv[2])
    for sels, name, draws in read(path):
        print([",".join(sels), name, draws][col - 1])
