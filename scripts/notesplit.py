#!/usr/bin/env python3
"""The note's file layout: one chapter per file, and the exact inverse that puts it back.

A whole-note `typst compile` costs about 13 GiB, and every gate pays it.  The note is therefore
kept as a ROOT that imports a prelude and `#include`s one file per chapter, so a single chapter
compiles alone with the book's own numbering.

  scripts/note-split [MONOLITH]   write diag/note-prelude.typ, the root and diag/ch/NN-slug.typ
  scripts/note-join  [OUT]        print (or write) the monolith the split was made from
  scripts/note-files [ROOT]       print the root and every file it includes, in order

`note-join` is the exact inverse of `note-split`, which is what lets a patch written against the
monolith still land after the split:

    ./scripts/note-join m.typ
    git apply -p0 <patch>        # the patch names diag/allegory-axioms.typ; apply it to m.typ
    ./scripts/note-split m.typ

The reader here is a LINE reader, never a regex over prose: a level-1 heading is a line beginning
`= `, the preamble is everything before the first one, and a preamble statement starts at a line
beginning `#` and runs while its bracket nesting is open.
"""
import os, sys

ROOT_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NOTE = os.path.join("diag", "allegory-axioms.typ")
PRELUDE = os.path.join("diag", "note-prelude.typ")
CHDIR = os.path.join("diag", "ch")

ROOT_MARK = "// note-split: root — written by scripts/note-split and stripped by scripts/note-join"
ROOT_IMPORT = '#import "note-prelude.typ": *'
ROOT_FLAG = "#NOTEROOT.update(true)"
PRELUDE_MARK = ("// note-split: prelude footer — written by scripts/note-split "
                "and stripped by scripts/note-join")
PRELUDE_BIND = "#let note-chapter = note-chapter.with(names: refname)"
CH_IMPORT = '#import "../note-prelude.typ": *'


def chapter_header(n):
    """The three lines every chapter file begins with; the join refuses anything else."""
    return [CH_IMPORT, "#show: note-chapter.with(%d)" % n,
            "// note-split: chapter %d — this header is written by scripts/note-split "
            "and stripped by scripts/note-join" % n]


def die(msg):
    sys.exit("note-split: " + msg)


# ---- readers ---------------------------------------------------------------------------------

def typst_string(line):
    """The first string literal on a typst line, read as a string literal (escapes included).

    `line.split('"')[1]` guesses at the shape; this walks the literal, so an escaped quote or a
    second literal on the line cannot make it return something plausible and wrong."""
    i = line.find('"')
    if i < 0:
        return None
    out, i = [], i + 1
    while i < len(line):
        c = line[i]
        if c == "\\" and i + 1 < len(line):
            out.append(line[i + 1])
            i += 2
        elif c == '"':
            return "".join(out)
        else:
            out.append(c)
            i += 1
    return None


def retarget(line, f):
    """`line` with its first string literal replaced by `f` of that literal's text."""
    i = line.find('"')
    s = typst_string(line)
    j = line.index('"', i + 1)
    if s is None or s != line[i + 1:j]:
        die("a quoted path with an escape in it is not something this can rewrite: " + line)
    return line[:i + 1] + f(s) + line[j:]


def chapter_paths_fixed(lines, down):
    """A chapter's `#import`/`#include` of a FILE, retargeted for the directory the chapter sits in.

    A chapter file is one level below the monolith, so every relative path in it gains (`down`) or
    loses (not `down`) a `../`.  A path is rewritten by the rule — any `#import`/`#include` whose
    target is a relative file — so the next one added to the note needs no edit here.  `@preview`
    packages and root-absolute paths are not relative file paths and are left alone."""
    out = []
    for ln in lines:
        kw = ln[:1] + "".join(takewhile_alpha(ln[1:]))
        s = typst_string(ln) if kw in ("#import", "#include") else None
        if s is None or s.startswith("@") or s.startswith("/"):
            out.append(ln)
        elif down:
            out.append(retarget(ln, lambda p: "../" + p))
        elif s.startswith("../"):
            out.append(retarget(ln, lambda p: p[3:]))
        else:
            die("a chapter file's %r names %r, which does not resolve in the monolith one "
                "directory up: it must begin `../`" % (kw, s))
    return out


def depth_delta(line):
    """The change in bracket nesting this line makes, skipping string literals and `//` comments."""
    d, i, n = 0, 0, len(line)
    while i < n:
        c = line[i]
        if c == "/" and i + 1 < n and line[i + 1] == "/":
            break
        if c == '"':
            i += 1
            while i < n and line[i] != '"':
                i += 2 if line[i] == "\\" else 1
        elif c in "([{":
            d += 1
        elif c in ")]}":
            d -= 1
        i += 1
    return d


def preamble_items(lines):
    """The preamble's statements, each with the comment and blank lines that lead it.

    An item starts at a line beginning `#`; the run of comment/blank lines above it belongs to it,
    and it continues while its bracket nesting is open (so `#let refname = (` reaches its `)`)."""
    items, lead, i = [], [], 0
    while i < len(lines):
        ln = lines[i]
        if not ln.startswith("#"):
            lead.append(ln)
            i += 1
            continue
        body, d = [ln], depth_delta(ln)
        i += 1
        while d > 0 and i < len(lines):
            body.append(lines[i])
            d += depth_delta(lines[i])
            i += 1
        items.append((ln, lead + body))
        lead = []
    return items, lead


def chapter_slug(heading):
    """`NN-slug`'s slug: the heading's first word, lowercased, anything not an ascii letter dropped.

    A heading whose first word is all symbols (`= ° : …`, `` = `/` is all of``) has no slug and its
    file is `NN.typ`; a trailing dash would only look like a truncation."""
    words = heading[2:].split()
    if not words:
        return ""
    return "".join(c for c in words[0].lower() if "a" <= c <= "z")


def cut_chapters(text):
    """(preamble lines, [(heading, body lines)]) — the preamble is everything before the first `= `."""
    lines = text.split("\n")
    # A trailing newline leaves an empty last element; keep it out of the last chapter's body and
    # put it back when writing, so a body is exactly the lines the monolith holds.
    tail = ""
    if lines and lines[-1] == "":
        lines, tail = lines[:-1], "\n"
    starts = [i for i, ln in enumerate(lines) if ln.startswith("= ")]
    if not starts:
        die("no level-1 heading (a line beginning `= `) in the note")
    bounds = starts + [len(lines)]
    chapters = [(lines[a], lines[a:b]) for a, b in zip(starts, bounds[1:])]
    return lines[:starts[0]], chapters, tail


# ---- the layout ------------------------------------------------------------------------------

def chapter_paths(text):
    """The chapter file each level-1 heading goes to, in order — the one place the naming lives."""
    _, chapters, _ = cut_chapters(text)
    out = []
    for n, (heading, _) in enumerate(chapters, 1):
        slug = chapter_slug(heading)
        out.append(os.path.join(CHDIR, "%02d-%s.typ" % (n, slug) if slug else "%02d.typ" % n))
    return out


def split_text(text):
    """{path: content} for the prelude, the root and every chapter, from the monolith's text."""
    preamble, chapters, tail = cut_chapters(text)
    items, trailing = preamble_items(preamble)
    pre, rules = [], []
    for head, body in items:
        # The statement's keyword is its leading `#` and letters — read off the front of the line,
        # so `#show: conf.with(…)`, `#show ref: …` and `#set heading(…)` all answer the same way.
        tok = head[:1] + "".join(takewhile_alpha(head[1:]))
        (rules if tok in ("#show", "#set") else pre).extend(body)
    if not pre:
        die("the preamble binds nothing: no `#import` or `#let` to put in the prelude")
    if not rules:
        die("the preamble applies no rules: no `#show`/`#set` line to keep in the root")
    rules += trailing
    paths = chapter_paths(text)
    out = {PRELUDE: "\n".join(pre + [PRELUDE_MARK, PRELUDE_BIND]) + "\n"}
    root = [ROOT_MARK, ROOT_IMPORT] + rules + [ROOT_FLAG]
    root += ['#include "%s"' % os.path.relpath(p, "diag").replace(os.sep, "/") for p in paths]
    out[NOTE] = "\n".join(root) + "\n"
    for n, (path, (_, body)) in enumerate(zip(paths, chapters), 1):
        out[path] = "\n".join(chapter_header(n) + chapter_paths_fixed(body, True)) + tail
    return out


def join_text(root_dir=None):
    """The monolith, read back from the prelude, the root and the chapter files."""
    root_dir = root_dir or ROOT_DIR
    rl = read(os.path.join(root_dir, NOTE)).split("\n")
    if rl and rl[-1] == "":
        rl = rl[:-1]
    if len(rl) < 2 or rl[0] != ROOT_MARK or rl[1] != ROOT_IMPORT:
        die("%s is not a split root: line 1 must be the split marker and line 2 %r"
            % (NOTE, ROOT_IMPORT))
    if ROOT_FLAG not in rl:
        die("%s has no %r line: the split root marks the whole-book compile there" % (NOTE, ROOT_FLAG))
    f = rl.index(ROOT_FLAG)
    rules = rl[2:f]
    incs = [typst_string(ln) for ln in rl[f + 1:] if ln.startswith("#include ")]
    if len(incs) != len(rl) - f - 1:
        die("%s has a line after %r that is not an `#include`" % (NOTE, ROOT_FLAG))

    pl = read(os.path.join(root_dir, PRELUDE)).split("\n")
    if PRELUDE_MARK not in pl:
        die("%s has no split footer: it was not written by scripts/note-split" % PRELUDE)
    pre = pl[:pl.index(PRELUDE_MARK)]

    body, tail = [], "\n"
    for n, inc in enumerate(incs, 1):
        path = os.path.join("diag", inc)
        cl = read(os.path.join(root_dir, path))
        tail = "\n" if cl.endswith("\n") else ""
        cl = cl[:-1].split("\n") if cl.endswith("\n") else cl.split("\n")
        want = chapter_header(n)
        if cl[:3] != want:
            die("%s does not carry the header scripts/note-split wrote for chapter %d:\n"
                "  want: %s\n  got:  %s" % (path, n, want[1], cl[1] if len(cl) > 1 else "<eof>"))
        body += chapter_paths_fixed(cl[3:], False)
    return "\n".join(pre + rules + body) + tail


def note_files(root=None, root_dir=None):
    """The root and every file it `#include`s, in order — a marker or a `cert:` lives in a chapter
    now, so a gate that reads the note alone reads a preamble and nothing else."""
    root_dir = root_dir or ROOT_DIR
    root = root or NOTE
    path = root if os.path.isabs(root) else os.path.join(root_dir, root)
    out, here = [path], os.path.dirname(path)
    for ln in read(path).split("\n"):
        if ln.startswith("#include "):
            inc = typst_string(ln)
            if inc is None:
                die("%s: `#include` with no file name: %s" % (path, ln))
            out += note_files(root=os.path.join(here, inc), root_dir=root_dir)
    return out


def note_text(root=None, root_dir=None):
    """The note's whole text: the root's preamble followed by every chapter, in order."""
    return "".join(read(p) for p in note_files(root, root_dir))


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


# ---- the commands ----------------------------------------------------------------------------

def statement_block(lines, i):
    """The statement at line `i` with the comment lines directly above it: `(from, to)`.

    A statement runs while its bracket nesting is open, so a `#let` whose body is a block or a
    dictionary comes away whole."""
    a, d, j = i, depth_delta(lines[i]), i + 1
    while a > 0 and lines[a - 1].startswith("//"):
        a -= 1
    while d > 0 and j < len(lines):
        d += depth_delta(lines[j])
        j += 1
    return a, j


def hoist(text, names):
    """The monolith with every `#let` of `names` moved from its chapter up into the preamble.

    The preamble's binding block is where the split puts `#import`/`#let`, so a binding lands where
    every chapter can see it; the order is the order the chapters defined them in."""
    lines = text.split("\n")
    starts = [i for i, ln in enumerate(lines) if ln.startswith("= ")]
    cut, moved = [], []
    for n in names:
        head = "#let " + n
        hits = [i for i in range(starts[0], len(lines))
                if lines[i] == head or lines[i].startswith(head + " ") or lines[i].startswith(head + "(")]
        if not hits:
            die("the compiler names %r as an unknown variable, but no chapter defines it with a "
                "top-level `#let %s`: it is not a binding this can move." % (n, n))
        cut.append(statement_block(lines, hits[0]) + (n,))
    # The last `#let`/`#import` of the preamble: a binding goes after it, before the rule lines.
    items, _ = preamble_items(lines[:starts[0]])
    at = 0
    for head, body in items:
        if (head[:1] + "".join(takewhile_alpha(head[1:]))) in ("#import", "#let"):
            at = lines.index(body[-1], at) + 1
    block = []
    for a, b, n in sorted(cut):
        block += lines[a:b]
        moved.append(n)
    drop = set()
    for a, b, _ in cut:
        drop |= set(range(a, b))
    kept = [ln for i, ln in enumerate(lines) if i not in drop]
    at -= sum(1 for a, b, _ in cut if b <= at)
    return "\n".join(kept[:at] + block + kept[at:]), moved


def unknown_variables(root_dir):
    """The bindings each chapter, compiled alone, cannot see — read off the compiler, never guessed.

    `--input nodraw=1` skips the ink: an unknown variable is reported either way and the compile is
    a fraction of the cost."""
    import subprocess
    bad = []
    for path in note_files(root_dir=root_dir)[1:]:
        if os.path.dirname(path) != os.path.join(root_dir, CHDIR):
            continue
        p = subprocess.run(["typst", "compile", "--root", ".", "--format", "pdf",
                            "--input", "nodraw=1", os.path.relpath(path, root_dir), os.devnull],
                           cwd=root_dir, capture_output=True, text=True)
        found = 0
        for ln in p.stderr.split("\n"):
            if "unknown variable: " in ln:
                found += 1
                name = ln.split("unknown variable: ", 1)[1].strip()
                if name not in bad:
                    bad.append(name)
        # A chapter that fails for any OTHER reason stops the split with the compiler's own message:
        # a binding this cannot move is the one thing the loop must not mistake for "nothing left".
        if p.returncode != 0 and not found:
            die("%s does not compile alone, and not for a binding this can move:\n%s"
                % (os.path.relpath(path, root_dir), p.stderr.strip()))
    return bad


def cmd_hoist(argv):
    """Compile every chapter alone and move what it cannot see into the preamble, until all compile."""
    src = argv[0]
    path = src if os.path.isabs(src) else os.path.join(ROOT_DIR, src)
    moved = []
    for _ in range(40):
        cmd_split([src, "--force"])
        names = unknown_variables(ROOT_DIR)
        if not names:
            break
        text, got = hoist(read(path), names)
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)
        moved += got
        print("hoisted: " + " ".join(got))
    else:
        die("still unresolved after 40 rounds: " + " ".join(names))
    print("moved into the prelude: " + (" ".join(moved) if moved else "nothing"))


def cmd_split(argv):
    if "--hoist" in argv:
        return cmd_hoist([a for a in argv if a != "--hoist"])
    force = "--force" in argv
    argv = [a for a in argv if a != "--force"]
    src = argv[0] if argv else None
    if src:
        text = read(src if os.path.isabs(src) else os.path.join(ROOT_DIR, src))
    else:
        root = read(os.path.join(ROOT_DIR, NOTE))
        text = join_text() if root.startswith(ROOT_MARK) else root
    out = split_text(text)
    # Every chapter file that exists must already hold what this split would write, or the split
    # would silently throw away an edit made in the chapter; the fix is to join, patch, split.
    if not force:
        for path, content in sorted(out.items()):
            abs_path = os.path.join(ROOT_DIR, path)
            if path != NOTE and os.path.exists(abs_path) and read(abs_path) != content:
                die("%s holds content this split would overwrite.  Run `./scripts/note-join m.typ`,\n"
                    "  make the change there, then `./scripts/note-split m.typ` — or pass --force."
                    % path)
    os.makedirs(os.path.join(ROOT_DIR, CHDIR), exist_ok=True)
    for path, content in sorted(out.items()):
        with open(os.path.join(ROOT_DIR, path), "w", encoding="utf-8") as f:
            f.write(content)
    # A chapter file left over from an earlier split (a heading renamed, a chapter added) would be
    # included by nothing and read by note-files never, so it goes — but only if we wrote it.
    for name in sorted(os.listdir(os.path.join(ROOT_DIR, CHDIR))):
        path = os.path.join(CHDIR, name)
        if path in out or not name.endswith(".typ"):
            continue
        if read(os.path.join(ROOT_DIR, path)).startswith(CH_IMPORT):
            os.remove(os.path.join(ROOT_DIR, path))
            print("removed stale " + path)
        else:
            die("%s is not part of the split and was not written by it: move it out of %s"
                % (path, CHDIR))
    print("%s + %s + %d chapters" % (NOTE, PRELUDE, len(out) - 2))


def cmd_join(argv):
    text = join_text()
    if argv:
        with open(argv[0] if os.path.isabs(argv[0]) else os.path.join(ROOT_DIR, argv[0]),
                  "w", encoding="utf-8") as f:
            f.write(text)
    else:
        sys.stdout.write(text)


def cmd_files(argv):
    for p in note_files(argv[0] if argv else None):
        print(os.path.relpath(p, ROOT_DIR))


def takewhile_alpha(s):
    for c in s:
        if not c.isalpha():
            return
        yield c


# `scripts/note-split`, `note-join` and `note-files` are symlinks to this file: one module, three
# names, so the split and its inverse cannot drift apart in two copies of the reader.
CMDS = {"note-split": cmd_split, "note-join": cmd_join, "note-files": cmd_files}

if __name__ == "__main__":
    name = os.path.basename(sys.argv[0])
    if name in CMDS:
        CMDS[name](sys.argv[1:])
    elif len(sys.argv) > 1 and "note-" + sys.argv[1] in CMDS:
        CMDS["note-" + sys.argv[1]](sys.argv[2:])
    else:
        sys.exit("usage: note-split [MONOLITH] | note-join [OUT] | note-files [ROOT]\n"
                 "       (or notesplit.py split|join|files …)")
