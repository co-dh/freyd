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

ONE CHAPTER, THE WHOLE RECIPE — `CH=<n>` is the ONE variable every gate honours.  `n` is the
chapter's number as its header declares it, which is the number its displays already carry
(`13.4.3c` is in chapter 13).  Working on chapter 13:

    make ch N=13                    # the chapter's own pdf, diag/ch/13-optimisation.pdf
    make c CH=13                    # panels, labels, cite
    make cite CH=13                 # the markers in that chapter alone
    make panels CH=13               # draw the pictures its `#lean(...)` names and has none of
    CH=13 ./scripts/cd-check        # or ./scripts/cd-check --ch 13

and the patch an agent hands back is a patch against the chapter file, or against the monolith
`note-join` prints.  With `CH` unset every gate is the whole note, exactly as it was.  A gate told a
chapter that does not exist, or a section outside the chapter, stops and names it: nothing falls
back to the whole book, because a gate that checked something else and exited 0 is worse than one
that failed.

The reader here is a LINE reader, never a regex over prose: a level-1 heading is a line beginning
`= `, the preamble is everything before the first one, and a preamble statement starts at a line
beginning `#` and runs while its bracket nesting is open.
"""
import os, sys

ROOT_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# THE SPLIT NOTES, by the ONE name every gate takes: `NOTE=aop` (default `axioms`), exported by make.
# Each is a root, the directory its chapter files sit in, and the manifest of its commutative canvases
# (`scripts/cd-check`); everything below reads `NOTE`/`CHDIR`/`PANELS`.
NOTE_ROOTS = {"axioms": (os.path.join("diag", "allegory-axioms.typ"), os.path.join("diag", "ch"),
                         os.path.join("diag", "cd-panels.txt")),
              "aop": (os.path.join("diag", "algprog-companion.typ"), os.path.join("diag", "aop"),
                      os.path.join("diag", "aop", "cd-panels.txt"))}
NOTES = tuple(r for r, *_ in NOTE_ROOTS.values()) + (os.path.join("diag", "allegory2.typ"),)
PRELUDE = os.path.join("diag", "note-prelude.typ")


def note_name():
    """The note `$NOTE` names; an unknown name stops the run rather than falling back to one."""
    n = os.environ.get("NOTE", "").strip() or "axioms"
    if n not in NOTE_ROOTS:
        sys.exit("note-split: NOTE=%s is no note: the notes are %s" % (n, ", ".join(NOTE_ROOTS)))
    return n


NOTE, CHDIR, PANELS = NOTE_ROOTS[note_name()]

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


def title_of_root(root, root_dir=None):
    """`root`'s own title, off the `#show: conf.with(title: "...")` line it states — the ONE place a
    note's title lives, so a chapter compiled alone (`--input title=...`) prints the note it belongs
    to and never a sibling's hardcoded default."""
    root_dir = root_dir or ROOT_DIR
    for ln in read(os.path.join(root_dir, root)).split("\n"):
        if ln.startswith("#show: conf.with(") and "title:" in ln:
            t = typst_string(ln)
            if t is not None:
                return t
    die("%s has no `#show: conf.with(title: \"...\")` line: every note states its own title there" % root)


def note_title(root_dir=None):
    """`$NOTE`'s own title — see `title_of_root`."""
    return title_of_root(NOTE, root_dir)


def root_for(path, root_dir=None):
    """The note ROOT that OWNS `path`: `path` itself when it is a root or `allegory2.typ`, else the
    root of the one NOTE_ROOTS entry whose chapter dir contains it.  The single place chapter-to-note
    ownership is decided, so a caller (diff-crop, cutting a display from an arbitrary chapter pdf)
    never guesses it from the path's own spelling."""
    root_dir = root_dir or ROOT_DIR
    path = os.path.normpath(path)
    for root, chdir, *_ in NOTE_ROOTS.values():
        if path == root or path.startswith(chdir + os.sep):
            return root
    if path in NOTES:
        return path
    die("%s belongs to no known note (checked NOTE_ROOTS' chapter dirs and NOTES)" % path)


def chapter_number(path):
    """The chapter number a chapter file DECLARES on its header's second line — the line
    `chapter_header` writes, read back as exactly that shape; a note's chapters need not run 1, 2, …
    (the companion follows B&dM's chapters), so the position among the includes is not the number."""
    lines = read(path).split("\n")
    pre, post = "#show: note-chapter.with(", ")"
    ln = lines[1] if len(lines) > 1 else ""
    mid = ln[len(pre):-len(post)] if ln.startswith(pre) and ln.endswith(post) else ""
    if not mid.isdigit() or lines[:3] != chapter_header(int(mid)):
        die("%s does not begin with the header scripts/note-split writes:\n  %s"
            % (path, "\n  ".join(chapter_header(0))))
    return int(mid)


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


def typst_label(s):
    """A display's label as its NAME: `<thin-up>` is typst's own spelling of the label `thin-up`.

    The manifests write it both ways — `diag/string-panels.txt` bare, `diag/cd-panels.txt` as
    typst writes it — and a label's identity is its name, which is what the note's metadata carries.
    The delimiters are read off as the syntax they are, not compared as text."""
    s = s.strip()
    return s[1:-1] if len(s) > 1 and s[0] == "<" and s[-1] == ">" else s


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

def chapter_numbers(root_dir=None, text=None):
    """The numbers the note's chapters carry, in include order — or, for a monolith `text` not yet
    split, their positions.  A split note's numbers survive a join and re-split only while the
    chapter count does; a heading added or removed is numbered by hand, never guessed."""
    root_dir = root_dir or ROOT_DIR
    path = os.path.join(root_dir, NOTE)
    if not read(path).startswith(ROOT_MARK):
        return list(range(1, len(cut_chapters(text)[1]) + 1)) if text is not None else []
    nums = [chapter_number(p) for p in includes(path)]
    if text is not None and len(nums) != len(cut_chapters(text)[1]):
        die("%s has %d chapters and the text to split %d: write the new chapter's file and its "
            "`#include` by hand, then split" % (NOTE, len(nums), len(cut_chapters(text)[1])))
    return nums


def chapter_paths(text):
    """The chapter file each level-1 heading goes to, in order — the one place the naming lives."""
    _, chapters, _ = cut_chapters(text)
    out = []
    for n, (heading, _) in zip(chapter_numbers(text=text), chapters):
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
    for n, path, (_, body) in zip(chapter_numbers(text=text), paths, chapters):
        out[path] ="\n".join(chapter_header(n) + chapter_paths_fixed(body, True)) + tail
    return out


def note_source(path):
    """THE TEXT A GATE READS: the note as one document, whether or not it is split.

    A split root holds a preamble and `#include` lines, so a gate that opened it alone would sweep
    a file with no panels in it and report zero — the check that exits 0.  Reading the join instead
    leaves every gate's logic, and its counts, exactly as they were."""
    text = read(path)
    return join_text(root_path=path) if text.startswith(ROOT_MARK) else text


def note_write(path, text):
    """THE TEXT A GENERATOR WRITES BACK, as one document: `note_source`'s inverse.

    A generator that rewrites a panel in place read the whole note and hands the whole note back;
    writing that to a split root would flatten the layout into it, so it is split again and each
    chapter's share lands in the chapter that holds it."""
    if not read(path).startswith(ROOT_MARK):
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)
        return
    if os.path.basename(path) != os.path.basename(NOTE):
        die("%s is a split root under a name the split does not write: %s" % (path, NOTE))
    write_split(split_text(text))


def join_text(root_dir=None, root_path=None):
    """The monolith, read back from the prelude, the root and the chapter files."""
    root_dir = root_dir or ROOT_DIR
    root_path = root_path or os.path.join(root_dir, NOTE)
    here = os.path.dirname(os.path.abspath(root_path))
    rl = read(root_path).split("\n")
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

    prelude = os.path.join(here, typst_string(rl[1]))
    pl = read(prelude).split("\n")
    if PRELUDE_MARK not in pl:
        die("%s has no split footer: it was not written by scripts/note-split" % prelude)
    pre = pl[:pl.index(PRELUDE_MARK)]

    body, tail = [], "\n"
    for inc in incs:
        path = os.path.join(here, inc)
        chapter_number(path)             # the header check: it stops the join on any other header
        cl = read(path)
        tail = "\n" if cl.endswith("\n") else ""
        cl = cl[:-1].split("\n") if cl.endswith("\n") else cl.split("\n")
        body += chapter_paths_fixed(cl[3:], False)
    return "\n".join(pre + rules + body) + tail


def includes(path):
    """The files this one `#include`s, in order, read with the string reader and not a regex.

    The ONE place an include is recognised: `note_files` walks it, `chapter_file` counts it."""
    here, out = os.path.dirname(path), []
    for ln in read(path).split("\n"):
        if ln.startswith("#include "):
            inc = typst_string(ln)
            if inc is None:
                die("%s: `#include` with no file name: %s" % (path, ln))
            out.append(os.path.join(here, inc))
    return out


def imports(path):
    """The local `.typ` files this one `#import`s, in order.

    A typst content literal `[...]` evaluates every embedded call it holds as soon as the literal
    is built, not when it is later placed — so `#import "shared-laws.typ": *` runs every
    `#leanf(...)`/`#lean(...)` inside EVERY `#let x = [...]` that file defines, whether or not `x`
    is ever placed by the importer.  A gate that compiles or queries `path` therefore needs
    whatever an import reaches exactly as much as an include, and a chapter narrowed to itself
    alone must follow its own imports too, not just the root's.  A package import (`@preview/…`)
    names no local file and is skipped."""
    here, out = os.path.dirname(path), []
    for ln in read(path).split("\n"):
        if ln.startswith("#import "):
            inc = typst_string(ln)
            if inc is not None and not inc.startswith("@") and inc.endswith(".typ"):
                out.append(os.path.join(here, inc))
    return out


def note_files(root=None, root_dir=None, ch=None, _seen=None):
    """The root and every file it `#include`s or `#import`s, in order — a marker or a `cert:`
    lives in a chapter now, so a gate that reads the note alone reads a preamble and nothing else.

    A chapter named (`--ch 13`, `CH=13`) narrows this to THAT ONE FILE — `Cite.lean`'s
    `chapterFile` and the Makefile's `NOTESRC` both require `--ch` to print exactly one path, the
    file `typst compile`s as the chapter's own root, and neither reads any further.  What a
    compile of that file also reaches through `#import` (`shared-laws.typ`, whose content is
    evaluated whether or not the chapter places it) is a SEPARATE question — `shared_files`
    answers it, for the one caller (`diag-export --list`) that needs it.

    `_seen` dedups by absolute path so a file imported from two places (`note-prelude.typ`, from
    every chapter) is walked once."""
    root_dir = root_dir or ROOT_DIR
    root = root or NOTE
    path = root if os.path.isabs(root) else os.path.join(root_dir, root)
    seen = set() if _seen is None else _seen
    n = chapter_env(ch)
    if n is not None and os.path.abspath(path) == os.path.abspath(os.path.join(root_dir, NOTE)):
        return [chapter_file(n, root_dir)]
    ap = os.path.abspath(path)
    if ap in seen:
        return []
    seen.add(ap)
    out = [path]
    # An exporter OUTPUT is drawn from the note, never a source of it: listed, not walked, so an
    # import `diag-regen` has yet to draw is listed instead of crashing the listing that draws it.
    if ap.startswith(os.path.join(os.path.abspath(root_dir), "diag", "generated") + os.sep):
        return out
    for inc in imports(path) + includes(path):
        out += note_files(root=inc, root_dir=root_dir, _seen=seen)
    return out


def shared_files(root_dir=None):
    """Every local file some chapter of EITHER note `#import`s besides the prelude.

    Typst evaluates a content literal's embedded calls (`#leanf(...)`, in a `#let law = [...]`)
    as soon as the literal is built, not when it is later placed — so importing such a file for
    one binding also runs every OTHER binding's calls, whether or not the importer places them.
    A chapter's compile therefore needs every selector such a file names, not only the ones it
    itself places; `rootsToList` (`DiagExport.lean`) queries each of these with `list-shared=1` so
    a chapter-scoped listing draws the same panels a chapter-scoped compile is about to need,
    exactly as the whole book already does by way of whichever OTHER chapter places them."""
    root_dir = root_dir or ROOT_DIR
    prelude = os.path.abspath(os.path.join(root_dir, PRELUDE))
    out, seen = [], set()
    for root, *_ in NOTE_ROOTS.values():
        for ch in includes(os.path.join(root_dir, root)):
            for imp in imports(ch):
                ap = os.path.abspath(imp)
                if ap != prelude and ap not in seen:
                    seen.add(ap)
                    out.append(imp)
    return out


# ---- one chapter -----------------------------------------------------------------------------
# `CH` is the ONE variable every gate honours, and the four functions below are the ONE resolution
# of it: which file to compile and query (`note_root`/`note_pdf`), which chapter that is
# (`chapter_file`/`chapter_pdf`), and which displays lie in it (`sections_of`).  A gate therefore
# takes no chapter flag of its own — it defaults its path through `note_root()` — and a second gate
# cannot come to disagree with the first about what chapter 13 is.

def chapter_env(ch=None):
    """The chapter a gate was told to work on: the argument, else `$CH`, else None for the book.

    An empty value is no chapter (`make c CH=` is the whole book); anything that is not a number
    stops the run rather than being read as one.

    `--ch N` is read off the running process's own command line, so a gate that resolves its paths
    at import time answers for the chapter too; `take_chapter` takes the flag back out of the
    arguments the gate parses and puts it in the environment for the processes it starts."""
    if ch is None or ch == "":
        rest = sys.argv[1:]
        if "--ch" in rest:
            i = rest.index("--ch")
            if i + 1 >= len(rest):
                die("--ch takes the chapter's number, e.g. --ch 13")
            ch = rest[i + 1]
        else:
            ch = os.environ.get("CH", "")
    if isinstance(ch, int):
        return ch
    if not ch.strip():
        return None
    try:
        return int(ch.strip())
    except ValueError:
        die("CH=%s is no chapter: give the number its header declares, e.g. CH=13 "
            "(./scripts/note-files lists the chapters in order)" % ch)


def take_chapter(argv):
    """`--ch N` taken off `argv` and put in the environment, so every child process sees it too.

    Returns the remaining arguments.  One reader for the flag, so `--ch` and `CH=` cannot drift."""
    if "--ch" not in argv:
        return list(argv)
    i = argv.index("--ch")
    if i + 1 >= len(argv):
        die("--ch takes the chapter's number, e.g. --ch 13")
    os.environ["CH"] = str(chapter_env(argv[i + 1]))
    return list(argv[:i]) + list(argv[i + 2:])


def chapter_file(n, root_dir=None):
    """Chapter N's file: the file the root includes whose header declares chapter N."""
    root_dir = root_dir or ROOT_DIR
    path = os.path.join(root_dir, NOTE)
    if not read(path).startswith(ROOT_MARK):
        die("CH=%d, but %s is not split into chapters: run ./scripts/note-split first" % (n, NOTE))
    chs = includes(path)
    hit = [p for p, k in zip(chs, chapter_numbers(root_dir)) if k == n]
    if len(hit) != 1:
        die("%s chapter %d: %s includes —\n  %s"
            % ("no" if not hit else "more than one", n, NOTE,
               "\n  ".join("%d %s" % (chapter_number(p), os.path.relpath(p, root_dir)) for p in chs)))
    return hit[0]


def chapter_pdf(n, root_dir=None):
    """The pdf chapter N compiles to, beside its source — `make ch N=13` writes exactly this."""
    return os.path.splitext(chapter_file(n, root_dir))[0] + ".pdf"


def note_root(ch=None, root_dir=None):
    """THE .typ EVERY GATE COMPILES, QUERIES AND SCANS: the chapter when one is named, else the note.

    Repository-relative, the spelling every gate already had as its default."""
    n = chapter_env(ch)
    root_dir = root_dir or ROOT_DIR
    return NOTE if n is None else os.path.relpath(chapter_file(n, root_dir), root_dir)


def note_pdf(ch=None, root_dir=None):
    """The pdf `note_root` compiles to: the chapter's own, so page numbers are the chapter's."""
    return os.path.splitext(note_root(ch, root_dir))[0] + ".pdf"


def sections_of(n=None, root_dir=None):
    """The displays chapter N holds, named as a manifest names them — its `#disp` LABEL, or its
    number where the note leaves it unlabelled.

    READ OFF THE NOTE'S OWN QUERY (`scripts/note-meta`, which answers for the chapter because it
    resolves its root the same way), never by matching a number against a string: which chapter a
    display lies in is where the note puts it, and a `13.` that a heading move turned into `12.`
    would answer for the wrong chapter without saying so."""
    import json
    import subprocess
    root_dir = root_dir or ROOT_DIR
    n = chapter_env(n)
    if n is None:
        return None                      # no chapter named: a manifest keeps every row
    env = dict(os.environ, CH=str(n))
    p = subprocess.run([os.path.join(root_dir, "scripts", "note-meta")], cwd=root_dir,
                       capture_output=True, text=True, env=env)
    if p.returncode:
        die("chapter %d: scripts/note-meta failed, so which displays lie in it is unknown:\n%s"
            % (n, p.stderr.strip()))
    ms = [m for m in json.loads(p.stdout) if isinstance(m, dict)]
    return {d.get("label") or d["id"] for d in ms if d.get("kind") == "disp"}


def generated_imports(root_dir=None):
    """Every picture under diag/generated/ that one of the NOTES draws BY `#import`, named as the
    exporter takes it — the older of the two routes `diag-regen` redraws.

    The `#lean(...)`/`#leanc(...)` calls are NOT here: those are the note's own metadata and
    `diag-export --list` reads them, which is the one place a route and its list live together.

    The notes' own files are the list — each root with its chapters, and the prelude the split
    moved the root's `#import` lines into — and nothing else under `diag/`: a walk over the
    directory read a scratch slice `note-view` left behind as if the note had imported its picture,
    and the redraw failed on a name only the string exporter can take.
    Each import is RESOLVED AS A PATH from the file that makes it, so the note's own
    `generated/x.typ` and a chapter's `../generated/x.typ` are one name.  A pattern matching the
    note's spelling alone went blind to every chapter the split created and redrew fewer pictures
    while exiting 0; a path resolution needs no edit at the next directory a file moves to."""
    root_dir = root_dir or ROOT_DIR
    gen = os.path.join(root_dir, "diag", "generated")
    out = []
    files = [os.path.join(root_dir, PRELUDE)] + [p for n in NOTES for p in note_files(n, root_dir)]
    # The outputs are what this lists, never where it reads: one not yet drawn has no text.
    for path in (p for p in files if not os.path.abspath(p).startswith(gen + os.sep)):
        d = os.path.dirname(path)
        for ln in read(path).split("\n"):
            if ln[:1] + "".join(takewhile_alpha(ln[1:])) != "#import":
                continue
            s = typst_string(ln)
            if s is None or s.startswith("@") or s.startswith("/"):
                continue
            tgt = os.path.normpath(os.path.join(d, s))
            if tgt.startswith(gen + os.sep) and tgt.endswith(".typ"):
                out.append(os.path.relpath(tgt, gen)[:-len(".typ")])
    return sorted(set(out))


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
                            "--input", "nodraw=1", "--input", "title=" + note_title(root_dir),
                            os.path.relpath(path, root_dir), os.devnull],
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
    write_split(out)


def write_split(out):
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
    """The files a gate reads — `--ch 13` prints chapter 13's alone, `--help` the chapter recipe."""
    if "--help" in argv or "-h" in argv:
        sys.stdout.write(__doc__)
        return
    if "--generated" in argv:
        print(*generated_imports(), sep="\n")
        return
    # `--root`: the root `$NOTE` names; `--roots`: every note make compiles; `--names`: the names
    # `NOTE=` takes; `--chapters`: the numbers `CH=` takes in `$NOTE`; `--title`: `$NOTE`'s own title,
    # for a chapter compiled alone (`--input title=`); `--title-for PATH`: the title of whichever note
    # OWNS an arbitrary chapter/root path, for a caller (diff-crop) that is not `$NOTE`-scoped.
    # `--panels`: `$NOTE`'s commutative-canvas manifest.  `--shared`: every file some chapter of
    # EITHER note `#import`s besides the prelude (see `shared_files`).  Make and the Lean gates ask
    # these, so the notes are listed in this file alone.
    if "--root" in argv:
        return print(NOTE)
    if "--title" in argv:
        return print(note_title())
    if "--title-for" in argv:
        return print(title_of_root(root_for(argv[argv.index("--title-for") + 1])))
    if "--panels" in argv:
        return print(PANELS)
    if "--shared" in argv:
        return print(*shared_files(), sep="\n")
    if "--roots" in argv:
        return print(*NOTES, sep="\n")
    if "--names" in argv:
        return print(*NOTE_ROOTS, sep="\n")
    if "--chapters" in argv:
        return print(*chapter_numbers(), sep="\n")
    argv = take_chapter(argv)
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
