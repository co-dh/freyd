// The acceptance render for CIRCUIT-GEN §5's slice: `./scripts/circuit --slice` pasted whole.
// Everything below the header is generator output, so a redraw is a re-run of that line — never a
// hand edit.  Compile with `typst compile --root . diag/circuit-slice.typ` from the repo root.
#import "cpanel.typ": cpanel
#set page(width: auto, height: auto, margin: 14pt)
#set par(spacing: 20pt)

// 13.3.3d r1  S%∋ est(R°)   [F([A]) ⟶ [A]]
#cpanel((k: "seq", nin: 1, nout: 1, items: (
    (k: "box", nin: 1, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(S)", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
  ), seams: (
    (0, "E(F([A]))", ),
    (1, "E([A])", ),
  ), src: ("F([A])", ), tgt: ("[A]", )),
  cert: (expect: "S%∋ est(R°)", src: "F([A])", tgt: "[A]"))

// 13.3.3c r1  (𝟙×R°)(⊸ nil ∪ (p×𝟙) cons)   [A×[A] ⟶ [A]]
#cpanel((k: "seq", nin: 2, nout: 1, items: (
    (k: "stack", nin: 2, nout: 2, lanes: (
        (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
        (k: "seq", nin: 1, nout: 1, items: (
            (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
          ), seams: ()),
      )),
    (k: "union", nin: 2, nout: 1, bodies: (
        (k: "seq", nin: 2, nout: 1, items: (
            (k: "konst", nin: 2, nout: 1, body: (k: "seq", nin: 0, nout: 1, items: (
                  (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
                ), seams: ())),
          ), seams: ()),
        (k: "seq", nin: 2, nout: 1, items: (
            (k: "stack", nin: 2, nout: 2, lanes: (
                (k: "seq", nin: 1, nout: 1, items: (
                    (k: "box", nin: 1, nout: 1, label: "p", chamfer: true, frac: false, flip: false),
                  ), seams: ()),
                (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
              )),
            (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
          ), seams: ()),
      )),
  ), seams: (), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "(𝟙×R°)(⊸ nil ∪ (p×𝟙) cons)", src: "A×[A]", tgt: "[A]"))

// 13.3.3b r2  F(prefix) [nil,⊸ nil ∪ cons] list(p)   [F([A]) ⟶ [A]]
#cpanel((k: "seq", nin: 1, nout: 1, items: (
    (k: "case", nin: 1, nout: 1, bodies: (
        (k: "seq", nin: 0, nout: 1, items: (
            (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
          ), seams: ()),
        (k: "seq", nin: 2, nout: 1, items: (
            (k: "stack", nin: 2, nout: 2, lanes: (
                (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
                (k: "seq", nin: 1, nout: 1, items: (
                    (k: "box", nin: 1, nout: 1, label: "prefix", chamfer: true, frac: false, flip: false),
                  ), seams: ()),
              )),
            (k: "union", nin: 2, nout: 1, bodies: (
                (k: "seq", nin: 2, nout: 1, items: (
                    (k: "konst", nin: 2, nout: 1, body: (k: "seq", nin: 0, nout: 1, items: (
                          (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
                        ), seams: ())),
                  ), seams: ()),
                (k: "seq", nin: 2, nout: 1, items: (
                    (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
                  ), seams: ()),
              )),
          ), seams: ()),
      ), ports: (
        (),
        ("A", "[A]", ),
      )),
    (k: "box", nin: 1, nout: 1, label: "list(p)", chamfer: true, frac: false, flip: false),
  ), seams: (), src: ("F([A])", ), tgt: ("[A]", )),
  cert: (expect: "F(prefix) [nil,⊸ nil ∪ cons] list(p)", src: "F([A])", tgt: "[A]"))

