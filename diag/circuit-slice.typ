// The acceptance render for CIRCUIT-GEN §5's slice, written whole by `./scripts/circuit --slice`.
// Everything here is generator output, so a redraw is a re-run of that line — never a hand edit.
// `make slice` regenerates and compiles it; `make p` runs that too.
#import "cpanel.typ": cpanel
#set page(width: auto, height: auto, margin: 0.8cm, fill: white)
#set par(spacing: 20pt)

// 13.3.3d r1  S%∋ est(R°)   [F([A]) ⟶ [A]]
#cpanel((k: "seq", nin: 2, nout: 1, items: (
    (k: "box", nin: 2, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(S)", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
  ), seams: (
    (0, "EF[A]", ),
    (1, "E[A]", ),
  ), src: ("A", "[A]", ), tgt: ("[A]", )),
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
  ), seams: (), src: ("F[A]", ), tgt: ("[A]", )),
  cert: (expect: "F(prefix) [nil,⊸ nil ∪ cons] list(p)", src: "F([A])", tgt: "[A]"))

// ∩ (13.3.3b)  prefix° prefix∩R   [[A] ⟶ [A]]
#cpanel((k: "cap", nin: 1, nout: 1, lanes: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 1, label: "prefix", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 1, nout: 1, label: "prefix", chamfer: true, frac: false, flip: false),
      ), seams: ()),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: false),
      ), seams: ()),
  ), src: ("[A]", ), tgt: ("[A]", )),
  cert: (expect: "prefix° prefix∩R", src: "[A]", tgt: "[A]"))

// → (13.3.3c)  (π₁p→cons,⊸ nil)   [A×[A] ⟶ [A]]
#cpanel((k: "cond", nin: 2, nout: 1, guard: (k: "seq", nin: 2, nout: 1, items: (
      (k: "proj", nin: 2, nout: 1, at: 0, label: "π₁", keep: (1, 1, )),
      (k: "box", nin: 1, nout: 1, label: "p", chamfer: true, frac: false, flip: false),
    ), seams: ()), bodies: (
    (k: "seq", nin: 2, nout: 1, items: (
        (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
      ), seams: ()),
    (k: "seq", nin: 2, nout: 1, items: (
        (k: "konst", nin: 2, nout: 1, body: (k: "seq", nin: 0, nout: 1, items: (
              (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
            ), seams: ())),
      ), seams: ()),
  ), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "(π₁p→cons,⊸ nil)", src: "A×[A]", tgt: "[A]"))

// ⦇⦈ (13.3.3b)  ⦇[nil,⊸ nil ∪ cons]⦈   [[A] ⟶ [A]]
#cpanel((k: "cata", nin: 1, nout: 1, body: (k: "seq", nin: 1, nout: 1, items: (
      (k: "case", nin: 1, nout: 1, bodies: (
          (k: "seq", nin: 0, nout: 1, items: (
              (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
            ), seams: ()),
          (k: "seq", nin: 2, nout: 1, items: (
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
    ), seams: ()), label: none, port: ("F[A]", ), src: ("[A]", ), tgt: ("[A]", )),
  cert: (expect: "⦇[nil,⊸ nil ∪ cons]⦈", src: "[A]", tgt: "[A]"))

// ⦇⦈ (13.4.4a)  ⦇S⦈   [tree(A) ⟶ [A]×[A]]
#cpanel((k: "cata", nin: 1, nout: 2, body: (k: "seq", nin: 2, nout: 2, items: (
      (k: "box", nin: 2, nout: 2, label: "S", chamfer: true, frac: false, flip: false),
    ), seams: ()), label: none, port: ("A", "[[A]×[A]]", ), src: ("tree(A)", ), tgt: ("[A]", "[A]", )),
  cert: (expect: "⦇S⦈", src: "tree(A)", tgt: "[A]×[A]"))

// 13.4.4a r2  𝟙%∋ E(⦇S⦈)E(choose)est(R°)   [tree(A) ⟶ [A]]
#cpanel((k: "seq", nin: 1, nout: 1, items: (
    (k: "box", nin: 1, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(⦇S⦈)", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(choose)", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
  ), seams: (
    (0, "E(tree(A))", ),
    (1, "E([A]×[A])", ),
    (2, "E[A]", ),
  ), src: ("tree(A)", ), tgt: ("[A]", )),
  cert: (expect: "𝟙%∋ E(⦇S⦈)E(choose)est(R°)", src: "tree(A)", tgt: "[A]"))

// 13.4.4a r4  𝟙%∋ E(⦇S⦈)est((R×R)°)𝟙%∋ E(choose)est(R°)   [tree(A) ⟶ [A]]
#cpanel((k: "seq", nin: 1, nout: 1, items: (
    (k: "box", nin: 1, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(⦇S⦈)", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 2, label: "est((R×R)°)", chamfer: true, frac: false, flip: false),
    (k: "box", nin: 2, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(choose)", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
  ), seams: (
    (0, "E(tree(A))", ),
    (1, "E([A]×[A])", ),
    (4, "E[A]", ),
  ), src: ("tree(A)", ), tgt: ("[A]", )),
  cert: (expect: "𝟙%∋ E(⦇S⦈)est((R×R)°)𝟙%∋ E(choose)est(R°)", src: "tree(A)", tgt: "[A]"))
