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
    (
      0,
      ("EF[A]", ),
    ),
    (
      1,
      ("E[A]", ),
    ),
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
        (k: "seq", nin: 1, nout: 1, items: (
            (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
            (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
          ), seams: ()),
        (k: "seq", nin: 1, nout: 1, items: (
            (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
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
          ), seams: (
            (
              0,
              ("A", "[A]", ),
            ),
          )),
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
#cpanel((k: "box", nin: 2, nout: 1, label: "(π₁p→cons,⊸ nil)", chamfer: false, frac: false, flip: false, src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "(π₁p→cons,⊸ nil)", src: "A×[A]", tgt: "[A]"))

// ⦇⦈ (13.3.3b)  ⦇[nil,⊸ nil ∪ cons]⦈   [[A] ⟶ [A]]
#cpanel((k: "cata", nin: 1, nout: 1, body: (k: "seq", nin: 1, nout: 1, items: (
      (k: "case", nin: 1, nout: 1, bodies: (
          (k: "seq", nin: 1, nout: 1, items: (
              (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
              (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
            ), seams: ()),
          (k: "seq", nin: 1, nout: 1, items: (
              (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
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
            ), seams: (
              (
                0,
                ("A", "[A]", ),
              ),
            )),
        )),
    ), seams: ()), label: none, port: ("F[A]", ), src: ("[A]", ), tgt: ("[A]", )),
  cert: (expect: "⦇[nil,⊸ nil ∪ cons]⦈", src: "[A]", tgt: "[A]"))

// ⦇⦈ (13.4.4a)  ⦇S⦈   [tree(A) ⟶ [A]×[A]]
#cpanel((k: "cata", nin: 1, nout: 2, body: (k: "seq", nin: 2, nout: 2, items: (
      (k: "box", nin: 2, nout: 2, label: "S", chamfer: true, frac: false, flip: false),
    ), seams: ()), label: none, port: ("A", "[[A]²]", ), src: ("tree A", ), tgt: ("[A]", "[A]", )),
  cert: (expect: "⦇S⦈", src: "tree(A)", tgt: "[A]×[A]"))

// 13.4.4a r2  𝟙%∋ E(⦇S⦈)E(choose)est(R°)   [tree(A) ⟶ [A]]
#cpanel((k: "seq", nin: 1, nout: 1, items: (
    (k: "box", nin: 1, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(⦇S⦈)", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(choose)", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
  ), seams: (
    (
      0,
      ("E tree A", ),
    ),
    (
      1,
      ("E[A]²", ),
    ),
    (
      2,
      ("E[A]", ),
    ),
  ), src: ("tree A", ), tgt: ("[A]", )),
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
    (
      0,
      ("E tree A", ),
    ),
    (
      1,
      ("E[A]²", ),
    ),
    (
      4,
      ("E[A]", ),
    ),
  ), src: ("tree A", ), tgt: ("[A]", )),
  cert: (expect: "𝟙%∋ E(⦇S⦈)est((R×R)°)𝟙%∋ E(choose)est(R°)", src: "tree(A)", tgt: "[A]"))

// subseq :2932 sbA4  [nil%∋,((𝟙×∋)(cons∪π₂))%∋]   [F(E([A])) ⟶ E([A])]
#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
        (k: "box", nin: 1, nout: 1, label: "E(nil)", chamfer: false, frac: false, flip: false),
      ), seams: (
        (
          1,
          ("E𝟏", ),
        ),
      )),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 2, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
        (k: "box", nin: 1, nout: 1, label: "E((𝟙×∋)(cons∪π₂))", chamfer: false, frac: false, flip: false),
      ), seams: (
        (
          0,
          ("A", "E[A]", ),
        ),
        (
          1,
          ("E(A×E[A])", ),
        ),
      )),
  ), src: ("FE[A]", ), tgt: ("E[A]", )),
  cert: (expect: "[nil%∋,((𝟙×∋)(cons∪π₂))%∋]", src: "F(E([A]))", tgt: "E([A])"))

// subseq :2936 sbA5  [nil 𝟙%∋,((𝟙×∋)(cons∪π₂))%∋]   [F(E([A])) ⟶ E([A])]
#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
        (k: "box", nin: 1, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
      ), seams: (
        (
          1,
          ("[A]", ),
        ),
      )),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 2, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
        (k: "box", nin: 1, nout: 1, label: "E((𝟙×∋)(cons∪π₂))", chamfer: false, frac: false, flip: false),
      ), seams: (
        (
          0,
          ("A", "E[A]", ),
        ),
        (
          1,
          ("E(A×E[A])", ),
        ),
      )),
  ), src: ("FE[A]", ), tgt: ("E[A]", )),
  cert: (expect: "[nil 𝟙%∋,((𝟙×∋)(cons∪π₂))%∋]", src: "F(E([A]))", tgt: "E([A])"))

// greedy :3920 mbp  R°R°   [A ⟶ A]
#cpanel((k: "seq", nin: 1, nout: 1, items: (
    (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
    (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
  ), seams: (), src: ("A", ), tgt: ("A", )),
  cert: (expect: "R°R°", src: "A", tgt: "A"))

// greedy :3925 mbp  R°   [A ⟶ A]
#cpanel((k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true, src: ("A", ), tgt: ("A", )),
  cert: (expect: "R°", src: "A", tgt: "A"))

// takewhile :4230 twp  α prefix list(p)   [F([A]) ⟶ [A]]
#cpanel((k: "seq", nin: 2, nout: 1, items: (
    (k: "box", nin: 2, nout: 1, label: "α", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "prefix", chamfer: true, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "list(p)", chamfer: true, frac: false, flip: false),
  ), seams: (), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "α prefix list(p)", src: "F([A])", tgt: "[A]"))

// takewhile :4239 twp  F(prefix) [nil,⊸ nil ∪ (p×list(p)) cons]   [F([A]) ⟶ [A]]
#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
      ), seams: ()),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
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
                (k: "stack", nin: 2, nout: 2, lanes: (
                    (k: "seq", nin: 1, nout: 1, items: (
                        (k: "box", nin: 1, nout: 1, label: "p", chamfer: true, frac: false, flip: false),
                      ), seams: ()),
                    (k: "seq", nin: 1, nout: 1, items: (
                        (k: "box", nin: 1, nout: 1, label: "list(p)", chamfer: true, frac: false, flip: false),
                      ), seams: ()),
                  )),
                (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
              ), seams: ()),
          )),
      ), seams: (
        (
          0,
          ("A", "[A]", ),
        ),
      )),
  ), src: ("F[A]", ), tgt: ("[A]", )),
  cert: (expect: "F(prefix) [nil,⊸ nil ∪ (p×list(p)) cons]", src: "F([A])", tgt: "[A]"))

// takewhile :4244 twp  [nil,⊸ nil ∪ (p×(prefix list(p))) cons]   [F([A]) ⟶ [A]]
#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
      ), seams: ()),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
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
                    (k: "seq", nin: 1, nout: 1, items: (
                        (k: "box", nin: 1, nout: 1, label: "prefix", chamfer: true, frac: false, flip: false),
                        (k: "box", nin: 1, nout: 1, label: "list(p)", chamfer: true, frac: false, flip: false),
                      ), seams: ()),
                  )),
                (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
              ), seams: ()),
          )),
      ), seams: (
        (
          0,
          ("A", "[A]", ),
        ),
      )),
  ), src: ("F[A]", ), tgt: ("[A]", )),
  cert: (expect: "[nil,⊸ nil ∪ (p×(prefix list(p))) cons]", src: "F([A])", tgt: "[A]"))

// takewhile :4247 twp  F(prefix list(p))S   [F([A]) ⟶ [A]]
#cpanel((k: "seq", nin: 2, nout: 1, items: (
    (k: "box", nin: 2, nout: 2, label: "F(prefix list(p))", chamfer: true, frac: false, flip: false),
    (k: "box", nin: 2, nout: 1, label: "S", chamfer: true, frac: false, flip: false),
  ), seams: (), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "F(prefix list(p))S", src: "F([A])", tgt: "[A]"))

// takewhile :4294 twp  (𝟙×R°)⊸ nil ∪ (p×R°) cons   [A×[A] ⟶ [A]]
#cpanel((k: "union", nin: 2, nout: 1, bodies: (
    (k: "seq", nin: 2, nout: 1, items: (
        (k: "stack", nin: 2, nout: 2, lanes: (
            (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
            (k: "seq", nin: 1, nout: 1, items: (
                (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
              ), seams: ()),
          )),
        (k: "konst", nin: 2, nout: 1, body: (k: "seq", nin: 0, nout: 1, items: (
              (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
            ), seams: ())),
      ), seams: ()),
    (k: "seq", nin: 2, nout: 1, items: (
        (k: "stack", nin: 2, nout: 2, lanes: (
            (k: "seq", nin: 1, nout: 1, items: (
                (k: "box", nin: 1, nout: 1, label: "p", chamfer: true, frac: false, flip: false),
              ), seams: ()),
            (k: "seq", nin: 1, nout: 1, items: (
                (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
              ), seams: ()),
          )),
        (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
      ), seams: ()),
  ), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "(𝟙×R°)⊸ nil ∪ (p×R°) cons", src: "A×[A]", tgt: "[A]"))

// takewhile :4299 twp  ⊸ nil ∪ (p×R°) cons   [A×[A] ⟶ [A]]
#cpanel((k: "union", nin: 2, nout: 1, bodies: (
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
            (k: "seq", nin: 1, nout: 1, items: (
                (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
              ), seams: ()),
          )),
        (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
      ), seams: ()),
  ), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "⊸ nil ∪ (p×R°) cons", src: "A×[A]", tgt: "[A]"))

// takewhile :4303 twp  ⊸ nil ∪ (p×𝟙) cons R°   [A×[A] ⟶ [A]]
#cpanel((k: "union", nin: 2, nout: 1, bodies: (
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
        (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
      ), seams: ()),
  ), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "⊸ nil ∪ (p×𝟙) cons R°", src: "A×[A]", tgt: "[A]"))

// takewhile :4307 twp  ⊸ nil R° ∪ (p×𝟙) cons R°   [A×[A] ⟶ [A]]
#cpanel((k: "union", nin: 2, nout: 1, bodies: (
    (k: "seq", nin: 2, nout: 1, items: (
        (k: "konst", nin: 2, nout: 1, body: (k: "seq", nin: 0, nout: 1, items: (
              (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
            ), seams: ())),
        (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
      ), seams: ()),
    (k: "seq", nin: 2, nout: 1, items: (
        (k: "stack", nin: 2, nout: 2, lanes: (
            (k: "seq", nin: 1, nout: 1, items: (
                (k: "box", nin: 1, nout: 1, label: "p", chamfer: true, frac: false, flip: false),
              ), seams: ()),
            (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
          )),
        (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
        (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
      ), seams: ()),
  ), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "⊸ nil R° ∪ (p×𝟙) cons R°", src: "A×[A]", tgt: "[A]"))

// takewhile :4312 twp  (⊸ nil ∪ (p×𝟙) cons)R°   [A×[A] ⟶ [A]]
#cpanel((k: "seq", nin: 2, nout: 1, items: (
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
    (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
  ), seams: (), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "(⊸ nil ∪ (p×𝟙) cons)R°", src: "A×[A]", tgt: "[A]"))

// takewhile :4345 twp  [nil%∋ est(R°),(⊸ nil ∪ (p×𝟙) cons)%∋ est(R°)]   [F([A]) ⟶ [A]]
#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
        (k: "box", nin: 1, nout: 1, label: "E(nil)", chamfer: false, frac: false, flip: false),
        (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
      ), seams: (
        (
          1,
          ("E𝟏", ),
        ),
        (
          2,
          ("E[A]", ),
        ),
      )),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 2, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
        (k: "box", nin: 1, nout: 1, label: "E(⊸ nil ∪ (p×𝟙) cons)", chamfer: false, frac: false, flip: false),
        (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
      ), seams: (
        (
          0,
          ("A", "[A]", ),
        ),
        (
          1,
          ("E(A×[A])", ),
        ),
        (
          2,
          ("E[A]", ),
        ),
      )),
  ), src: ("F[A]", ), tgt: ("[A]", )),
  cert: (expect: "[nil%∋ est(R°),(⊸ nil ∪ (p×𝟙) cons)%∋ est(R°)]", src: "F([A])", tgt: "[A]"))

// takewhile :4348 twp  [nil,(⊸ nil ∪ (p×𝟙) cons)%∋ est(R°)]   [F([A]) ⟶ [A]]
#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
      ), seams: ()),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 2, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
        (k: "box", nin: 1, nout: 1, label: "E(⊸ nil ∪ (p×𝟙) cons)", chamfer: false, frac: false, flip: false),
        (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
      ), seams: (
        (
          0,
          ("A", "[A]", ),
        ),
        (
          1,
          ("E(A×[A])", ),
        ),
        (
          2,
          ("E[A]", ),
        ),
      )),
  ), src: ("F[A]", ), tgt: ("[A]", )),
  cert: (expect: "[nil,(⊸ nil ∪ (p×𝟙) cons)%∋ est(R°)]", src: "F([A])", tgt: "[A]"))

// takewhile :4351 twp  [nil,(π₁p→cons,⊸ nil)]   [F([A]) ⟶ [A]]
#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
      ), seams: ()),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 2, nout: 1, label: "(π₁p→cons,⊸ nil)", chamfer: false, frac: false, flip: false),
      ), seams: (
        (
          0,
          ("A", "[A]", ),
        ),
      )),
  ), src: ("F[A]", ), tgt: ("[A]", )),
  cert: (expect: "[nil,(π₁p→cons,⊸ nil)]", src: "F([A])", tgt: "[A]"))

// takewhile :4422 twp  (prefix list(p))%∋ est(R°)   [[A] ⟶ [A]]
#cpanel((k: "seq", nin: 1, nout: 1, items: (
    (k: "box", nin: 1, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(prefix list(p))", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
  ), seams: (
    (
      1,
      ("E[A]", ),
    ),
  ), src: ("[A]", ), tgt: ("[A]", )),
  cert: (expect: "(prefix list(p))%∋ est(R°)", src: "[A]", tgt: "[A]"))

// takewhile :4433 :5120 twp  ⦇S%∋ est(R°)⦈   [[A] ⟶ [A]]
#cpanel((k: "cata", nin: 1, nout: 1, body: (k: "seq", nin: 2, nout: 1, items: (
      (k: "box", nin: 2, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
      (k: "box", nin: 1, nout: 1, label: "E(S)", chamfer: false, frac: false, flip: false),
      (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
    ), seams: (
      (
        0,
        ("EF[A]", ),
      ),
      (
        1,
        ("E[A]", ),
      ),
    )), label: none, port: ("A", "[A]", ), src: ("[A]", ), tgt: ("[A]", )),
  cert: (expect: "⦇S%∋ est(R°)⦈", src: "[A]", tgt: "[A]"))

// takewhile :4440 twp  ⦇[nil,(π₁p→cons,⊸ nil)]⦈   [[A] ⟶ [A]]
#cpanel((k: "cata", nin: 1, nout: 1, body: (k: "seq", nin: 1, nout: 1, items: (
      (k: "case", nin: 1, nout: 1, bodies: (
          (k: "seq", nin: 1, nout: 1, items: (
              (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
              (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
            ), seams: ()),
          (k: "seq", nin: 1, nout: 1, items: (
              (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
              (k: "box", nin: 2, nout: 1, label: "(π₁p→cons,⊸ nil)", chamfer: false, frac: false, flip: false),
            ), seams: (
              (
                0,
                ("A", "[A]", ),
              ),
            )),
        )),
    ), seams: ()), label: none, port: ("F[A]", ), src: ("[A]", ), tgt: ("[A]", )),
  cert: (expect: "⦇[nil,(π₁p→cons,⊸ nil)]⦈", src: "[A]", tgt: "[A]"))

// mss :4528 :4925 mss-pic  (segment sum)%∋ est(≥)   [[A] ⟶ A]
#cpanel((k: "seq", nin: 1, nout: 1, items: (
    (k: "box", nin: 1, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(segment sum)", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "est(≥)", chamfer: true, frac: false, flip: false),
  ), seams: (
    (
      0,
      ("E[A]", ),
    ),
    (
      1,
      ("EA", ),
    ),
  ), src: ("[A]", ), tgt: ("A", )),
  cert: (expect: "(segment sum)%∋ est(≥)", src: "[A]", tgt: "A"))

// mss :4530 mss-pic  (suffix (prefix sum))%∋ est(≥)   [[A] ⟶ A]
#cpanel((k: "seq", nin: 1, nout: 1, items: (
    (k: "box", nin: 1, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(suffix prefix sum)", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "est(≥)", chamfer: true, frac: false, flip: false),
  ), seams: (
    (
      0,
      ("E[A]", ),
    ),
    (
      1,
      ("EA", ),
    ),
  ), src: ("[A]", ), tgt: ("A", )),
  cert: (expect: "(suffix (prefix sum))%∋ est(≥)", src: "[A]", tgt: "A"))

// mss :4533 mss-pic  suffix%∋ E(prefix sum) est(≥)   [[A] ⟶ A]
#cpanel((k: "seq", nin: 1, nout: 1, items: (
    (k: "box", nin: 1, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(suffix)", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(prefix sum)", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "est(≥)", chamfer: true, frac: false, flip: false),
  ), seams: (
    (
      1,
      ("E[A]", ),
    ),
    (
      2,
      ("EA", ),
    ),
  ), src: ("[A]", ), tgt: ("A", )),
  cert: (expect: "suffix%∋ E(prefix sum) est(≥)", src: "[A]", tgt: "A"))

// mss :4536 mss-pic  suffix%∋ E((prefix sum)%∋)union est(≥)   [[A] ⟶ A]
#cpanel((k: "seq", nin: 1, nout: 1, items: (
    (k: "box", nin: 1, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(suffix)", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(𝟙%∋ E(prefix sum))", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "union", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "est(≥)", chamfer: true, frac: false, flip: false),
  ), seams: (
    (
      1,
      ("E[A]", ),
    ),
    (
      2,
      ("EEA", ),
    ),
    (
      3,
      ("EA", ),
    ),
  ), src: ("[A]", ), tgt: ("A", )),
  cert: (expect: "suffix%∋ E((prefix sum)%∋)union est(≥)", src: "[A]", tgt: "A"))

// mss :4541 mss-pic  suffix%∋ E((prefix sum)%∋)E(est(≥)) est(≥)   [[A] ⟶ A]
#cpanel((k: "seq", nin: 1, nout: 1, items: (
    (k: "box", nin: 1, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(suffix)", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(𝟙%∋ E(prefix sum))", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(est(≥))", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "est(≥)", chamfer: true, frac: false, flip: false),
  ), seams: (
    (
      1,
      ("E[A]", ),
    ),
    (
      2,
      ("EEA", ),
    ),
    (
      3,
      ("EA", ),
    ),
  ), src: ("[A]", ), tgt: ("A", )),
  cert: (expect: "suffix%∋ E((prefix sum)%∋)E(est(≥)) est(≥)", src: "[A]", tgt: "A"))

// mss :4544 :4933 mss-pic  suffix%∋ E((prefix sum)%∋ est(≥))est(≥)   [[A] ⟶ A]
#cpanel((k: "seq", nin: 1, nout: 1, items: (
    (k: "box", nin: 1, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(suffix)", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(𝟙%∋ E(prefix sum)est(≥))", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "est(≥)", chamfer: true, frac: false, flip: false),
  ), seams: (
    (
      1,
      ("E[A]", ),
    ),
    (
      2,
      ("EA", ),
    ),
  ), src: ("[A]", ), tgt: ("A", )),
  cert: (expect: "suffix%∋ E((prefix sum)%∋ est(≥))est(≥)", src: "[A]", tgt: "A"))

// filter :5025 twp  (𝟙×R°)(π₂∪(p×𝟙) cons)   [A×[A] ⟶ [A]]
#cpanel((k: "seq", nin: 2, nout: 1, items: (
    (k: "stack", nin: 2, nout: 2, lanes: (
        (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
        (k: "seq", nin: 1, nout: 1, items: (
            (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
          ), seams: ()),
      )),
    (k: "union", nin: 2, nout: 1, bodies: (
        (k: "seq", nin: 2, nout: 1, items: (
            (k: "proj", nin: 2, nout: 1, at: 1, label: "π₂", keep: (1, 1, )),
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
  cert: (expect: "(𝟙×R°)(π₂∪(p×𝟙) cons)", src: "A×[A]", tgt: "[A]"))

// filter :5027 twp  (π₂∪(p×𝟙) cons)R°   [A×[A] ⟶ [A]]
#cpanel((k: "seq", nin: 2, nout: 1, items: (
    (k: "union", nin: 2, nout: 1, bodies: (
        (k: "seq", nin: 2, nout: 1, items: (
            (k: "proj", nin: 2, nout: 1, at: 1, label: "π₂", keep: (1, 1, )),
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
    (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
  ), seams: (), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "(π₂∪(p×𝟙) cons)R°", src: "A×[A]", tgt: "[A]"))

// filter :5052 twp  [nil,(π₂∪(p×𝟙) cons)%∋ est(R°)]   [F([A]) ⟶ [A]]
#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
      ), seams: ()),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 2, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
        (k: "box", nin: 1, nout: 1, label: "E(π₂∪(p×𝟙) cons)", chamfer: false, frac: false, flip: false),
        (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
      ), seams: (
        (
          0,
          ("A", "[A]", ),
        ),
        (
          1,
          ("E(A×[A])", ),
        ),
        (
          2,
          ("E[A]", ),
        ),
      )),
  ), src: ("F[A]", ), tgt: ("[A]", )),
  cert: (expect: "[nil,(π₂∪(p×𝟙) cons)%∋ est(R°)]", src: "F([A])", tgt: "[A]"))

// filter :5055 twp  [nil,(π₁p→cons,π₂)]   [F([A]) ⟶ [A]]
#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
      ), seams: ()),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 2, nout: 1, label: "(π₁p→cons,π₂)", chamfer: false, frac: false, flip: false),
      ), seams: (
        (
          0,
          ("A", "[A]", ),
        ),
      )),
  ), src: ("F[A]", ), tgt: ("[A]", )),
  cert: (expect: "[nil,(π₁p→cons,π₂)]", src: "F([A])", tgt: "[A]"))

// filter :5128 fpic  ⦇[nil,(π₁p→cons,π₂)]⦈   [[A] ⟶ [A]]
#cpanel((k: "cata", nin: 1, nout: 1, body: (k: "seq", nin: 1, nout: 1, items: (
      (k: "case", nin: 1, nout: 1, bodies: (
          (k: "seq", nin: 1, nout: 1, items: (
              (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
              (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
            ), seams: ()),
          (k: "seq", nin: 1, nout: 1, items: (
              (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
              (k: "box", nin: 2, nout: 1, label: "(π₁p→cons,π₂)", chamfer: false, frac: false, flip: false),
            ), seams: (
              (
                0,
                ("A", "[A]", ),
              ),
            )),
        )),
    ), seams: ()), label: none, port: ("F[A]", ), src: ("[A]", ), tgt: ("[A]", )),
  cert: (expect: "⦇[nil,(π₁p→cons,π₂)]⦈", src: "[A]", tgt: "[A]"))
