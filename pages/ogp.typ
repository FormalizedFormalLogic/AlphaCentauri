// The image shown where a page of the site is shared (Open Graph and Twitter cards), 1200 × 630
// pixels. `pages/ogp.png` is generated from it by `just ogp`, and committed: regenerate it after
// editing this file.

#let accent = rgb("#4493f8")
#let muted = rgb("#9198a1")

#set page(width: 1200pt, height: 630pt, margin: (x: 90pt, y: 0pt), fill: rgb("#0d1117"))
#set text(font: ("New Computer Modern", "Libertinus Serif"), fill: rgb("#e6edf3"))

#place(top + left, dy: 120pt)[
  #text(size: 118pt, weight: "bold")[AlphaCentauri]
]

#place(top + left, dy: 290pt)[
  #text(size: 40pt, fill: muted)[Formalization of first-order arithmetic in Lean 4]
]

// The hierarchy of the theories, the subject of the library.
#place(top + left, dy: 385pt)[
  #text(size: 40pt, fill: accent)[
    $ sans("I")Delta_0 subset.neq sans("I")Sigma_1 subset.neq sans("I")Sigma_2 subset.neq dots.c subset.neq sans("PA") $
  ]
]

#place(bottom + left, dy: -60pt)[
  #text(size: 28pt, fill: muted)[formalizedformallogic.org/AlphaCentauri]
]
