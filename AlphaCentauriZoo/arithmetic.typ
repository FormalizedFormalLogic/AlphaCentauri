#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let Con(T) = $sans("Con")(#T)$

#figure(
  caption: [
    Arithmetic Theory Zoo. An arrow points from a theory to a weaker one: solid if strictly weaker,
    dashed if weaker or equivalent. Red marks an open problem. A vertex lists equivalent theories.
  ],
  numbering: none,
)[
  #zoo(
    "./arithmetic.json",
    // The functions and sentences occurring in the theories, by the last component of their Lean
    // names. Theories in Lean's notation, such as `𝗜𝚺₁` or `𝗕𝚺 2`, need no entry.
    names: (
      "Con": T => Con(T),
      "Incon": T => $not#Con(T)$,
      "expAxiom": $sans("Exp")$,
      "LeastNumberScheme": Γ => $Theory(L)#Γ$,
      "BoundedUniversal": n => $U_#n$,
    ),
    // Labels of whole theories the rule above draws badly, keyed by the pretty-printed theory.
    labels: (:),
  )
]
