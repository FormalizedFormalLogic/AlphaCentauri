#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let Con(T) = $sans("Con")(#T)$
#let RFN(Γ, T) = $sans("RFN")_#Γ (#T)$
// The theory `𝗜𝚺₀` with the scheme `name` for the class `Γ` with index `n`, `𝗣𝗛𝗣 𝚺 0`.
#let ISigma0Scheme(name) = (Γ, n) => $Theory(I)Σ_0 + #math.attach(Γ, b: n)"-"Theory(#name)$

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
    // names, and the theories whose notation abbreviates a base theory with a scheme, by their
    // symbol. Other theories in Lean's notation, such as `𝗜𝚺₁` or `𝗕𝚺 2`, need no entry.
    names: (
      "Con": T => Con(T),
      "Incon": T => $not#Con(T)$,
      "𝗥𝗙𝗡": RFN,
      "expAxiom": $sans("Exp")$,
      "LeastNumberScheme": Γ => $Theory(L)#Γ$,
      "BoundedUniversal": n => $Theory(U)_#n$,
      "𝗣𝗛𝗣": ISigma0Scheme("PHP"),
      "𝗪𝗣𝗛𝗣": ISigma0Scheme("WPHP"),
      "ZRing": $sans("ZR")$,
    ),
    // Labels of whole theories the rule above draws badly, keyed by the pretty-printed theory.
    labels: (:),
  )
]
