module

public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Finite axiomatizability of `𝗜𝚺 n`

For `n ≥ 1`, `𝗜𝚺 n` is finitely axiomatizable by a single `𝚷-[n + 2]` sentence.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

/-- For `n ≥ 1`, `𝗜𝚺 n` is finitely axiomatizable.
- [HP98, Theorem I.2.52] -/
axiom ISigma.finiteAxiomatizable (n : ℕ) (hn : 1 ≤ n) : Entailment.FiniteAxiomatizable (𝗜𝚺 n)

/-- For `n ≥ 1`, `𝗜𝚺 n` is axiomatized by a single `𝚷 (n + 2)` sentence.
- [HP98, Remark I.4.35(1)] -/
axiom ISigma.exists_pi_sentence (n : ℕ) (hn : 1 ≤ n) :
    ∃ σ : ArithmeticSentence, Hierarchy 𝚷 (n + 2) σ ∧ ({σ} : ArithmeticTheory) ≊ 𝗜𝚺 n

end LO.FirstOrder.Arithmetic
