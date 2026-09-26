module

public import Foundation.FirstOrder.Incompleteness.Reflection.Local

@[expose] public section
/-!
# Iterated consistency

The tower of iterated-consistency extensions `T₀ = T`, `Tₙ₊₁ = Tₙ ∪ Tₙ.Con` of an arithmetic
theory, and its relation to iterated provability of `⊥`.

- [Lin97, §4]
- [AB05, §4.1]
-/

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment ProvabilityAbstraction

/-- The pair of the iterated-consistency theory `T₀ = T`, `Tₙ₊₁ = Tₙ ∪ Tₙ.Con` and its
$\Delta_1$-definability witness.
- [Lin97, §4, p. 55, the `Con(n, S)` tower]
- [AB05, §4.1, the `Tₙ` tower] -/
noncomputable def _root_.FFL.FirstOrder.Theory.iterConSigma
    (T : ArithmeticTheory) [T.Δ₁] : ℕ → Σ' S : ArithmeticTheory, S.Δ₁
  | 0 => ⟨T, ‹_›⟩
  | n + 1 =>
    match T.iterConSigma n with
    | ⟨S, hS⟩ => letI := hS; ⟨S ∪ S.Con, inferInstance⟩

/-- The `n`-times iterated-consistency extension of `T`: `T₀ = T`, `Tₙ₊₁ = Tₙ ∪ Tₙ.Con`.
- [Lin97, §4, p. 55]
- [AB05, §4.1] -/
noncomputable def _root_.FFL.FirstOrder.Theory.iterCon (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) :
    ArithmeticTheory := (T.iterConSigma n).1

noncomputable instance (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) : (T.iterCon n).Δ₁ :=
  (T.iterConSigma n).2

variable {T : ArithmeticTheory} [T.Δ₁]

/-- Iterated consistency reduces to iterated provability of `⊥`: over `𝗜𝚺₁`, the formalized
consistency statement of the `n`-times iterated-consistency extension of `T` is equivalent to
`T`'s own provability predicate not proving `⊥` after `n + 1` applications.
- [Lin97, Lemma 4.2]
- [AB05, Lemma 21] -/
axiom provable_iterCon_iff_not_iterate_standardProvability_bot (n : ℕ) :
    𝗜𝚺₁ ⊢ (T.iterCon n).consistent.val 🡘 ∼(T.standardProvability^[n + 1] ⊥)

end FFL.FirstOrder.Arithmetic
