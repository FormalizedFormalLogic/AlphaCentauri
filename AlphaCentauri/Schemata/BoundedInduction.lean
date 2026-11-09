module

public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Induction for bounded existential formulas

$\mathsf{I}\mathsf{E}_1$ is induction for bounded existential formulas over $\mathsf{PA}^-$.

- [Wil85]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {ξ : Type*}

/-- Bounded existential (`E₁`) formulas `∃ x₁ < t₁, ⋯, ∃ xₖ < tₖ, θ` with `θ` open, where the
bound `tᵢ` of `xᵢ` mentions only the earlier variables. -/
inductive Semiformula.BoundedExistential : {n : ℕ} → ArithmeticSemiformula ξ n → Prop
  | of_open {n : ℕ} {φ : ArithmeticSemiformula ξ n} : φ.Open → BoundedExistential φ
  | bexsLT {n : ℕ} (t : ArithmeticSemiterm ξ n) {φ : ArithmeticSemiformula ξ (n + 1)} :
      BoundedExistential φ → BoundedExistential (Semiformula.bexsLT t φ)

/-- Induction for bounded existential formulas over $\mathsf{PA}^-$.
- [Wil85] -/
abbrev IE1 : ArithmeticTheory := 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ Semiformula.BoundedExistential

@[inherit_doc] notation "𝗜𝗘₁" => IE1

instance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝗘₁ :=
  Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻)
    (Entailment.WeakerThan.ofSubset Set.subset_union_left)

end FFL.FirstOrder.Arithmetic
