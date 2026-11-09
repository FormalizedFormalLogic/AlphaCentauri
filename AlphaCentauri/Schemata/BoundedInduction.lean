module

public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Induction for bounded existential formulas

$\mathsf{I}\mathsf{E}_k$ is induction for $E_k$ formulas over $\mathsf{PA}^-$, where $E_k$ and
$U_k$ count the alternations of blocks of bounded quantifiers over an open matrix.

- [Wil85]
- [Smi93, Definition 2.1, Definition 2.2]
- [DAq05, §8]
- [Car16]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {ξ : Type*}

mutual

/-- `Eₖ` formulas: a block `∃ x₁ < t₁, ⋯, ∃ xₘ < tₘ` over a `Uₖ₋₁` formula, or an open formula
for `k = 0`, where the bound `tᵢ` of `xᵢ` mentions only the earlier variables.
- [Wil85]
- [Smi93, Definition 2.1] -/
inductive Semiformula.BoundedExistential : ℕ → {n : ℕ} → ArithmeticSemiformula ξ n → Prop
  | of_open {k n : ℕ} {φ : ArithmeticSemiformula ξ n} : φ.Open → BoundedExistential k φ
  | of_boundedUniversal {k n : ℕ} {φ : ArithmeticSemiformula ξ n} :
      BoundedUniversal k φ → BoundedExistential (k + 1) φ
  | bexsLT {k n : ℕ} (t : ArithmeticSemiterm ξ n) {φ : ArithmeticSemiformula ξ (n + 1)} :
      BoundedExistential (k + 1) φ → BoundedExistential (k + 1) (Semiformula.bexsLT t φ)

/-- `Uₖ` formulas: a block `∀ x₁ < t₁, ⋯, ∀ xₘ < tₘ` over an `Eₖ₋₁` formula, or an open formula
for `k = 0`, where the bound `tᵢ` of `xᵢ` mentions only the earlier variables.
- [Wil85]
- [Smi93, Definition 2.1] -/
inductive Semiformula.BoundedUniversal : ℕ → {n : ℕ} → ArithmeticSemiformula ξ n → Prop
  | of_open {k n : ℕ} {φ : ArithmeticSemiformula ξ n} : φ.Open → BoundedUniversal k φ
  | of_boundedExistential {k n : ℕ} {φ : ArithmeticSemiformula ξ n} :
      BoundedExistential k φ → BoundedUniversal (k + 1) φ
  | ballLT {k n : ℕ} (t : ArithmeticSemiterm ξ n) {φ : ArithmeticSemiformula ξ (n + 1)} :
      BoundedUniversal (k + 1) φ → BoundedUniversal (k + 1) (Semiformula.ballLT t φ)

end

/-- Induction for `Eₖ` formulas over $\mathsf{PA}^-$.
- [Wil85]
- [Smi93, Definition 2.2] -/
abbrev IE (k : ℕ) : ArithmeticTheory :=
  𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ (Semiformula.BoundedExistential k)

@[inherit_doc] notation "𝗜𝗘₁" => IE 1

@[inherit_doc] notation "𝗜𝗘₂" => IE 2

instance (k : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ IE k :=
  Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻)
    (Entailment.WeakerThan.ofSubset Set.subset_union_left)

/-- $\mathsf{I}\mathsf{E}_1$ is strictly weaker than $\mathsf{I}\Delta_0$. An open problem.
- [DAq05, §8] -/
axiom IE1_strictlyWeakerThan_ISigma0 : 𝗜𝗘₁ ⪱ 𝗜𝚺₀

/-- $\mathsf{I}\mathsf{E}_k$ is strictly weaker than $\mathsf{I}\mathsf{E}_{k + 1}$ for each
$k \ge 1$. An open problem.
- [Wil85, §4.13, Problem (1)]
- [Car16] -/
axiom IE_strictlyWeakerThan_IE_succ {k : ℕ} (hk : 1 ≤ k) : IE k ⪱ IE (k + 1)

/-- $\mathsf{I}\mathsf{E}_1$ proves the least number principle for $U_1$ formulas. An open problem.
- [Wil85, §4.13, Problem (2)] -/
axiom leastNumberBoundedUniversal_weakerThan_IE1 :
    𝗣𝗔⁻ ∪ LeastNumberScheme (Semiformula.BoundedUniversal 1) ⪯ 𝗜𝗘₁

mutual

lemma Semiformula.BoundedExistential.hierarchy {k n : ℕ} {φ : ArithmeticSemiformula ξ n} :
    Semiformula.BoundedExistential k φ → ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ
  | .of_open h => Bounding.Hierarchy.of_open h
  | .of_boundedUniversal h => h.hierarchy
  | .bexsLT _ h => Bounding.Hierarchy.arithmetic_bexsLT_iff.mpr h.hierarchy

lemma Semiformula.BoundedUniversal.hierarchy {k n : ℕ} {φ : ArithmeticSemiformula ξ n} :
    Semiformula.BoundedUniversal k φ → ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ
  | .of_open h => Bounding.Hierarchy.of_open h
  | .of_boundedExistential h => h.hierarchy
  | .ballLT _ h => Bounding.Hierarchy.arithmetic_ballLT_iff.mpr h.hierarchy

end

/-- $\mathsf{I}\mathsf{E}_k$ is weaker than $\mathsf{I}\Delta_0$. -/
lemma IE_weakerThan_ISigma0 (k : ℕ) : IE k ⪯ 𝗜𝚺₀ := by
  rw [ISigmaZero_eq_IBroadSigmaZero]
  exact Entailment.WeakerThan.ofSubset
    (Set.union_subset_union_right _ (InductionScheme_subset (·.hierarchy)))

end FFL.FirstOrder.Arithmetic
