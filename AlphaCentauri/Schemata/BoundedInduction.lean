module

public import Foundation.FirstOrder.Arithmetic.Schemata

/-! # Induction for bounded existential formulas

$\mathsf{I}\mathsf{E}_k$ is induction for $E_k$ formulas over $\mathsf{PA}^-$, where $E_k$ and
$U_k$ count the alternations of blocks of bounded quantifiers over an open matrix.

- [Wil85]
- [Smi93, Definition 2.1, Definition 2.2]
- [DAq05, §8]
- [Car16]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.FFL.Entailment

section BoundedInduction

variable {ξ : Type*}

mutual

/-- `Eₖ` formulas: a block `∃ x₁ < t₁, ⋯, ∃ xₘ < tₘ` over a `Uₖ₋₁` formula, or an open formula
for `k = 0`, where the bound `tᵢ` of `xᵢ` mentions only the earlier variables.
- [Wil85]
- [Smi93, Definition 2.1] -/
inductive IsBoundedExistential : ℕ → {n : ℕ} → ArithmeticSemiformula ξ n → Prop
  | of_open {k n : ℕ} {φ : ArithmeticSemiformula ξ n} : φ.Open → IsBoundedExistential k φ
  | of_boundedUniversal {k n : ℕ} {φ : ArithmeticSemiformula ξ n} :
      IsBoundedUniversal k φ → IsBoundedExistential (k + 1) φ
  | bexsLT {k n : ℕ} (t : ArithmeticSemiterm ξ n) {φ : ArithmeticSemiformula ξ (n + 1)} :
      IsBoundedExistential (k + 1) φ → IsBoundedExistential (k + 1) (Semiformula.bexsLT t φ)

/-- `Uₖ` formulas: a block `∀ x₁ < t₁, ⋯, ∀ xₘ < tₘ` over an `Eₖ₋₁` formula, or an open formula
for `k = 0`, where the bound `tᵢ` of `xᵢ` mentions only the earlier variables.
- [Wil85]
- [Smi93, Definition 2.1] -/
inductive IsBoundedUniversal : ℕ → {n : ℕ} → ArithmeticSemiformula ξ n → Prop
  | of_open {k n : ℕ} {φ : ArithmeticSemiformula ξ n} : φ.Open → IsBoundedUniversal k φ
  | of_boundedExistential {k n : ℕ} {φ : ArithmeticSemiformula ξ n} :
      IsBoundedExistential k φ → IsBoundedUniversal (k + 1) φ
  | ballLT {k n : ℕ} (t : ArithmeticSemiterm ξ n) {φ : ArithmeticSemiformula ξ (n + 1)} :
      IsBoundedUniversal (k + 1) φ → IsBoundedUniversal (k + 1) (Semiformula.ballLT t φ)

end

/-- Induction for `Eₖ` formulas over $\mathsf{PA}^-$.
- [Wil85]
- [Smi93, Definition 2.2] -/
abbrev IE (k : ℕ) : ArithmeticTheory :=
  𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ (IsBoundedExistential k)

@[inherit_doc] notation "𝗜𝗘₁" => IE 1

@[inherit_doc] notation "𝗜𝗘₂" => IE 2

instance (k : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ IE k :=
  Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻)
    (Entailment.WeakerThan.ofSubset Set.subset_union_left)

section

variable {V : Type*} [ORingStructure V]

instance [V↓[ℒₒᵣ] ⊧* 𝗜𝗘₁] : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  Semantics.ModelsSet.of_subset (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗜𝗘₁) Set.subset_union_left

instance {k : ℕ} [V↓[ℒₒᵣ] ⊧* IE k] :
    V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (IsBoundedExistential k) :=
  Semantics.ModelsSet.of_subset (inferInstance : V↓[ℒₒᵣ] ⊧* IE k) Set.subset_union_right

end

/-- $\mathsf{I}\mathsf{E}_1$ is strictly weaker than $\mathsf{I}\Delta_0$. An open problem.
- [DAq05, §8] -/
def IE1StrictlyWeakerThanISigma0 : Prop := 𝗜𝗘₁ ⪱ 𝗜𝚺₀

/-- $\mathsf{I}\mathsf{E}_k$ is strictly weaker than $\mathsf{I}\mathsf{E}_{k + 1}$ for each
$k \ge 1$. An open problem.
- [Wil85, §4.13, Problem (1)]
- [Car16] -/
def IEStrictlyWeakerThanIESucc : Prop := ∀ k : ℕ, 1 ≤ k → IE k ⪱ IE (k + 1)

/-- $\mathsf{I}\mathsf{E}_1$ proves the least number principle for $U_1$ formulas. An open problem.
- [Wil85, §4.13, Problem (2)] -/
def LeastNumberBoundedUniversalWeakerThanIE1 : Prop :=
  𝗣𝗔⁻ ∪ LeastNumberScheme (IsBoundedUniversal 1) ⪯ 𝗜𝗘₁

end BoundedInduction

end FFL.FirstOrder.Arithmetic
