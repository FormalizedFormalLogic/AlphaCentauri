module

public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy

/-!
# Boolean combinations of a class of formulas

`BooleanCombination Γ` is the closure of a predicate `Γ` on formulas, together with the negations
of its members, under `⋏` and `⋎`.

- [Bek99, §2]
-/

@[expose] public section

namespace FFL.FirstOrder

variable {L : Language} {ξ : Type*} {n : ℕ}

/-- The Boolean combinations of the formulas satisfying `Γ`.
- [Bek99, §2] -/
inductive BooleanCombination (Γ : Semiformula L ξ n → Prop) : Semiformula L ξ n → Prop
  | mem {φ} : Γ φ → BooleanCombination Γ φ
  | negMem {φ} : Γ φ → BooleanCombination Γ (∼φ)
  | and {φ ψ} : BooleanCombination Γ φ → BooleanCombination Γ ψ → BooleanCombination Γ (φ ⋏ ψ)
  | or {φ ψ} : BooleanCombination Γ φ → BooleanCombination Γ ψ → BooleanCombination Γ (φ ⋎ ψ)

namespace BooleanCombination

variable {Γ Γ' : Semiformula L ξ n → Prop} {φ ψ : Semiformula L ξ n}

lemma neg (h : BooleanCombination Γ φ) : BooleanCombination Γ (∼φ) := by
  induction h with
  | mem hφ => exact negMem hφ
  | negMem hφ => simpa using mem hφ
  | and _ _ ih₁ ih₂ => simpa using ih₁.or ih₂
  | or _ _ ih₁ ih₂ => simpa using ih₁.and ih₂

lemma mono (h : ∀ {φ}, Γ' φ → BooleanCombination Γ φ) :
    BooleanCombination Γ' φ → BooleanCombination Γ φ := by
  intro hφ
  induction hφ with
  | mem hφ' => exact h hφ'
  | negMem hφ' => exact (h hφ').neg
  | and _ _ ih₁ ih₂ => exact ih₁.and ih₂
  | or _ _ ih₁ ih₂ => exact ih₁.or ih₂

end BooleanCombination

end FFL.FirstOrder

namespace FFL.FirstOrder.Arithmetic

open FFL.FirstOrder (BooleanCombination)
open FFL.FirstOrder.BooleanCombination

variable {L : Language} [L.LT] {ξ : Type*} {Γ : Polarity} {s n : ℕ} {φ : Semiformula L ξ n}

/-- Every formula strictly at level `s` of the hierarchy is a Boolean combination of such
formulas.
- [Bek99, §2] -/
theorem StrictHierarchy.booleanCombination (h : StrictHierarchy Γ s φ) :
    BooleanCombination (StrictHierarchy Γ s) φ := .mem h

/-- Every Boolean combination of formulas strictly at level `s` lies in $\Sigma_{s + 1}$ and in
$\Pi_{s + 1}$.
- [Bek99, §2] -/
theorem BooleanCombination.hierarchy_succ (h : BooleanCombination (StrictHierarchy Γ s) φ) :
    Hierarchy 𝚺 (s + 1) φ ∧ Hierarchy 𝚷 (s + 1) φ := by
  induction h with
  | mem hφ => exact ⟨hφ.hierarchy.strict_mono 𝚺 (by omega), hφ.hierarchy.strict_mono 𝚷 (by omega)⟩
  | negMem hφ =>
    exact ⟨hφ.neg.hierarchy.strict_mono 𝚺 (by omega), hφ.neg.hierarchy.strict_mono 𝚷 (by omega)⟩
  | and _ _ ih₁ ih₂ => exact ⟨ih₁.1.and ih₂.1, ih₁.2.and ih₂.2⟩
  | or _ _ ih₁ ih₂ => exact ⟨ih₁.1.or ih₂.1, ih₁.2.or ih₂.2⟩

theorem BooleanCombination.strictHierarchy_alt_subset
    (h : BooleanCombination (StrictHierarchy Γ s) φ) :
    BooleanCombination (StrictHierarchy Γ.alt s) φ := by
  induction h with
  | mem hφ => simpa using hφ.neg.booleanCombination.neg
  | negMem hφ => exact .mem hφ.neg
  | and _ _ ih₁ ih₂ => exact ih₁.and ih₂
  | or _ _ ih₁ ih₂ => exact ih₁.or ih₂

/-- $\mathcal{B}(\Sigma_s) = \mathcal{B}(\Pi_s)$: a Boolean combination of formulas strictly at
level `s` and polarity `Γ` is the same as one of polarity `Γ.alt`.
- [Bek99, §2] -/
theorem BooleanCombination.strictHierarchy_alt_iff :
    BooleanCombination (StrictHierarchy Γ s) φ ↔ BooleanCombination (StrictHierarchy Γ.alt s) φ :=
  ⟨strictHierarchy_alt_subset,
    fun h ↦ by simpa using BooleanCombination.strictHierarchy_alt_subset h⟩

end FFL.FirstOrder.Arithmetic
