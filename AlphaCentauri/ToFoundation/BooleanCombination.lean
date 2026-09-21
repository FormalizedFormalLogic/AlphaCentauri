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
  | pos {φ} : Γ φ → BooleanCombination Γ φ
  | neg {φ} : Γ φ → BooleanCombination Γ (∼φ)
  | and {φ ψ} : BooleanCombination Γ φ → BooleanCombination Γ ψ → BooleanCombination Γ (φ ⋏ ψ)
  | or {φ ψ} : BooleanCombination Γ φ → BooleanCombination Γ ψ → BooleanCombination Γ (φ ⋎ ψ)

namespace BooleanCombination

variable {Γ Γ' : Semiformula L ξ n → Prop} {φ ψ : Semiformula L ξ n}

@[simp, grind =] lemma neg_iff : BooleanCombination Γ (∼φ) ↔ BooleanCombination Γ φ := by
  have H : ∀ {φ : Semiformula L ξ n}, BooleanCombination Γ φ → BooleanCombination Γ (∼φ) := by
    intro φ h
    induction h with
    | pos hφ => exact neg hφ
    | neg hφ => simpa using pos hφ
    | and _ _ ih₁ ih₂ => simpa using ih₁.or ih₂
    | or _ _ ih₁ ih₂ => simpa using ih₁.and ih₂
  exact ⟨fun h ↦ by simpa using H h, H⟩

lemma mono (h : ∀ {φ}, Γ' φ → BooleanCombination Γ φ) :
    BooleanCombination Γ' φ → BooleanCombination Γ φ := by
  intro hφ
  induction hφ with
  | pos hφ' => exact h hφ'
  | neg hφ' => simpa using h hφ'
  | and _ _ ih₁ ih₂ => exact ih₁.and ih₂
  | or _ _ ih₁ ih₂ => exact ih₁.or ih₂

end BooleanCombination

end FFL.FirstOrder

namespace FFL.FirstOrder.Arithmetic

open FFL.FirstOrder (BooleanCombination)

variable {L : Language} [L.LT] {ξ : Type*} {Γ : Polarity} {s n : ℕ} {φ : Semiformula L ξ n}

namespace BooleanCombination

/-- Every Boolean combination of formulas strictly at level `s` lies at level `s + 1` of either
polarity.
- [Bek99, §2] -/
theorem hierarchy_succ (h : BooleanCombination (StrictHierarchy Γ s) φ)
    (Γ' : Polarity) : Hierarchy Γ' (s + 1) φ := by
  induction h with
  | pos hφ => exact hφ.hierarchy.strict_mono Γ' (by omega)
  | neg hφ => exact hφ.neg.hierarchy.strict_mono Γ' (by omega)
  | and _ _ ih₁ ih₂ => exact ih₁.and ih₂
  | or _ _ ih₁ ih₂ => exact ih₁.or ih₂

theorem strictHierarchy_alt (h : BooleanCombination (StrictHierarchy Γ s) φ) :
    BooleanCombination (StrictHierarchy Γ.alt s) φ := by
  induction h with
  | pos hφ => simpa using (BooleanCombination.neg hφ.neg)
  | neg hφ => exact .pos hφ.neg
  | and _ _ ih₁ ih₂ => exact ih₁.and ih₂
  | or _ _ ih₁ ih₂ => exact ih₁.or ih₂

/-- $\mathcal{B}(\Sigma_s) = \mathcal{B}(\Pi_s)$: a Boolean combination of formulas strictly at
level `s` and polarity `Γ` is one of polarity `Γ.alt`, and conversely.
- [Bek99, §2] -/
theorem strictHierarchy_alt_iff :
    BooleanCombination (StrictHierarchy Γ s) φ ↔ BooleanCombination (StrictHierarchy Γ.alt s) φ :=
  ⟨strictHierarchy_alt, fun h ↦ by simpa using strictHierarchy_alt h⟩

end BooleanCombination

end FFL.FirstOrder.Arithmetic
