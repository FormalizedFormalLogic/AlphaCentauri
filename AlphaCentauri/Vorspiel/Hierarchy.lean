module

public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-!
# The arithmetical hierarchy of a universal closure

`Hierarchy 𝚷 (s + 1)` passes through `Semiformula.univCl`, and every axiom of `𝗣𝗔⁻` is `𝚷-[2]`.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

namespace Hierarchy

variable {L : Language} [L.LT] {ξ : Type*} {Γ : Polarity} {s n : ℕ}

@[simp] lemma toEmpty_iff [DecidableEq ξ] {φ : Semiformula L ξ n} (h : φ.freeVariables = ∅) :
    Hierarchy Γ s (φ.toEmpty h) ↔ Hierarchy Γ s φ := by
  have : Hierarchy Γ s (Rew.emb ▹ (φ.toEmpty h) : Semiformula L ξ n) ↔
      Hierarchy Γ s (φ.toEmpty h) := rew_iff
  rwa [show (Rew.emb ▹ (φ.toEmpty h) : Semiformula L ξ n) = φ from Semiformula.emb_toEmpty φ h,
    iff_comm] at this

@[simp] lemma allClosure_iff {φ : Semiformula L ξ n} :
    Hierarchy 𝚷 (s + 1) (∀¹* φ) ↔ Hierarchy 𝚷 (s + 1) φ := by
  induction n with
  | zero => simp
  | succ n ih => rw [allClosure_succ]; simp [ih]

@[simp] lemma univCl_iff {φ : Proposition L} :
    Hierarchy 𝚷 (s + 1) (Semiformula.univCl φ) ↔ Hierarchy 𝚷 (s + 1) φ := by
  simp [Semiformula.univCl, Semiformula.univCl']

/-- Every axiom of `𝗘𝗤 ℒₒᵣ` is `𝚷-[2]`. -/
lemma of_mem_eqAxiom {σ : ArithmeticSentence} (hσ : σ ∈ 𝗘𝗤 ℒₒᵣ) : Hierarchy 𝚷 2 σ := by
  cases hσ with
  | funcExt f => simp [Theory.Eq.funcExt]
  | relExt r => simp [Theory.Eq.relExt]
  | _ => simp

/-- Every axiom of `𝗣𝗔⁻` is `𝚷-[2]`. -/
lemma of_mem_peanoMinus {σ : ArithmeticSentence} (hσ : σ ∈ 𝗣𝗔⁻) :
    Hierarchy 𝚷 2 σ := by
  cases hσ with
  | equal φ hφ => exact of_mem_eqAxiom hφ
  | addEqOfLt =>
    simp only [PeanoMinus.Axiom.addEqOfLt]
    exact .all (.all (by rw [Semiformula.imp_eq]; exact .or (by simp) (.dummy_pi (by simp))))
  | _ => simp

end Hierarchy

namespace HierarchySymbol.Semiformula

variable {ξ : Type*} {n s : ℕ}

/-- A formula of a hierarchy class strictly below `s` is `Γ-[s]` for either polarity `Γ`. -/
lemma hierarchy_of_lt {C : HierarchySymbol} {Γ : Polarity} (φ : C.Semiformula ξ n)
    (h : C.rank < s) : Hierarchy Γ s φ.val := by
  rcases C with ⟨_ | _ | _, m⟩
  · exact φ.sigma_prop.strict_mono _ h
  · exact φ.pi_prop.strict_mono _ h
  · exact (val_sigma φ ▸ φ.sigma.sigma_prop).strict_mono _ h

@[simp] lemma hierarchy_succ {C : HierarchySymbol} {Γ : Polarity} (φ : C.Semiformula ξ n)
    (h : C.rank ≤ s + 1) : Hierarchy Γ (s + 2) φ.val := hierarchy_of_lt φ (by omega)

end HierarchySymbol.Semiformula

end LO.FirstOrder.Arithmetic
