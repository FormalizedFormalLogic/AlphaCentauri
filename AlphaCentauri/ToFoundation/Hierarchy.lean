module

public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-!
# The arithmetical hierarchy of a universal closure

`Hierarchy 𝚷 (s + 1)` passes through `Semiformula.univCl`, and every axiom of `𝗣𝗔⁻` is $\Pi_2$.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

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

/-- Every axiom of `𝗘𝗤 ℒₒᵣ` is $\Pi_2$. -/
lemma of_mem_eqAxiom {σ : ArithmeticSentence} (hσ : σ ∈ 𝗘𝗤 ℒₒᵣ) : Hierarchy 𝚷 2 σ := by
  cases hσ with
  | funcExt f => simp [Theory.Eq.funcExt]
  | relExt r => simp [Theory.Eq.relExt]
  | _ => simp

/-- Every axiom of `𝗣𝗔⁻` is $\Pi_2$. -/
lemma of_mem_peanoMinus {σ : ArithmeticSentence} (hσ : σ ∈ 𝗣𝗔⁻) :
    Hierarchy 𝚷 2 σ := by
  cases hσ with
  | equal φ hφ => exact of_mem_eqAxiom hφ
  | addEqOfLt =>
    simp only [PeanoMinus.Axiom.addEqOfLt]
    exact .all (.all (by rw [Semiformula.imp_eq]; exact .or (by simp) (.dummy_pi (by simp))))
  | _ => simp

end Hierarchy

namespace StrictHierarchy

variable {L : Language} [L.LT] {ξ : Type*} {Γ : Polarity} {s n : ℕ}

/-- A strict formula of level `0` is $\Delta_0$. -/
lemma bounded_of_zero {φ : Semiformula L ξ n} (h : StrictHierarchy Γ 0 φ) : Hierarchy 𝚺 0 φ := by
  cases h with | zero h => exact h

/-- The body of a $\Delta_0$ existential is $\Delta_0$. -/
lemma _root_.FFL.FirstOrder.Arithmetic.Hierarchy.of_bounded_exs {φ : Semiformula L ξ (n + 1)}
    (h : Hierarchy 𝚺 0 (∃¹ φ)) : Hierarchy 𝚺 0 φ := by
  cases h with
  | bexs _ hφ => exact Hierarchy.and (Hierarchy.rel _ _ _ _) hφ

/-- The body of a strict $\Sigma_1$ existential is strict $\Sigma_1$. -/
lemma of_exs {φ : Semiformula L ξ (n + 1)} (h : StrictHierarchy 𝚺 1 (∃¹ φ)) :
    StrictHierarchy 𝚺 1 φ := by
  cases h with
  | ofAlt h => exact .ofAlt (.zero (Hierarchy.of_bounded_exs (bounded_of_zero h)))
  | exs h => exact h

/-- A formula that is both strict $\Sigma_1$ and strict $\Pi_1$ is $\Delta_0$. -/
lemma bounded_of_sigmaOne_of_piOne {φ : Semiformula L ξ n} (hσ : StrictHierarchy 𝚺 1 φ)
    (hπ : StrictHierarchy 𝚷 1 φ) : Hierarchy 𝚺 0 φ := by
  cases hσ with
  | ofAlt h => exact bounded_of_zero h
  | exs _ => cases hπ with | ofAlt h => exact bounded_of_zero h

/-- A $\Delta_0$ formula is strict at every positive level. -/
lemma of_bounded : {Γ : Polarity} → {s : ℕ} → {φ : Semiformula L ξ n} → Hierarchy 𝚺 0 φ →
    StrictHierarchy Γ (s + 1) φ
  | _, 0, _, h => .ofAlt (.zero h)
  | _, _ + 1, _, h => .ofAlt (of_bounded h)

end StrictHierarchy

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

end FFL.FirstOrder.Arithmetic
