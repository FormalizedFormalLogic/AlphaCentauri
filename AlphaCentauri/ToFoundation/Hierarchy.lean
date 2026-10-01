module

public import AlphaCentauri.Hierarchy.Bounded
public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-!
# The arithmetical hierarchy of a universal closure

`ℬ[<, L].Hierarchy 𝚷 (s + 1)` passes through `Semiformula.univCl`, and every axiom of `𝗣𝗔⁻` is
$\Pi_2$.
-/

@[expose] public section

namespace FFL.FirstOrder.Bounding.Hierarchy

open Arithmetic

variable {L : Language} [L.LT] {ξ : Type*} {Γ : Polarity} {s n : ℕ}

@[simp] lemma toEmpty_iff [DecidableEq ξ] {φ : Semiformula L ξ n} (h : φ.freeVariables = ∅) :
    ℬ[<, L].Hierarchy Γ s (φ.toEmpty h) ↔ ℬ[<, L].Hierarchy Γ s φ := by
  have : ℬ[<, L].Hierarchy Γ s (Rew.emb ▹ (φ.toEmpty h) : Semiformula L ξ n) ↔
      ℬ[<, L].Hierarchy Γ s (φ.toEmpty h) := rew_iff
  rwa [show (Rew.emb ▹ (φ.toEmpty h) : Semiformula L ξ n) = φ from Semiformula.emb_toEmpty φ h,
    iff_comm] at this

@[simp] lemma allClosure_iff {φ : Semiformula L ξ n} :
    ℬ[<, L].Hierarchy 𝚷 (s + 1) (∀¹* φ) ↔ ℬ[<, L].Hierarchy 𝚷 (s + 1) φ := by
  induction n with
  | zero => simp
  | succ n ih => rw [allClosure_succ]; simp [ih]

@[simp] lemma univCl_iff {φ : Proposition L} :
    ℬ[<, L].Hierarchy 𝚷 (s + 1) (Semiformula.univCl φ) ↔ ℬ[<, L].Hierarchy 𝚷 (s + 1) φ := by
  simp [Semiformula.univCl, Semiformula.univCl']

/-- Every formula lies at some level of the arithmetical hierarchy. -/
lemma exists_forall_hierarchy (φ : Semiformula L ξ n) : ∃ s, ∀ Γ, ℬ[<, L].Hierarchy Γ s φ := by
  induction φ using Semiformula.rec' with
  | hverum | hfalsum | hrel | hnrel => exact ⟨0, by simp⟩
  | hand φ ψ ihφ ihψ | hor φ ψ ihφ ihψ =>
    obtain ⟨s, hs⟩ := ihφ
    obtain ⟨t, ht⟩ := ihψ
    use max s t;
    intro Γ;
    simp [(hs Γ).mono (le_max_left s t), (ht Γ).mono (le_max_right s t)]
  | hall φ ih =>
    obtain ⟨s, hs⟩ := ih;
    exact ⟨s + 2, (pi (hs 𝚺)).accum⟩
  | hexs φ ih =>
    obtain ⟨s, hs⟩ := ih
    exact ⟨s + 2, (sigma (hs 𝚷)).accum⟩

/-- Every axiom of `𝗘𝗤 ℒₒᵣ` is $\Pi_2$. -/
lemma of_mem_eqAxiom {σ : ArithmeticSentence} (hσ : σ ∈ 𝗘𝗤 ℒₒᵣ) :
    ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2 σ := by
  cases hσ with
  | funcExt f => simp [Theory.Eq.funcExt]
  | relExt r => simp [Theory.Eq.relExt]
  | _ => simp

/-- Every axiom of `𝗣𝗔⁻` is $\Pi_2$. -/
lemma of_mem_peanoMinus {σ : ArithmeticSentence} (hσ : σ ∈ 𝗣𝗔⁻) :
    ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2 σ := by
  cases hσ with
  | equal φ hφ => exact of_mem_eqAxiom hφ
  | addEqOfLt =>
    simp only [PeanoMinus.Axiom.addEqOfLt]
    exact .all (.all (by rw [Semiformula.imp_eq]; exact .or (by simp) (.dummy_pi (by simp))))
  | _ => simp

end FFL.FirstOrder.Bounding.Hierarchy

namespace FFL.FirstOrder.Arithmetic

namespace StrictHierarchy

variable {L : Language} [L.LT] {ξ : Type*} {Γ : Polarity} {s n : ℕ}

/-- The body of a bounded existential is bounded. -/
@[grind →]
lemma _root_.FFL.FirstOrder.Bounding.Closure.of_exs {φ : Semiformula L ξ (n + 1)}
    (h : ℬ[<, L].Closure (∃¹ φ)) : ℬ[<, L].Closure φ := by
  cases h with
  | bexs hR _ hφ =>
    obtain rfl := Set.mem_singleton_iff.mp hR
    exact .and (.rel _ _) hφ

/-- The body of a bounded universal is bounded. -/
@[grind →]
lemma _root_.FFL.FirstOrder.Bounding.Closure.of_all {φ : Semiformula L ξ (n + 1)}
    (h : ℬ[<, L].Closure (∀¹ φ)) : ℬ[<, L].Closure φ := by
  cases h with
  | ball hR _ hφ =>
    obtain rfl := Set.mem_singleton_iff.mp hR
    exact Bounding.Closure.imp_iff.mpr ⟨.rel _ _, hφ⟩

/-- A bounded universal quantifies below a term. -/
@[grind →]
lemma _root_.FFL.FirstOrder.Bounding.Closure.exists_of_all
    {φ : Semiformula L ξ (n + 1)} (h : ℬ[<, L].Closure (∀¹ φ)) :
    ∃ (t : Semiterm L ξ n) (ψ : Semiformula L ξ (n + 1)),
      φ = “#0 < !!(Rew.bShift t)” 🡒 ψ ∧ ℬ[<, L].Closure ψ := by
  cases h with
  | ball hR pt hψ =>
    rename_i ψ _
    obtain rfl := Set.mem_singleton_iff.mp hR
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp pt
    exact ⟨t, ψ, rfl, hψ⟩

/-- The body of a strict $\Sigma_1$ existential is strict $\Sigma_1$. -/
@[grind →]
lemma of_exs {φ : Semiformula L ξ (n + 1)} (h : StrictHierarchy 𝚺 1 (∃¹ φ)) :
    StrictHierarchy 𝚺 1 φ := by
  cases h with
  | ofAlt h => exact .ofAlt (.zero (Bounding.Closure.of_exs (zero_iff_bounded.mp h)))
  | exs h => exact h

-- `witnesses_exs`/`exists_witnesses`'s `exs` case transport a `StrictHierarchy` fact across a
-- substitution, and their bounded cases read a level-`0` formula as bounded; `rew_iff` and
-- `zero_iff_bounded` are not `@[grind]` upstream.
attribute [grind =] rew_iff zero_iff_bounded

/-- A formula that is both strict $\Sigma_1$ and strict $\Pi_1$ is $\Delta_0$. -/
@[grind →]
lemma bounded_of_sigmaOne_of_piOne {φ : Semiformula L ξ n} (hσ : StrictHierarchy 𝚺 1 φ)
    (hπ : StrictHierarchy 𝚷 1 φ) : ℬ[<, L].Closure φ := by
  cases hσ with
  | ofAlt h => exact zero_iff_bounded.mp h
  | exs _ => cases hπ with | ofAlt h => exact zero_iff_bounded.mp h

end StrictHierarchy

end FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Bounding.HierarchySymbol.Semiformula

variable {L : Language} {ℬ : Bounding L} {ξ : Type*} {n s : ℕ}

@[simp] lemma hierarchy_succ {C : HierarchySymbol ℬ} {Γ : Polarity} (φ : C.Semiformula ξ n)
    (h : C.rank ≤ s + 1) : ℬ.Hierarchy Γ (s + 2) φ.val := hierarchy_of_lt φ (by omega)

end FFL.FirstOrder.Bounding.HierarchySymbol.Semiformula

-- The sequent bookkeeping in `Witnessing.lean` (`Γ + ⦃φ⦄` membership) relies on
-- `Multiset.mem_atom_iff`; it is `@[simp]` upstream but not `@[grind]`. `Multiset.mem_add` is
-- already `@[simp, grind =]` in Mathlib.
attribute [grind =] Multiset.mem_atom_iff
