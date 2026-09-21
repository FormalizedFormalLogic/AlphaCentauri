module

public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy
public import Foundation.FirstOrder.Arithmetic.Definability.Definable

/-! # Definability by strict-hierarchy formulas

`StrictDefinable Γ s P` says that `P` is defined, with parameters from the model, by a formula of
the strict hierarchy class `Γ-[s]`; `StrictDefinablePred`, `StrictDefinableRel` and their variants
are its arities.

This file is a local stand-in for the upstream definition proposed in
<https://github.com/FormalizedFormalLogic/Foundation/pull/929>. Once Foundation carries
`StrictDefinable` itself, delete this file and import Foundation's in its place: everything below
is stated in the names the upstream definition will provide.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] {k : ℕ}

variable (Γ : Polarity) (s : ℕ)

structure IsStrictDefinedBy (R : (Fin k → V) → Prop) (φ : ArithmeticSemisentence k) : Prop where
  strictHierarchy : StrictHierarchy Γ s φ
  defined : FirstOrder.IsDefinedBy R φ

structure IsStrictDefinedByWithParam (R : (Fin k → V) → Prop) (φ : ArithmeticSemiformula V k) :
    Prop where
  strictHierarchy : StrictHierarchy Γ s φ
  defined : FirstOrder.IsDefinedByWithParam R φ

abbrev StrictDefinable {k} (P : (Fin k → V) → Prop) := ∃ φ, IsStrictDefinedByWithParam Γ s P φ

abbrev StrictDefinablePred (P : V → Prop) : Prop :=
  StrictDefinable Γ s (k := 1) fun v ↦ P (v 0)

abbrev StrictDefinableRel (R : V → V → Prop) : Prop :=
  StrictDefinable Γ s (k := 2) fun v ↦ R (v 0) (v 1)

abbrev StrictDefinableRel₃ (R : V → V → V → Prop) : Prop :=
  StrictDefinable Γ s (k := 3) fun v ↦ R (v 0) (v 1) (v 2)

abbrev StrictDefinableRel₄ (R : V → V → V → V → Prop) : Prop :=
  StrictDefinable Γ s (k := 4) fun v ↦ R (v 0) (v 1) (v 2) (v 3)

variable {Γ s}

namespace StrictDefinable

lemma of_iff {P Q : (Fin k → V) → Prop} (h : StrictDefinable Γ s Q) (H : ∀ v, P v ↔ Q v) :
    StrictDefinable Γ s P := by
  rwa [show P = Q from by funext v; simp [H]]

lemma definable {P : (Fin k → V) → Prop} (h : StrictDefinable Γ s P) : Γ-[s].Definable P := by
  obtain ⟨φ, hs, hφ⟩ := h
  exact .mkPolarity φ hs.hierarchy fun v ↦ (hφ v).symm

lemma exists_eval_iff {P : (Fin k → V) → Prop} (h : StrictDefinable Γ s P) :
    ∃ (e : ℕ → V) (φ : ArithmeticSemiformula ℕ k),
      StrictHierarchy Γ s φ ∧ ∀ v, P v ↔ φ.Eval v e := by
  classical
  obtain ⟨φ, hs, hφ⟩ := h
  have : Inhabited V := Classical.inhabited_of_nonempty'
  exact ⟨φ.enumerateFVar, Rew.rewriteMap φ.idxOfFVar ▹ φ, hs.rew _,
    fun v ↦ by simp [Semiformula.eval_rewriteMap, hφ]⟩

lemma of_strictHierarchy {ξ : Type*} {m : ℕ} {θ : ArithmeticSemiformula ξ (m + 2)}
    (hθ : StrictHierarchy Γ s θ) (e : Fin m → V) (f : ξ → V) :
    StrictDefinableRel Γ s fun x y ↦ Semiformula.Eval (y :> x :> e) f θ := by
  refine ⟨Rew.bind (#1 :> #0 :> fun i : Fin m ↦ (&(e i) : ArithmeticSemiterm V 2))
    (fun x : ξ ↦ (&(f x) : ArithmeticSemiterm V 2)) ▹ θ, hθ.rew _, ?_⟩
  intro v
  simp only [Semiformula.eval_rew]
  have hb : (Semiterm.val (L := ℒₒᵣ) (M := V) v id) ∘
      (Rew.bind (#1 :> #0 :> fun i : Fin m ↦ (&(e i) : ArithmeticSemiterm V 2))
        (fun x : ξ ↦ (&(f x) : ArithmeticSemiterm V 2))) ∘ Semiterm.bvar
      = (v 1 :> v 0 :> e : Fin (m + 2) → V) := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ i =>
      cases i using Fin.cases with
      | zero => simp
      | succ i => simp
  have hf : (Semiterm.val (L := ℒₒᵣ) (M := V) v id) ∘
      (Rew.bind (#1 :> #0 :> fun i : Fin m ↦ (&(e i) : ArithmeticSemiterm V 2))
        (fun x : ξ ↦ (&(f x) : ArithmeticSemiterm V 2))) ∘ Semiterm.fvar
      = f := by
    funext x; simp
  rw [hb, hf]

end StrictDefinable

end FFL.FirstOrder.Arithmetic
