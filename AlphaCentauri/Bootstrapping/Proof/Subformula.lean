module

public import AlphaCentauri.Bootstrapping.Proof.CutFree
public import AlphaCentauri.Bootstrapping.Proof.FvSubst

/-!
# Internal subformula closure

This module defines the bounded primitive-recursive closure of a formula code under immediate
subformulas.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

namespace Subformula

/-- `q` is an immediate subformula of `p`.

- [HP98, §V.3(g)]
-/
def child (q p : V) : Prop :=
  (∃ a b, p = a ^⋏ b ∧ (q = a ∨ q = b)) ∨
  (∃ a b, p = a ^⋎ b ∧ (q = a ∨ q = b)) ∨
  (∃ a, p = ^∀ a ∧ q = a) ∨
  (∃ a, p = ^∃ a ∧ q = a)

namespace Step

def childB (p q r : V) : Prop :=
  (∃ a < p + 1, ∃ b < p + 1, r = a ^⋏ b ∧ (q = a ∨ q = b)) ∨
  (∃ a < p + 1, ∃ b < p + 1, r = a ^⋎ b ∧ (q = a ∨ q = b)) ∨
  (∃ a < p + 1, r = ^∀ a ∧ q = a) ∨
  (∃ a < p + 1, r = ^∃ a ∧ q = a)

def P (p C q : V) : Prop :=
  q < p + 1 ∧ (q ∈ C ∨ ∃ r < p + 1, r ∈ C ∧ childB p q r)

noncomputable def step (p C : V) : V := Classical.choose! <| finset_comprehension₁!
    (P := P p C)
    (by definability : 𝚺₁-Predicate (P p C))
    (p + 1)

lemma spec (p C q : V) (hq : q < p + 1) : q ∈ step p C ↔ P p C q := by
  simpa [step] using (Classical.choose!_spec (finset_comprehension₁!
    (P := P p C) (by definability : 𝚺₁-Predicate (P p C)) (p + 1))).2 q hq

private def graphMatrix : 𝚺₀.Semisentence 4 := .mkSigma
  “y p C e. y < e ∧ ∀ q < p + 1, (q ∈ y ↔
    (q ∈ C ∨ ∃ r < p + 1, r ∈ C ∧
      ((∃ a < p + 1, ∃ b < p + 1, !qqAndDef r a b ∧ (q = a ∨ q = b)) ∨
       (∃ a < p + 1, ∃ b < p + 1, !qqOrDef r a b ∧ (q = a ∨ q = b)) ∨
       (∃ a < p + 1, !qqAllDef r a ∧ q = a) ∨
       (∃ a < p + 1, !qqExsDef r a ∧ q = a))))”

def graph : 𝚺₁.Semisentence 3 := .mkSigma
  “y p C. ∃ e, !expDef e (p + 1) ∧ !graphMatrix y p C e”

instance defined : 𝚺₁-Function₂ (step : V → V → V) via graph := .mk fun v ↦ by
  simp [graph, graphMatrix, step, P, childB, Classical.choose!_eq_iff_right]

instance definable : 𝚺₁-Function₂ (step : V → V → V) := defined.to_definable

end Step

namespace Iterate

def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y p. !insertDef y p 0”
  succ := .mkSigma “y ih n p. ∃ s, !(Step.graph) s p ih ∧ y = s”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun v ↦ insert (v 0) ∅
  succ := fun v _ C ↦ Step.step (v 0) C
  zero_defined := .mk fun v ↦ by simp [blueprint, emptyset_def]
  succ_defined := .mk fun v ↦ by simp [blueprint, Step.graph, Step.step]

noncomputable def iterate (p n : V) : V := construction.result ![p] n

noncomputable def graph : 𝚺₁.Semisentence 3 :=
  blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])
noncomputable def deltaGraph : 𝚫₁.Semisentence 3 := graph.graphDelta

instance defined : 𝚺₁-Function₂ (iterate : V → V → V) via graph := .mk fun v ↦ by
  simp [construction.result_defined_iff, graph, iterate,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
    construction.result_defined.defined ![v 0, v 2, v 1]

instance defined_delta : 𝚫₁-Function₂ (iterate : V → V → V) via deltaGraph :=
  defined.graph_delta

instance definable : 𝚺₁-Function₂ (iterate : V → V → V) := defined.to_definable
instance definable_delta : 𝚫₁-Function₂ (iterate : V → V → V) := defined_delta.to_definable

@[simp] lemma zero (p : V) : iterate p 0 = insert p ∅ := by
  simp [iterate, construction]

@[simp] lemma succ (p n : V) : iterate p (n + 1) = Step.step p (iterate p n) := by
  simp [iterate, construction]

end Iterate

/-- `q` occurs in the bounded closure of `p` under immediate subformulas.

- [HP98, §V.3(g)]
-/
noncomputable def subformulas (p q : V) : Prop := q ∈ Iterate.iterate p (p + 1)

noncomputable def graph : 𝚺₁.Semisentence 2 := .mkSigma
  “p q. ∃ s, !(Iterate.graph) s p (p + 1) ∧ q ∈ s”

noncomputable def deltaGraph : 𝚫₁.Semisentence 2 := graph.graphDelta

instance defined : 𝚺₁-Relation subformulas (V := V) via graph := by
  exact .mk fun v ↦ by simp [graph, subformulas]

instance defined_delta : 𝚫₁-Relation subformulas (V := V) via deltaGraph :=
  defined.graph_delta

instance definable : 𝚺₁-Relation subformulas (V := V) := defined.to_definable
instance definable_delta : 𝚫₁-Relation subformulas (V := V) := defined_delta.to_definable

lemma root_mem (p n : V) : p ∈ Iterate.iterate p n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [Iterate.succ, Step.spec _ _ _ (by simp)]
    exact ⟨by simp, Or.inl ih⟩

@[simp] lemma refl (p : V) : subformulas p p := by
  exact root_mem p (p + 1)

lemma child_lt {p q : V} (h : child q p) : q < p := by
  rcases h with (⟨a, b, rfl, hq⟩ | ⟨a, b, rfl, hq⟩ | ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl⟩)
  · rcases hq with rfl | rfl <;> simp
  · rcases hq with rfl | rfl <;> simp
  · simp
  · simp

lemma child_mem {p q : V} (h : child q p) : subformulas p q := by
  have hB : Step.childB p q p := by
    rcases h with (⟨a, b, hp, hq⟩ | ⟨a, b, hp, hq⟩ | ⟨a, hp, hq⟩ | ⟨a, hp, hq⟩)
    · exact Or.inl ⟨a, by simpa [hp], b, by simpa [hp], hp, hq⟩
    · exact Or.inr <| Or.inl ⟨a, by simpa [hp], b, by simpa [hp], hp, hq⟩
    · exact Or.inr <| Or.inr <| Or.inl ⟨a, by simpa [hp], hp, hq⟩
    · exact Or.inr <| Or.inr <| Or.inr ⟨a, by simpa [hp], hp, hq⟩
  have hq : q < p + 1 := lt_trans (child_lt h) (by simp)
  unfold subformulas
  rw [Iterate.succ]
  exact (Step.spec p (Iterate.iterate p p) q).mpr
    ⟨hq, Or.inr ⟨p, by simp, root_mem p p, hB⟩⟩

end Subformula

end LO.FirstOrder.Arithmetic.Bootstrapping
