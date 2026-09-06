module

public import AlphaCentauri.Hierarchy.DeltaZero
public import Foundation.FirstOrder.Incompleteness.Delta1

/-!
# Internal `Δ₀` formulas

This module introduces the bounded-existential coding operation and the internal shape
predicate `IsDelta0` for `Δ₀` formulas, built as a least fixpoint in the manner of Foundation's
`IsSigma1`, and proves that it agrees with the external class `Hierarchy 𝚺 0` on quoted
formulas.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `qqBex u q = ^∃ ((^#0 ^< u) ^⋏ q)`, the code of `∃¹[“#0 < u”] q`; dual of `qqBall`.
- [HP98, 0.30] -/
noncomputable def qqBex (u q : V) : V := ^∃ ((^#0 ^< u) ^⋏ q)

/-- The coded body is a proper subcode of the bounded existential formula.
- [HP98, 0.30] -/
@[simp] lemma lt_q_qqBex (u q : V) : q < qqBex u q :=
  lt_trans (lt_K!_right _ _) (lt_exists _)
/-- The coded bound is a proper subcode of the bounded existential formula.
- [HP98, 0.30] -/
@[simp] lemma lt_u_qqBex (u q : V) : u < qqBex u q :=
  lt_trans (Arithmetic.lt_qqLT_right _ _) (lt_trans (lt_K!_left _ _) (lt_exists _))

/-- Defining formula for the bounded existential coding operation.
- [HP98, 0.30] -/
def _root_.LO.FirstOrder.Arithmetic.qqBexDef : 𝚺₁.Semisentence 3 := .mkSigma
  “p u q. ∃ bv, !qqBvarDef bv 0 ∧ ∃ lt, !qqLTDef lt bv u ∧ ∃ g, !qqAndDef g lt q ∧ !qqExsDef p g”

/-- The bounded existential coding operation is `𝚺₁`-definable.
- [HP98, 0.30] -/
instance qqBex_defined : 𝚺₁-Function₂ (qqBex : V → V → V) via qqBexDef := .mk fun v ↦ by
  simp [qqBexDef, qqBex, (Arithmetic.qqLT_defined (V := V)).df]
/-- The bounded existential coding operation is definable at every hierarchy level.
- [HP98, 0.30] -/
instance qqBex_definable (Γ m) : Γ-[m + 1]-Function₂ (qqBex : V → V → V) :=
  .of_sigmaOne qqBex_defined.to_definable

lemma neg_qqBall {u q : V} (hu : IsUTerm ℒₒᵣ u) (hq : IsUFormula ℒₒᵣ q) :
    neg ℒₒᵣ (qqBall u q) = qqBex u (neg ℒₒᵣ q) := by
  have hlt : IsUFormula ℒₒᵣ (Arithmetic.qqNLT (qqBvar 0) u) := by simp [Arithmetic.qqNLT, hu]
  rw [show qqBall u q = ^∀ ((Arithmetic.qqNLT (qqBvar 0) u) ^⋎ q) from rfl,
    show qqBex u (neg ℒₒᵣ q) = ^∃ ((Arithmetic.qqLT (qqBvar 0) u) ^⋏ neg ℒₒᵣ q) from rfl,
    neg_all (by simp [hlt, hq]), neg_or hlt hq]
  simp [Arithmetic.qqNLT, Arithmetic.qqLT, hu]

lemma neg_qqBex {u q : V} (hu : IsUTerm ℒₒᵣ u) (hq : IsUFormula ℒₒᵣ q) :
    neg ℒₒᵣ (qqBex u q) = qqBall u (neg ℒₒᵣ q) := by
  have hlt : IsUFormula ℒₒᵣ (Arithmetic.qqLT (qqBvar 0) u) := by simp [Arithmetic.qqLT, hu]
  rw [show qqBex u q = ^∃ ((Arithmetic.qqLT (qqBvar 0) u) ^⋏ q) from rfl,
    show qqBall u (neg ℒₒᵣ q) = ^∀ ((Arithmetic.qqNLT (qqBvar 0) u) ^⋎ neg ℒₒᵣ q) from rfl,
    neg_ex (by simp [hlt, hq]), neg_and hlt hq]
  simp [Arithmetic.qqNLT, Arithmetic.qqLT, hu]

namespace IsDelta0F

/-- `Phi C p` recognizes one `Δ₀` constructor step over the class `C`.
- [HP98, Lemma I.1.68] -/
def Phi (C : Set V) (p : V) : Prop :=
  (p = ^⊤) ∨
  (p = ^⊥) ∨
  (∃ k r v, p = ^rel k r v) ∨
  (∃ k r v, p = ^nrel k r v) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
  (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C ∧ p = qqBall u q) ∨
  (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C ∧ p = qqBex u q)

private lemma phi_iff (C p : V) :
    Phi {x | x ∈ C} p ↔
    (p = ^⊤) ∨
    (p = ^⊥) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, p = ^rel k r v) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, p = ^nrel k r v) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
    (∃ u < p, ∃ q < p, (∃ t < p, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C
        ∧ p = qqBall u q) ∨
    (∃ u < p, ∃ q < p, (∃ t < p, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ C
        ∧ p = qqBex u q) where
  mp := by
    rintro (rfl | rfl | ⟨k, r, v, rfl⟩ | ⟨k, r, v, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩
      | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ | ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩)
    · tauto
    · tauto
    · exact Or.inr (Or.inr (Or.inl ⟨k, by simp, r, by simp, v, by simp, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, by simp, r, by simp, v, by simp, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, by simp, p₂, by simp, hp, hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, by simp, p₂, by simp, hp, hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨termBShift ℒₒᵣ t, lt_u_qqBall _ _, q, lt_q_qqBall _ _,
          ⟨t, lt_of_le_of_lt (le_termBShift ht) (lt_u_qqBall _ _), ht, rfl⟩, hq, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨termBShift ℒₒᵣ t, lt_u_qqBex _ _, q, lt_q_qqBex _ _,
          ⟨t, lt_of_le_of_lt (le_termBShift ht) (lt_u_qqBex _ _), ht, rfl⟩, hq, rfl⟩))))))
  mpr := by
    unfold Phi
    rintro (rfl | rfl | ⟨k, _, r, _, v, _, rfl⟩ | ⟨k, _, r, _, v, _, rfl⟩
      | ⟨p₁, _, p₂, _, hp, hq, rfl⟩ | ⟨p₁, _, p₂, _, hp, hq, rfl⟩
      | ⟨u, _, q, _, ⟨t, _, ht, rfl⟩, hq, rfl⟩ | ⟨u, _, q, _, ⟨t, _, ht, rfl⟩, hq, rfl⟩) <;> grind

/-- Fixpoint blueprint whose least fixpoint is the internal `Δ₀` shape predicate.
- [HP98, Lemma I.1.68(1)] -/
noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “p C.
    !qqVerumDef p ∨ !qqFalsumDef p ∨
    (∃ k < p, ∃ r < p, ∃ v < p, !qqRelDef p k r v) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, !qqNRelDef p k r v) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqAndDef p p₁ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqOrDef p p₁ p₂) ∨
    (∃ u < p, ∃ q < p,
       (∃ t < p, !(isUTerm ℒₒᵣ).sigma t ∧ !(termBShiftGraph ℒₒᵣ) u t) ∧ q ∈ C
       ∧ !qqBallDef p u q) ∨
    (∃ u < p, ∃ q < p,
       (∃ t < p, !(isUTerm ℒₒᵣ).sigma t ∧ !(termBShiftGraph ℒₒᵣ) u t) ∧ q ∈ C
       ∧ !qqBexDef p u q)”)
  (.mkPi “p C.
    !qqVerumDef p ∨ !qqFalsumDef p ∨
    (∃ k < p, ∃ r < p, ∃ v < p, !qqRelDef p k r v) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, !qqNRelDef p k r v) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqAndDef p p₁ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqOrDef p p₁ p₂) ∨
    (∃ u < p, ∃ q < p,
       (∃ t < p, !(isUTerm ℒₒᵣ).pi t ∧ ∀ u', !(termBShiftGraph ℒₒᵣ) u' t → u = u') ∧ q ∈ C
       ∧ ∀ p', !qqBallDef p' u q → p = p') ∨
    (∃ u < p, ∃ q < p,
       (∃ t < p, !(isUTerm ℒₒᵣ).pi t ∧ ∀ u', !(termBShiftGraph ℒₒᵣ) u' t → u = u') ∧ q ∈ C
       ∧ ∀ p', !qqBexDef p' u q → p = p')”)⟩

/-- The fixpoint construction for `blueprint`.
- [HP98, Lemma I.1.68(1)] -/
def construction : Fixpoint.Construction V blueprint where
  Φ := fun _ ↦ Phi
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, HierarchySymbol.Semiformula.val_sigma, eq_comm,
        (termBShift.defined (L := ℒₒᵣ) (V := V)).df, (qqBall_defined (V := V)).df,
        (qqBex_defined (V := V)).df]
    · intro v
      symm
      simpa [blueprint, HierarchySymbol.Semiformula.val_sigma, eq_comm,
        (termBShift.defined (L := ℒₒᵣ) (V := V)).df, (qqBall_defined (V := V)).df,
        (qqBex_defined (V := V)).df]
        using phi_iff (V := V) _ _
  monotone := by
    unfold Phi
    rintro C C' hC _ x (h | h | h | h | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩
      | ⟨u, q, ht, hq, rfl⟩ | ⟨u, q, ht, hq, rfl⟩) <;> grind

instance : construction.StrongFinite V where
  strong_finite := by
    unfold construction Phi
    rintro C _ x (h | h | h | h | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩
      | ⟨u, q, ht, hq, rfl⟩ | ⟨u, q, ht, hq, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p₁, p₂, ⟨hp, by simp⟩, ⟨hq, by simp⟩, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p₁, p₂, ⟨hp, by simp⟩, ⟨hq, by simp⟩, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨u, q, ht, ⟨hq, lt_q_qqBall _ _⟩, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨u, q, ht, ⟨hq, lt_q_qqBex _ _⟩, rfl⟩))))))

end IsDelta0F

lemma shift_qqBall {u q : V} (hu : IsUTerm ℒₒᵣ u) (hq : IsUFormula ℒₒᵣ q) :
    shift ℒₒᵣ (qqBall u q) = qqBall (termShift ℒₒᵣ u) (shift ℒₒᵣ q) := by
  have hlt : IsUFormula ℒₒᵣ (Arithmetic.qqNLT (qqBvar 0) u) := by simp [Arithmetic.qqNLT, hu]
  rw [show qqBall u q = ^∀ ((Arithmetic.qqNLT (qqBvar 0) u) ^⋎ q) from rfl,
    show qqBall (termShift ℒₒᵣ u) (shift ℒₒᵣ q)
      = ^∀ ((Arithmetic.qqNLT (qqBvar 0) (termShift ℒₒᵣ u)) ^⋎ shift ℒₒᵣ q) from rfl,
    shift_all (by simp [hlt, hq]), shift_or hlt hq]
  simp [Arithmetic.qqNLT, hu]

lemma shift_qqBex {u q : V} (hu : IsUTerm ℒₒᵣ u) (hq : IsUFormula ℒₒᵣ q) :
    shift ℒₒᵣ (qqBex u q) = qqBex (termShift ℒₒᵣ u) (shift ℒₒᵣ q) := by
  have hlt : IsUFormula ℒₒᵣ (Arithmetic.qqLT (qqBvar 0) u) := by simp [Arithmetic.qqLT, hu]
  rw [show qqBex u q = ^∃ ((Arithmetic.qqLT (qqBvar 0) u) ^⋏ q) from rfl,
    show qqBex (termShift ℒₒᵣ u) (shift ℒₒᵣ q)
      = ^∃ ((Arithmetic.qqLT (qqBvar 0) (termShift ℒₒᵣ u)) ^⋏ shift ℒₒᵣ q) from rfl,
    shift_exs (by simp [hlt, hq]), shift_and hlt hq]
  simp [Arithmetic.qqLT, hu]

/-- `IsDelta0 p` says that `p` has the internal shape of a `Δ₀` formula.
- [HP98, Lemma I.1.68] -/
def IsDelta0 (p : V) : Prop := IsDelta0F.construction.Fixpoint ![] p

/-- `𝚫₁` recognizer for `IsDelta0`.
- [HP98, Lemma I.1.68(1)] -/
noncomputable def isDelta0 : 𝚫₁.Semisentence 1 := IsDelta0F.blueprint.fixpointDefΔ₁

/-- The recognizer defines the internal `Δ₀` shape predicate.
- [HP98, Lemma I.1.68(1)] -/
instance IsDelta0.defined : 𝚫₁-Predicate (IsDelta0 (V := V)) via isDelta0 :=
  IsDelta0F.construction.fixpoint_definedΔ₁

/-- The internal `Δ₀` shape predicate is `𝚫₁`-definable.
- [HP98, Lemma I.1.68(1)] -/
instance IsDelta0.definable : 𝚫₁-Predicate (IsDelta0 : V → Prop) := IsDelta0.defined.to_definable

/-- Characterization of internal `Δ₀` formulas by their outermost coding constructor.
- [HP98, Lemma I.1.68(2)] -/
lemma IsDelta0.case_iff {p : V} :
    IsDelta0 p ↔
    (p = ^⊤) ∨ (p = ^⊥) ∨
    (∃ k r v, p = ^rel k r v) ∨ (∃ k r v, p = ^nrel k r v) ∨
    (∃ p₁ p₂, IsDelta0 p₁ ∧ IsDelta0 p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, IsDelta0 p₁ ∧ IsDelta0 p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsDelta0 q ∧ p = qqBall u q) ∨
    (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsDelta0 q ∧ p = qqBex u q) :=
  IsDelta0F.construction.case

alias ⟨IsDelta0.case, IsDelta0.mk⟩ := IsDelta0.case_iff

@[simp] lemma IsDelta0.verum : IsDelta0 (V := V) (^⊤) := IsDelta0.mk (Or.inl rfl)
@[simp] lemma IsDelta0.falsum : IsDelta0 (V := V) (^⊥) := IsDelta0.mk (Or.inr (Or.inl rfl))
@[simp] lemma IsDelta0.rel {k r v : V} : IsDelta0 (^rel k r v) :=
  IsDelta0.mk (Or.inr (Or.inr (Or.inl ⟨k, r, v, rfl⟩)))
@[simp] lemma IsDelta0.nrel {k r v : V} : IsDelta0 (^nrel k r v) :=
  IsDelta0.mk (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, r, v, rfl⟩))))

/-- `Δ₀` shape is exactly inherited through internal conjunction.
- [HP98, Lemma I.1.68(2)] -/
@[simp] lemma IsDelta0.and_iff {p q : V} : IsDelta0 (p ^⋏ q) ↔ IsDelta0 p ∧ IsDelta0 q := by
  constructor
  · intro h
    rcases h.case with
      (h | h | ⟨_,_,_,h⟩ | ⟨_,_,_,h⟩ | ⟨p₁,p₂,hp,hq,h⟩ | ⟨_,_,_,_,h⟩ | ⟨_,_,_,_,h⟩ | ⟨_,_,_,_,h⟩) <;>
      simp only [qqAnd, qqVerum, qqFalsum, qqRel, qqNRel, qqOr, qqExs, qqBall, qqBex, qqAll,
        add_left_inj, pair_ext_iff, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_zero,
        OfNat.ofNat_ne_one, Nat.succ_ne_self, false_and, true_and] at h
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨hp, hq⟩
  · rintro ⟨hp, hq⟩
    exact IsDelta0.mk (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, hp, hq, rfl⟩)))))

/-- `Δ₀` shape is exactly inherited through internal disjunction.
- [HP98, Lemma I.1.68(2)] -/
@[simp] lemma IsDelta0.or_iff {p q : V} : IsDelta0 (p ^⋎ q) ↔ IsDelta0 p ∧ IsDelta0 q := by
  constructor
  · intro h
    rcases h.case with
      (h | h | ⟨_,_,_,h⟩ | ⟨_,_,_,h⟩ | ⟨_,_,_,_,h⟩ | ⟨p₁,p₂,hp,hq,h⟩ | ⟨_,_,_,_,h⟩ | ⟨_,_,_,_,h⟩) <;>
      simp only [qqOr, qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqExs, qqBall, qqBex, qqAll,
        add_left_inj, pair_ext_iff, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_zero,
        OfNat.ofNat_ne_one, Nat.succ_ne_self, false_and, true_and] at h
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨hp, hq⟩
  · rintro ⟨hp, hq⟩
    exact IsDelta0.mk (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, hp, hq, rfl⟩))))))

/-- A bounded universal quantification of a `Δ₀` code is `Δ₀`.
- [HP98, Lemma I.1.68(2)] -/
lemma IsDelta0.ball {t q : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsDelta0 q) :
    IsDelta0 (qqBall (termBShift ℒₒᵣ t) q) :=
  IsDelta0.mk (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨termBShift ℒₒᵣ t, q, ⟨t, ht, rfl⟩, hq, rfl⟩)))))))

/-- A bounded existential quantification of a `Δ₀` code is `Δ₀`.
- [HP98, Lemma I.1.68(2)] -/
lemma IsDelta0.bex {t q : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsDelta0 q) :
    IsDelta0 (qqBex (termBShift ℒₒᵣ t) q) :=
  IsDelta0.mk (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨termBShift ℒₒᵣ t, q, ⟨t, ht, rfl⟩, hq, rfl⟩)))))))

/-- Inversion for the universal quantifier: a `Δ₀` code beginning with `^∀` is a bounded
universal quantification.
- [HP98, Lemma I.1.68(2)] -/
lemma IsDelta0.of_all {p : V} (h : IsDelta0 (^∀ p)) :
    ∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsDelta0 q
      ∧ p = qqOr (Arithmetic.qqNLT (qqBvar 0) u) q := by
  rcases h.case with (h | h | ⟨_,_,_,h⟩ | ⟨_,_,_,h⟩ | ⟨_,_,_,_,h⟩ | ⟨_,_,_,_,h⟩
    | ⟨u, q, hguard, hq, h⟩ | ⟨_,_,_,_,h⟩) <;>
    first
      | (simp [qqAll, qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqExs, qqBex] at h
         done)
      | (rw [show qqBall u q = ^∀ (qqOr (Arithmetic.qqNLT (qqBvar 0) u) q) from rfl, qqAll_inj] at h
         exact ⟨u, q, hguard, hq, h⟩)

/-- Inversion for the existential quantifier: a `Δ₀` code beginning with `^∃` is a bounded
existential quantification.
- [HP98, Lemma I.1.68(2)] -/
lemma IsDelta0.of_ex {p : V} (h : IsDelta0 (^∃ p)) :
    ∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsDelta0 q
      ∧ p = (Arithmetic.qqLT (qqBvar 0) u) ^⋏ q := by
  rcases h.case with (h | h | ⟨_,_,_,h⟩ | ⟨_,_,_,h⟩ | ⟨_,_,_,_,h⟩ | ⟨_,_,_,_,h⟩
    | ⟨_,_,_,_,h⟩ | ⟨u, q, hguard, hq, h⟩) <;>
    first
      | (simp [qqExs, qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll, qqBall] at h
         done)
      | (rw [show qqBex u q = ^∃ ((Arithmetic.qqLT (qqBvar 0) u) ^⋏ q) from rfl, qqExs_inj] at h
         exact ⟨u, q, hguard, hq, h⟩)

/-- Recursion on the internal `Δ₀` shape.
- [HP98, Lemma I.1.68(2)] -/
lemma IsDelta0.induction (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (hverum : P ^⊤) (hfalsum : P ^⊥)
    (hrel : ∀ k r v, P (^rel k r v)) (hnrel : ∀ k r v, P (^nrel k r v))
    (hand : ∀ p q, IsDelta0 p → IsDelta0 q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsDelta0 p → IsDelta0 q → P p → P q → P (p ^⋎ q))
    (hball : ∀ t q, IsUTerm ℒₒᵣ t → IsDelta0 q → P q → P (qqBall (termBShift ℒₒᵣ t) q))
    (hbex : ∀ t q, IsUTerm ℒₒᵣ t → IsDelta0 q → P q → P (qqBex (termBShift ℒₒᵣ t) q)) :
    ∀ p, IsDelta0 p → P p :=
  IsDelta0F.construction.induction (v := ![]) hP (by
    rintro C hC x (rfl | rfl | ⟨k, r, v, rfl⟩ | ⟨k, r, v, rfl⟩ | ⟨p, q, hp, hq, rfl⟩
      | ⟨p, q, hp, hq, rfl⟩ | ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ | ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩)
    · exact hverum
    · exact hfalsum
    · exact hrel k r v
    · exact hnrel k r v
    · exact hand p q (hC p hp).1 (hC q hq).1 (hC p hp).2 (hC q hq).2
    · exact hor p q (hC p hp).1 (hC q hq).1 (hC p hp).2 (hC q hq).2
    · exact hball t q ht (hC q hq).1 (hC q hq).2
    · exact hbex t q ht (hC q hq).1 (hC q hq).2)

/-- `Δ₀` shape is preserved by syntactic negation.
- [HP98, Lemma I.1.68(2)(ii)] -/
lemma IsDelta0.neg {p : V} (hp : IsUFormula ℒₒᵣ p) (h : IsDelta0 p) :
    IsDelta0 (Bootstrapping.neg ℒₒᵣ p) := by
  have H : ∀ p : V, IsDelta0 p → IsUFormula ℒₒᵣ p → IsDelta0 (Bootstrapping.neg ℒₒᵣ p) := by
    apply IsDelta0.induction 𝚺
      (P := fun p ↦ IsUFormula ℒₒᵣ p → IsDelta0 (Bootstrapping.neg ℒₒᵣ p))
    · definability
    · simp
    · simp
    · intro k r v h
      obtain ⟨hr, hv⟩ := IsUFormula.rel.mp h
      simp [hr, hv]
    · intro k r v h
      obtain ⟨hr, hv⟩ := IsUFormula.nrel.mp h
      simp [hr, hv]
    · intro p q _ _ ihp ihq h
      obtain ⟨hp, hq⟩ := IsUFormula.and.mp h
      simp [hp, hq, ihp hp, ihq hq]
    · intro p q _ _ ihp ihq h
      obtain ⟨hp, hq⟩ := IsUFormula.or.mp h
      simp [hp, hq, ihp hp, ihq hq]
    · intro t q ht _ ih h
      obtain ⟨-, hq⟩ : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) ∧ IsUFormula ℒₒᵣ q := by
        simpa [qqBall, Arithmetic.qqNLT] using h
      rw [neg_qqBall ht.termBShift hq]
      exact IsDelta0.bex ht (ih hq)
    · intro t q ht _ ih h
      obtain ⟨-, hq⟩ : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) ∧ IsUFormula ℒₒᵣ q := by
        simpa [qqBex, Arithmetic.qqLT] using h
      rw [neg_qqBex ht.termBShift hq]
      exact IsDelta0.ball ht (ih hq)
  exact H p h hp

/-- `Δ₀` shape is preserved by the free-variable shift.
- [HP98, Lemma I.1.68(2)] -/
lemma IsDelta0.shift {p : V} (hp : IsUFormula ℒₒᵣ p) (h : IsDelta0 p) :
    IsDelta0 (Bootstrapping.shift ℒₒᵣ p) := by
  have H : ∀ p : V, IsDelta0 p → IsUFormula ℒₒᵣ p → IsDelta0 (Bootstrapping.shift ℒₒᵣ p) := by
    apply IsDelta0.induction 𝚺
      (P := fun p ↦ IsUFormula ℒₒᵣ p → IsDelta0 (Bootstrapping.shift ℒₒᵣ p))
    · definability
    · simp
    · simp
    · intro k r v h
      obtain ⟨hr, hv⟩ := IsUFormula.rel.mp h
      simp [hr, hv]
    · intro k r v h
      obtain ⟨hr, hv⟩ := IsUFormula.nrel.mp h
      simp [hr, hv]
    · intro p q _ _ ihp ihq h
      obtain ⟨hp, hq⟩ := IsUFormula.and.mp h
      simp [hp, hq, ihp hp, ihq hq]
    · intro p q _ _ ihp ihq h
      obtain ⟨hp, hq⟩ := IsUFormula.or.mp h
      simp [hp, hq, ihp hp, ihq hq]
    · intro t q ht _ ih h
      obtain ⟨-, hq⟩ : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) ∧ IsUFormula ℒₒᵣ q := by
        simpa [qqBall, Arithmetic.qqNLT] using h
      rw [shift_qqBall ht.termBShift hq, ← termBShift_termShift ht.isSemiterm]
      exact IsDelta0.ball ht.termShift (ih hq)
    · intro t q ht _ ih h
      obtain ⟨-, hq⟩ : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) ∧ IsUFormula ℒₒᵣ q := by
        simpa [qqBex, Arithmetic.qqLT] using h
      rw [shift_qqBex ht.termBShift hq, ← termBShift_termShift ht.isSemiterm]
      exact IsDelta0.bex ht.termShift (ih hq)
  exact H p h hp

lemma IsDelta0.isSigma1 {p : V} (h : IsDelta0 p) : IsSigma1 p := by
  have : 𝚫₁-Predicate (IsSigma1 : V → Prop) := IsSigma1.defined.to_definable
  have H : ∀ p : V, IsDelta0 p → IsSigma1 p := by
    apply IsDelta0.induction 𝚺 (P := fun p ↦ IsSigma1 p)
    · definability
    · simp
    · simp
    · intro k r v; simp
    · intro k r v; simp
    · intro p q _ _ ihp ihq; simp [ihp, ihq]
    · intro p q _ _ ihp ihq; simp [ihp, ihq]
    · intro t q ht _ ih
      exact IsSigma1.mk (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨termBShift ℒₒᵣ t, q, ⟨t, ht, rfl⟩, ih, rfl⟩)))))))
    · intro t q _ _ ih
      simp [qqBex, Arithmetic.qqLT, ih]
  exact H p h

end LO.FirstOrder.Arithmetic.Bootstrapping

namespace LO.FirstOrder.Arithmetic

/-! ## Correctness of `IsDelta0`: `IsDelta0 ⌜ψ⌝ ↔ Hierarchy 𝚺 0 ψ` -/

open Bootstrapping in
/-- The code of a bounded existential quantification is `qqBex` of its bound and body codes.
- [HP98, 0.30] -/
lemma quote_bex {n : ℕ} (t : SyntacticSemiterm ℒₒᵣ n) (φ : ArithmeticSemiproposition (n + 1)) :
    (⌜(∃¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemiproposition n)⌝ : ℕ)
      = qqBex (termBShift ℒₒᵣ (⌜t⌝ : ℕ)) (⌜φ⌝ : ℕ) := by
  rw [Semiformula.bexs_eq]
  simp only [Semiformula.Operator.lt_def, Semiformula.quote_ex,
    Semiformula.quote_and, qqBex, qqExs_inj, qqAnd_inj, and_true]
  simp [Semiformula.quote_rel, Arithmetic.qqLT, Arithmetic.ltIndex, Semiterm.quote_def,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

open Bootstrapping in
/-- A bounded formula has a `Δ₀` code.
- [HP98, Lemma I.1.68] -/
lemma isDelta0_of_hierarchy {n : ℕ} {ψ : ArithmeticSemiproposition n} (h : Hierarchy 𝚺 0 ψ) :
    IsDelta0 (⌜ψ⌝ : ℕ) := by
  refine delta₀_induction (P := fun n φ ↦ IsDelta0 (⌜φ⌝ : ℕ))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ n ψ h
  · intro n; simp
  · intro n; simp
  · intro n t₁ t₂; simp [Semiformula.quote_rel]
  · intro n t₁ t₂; simp [Semiformula.quote_nrel]
  · intro n t₁ t₂; simp [Semiformula.quote_rel]
  · intro n t₁ t₂; simp [Semiformula.quote_nrel]
  · intro n φ ψ hφ hψ ihφ ihψ; simpa [Semiformula.quote_and] using ⟨ihφ, ihψ⟩
  · intro n φ ψ hφ hψ ihφ ihψ; simpa [Semiformula.quote_or] using ⟨ihφ, ihψ⟩
  · intro n t φ hφ ihφ
    rw [quote_ball]
    exact IsDelta0.ball (by simp [Semiterm.quote_def]) ihφ
  · intro n t φ hφ ihφ
    rw [quote_bex]
    exact IsDelta0.bex (by simp [Semiterm.quote_def]) ihφ

open Bootstrapping in
/-- A formula with a `Δ₀` code is bounded.
- [HP98, Lemma I.1.68] -/
lemma hierarchy_of_isDelta0 {n : ℕ} (ψ : ArithmeticSemiproposition n) :
    IsDelta0 (⌜ψ⌝ : ℕ) → Hierarchy 𝚺 0 ψ := by
  induction ψ using Semiformula.rec' with
  | hverum => intro _; simp
  | hfalsum => intro _; simp
  | hrel R v => intro _; exact Hierarchy.rel _ _ _ _
  | hnrel R v => intro _; exact Hierarchy.nrel _ _ _ _
  | hand φ ψ ihφ ihψ =>
      intro h; rw [Semiformula.quote_and (V := ℕ) φ ψ, IsDelta0.and_iff] at h
      exact Hierarchy.and (ihφ h.1) (ihψ h.2)
  | hor φ ψ ihφ ihψ =>
      intro h; rw [Semiformula.quote_or (V := ℕ) φ ψ, IsDelta0.or_iff] at h
      exact Hierarchy.or (ihφ h.1) (ihψ h.2)
  | hall φ ihφ =>
      intro h
      rw [Semiformula.quote_all (V := ℕ) φ] at h
      obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, hφeq⟩ := IsDelta0.of_all h
      have hsf := Semiformula.quote_isSemiformula (V := ℕ) φ
      simp only [natCast_nat] at hsf
      rw [hφeq, Arithmetic.qqNLT] at hsf
      simp only [IsSemiformula.or, IsSemiformula.nrel] at hsf
      obtain ⟨⟨_, hvec⟩, hqsf⟩ := hsf
      obtain ⟨φ₂, hφ₂⟩ := IsSemiformula.sound hqsf
      have htmsf := hvec.nth (i := 1) (show (1 : ℕ) < 2 by simp)
      simp only [nth_adjoin_one, nth_adjoin_zero] at htmsf
      obtain ⟨s, hs⟩ := IsSemiterm.sound
        ((IsSemiterm.def (L := ℒₒᵣ)).mpr ⟨ht,
          (termBV_termBShift_le (L := ℒₒᵣ) ht _).mp ((IsSemiterm.def (L := ℒₒᵣ)).mp htmsf).2⟩)
      have heq : (∀¹ φ) = ∀¹[“#0 < !!(Rew.bShift s)”] φ₂ := by
        apply (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp
        rw [Semiformula.quote_all (V := ℕ) φ, hφeq, quote_ball, hs, hφ₂]
        rfl
      have hφ : Hierarchy 𝚺 0 φ := ihφ (by rw [hφeq]; simp [IsDelta0.or_iff, hq, Arithmetic.qqNLT])
      have hφ2 : Hierarchy 𝚺 0 φ₂ := by
        have hform : φ = (“#0 < !!(Rew.bShift s)” 🡒 φ₂) :=
          (Semiformula.all_inj _ _).mp (by rw [← Semiformula.ball_eq]; exact heq)
        rw [hform, Semiformula.imp_eq, Hierarchy.or_iff] at hφ
        exact hφ.2
      rw [heq]
      exact Hierarchy.ball (Rew.positive_iff.mpr ⟨s, rfl⟩) hφ2
  | hexs φ ihφ =>
      intro h
      rw [Semiformula.quote_ex (V := ℕ) φ] at h
      obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, hφeq⟩ := IsDelta0.of_ex h
      have hsf := Semiformula.quote_isSemiformula (V := ℕ) φ
      simp only [natCast_nat] at hsf
      rw [hφeq, Arithmetic.qqLT] at hsf
      simp only [IsSemiformula.and, IsSemiformula.rel] at hsf
      obtain ⟨⟨_, hvec⟩, hqsf⟩ := hsf
      obtain ⟨φ₂, hφ₂⟩ := IsSemiformula.sound hqsf
      have htmsf := hvec.nth (i := 1) (show (1 : ℕ) < 2 by simp)
      simp only [nth_adjoin_one, nth_adjoin_zero] at htmsf
      obtain ⟨s, hs⟩ := IsSemiterm.sound
        ((IsSemiterm.def (L := ℒₒᵣ)).mpr ⟨ht,
          (termBV_termBShift_le (L := ℒₒᵣ) ht _).mp ((IsSemiterm.def (L := ℒₒᵣ)).mp htmsf).2⟩)
      have heq : (∃¹ φ) = ∃¹[“#0 < !!(Rew.bShift s)”] φ₂ := by
        apply (Semiformula.quote_inj_iff (L := ℒₒᵣ) (V := ℕ)).mp
        rw [Semiformula.quote_ex (V := ℕ) φ, hφeq, quote_bex, hs, hφ₂]
        rfl
      have hφ : Hierarchy 𝚺 0 φ := ihφ (by rw [hφeq]; simp [IsDelta0.and_iff, hq, Arithmetic.qqLT])
      have hφ2 : Hierarchy 𝚺 0 φ₂ := by
        have hform : φ = (“#0 < !!(Rew.bShift s)” ⋏ φ₂) :=
          (Semiformula.exs_inj _ _).mp (by rw [← Semiformula.bexs_eq]; exact heq)
        rw [hform, Hierarchy.and_iff] at hφ
        exact hφ.2
      rw [heq]
      exact Hierarchy.bexs (Rew.positive_iff.mpr ⟨s, rfl⟩) hφ2

/-- Correctness of the `Δ₀`-code recognizer over the standard model.
- [HP98, Lemma I.1.68] -/
lemma isDelta0_iff_hierarchy {n : ℕ} (ψ : ArithmeticSemiproposition n) :
    Bootstrapping.IsDelta0 (⌜ψ⌝ : ℕ) ↔ Hierarchy 𝚺 0 ψ :=
  ⟨hierarchy_of_isDelta0 ψ, isDelta0_of_hierarchy⟩

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open Bootstrapping in
/-- Internal `Δ₀` recognition of a quoted formula agrees with its external hierarchy class.
- [HP98, Lemma I.1.68] -/
lemma isDelta0_quote_iff_s {n : ℕ} (ψ : ArithmeticSemiproposition n) :
    IsDelta0 (⌜ψ⌝ : V) ↔ Hierarchy 𝚺 0 ψ :=
  have h : V ⊧/![(⌜ψ⌝ : V)] isDelta0.val ↔ ℕ ⊧/![(⌜ψ⌝ : ℕ)] isDelta0.val := by
    simpa [Semiformula.coe_quote_eq_quote, Matrix.constant_eq_singleton]
      using models_iff_of_Delta1 (V := V) (σ := isDelta0)
        (IsDelta0.defined (V := ℕ)).proper (IsDelta0.defined (V := V)).proper (e := ![⌜ψ⌝])
  by simpa [(IsDelta0.defined (V := V)).df, (IsDelta0.defined (V := ℕ)).df,
    isDelta0_iff_hierarchy] using h

open Bootstrapping in
/-- Agreement with the external class on quoted semisentences.
- [HP98, Lemma I.1.68] -/
lemma isDelta0_quote_iff {n : ℕ} (σ : ArithmeticSemisentence n) :
    IsDelta0 (⌜σ⌝ : V) ↔ Hierarchy 𝚺 0 σ := by
  simp [Sentence.quote_def, isDelta0_quote_iff_s]

end LO.FirstOrder.Arithmetic
