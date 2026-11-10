module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping.Syntax.Formula.Functions
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Bounded

/-!
# Internal $\Delta_0$ formulas in models of $\mathsf{EA}$

The part of `Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Formula/Bounded.lean` in the
namespace `Bootstrapping`, ported to models of $\mathsf{EA}$: the bounded existential quantifier
`qqBex` on codes and the predicate `IsBounded` on codes of bounded arithmetical formulas, with
induction on locally $\Delta_0$ predicates, closed under negation and shift. The formulas are
Foundation's `qqBexDef`, `IsBoundedF.blueprint` and `isBounded`.

## References

- [HP98, 0.30, Lemma I.1.68]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (isBounded)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

/-! ## Internal bounded existential quantifier `qqBex` -/

section qqBex

/-- The code of the bounded existential quantifier `∃¹[“#0 < u”] q`. -/
noncomputable def qqBex (u q : V) : V := ^∃ ((^#0 ^< u) ^⋏ q)

@[simp] lemma lt_q_qqBex (u q : V) : q < qqBex u q := lt_trans (lt_K!_right _ _) (lt_exists _)

@[simp] lemma lt_u_qqBex (u q : V) : u < qqBex u q :=
  lt_trans (Arithmetic.lt_qqLT_right _ _) (lt_trans (lt_K!_left _ _) (lt_exists _))

instance qqBex_defined : 𝚺ᴬ₁-Function₂ (qqBex : V → V → V) via qqBexDef := .mk fun v ↦ by
  simp [qqBexDef, qqBex, Arithmetic.qqLT_defined.df]

instance qqBex_definable (Γ m) : Γᴬ_[m + 1]-Function₂ (qqBex : V → V → V) :=
  .of_sigmaOne qqBex_defined.to_definable

lemma qqNLT_locallyDelta0 : LocallyDelta0Function₂ (Arithmetic.qqNLT : V → V → V) :=
  qqNRel_locallyDelta0.comp₃ (LocallyDelta0Function.const _) (LocallyDelta0Function.const _)
    (LocallyDelta0Function.adjoin.comp₂ (LocallyDelta0Function.var 0)
      (LocallyDelta0Function.adjoin.comp₂ (LocallyDelta0Function.var 1)
        (LocallyDelta0Function.const 0)))

lemma qqLT_locallyDelta0 : LocallyDelta0Function₂ (Arithmetic.qqLT : V → V → V) :=
  qqRel_locallyDelta0.comp₃ (LocallyDelta0Function.const _) (LocallyDelta0Function.const _)
    (LocallyDelta0Function.adjoin.comp₂ (LocallyDelta0Function.var 0)
      (LocallyDelta0Function.adjoin.comp₂ (LocallyDelta0Function.var 1)
        (LocallyDelta0Function.const 0)))

lemma qqBall_locallyDelta0 : LocallyDelta0Function₂ (qqBall : V → V → V) :=
  qqAll_locallyDelta0.comp₁ <| qqOr_locallyDelta0.comp₂
    (qqNLT_locallyDelta0.comp₂ (qqBvar_locallyDelta0.comp₁ (LocallyDelta0Function.const 0))
      (LocallyDelta0Function.var 0))
    (LocallyDelta0Function.var 1)

lemma qqBex_locallyDelta0 : LocallyDelta0Function₂ (qqBex : V → V → V) :=
  qqExs_locallyDelta0.comp₁ <| qqAnd_locallyDelta0.comp₂
    (qqLT_locallyDelta0.comp₂ (qqBvar_locallyDelta0.comp₁ (LocallyDelta0Function.const 0))
      (LocallyDelta0Function.var 0))
    (LocallyDelta0Function.var 1)

variable {u q : V} (hu : IsUTerm ℒₒᵣ u) (hq : IsUFormula ℒₒᵣ q)
include hu hq

lemma neg_qqBall : neg ℒₒᵣ (qqBall u q) = qqBex u (neg ℒₒᵣ q) := by
  simp [qqBall, qqBex, Arithmetic.qqNLT, Arithmetic.qqLT, hu, hq]

lemma neg_qqBex : neg ℒₒᵣ (qqBex u q) = qqBall u (neg ℒₒᵣ q) := by
  simp [qqBall, qqBex, Arithmetic.qqNLT, Arithmetic.qqLT, hu, hq]

lemma shift_qqBall : shift ℒₒᵣ (qqBall u q) = qqBall (termShift ℒₒᵣ u) (shift ℒₒᵣ q) := by
  simp [qqBall, Arithmetic.qqNLT, hu, hq]

lemma shift_qqBex : shift ℒₒᵣ (qqBex u q) = qqBex (termShift ℒₒᵣ u) (shift ℒₒᵣ q) := by
  simp [qqBex, Arithmetic.qqLT, hu, hq]

end qqBex

/-! ## Internal $\Delta_0$ predicate `IsBounded` -/

section isBounded

namespace IsBoundedF

/-- The operator generating the codes of bounded formulas. -/
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
    · disj 1; rfl
    · disj 2; rfl
    · disj 3; exact ⟨k, by simp, r, by simp, v, by simp, rfl⟩
    · disj 4; exact ⟨k, by simp, r, by simp, v, by simp, rfl⟩
    · disj 5; exact ⟨p₁, by simp, p₂, by simp, hp, hq, rfl⟩
    · disj 6; exact ⟨p₁, by simp, p₂, by simp, hp, hq, rfl⟩
    · disj 7
      exact ⟨termBShift ℒₒᵣ t, lt_u_qqBall _ _, q, lt_q_qqBall _ _,
        ⟨t, (le_termBShift ht).trans_lt (lt_u_qqBall _ _), ht, rfl⟩, hq, rfl⟩
    · disj 8
      exact ⟨termBShift ℒₒᵣ t, lt_u_qqBex _ _, q, lt_q_qqBex _ _,
        ⟨t, (le_termBShift ht).trans_lt (lt_u_qqBex _ _), ht, rfl⟩, hq, rfl⟩
  mpr := by
    unfold Phi
    rintro (rfl | rfl | ⟨k, _, r, _, v, _, rfl⟩ | ⟨k, _, r, _, v, _, rfl⟩
      | ⟨p₁, _, p₂, _, hp, hq, rfl⟩ | ⟨p₁, _, p₂, _, hp, hq, rfl⟩
      | ⟨u, _, q, _, ⟨t, _, ht, rfl⟩, hq, rfl⟩ | ⟨u, _, q, _, ⟨t, _, ht, rfl⟩, hq, rfl⟩) <;> grind

lemma locallyDelta0_mem (i j : Fin 4) : LocallyDelta0 fun y : Fin 4 → V ↦ y i ∈ y j :=
  LocallyDelta0.mem (LocallyDelta0Function.var i) (LocallyDelta0Function.var j)

lemma locallyDelta0_binary {f : V → V → V} (hf : LocallyDelta0Function₂ f) :
    LocallyDelta0 fun w : Fin 2 → V ↦
      ∃ p₁ < w 0, ∃ p₂ < w 0, p₁ ∈ w 1 ∧ p₂ ∈ w 1 ∧ w 0 = f p₁ p₂ :=
  LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var (0 : Fin 2)) <|
    LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 1) <|
      (locallyDelta0_mem 1 3).and <| (locallyDelta0_mem 0 3).and <|
        LocallyDelta0.eq (LocallyDelta0Function.var 2) <|
          hf.comp₂ (LocallyDelta0Function.var 1) (LocallyDelta0Function.var 0)

lemma locallyDelta0_bounded {f : V → V → V} (hf : LocallyDelta0Function₂ f) :
    LocallyDelta0 fun w : Fin 2 → V ↦
      ∃ u < w 0, ∃ q < w 0,
        (∃ t < w 0, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ q ∈ w 1 ∧ w 0 = f u q := by
  have hterm : LocallyDelta0 fun y : Fin 5 → V ↦ IsUTerm ℒₒᵣ (y 0) ∧ y 2 = termBShift ℒₒᵣ (y 0) :=
    (isUTerm_locallyDelta0.pred_comp (LocallyDelta0Function.var 0)).and <|
      LocallyDelta0.eq (LocallyDelta0Function.var 2)
        (termBShift_locallyDelta0.comp₁ (LocallyDelta0Function.var 0))
  exact LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var (0 : Fin 2)) <|
    LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 1) <|
      (LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var (2 : Fin 4)) hterm).and <|
        (locallyDelta0_mem 0 3).and <| LocallyDelta0.eq (LocallyDelta0Function.var 2) <|
          hf.comp₂ (LocallyDelta0Function.var 1) (LocallyDelta0Function.var 0)

lemma phi_locallyDelta0 :
    LocallyDelta0 fun w : Fin 2 → V ↦ Phi {x | x ∈ w 1} (w 0) := by
  have hrel : LocallyDelta0 fun y : Fin 5 → V ↦ y 3 = qqRel (y 2) (y 1) (y 0) :=
    LocallyDelta0.eq (LocallyDelta0Function.var 3) <|
      qqRel_locallyDelta0.comp₃ (LocallyDelta0Function.var 2) (LocallyDelta0Function.var 1)
        (LocallyDelta0Function.var 0)
  have hnrel : LocallyDelta0 fun y : Fin 5 → V ↦ y 3 = qqNRel (y 2) (y 1) (y 0) :=
    LocallyDelta0.eq (LocallyDelta0Function.var 3) <|
      qqNRel_locallyDelta0.comp₃ (LocallyDelta0Function.var 2) (LocallyDelta0Function.var 1)
        (LocallyDelta0Function.var 0)
  have hverum : LocallyDelta0 fun w : Fin 2 → V ↦ w 0 = qqVerum :=
    LocallyDelta0.eq (LocallyDelta0Function.var 0) (LocallyDelta0Function.const _)
  have hfalsum : LocallyDelta0 fun w : Fin 2 → V ↦ w 0 = qqFalsum :=
    LocallyDelta0.eq (LocallyDelta0Function.var 0) (LocallyDelta0Function.const _)
  have hex₁ := LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var (0 : Fin 2)) <|
    LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 1) <|
      LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 2) hrel
  have hex₂ := LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var (0 : Fin 2)) <|
    LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 1) <|
      LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 2) hnrel
  exact (hverum.or <| hfalsum.or <| hex₁.or <| hex₂.or <|
    (locallyDelta0_binary qqAnd_locallyDelta0).or <|
    (locallyDelta0_binary qqOr_locallyDelta0).or <|
    (locallyDelta0_bounded qqBall_locallyDelta0).or
    (locallyDelta0_bounded qqBex_locallyDelta0)).of_iff
    fun w ↦ by simpa using phi_iff (w 1) (w 0)

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.IsBoundedF (blueprint) in
/-- The construction of the codes of bounded formulas. -/
def construction : Fixpoint.Construction V blueprint where
  Φ := fun _ ↦ Phi
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm,
        (termBShift.defined (L := ℒₒᵣ)).df, qqBall_defined.df, qqBex_defined.df]
    · intro v
      simpa [blueprint, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm,
        (termBShift.defined (L := ℒₒᵣ)).df, qqBall_defined.df, qqBex_defined.df]
        using (phi_iff _ _).symm
  monotone := by
    unfold Phi
    intro C C' hC _ x
    grind
  Φ_locallyDelta0 := phi_locallyDelta0

instance : construction.StrongFinite V where
  strong_finite := by
    unfold construction Phi
    rintro C _ x (h | h | h | h | ⟨p₁, p₂, hp, hq, rfl⟩ | ⟨p₁, p₂, hp, hq, rfl⟩
      | ⟨u, q, ht, hq, rfl⟩ | ⟨u, q, ht, hq, rfl⟩) <;>
      grind [lt_K!_left, lt_K!_right, lt_or_left, lt_or_right, lt_q_qqBall, lt_q_qqBex]

end IsBoundedF

open IsBoundedF

/-- The predicate that `p` is the code of a bounded formula. -/
def IsBounded (p : V) : Prop := construction.Fixpoint ![] p

instance IsBounded.defined : 𝚫ᴬ₁-Predicate (IsBounded (V := V)) via isBounded :=
  construction.fixpoint_definedΔ₁

instance IsBounded.definable : 𝚫ᴬ₁-Predicate (IsBounded : V → Prop) :=
  IsBounded.defined.to_definable

lemma isBounded_locallyDelta0 : LocallyDelta0Pred (IsBounded (V := V)) :=
  construction.fixpoint_locallyDelta0.of_iff fun w ↦
    iff_of_eq <| congrArg (fun u ↦ construction.Fixpoint u (w 0)) (Subsingleton.elim _ _)

lemma IsBounded.case_iff {p : V} :
    IsBounded p ↔
    (p = ^⊤) ∨
    (p = ^⊥) ∨
    (∃ k r v, p = ^rel k r v) ∨
    (∃ k r v, p = ^nrel k r v) ∨
    (∃ p₁ p₂, IsBounded p₁ ∧ IsBounded p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, IsBounded p₁ ∧ IsBounded p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsBounded q ∧ p = qqBall u q) ∨
    (∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsBounded q ∧ p = qqBex u q) :=
  construction.case

alias ⟨IsBounded.case, IsBounded.mk⟩ := IsBounded.case_iff

@[simp] lemma IsBounded.verum : IsBounded (V := V) (^⊤) := IsBounded.mk <| by disj 1; rfl
@[simp] lemma IsBounded.falsum : IsBounded (V := V) (^⊥) := IsBounded.mk <| by disj 2; rfl

@[simp] lemma IsBounded.rel {k r v : V} : IsBounded (^rel k r v) :=
  IsBounded.mk <| by disj 3; exact ⟨k, r, v, rfl⟩

@[simp] lemma IsBounded.nrel {k r v : V} : IsBounded (^nrel k r v) :=
  IsBounded.mk <| by disj 4; exact ⟨k, r, v, rfl⟩

@[simp] lemma IsBounded.and_iff {p q : V} : IsBounded (p ^⋏ q) ↔ IsBounded p ∧ IsBounded q := by
  constructor
  · intro h
    rcases h.case with (h | h | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
      | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩) <;>
      simp_all [qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll, qqExs, qqBall, qqBex]
  · rintro ⟨hp, hq⟩
    exact IsBounded.mk <| by disj 5; exact ⟨p, q, hp, hq, rfl⟩

@[simp] lemma IsBounded.or_iff {p q : V} : IsBounded (p ^⋎ q) ↔ IsBounded p ∧ IsBounded q := by
  constructor
  · intro h
    rcases h.case with (h | h | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
      | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩) <;>
      simp_all [qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll, qqExs, qqBall, qqBex]
  · rintro ⟨hp, hq⟩
    exact IsBounded.mk <| by disj 6; exact ⟨p, q, hp, hq, rfl⟩

lemma IsBounded.ball {t q : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsBounded q) :
    IsBounded (qqBall (termBShift ℒₒᵣ t) q) :=
  IsBounded.mk <| by disj 7; exact ⟨_, q, ⟨t, ht, rfl⟩, hq, rfl⟩

lemma IsBounded.bex {t q : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsBounded q) :
    IsBounded (qqBex (termBShift ℒₒᵣ t) q) :=
  IsBounded.mk <| by disj 8; exact ⟨_, q, ⟨t, ht, rfl⟩, hq, rfl⟩

lemma IsBounded.of_all {p : V} (h : IsBounded (^∀ p)) :
    ∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsBounded q ∧ p = (^#0 ^≮ u) ^⋎ q := by
  rcases h.case with (h | h | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
    | ⟨_, _, ht, hq, h⟩ | ⟨_, _, _, _, h⟩) <;>
    simp_all [qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll, qqExs, qqBall, qqBex,
      Arithmetic.qqNLT]

lemma IsBounded.of_ex {p : V} (h : IsBounded (^∃ p)) :
    ∃ u q, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ IsBounded q ∧ p = (^#0 ^< u : V) ^⋏ q := by
  rcases h.case with (h | h | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
    | ⟨_, _, _, _, h⟩ | ⟨_, _, ht, hq, h⟩) <;>
    simp_all [qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll, qqExs, qqBall, qqBex,
      Arithmetic.qqLT]

lemma IsBounded.of_qqBall {u p : V} (h : IsBounded (qqBall u p)) : IsBounded p := by
  obtain ⟨u', q', -, hq', heq⟩ := IsBounded.of_all (p := (Arithmetic.qqNLT (qqBvar 0) u) ^⋎ p) h
  obtain ⟨-, rfl⟩ := (qqOr_inj _ _ _ _).mp heq
  exact hq'

lemma IsBounded.of_qqBex {u p : V} (h : IsBounded (qqBex u p)) : IsBounded p := by
  obtain ⟨u', q', -, hq', heq⟩ := IsBounded.of_ex (p := (Arithmetic.qqLT (qqBvar 0) u) ^⋏ p) h
  obtain ⟨-, rfl⟩ := (qqAnd_inj _ _ _ _).mp heq
  exact hq'

lemma IsBounded.induction {P : V → Prop} (hP : LocallyDelta0Pred P)
    (hverum : P ^⊤) (hfalsum : P ^⊥)
    (hrel : ∀ k r v, P (^rel k r v)) (hnrel : ∀ k r v, P (^nrel k r v))
    (hand : ∀ p q, IsBounded p → IsBounded q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsBounded p → IsBounded q → P p → P q → P (p ^⋎ q))
    (hball : ∀ t q, IsUTerm ℒₒᵣ t → IsBounded q → P q → P (qqBall (termBShift ℒₒᵣ t) q))
    (hbex : ∀ t q, IsUTerm ℒₒᵣ t → IsBounded q → P q → P (qqBex (termBShift ℒₒᵣ t) q)) :
    ∀ p, IsBounded p → P p :=
  construction.induction (v := ![]) hP (by
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

lemma IsBounded.neg {p : V} (hp : IsUFormula ℒₒᵣ p) (h : IsBounded p) :
    IsBounded (Bootstrapping.neg ℒₒᵣ p) := by
  suffices ∀ p : V, IsBounded p → IsUFormula ℒₒᵣ p → IsBounded (Bootstrapping.neg ℒₒᵣ p) from
    this p h hp
  apply IsBounded.induction
    (P := fun p ↦ IsUFormula ℒₒᵣ p → IsBounded (Bootstrapping.neg ℒₒᵣ p))
    ((isUFormula_locallyDelta0 (L := ℒₒᵣ)).imp <| isBounded_locallyDelta0.pred_comp <|
      neg_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
    (by simp) (by simp) (by simp +contextual) (by simp +contextual) (by simp +contextual)
    (by simp +contextual)
  · intro t q ht _ ih h
    have hq : IsUFormula ℒₒᵣ q := by simp_all [qqBall]
    simpa [neg_qqBall ht.termBShift hq] using IsBounded.bex ht (ih hq)
  · intro t q ht _ ih h
    have hq : IsUFormula ℒₒᵣ q := by simp_all [qqBex]
    simpa [neg_qqBex ht.termBShift hq] using IsBounded.ball ht (ih hq)

lemma IsBounded.shift {p : V} (hp : IsUFormula ℒₒᵣ p) (h : IsBounded p) :
    IsBounded (Bootstrapping.shift ℒₒᵣ p) := by
  suffices ∀ p : V, IsBounded p → IsUFormula ℒₒᵣ p → IsBounded (Bootstrapping.shift ℒₒᵣ p) from
    this p h hp
  apply IsBounded.induction
    (P := fun p ↦ IsUFormula ℒₒᵣ p → IsBounded (Bootstrapping.shift ℒₒᵣ p))
    ((isUFormula_locallyDelta0 (L := ℒₒᵣ)).imp <| isBounded_locallyDelta0.pred_comp <|
      shift_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 1)))
    (by simp) (by simp) (by simp +contextual) (by simp +contextual) (by simp +contextual)
    (by simp +contextual)
  · intro t q ht _ ih h
    have hq : IsUFormula ℒₒᵣ q := by simp_all [qqBall]
    simpa [shift_qqBall ht.termBShift hq, ← termBShift_termShift ht.isSemiterm]
      using IsBounded.ball ht.termShift (ih hq)
  · intro t q ht _ ih h
    have hq : IsUFormula ℒₒᵣ q := by simp_all [qqBex]
    simpa [shift_qqBex ht.termBShift hq, ← termBShift_termShift ht.isSemiterm]
      using IsBounded.bex ht.termShift (ih hq)

end isBounded

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping
