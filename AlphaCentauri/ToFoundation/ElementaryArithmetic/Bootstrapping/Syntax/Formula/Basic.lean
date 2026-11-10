module

public import AlphaCentauri.ToFoundation.ElementaryArithmetic.Bootstrapping.Syntax.Term.Basic
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Basic

/-!
# Codes of formulas in models of $\mathsf{EA}$

The part of `Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Formula/Basic.lean` before the
recursion on formulas, ported to models of $\mathsf{EA}$: the codes `qqRel`, `qqNRel`, `qqVerum`,
`qqFalsum`, `qqAnd`, `qqOr`, `qqAll` and `qqExs` of atomic formulas, their negations, the
constants, conjunctions, disjunctions and quantifications, and the predicate `IsUFormula L` of
codes of formulas with induction on locally $\Delta_0$ predicates. The formulas are Foundation's
`qqRelDef`, …, `qqExsDef` and `isUFormula`. The bound variables `bv` of a formula and the predicate
`IsSemiformula` follow, defined by Foundation's `bvGraph` and `isSemiformula`.

- [HP98, §V.3]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (isUFormula)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]
  {L : Language} [L.Encodable] [L.LORDefinable]

section formula

/-- The code of the atomic formula given by the relation symbol `r` of arity `k` and the list `v`
of terms. -/
noncomputable def qqRel (k r v : V) : V := ⟪0, k, r, v⟫ + 1

/-- The code of the negated atomic formula given by the relation symbol `r` of arity `k` and the
list `v` of terms. -/
noncomputable def qqNRel (k r v : V) : V := ⟪1, k, r, v⟫ + 1

/-- The code of the verum. -/
noncomputable def qqVerum : V := ⟪2, 0⟫ + 1

/-- The code of the falsum. -/
noncomputable def qqFalsum : V := ⟪3, 0⟫ + 1

/-- The code of the conjunction of `p` and `q`. -/
noncomputable def qqAnd (p q : V) : V := ⟪4, p, q⟫ + 1

/-- The code of the disjunction of `p` and `q`. -/
noncomputable def qqOr (p q : V) : V := ⟪5, p, q⟫ + 1

/-- The code of the universal quantification of `p`. -/
noncomputable def qqAll (p : V) : V := ⟪6, p⟫ + 1

/-- The code of the existential quantification of `p`. -/
noncomputable def qqExs (p : V) : V := ⟪7, p⟫ + 1

scoped prefix:max "^rel " => qqRel

scoped prefix:max "^nrel " => qqNRel

scoped notation "^⊤" => qqVerum

scoped notation "^⊥" => qqFalsum

scoped notation p:69 " ^⋏ " q:70 => qqAnd p q

scoped notation p:68 " ^⋎ " q:69 => qqOr p q

scoped notation "^∀ " p:64 => qqAll p

scoped notation "^∃ " p:64 => qqExs p

instance qqRel_defined : 𝚺ᴬ₀-Function₃ (qqRel : V → V → V → V) via qqRelDef :=
  .mk fun v ↦ by simp_all [qqRelDef, qqRel]

instance qqNRel_defined : 𝚺ᴬ₀-Function₃ (qqNRel : V → V → V → V) via qqNRelDef :=
  .mk fun v ↦ by simp_all [qqNRelDef, qqNRel]

instance qqVerum_defined : 𝚺ᴬ₀-Function₀ (qqVerum : V) via qqVerumDef :=
  .mk fun v ↦ by simp_all [qqVerumDef, qqVerum]

instance qqFalsum_defined : 𝚺ᴬ₀-Function₀ (qqFalsum : V) via qqFalsumDef :=
  .mk fun v ↦ by simp_all [qqFalsumDef, qqFalsum]

instance qqAnd_defined : 𝚺ᴬ₀-Function₂ (qqAnd : V → V → V) via qqAndDef :=
  .mk fun v ↦ by simp_all [qqAndDef, qqAnd]

instance qqOr_defined : 𝚺ᴬ₀-Function₂ (qqOr : V → V → V) via qqOrDef :=
  .mk fun v ↦ by simp_all [qqOrDef, numeral_eq_natCast, qqOr]

instance qqForall_defined : 𝚺ᴬ₀-Function₁ (qqAll : V → V) via qqAllDef :=
  .mk fun v ↦ by simp_all [qqAllDef, numeral_eq_natCast, qqAll]

instance qqExsists_defined : 𝚺ᴬ₀-Function₁ (qqExs : V → V) via qqExsDef :=
  .mk fun v ↦ by simp_all [qqExsDef, numeral_eq_natCast, qqExs]

instance qqRel_definable : 𝚺ᴬ₀-Function₃ (qqRel : V → V → V → V) := qqRel_defined.to_definable

instance qqNRel_definable : 𝚺ᴬ₀-Function₃ (qqNRel : V → V → V → V) := qqNRel_defined.to_definable

instance qqAnd_definable : 𝚺ᴬ₀-Function₂ (qqAnd : V → V → V) := qqAnd_defined.to_definable

instance qqOr_definable : 𝚺ᴬ₀-Function₂ (qqOr : V → V → V) := qqOr_defined.to_definable

instance qqAll_definable : 𝚺ᴬ₀-Function₁ (qqAll : V → V) := qqForall_defined.to_definable

instance qqExs_definable : 𝚺ᴬ₀-Function₁ (qqExs : V → V) := qqExsists_defined.to_definable

@[simp] lemma qqRel_inj (k₁ r₁ v₁ k₂ r₂ v₂ : V) :
    ^rel k₁ r₁ v₁ = ^rel k₂ r₂ v₂ ↔ k₁ = k₂ ∧ r₁ = r₂ ∧ v₁ = v₂ := by simp [qqRel]

@[simp] lemma qqNRel_inj (k₁ r₁ v₁ k₂ r₂ v₂ : V) :
    ^nrel k₁ r₁ v₁ = ^nrel k₂ r₂ v₂ ↔ k₁ = k₂ ∧ r₁ = r₂ ∧ v₁ = v₂ := by simp [qqNRel]

@[simp] lemma qqAnd_inj (p₁ q₁ p₂ q₂ : V) :
    p₁ ^⋏ q₁ = p₂ ^⋏ q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ := by simp [qqAnd]

@[simp] lemma qqOr_inj (p₁ q₁ p₂ q₂ : V) :
    p₁ ^⋎ q₁ = p₂ ^⋎ q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ := by simp [qqOr]

@[simp] lemma qqAll_inj (p₁ p₂ : V) : ^∀ p₁ = ^∀ p₂ ↔ p₁ = p₂ := by simp [qqAll]

@[simp] lemma qqExs_inj (p₁ p₂ : V) : ^∃ p₁ = ^∃ p₂ ↔ p₁ = p₂ := by simp [qqExs]

@[simp] lemma arity_lt_rel (k r v : V) : k < ^rel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left k ⟪r, v⟫) <| le_pair_right _ _

@[simp] lemma r_lt_rel (k r v : V) : r < ^rel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <|
    le_pair_right _ _

@[simp] lemma v_lt_rel (k r v : V) : v < ^rel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <|
    le_pair_right _ _

@[simp] lemma arity_lt_nrel (k r v : V) : k < ^nrel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left _ _) <| le_pair_right _ _

@[simp] lemma r_lt_nrel (k r v : V) : r < ^nrel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <|
    le_pair_right _ _

@[simp] lemma v_lt_nrel (k r v : V) : v < ^nrel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <|
    le_pair_right _ _

lemma nth_lt_qqRel_of_lt {i k r v : V} (hi : i < len v) : v.[i] < ^rel k r v :=
  lt_trans (nth_lt_self hi) (v_lt_rel _ _ _)

lemma nth_lt_qqNRel_of_lt {i k r v : V} (hi : i < len v) : v.[i] < ^nrel k r v :=
  lt_trans (nth_lt_self hi) (v_lt_nrel _ _ _)

@[simp] lemma lt_K!_left (p q : V) : p < p ^⋏ q :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left _ _) <| le_pair_right _ _

@[simp] lemma lt_K!_right (p q : V) : q < p ^⋏ q :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma lt_or_left (p q : V) : p < p ^⋎ q :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left _ _) <| le_pair_right _ _

@[simp] lemma lt_or_right (p q : V) : q < p ^⋎ q :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma lt_forall (p : V) : p < ^∀ p := le_iff_lt_succ.mp <| le_pair_right _ _

@[simp] lemma lt_exists (p : V) : p < ^∃ p := le_iff_lt_succ.mp <| le_pair_right _ _

private lemma pair_le_square (a b : V) : ⟪a, b⟫ ≤ (a + b + 1) * (a + b + 1) := by
  simpa [sq] using pair_polybound a b

instance qqRel_bounded : Bounded₃ (qqRel : V → V → V → V) := by
  obtain ⟨t, ht⟩ := (qqFunc_bounded (V := V)).bounded
  refine ⟨t, fun w ↦ le_trans ?_ (ht w)⟩
  unfold qqRel qqFunc
  gcongr
  exact pair_le_pair_left (by simp) _

instance qqNRel_bounded : Bounded₃ (qqNRel : V → V → V → V) := by
  obtain ⟨t, ht⟩ := (qqFunc_bounded (V := V)).bounded
  refine ⟨t, fun w ↦ le_trans ?_ (ht w)⟩
  unfold qqNRel qqFunc
  gcongr
  exact pair_le_pair_left (by simp) _

instance qqAnd_bounded : Bounded₂ (qqAnd : V → V → V) :=
  ⟨‘p q. (4 + (p + q + 1) * (p + q + 1) + 1) * (4 + (p + q + 1) * (p + q + 1) + 1) + 1’,
    fun w ↦ by
      have h := le_trans (pair_le_pair_right 4 (pair_le_square (w 0) (w 1)))
        (pair_le_square 4 _)
      simpa [qqAnd, numeral_eq_natCast] using add_le_add_right h 1⟩

instance qqOr_bounded : Bounded₂ (qqOr : V → V → V) :=
  ⟨‘p q. (5 + (p + q + 1) * (p + q + 1) + 1) * (5 + (p + q + 1) * (p + q + 1) + 1) + 1’,
    fun w ↦ by
      have h := le_trans (pair_le_pair_right 5 (pair_le_square (w 0) (w 1)))
        (pair_le_square 5 _)
      simpa [qqOr, numeral_eq_natCast] using add_le_add_right h 1⟩

instance qqAll_bounded : Bounded₁ (qqAll : V → V) :=
  ⟨‘p. (6 + p + 1) * (6 + p + 1) + 1’, fun w ↦ by
    simpa [qqAll, numeral_eq_natCast] using add_le_add_right (pair_le_square 6 (w 0)) 1⟩

instance qqExs_bounded : Bounded₁ (qqExs : V → V) :=
  ⟨‘p. (7 + p + 1) * (7 + p + 1) + 1’, fun w ↦ by
    simpa [qqExs, numeral_eq_natCast] using add_le_add_right (pair_le_square 7 (w 0)) 1⟩

lemma qqRel_locallyDelta0 :
    LocallyDelta0Function (k := 3) fun w : Fin 3 → V ↦ qqRel (w 0) (w 1) (w 2) :=
  LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, qqRel_definable⟩

lemma qqNRel_locallyDelta0 :
    LocallyDelta0Function (k := 3) fun w : Fin 3 → V ↦ qqNRel (w 0) (w 1) (w 2) :=
  LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, qqNRel_definable⟩

lemma qqAnd_locallyDelta0 : LocallyDelta0Function₂ (qqAnd : V → V → V) :=
  LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, qqAnd_definable⟩

lemma qqOr_locallyDelta0 : LocallyDelta0Function₂ (qqOr : V → V → V) :=
  LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, qqOr_definable⟩

lemma qqAll_locallyDelta0 : LocallyDelta0Function₁ (qqAll : V → V) :=
  LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, qqAll_definable⟩

lemma qqExs_locallyDelta0 : LocallyDelta0Function₁ (qqExs : V → V) :=
  LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, qqExs_definable⟩

namespace FormalizedFormula

variable (L)

/-- The operator generating the codes of formulas. -/
def Phi (C : Set V) (p : V) : Prop :=
  (∃ k R v, L.IsRel k R ∧ IsUTermVec L k v ∧ p = ^rel k R v) ∨
  (∃ k R v, L.IsRel k R ∧ IsUTermVec L k v ∧ p = ^nrel k R v) ∨
  (p = ^⊤) ∨
  (p = ^⊥) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
  (∃ p₁, p₁ ∈ C ∧ p = ^∀ p₁) ∨
  (∃ p₁, p₁ ∈ C ∧ p = ^∃ p₁)

private lemma phi_iff (C p : V) :
    Phi L {x | x ∈ C} p ↔
    (∃ k < p, ∃ r < p, ∃ v < p, L.IsRel k r ∧ IsUTermVec L k v ∧ p = ^rel k r v) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, L.IsRel k r ∧ IsUTermVec L k v ∧ p = ^nrel k r v) ∨
    (p = ^⊤) ∨
    (p = ^⊥) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ p = ^∀ p₁) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ p = ^∃ p₁) where
  mp := by
    rintro (⟨k, r, v, hkr, hv, rfl⟩ | ⟨k, r, v, hkr, hv, rfl⟩ | rfl | rfl |
      ⟨q, r, hp, hq, rfl⟩ | ⟨q, r, hp, hq, rfl⟩ | ⟨q, h, rfl⟩ | ⟨q, h, rfl⟩)
    · disj 1; exact ⟨k, by simp, r, by simp, v, by simp, hkr, hv, rfl⟩
    · disj 2; exact ⟨k, by simp, r, by simp, v, by simp, hkr, hv, rfl⟩
    · disj 3; rfl
    · disj 4; rfl
    · disj 5; exact ⟨q, by simp, r, by simp, hp, hq, rfl⟩
    · disj 6; exact ⟨q, by simp, r, by simp, hp, hq, rfl⟩
    · disj 7; exact ⟨q, by simp, h, rfl⟩
    · disj 8; exact ⟨q, by simp, h, rfl⟩
  mpr := by
    unfold Phi
    rintro (⟨k, _, r, _, v, _, hkr, hv, rfl⟩ | ⟨k, _, r, _, v, _, hkr, hv, rfl⟩ | rfl | rfl |
      ⟨q, _, r, _, hq, hr, rfl⟩ | ⟨q, _, r, _, hq, hr, rfl⟩ | ⟨q, _, hq, rfl⟩ | ⟨q, _, hq, rfl⟩)
    · disj 1; exact ⟨k, r, v, hkr, hv, rfl⟩
    · disj 2; exact ⟨k, r, v, hkr, hv, rfl⟩
    · disj 3; rfl
    · disj 4; rfl
    · disj 5; exact ⟨q, r, hq, hr, rfl⟩
    · disj 6; exact ⟨q, r, hq, hr, rfl⟩
    · disj 7; exact ⟨q, hq, rfl⟩
    · disj 8; exact ⟨q, hq, rfl⟩

lemma phi_locallyDelta0 :
    LocallyDelta0 fun w : Fin 2 → V ↦ Phi L {x | x ∈ w 1} (w 0) := by
  have hisRel : LocallyDelta0 fun y : Fin 5 → V ↦ L.IsRel (y 2) (y 1) :=
    (LocallyDelta0.of_definable (R := fun w : Fin 2 → V ↦ L.IsRel (w 0) (w 1))
      (by definability)).comp₂ (LocallyDelta0Function.var 2) (LocallyDelta0Function.var 1)
  have hvec : LocallyDelta0 fun y : Fin 5 → V ↦ IsUTermVec L (y 2) (y 0) :=
    isUTermVec_locallyDelta0.rel_comp₂ (LocallyDelta0Function.var 2) (LocallyDelta0Function.var 0)
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
  have hmem (i j : Fin 4) : LocallyDelta0 fun y : Fin 4 → V ↦ y i ∈ y j :=
    LocallyDelta0.mem (LocallyDelta0Function.var i) (LocallyDelta0Function.var j)
  have hand : LocallyDelta0 fun y : Fin 4 → V ↦ y 2 = qqAnd (y 1) (y 0) :=
    LocallyDelta0.eq (LocallyDelta0Function.var 2) <|
      qqAnd_locallyDelta0.comp₂ (LocallyDelta0Function.var 1) (LocallyDelta0Function.var 0)
  have hor : LocallyDelta0 fun y : Fin 4 → V ↦ y 2 = qqOr (y 1) (y 0) :=
    LocallyDelta0.eq (LocallyDelta0Function.var 2) <|
      qqOr_locallyDelta0.comp₂ (LocallyDelta0Function.var 1) (LocallyDelta0Function.var 0)
  have hmem' (i j : Fin 3) : LocallyDelta0 fun y : Fin 3 → V ↦ y i ∈ y j :=
    LocallyDelta0.mem (LocallyDelta0Function.var i) (LocallyDelta0Function.var j)
  have hall : LocallyDelta0 fun y : Fin 3 → V ↦ y 1 = qqAll (y 0) :=
    LocallyDelta0.eq (LocallyDelta0Function.var 1) <|
      qqAll_locallyDelta0.comp₁ (LocallyDelta0Function.var 0)
  have hexs : LocallyDelta0 fun y : Fin 3 → V ↦ y 1 = qqExs (y 0) :=
    LocallyDelta0.eq (LocallyDelta0Function.var 1) <|
      qqExs_locallyDelta0.comp₁ (LocallyDelta0Function.var 0)
  have hex₁ := LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var (0 : Fin 2)) <|
    LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 1) <|
      LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 2) <|
        hisRel.and <| hvec.and hrel
  have hex₂ := LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var (0 : Fin 2)) <|
    LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 1) <|
      LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 2) <|
        hisRel.and <| hvec.and hnrel
  have hex₃ := LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var (0 : Fin 2)) <|
    LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 1) <|
      (hmem 1 3).and <| (hmem 0 3).and hand
  have hex₄ := LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var (0 : Fin 2)) <|
    LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 1) <|
      (hmem 1 3).and <| (hmem 0 3).and hor
  have hex₅ := LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var (0 : Fin 2)) <|
    (hmem' 0 2).and hall
  have hex₆ := LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var (0 : Fin 2)) <|
    (hmem' 0 2).and hexs
  exact (hex₁.or <| hex₂.or <| hverum.or <| hfalsum.or <| hex₃.or <| hex₄.or <| hex₅.or hex₆).of_iff
    fun w ↦ by simpa using phi_iff L (w 1) (w 0)

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.FormalizedFormula (blueprint formulaAux) in
/-- The construction of the codes of formulas. -/
def construction : Fixpoint.Construction V (blueprint L) where
  Φ := fun _ ↦ Phi L
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint]
    · intro v
      symm
      simpa [blueprint, formulaAux] using phi_iff L _ _
  monotone := by
    unfold Phi
    rintro C C' hC _ x (h | h | h | h | ⟨q, r, hqC, hrC, rfl⟩ | ⟨q, r, hqC, hrC, rfl⟩ |
      ⟨q, hqC, rfl⟩ | ⟨q, hqC, rfl⟩)
    · disj 1; exact h
    · disj 2; exact h
    · disj 3; exact h
    · disj 4; exact h
    · disj 5; exact ⟨q, r, hC hqC, hC hrC, rfl⟩
    · disj 6; exact ⟨q, r, hC hqC, hC hrC, rfl⟩
    · disj 7; exact ⟨q, hC hqC, rfl⟩
    · disj 8; exact ⟨q, hC hqC, rfl⟩
  Φ_locallyDelta0 := phi_locallyDelta0 L

instance : (construction L).StrongFinite V where
  strong_finite := by
    unfold construction Phi
    rintro C _ x (h | h | h | h | ⟨q, r, hqC, hrC, rfl⟩ | ⟨q, r, hqC, hrC, rfl⟩ |
      ⟨q, hqC, rfl⟩ | ⟨q, hqC, rfl⟩)
    · disj 1; exact h
    · disj 2; exact h
    · disj 3; exact h
    · disj 4; exact h
    · disj 5; exact ⟨q, r, by simp [hqC], by simp [hrC], rfl⟩
    · disj 6; exact ⟨q, r, by simp [hqC], by simp [hrC], rfl⟩
    · disj 7; exact ⟨q, by simp [hqC], rfl⟩
    · disj 8; exact ⟨q, by simp [hqC], rfl⟩

end FormalizedFormula

open FormalizedFormula

variable (L)

/-- The predicate that `p` is the code of a formula in the language `L`, possibly with dangling
bound variables. -/
def IsUFormula : V → Prop := (construction L).Fixpoint ![]

variable {L}

namespace IsUFormula

instance defined : 𝚫ᴬ₁-Predicate (IsUFormula L (V := V)) via (isUFormula L) :=
  (construction L).fixpoint_definedΔ₁

instance definable : 𝚫ᴬ₁-Predicate (IsUFormula L (V := V)) := defined.to_definable

instance definable' (Γ) {m : ℕ} : Γᴬ_[m + 1]-Predicate (IsUFormula L (V := V)) :=
  definable.of_deltaOne

end IsUFormula

lemma isUFormula_locallyDelta0 : LocallyDelta0Pred (IsUFormula L (V := V)) :=
  (construction L).fixpoint_locallyDelta0.of_iff fun w ↦
    iff_of_eq <| congrArg (fun u ↦ (construction L).Fixpoint u (w 0)) (Subsingleton.elim _ _)

namespace IsUFormula

lemma case_iff {p : V} :
    IsUFormula L p ↔
    (∃ k R v, L.IsRel k R ∧ IsUTermVec L k v ∧ p = ^rel k R v) ∨
    (∃ k R v, L.IsRel k R ∧ IsUTermVec L k v ∧ p = ^nrel k R v) ∨
    (p = ^⊤) ∨
    (p = ^⊥) ∨
    (∃ p₁ p₂, IsUFormula L p₁ ∧ IsUFormula L p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, IsUFormula L p₁ ∧ IsUFormula L p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (∃ p₁, IsUFormula L p₁ ∧ p = ^∀ p₁) ∨
    (∃ p₁, IsUFormula L p₁ ∧ p = ^∃ p₁) :=
  (construction L).case

alias ⟨case, mk⟩ := case_iff

set_option linter.flexible false in
@[simp] lemma rel {k r v : V} :
    IsUFormula L (^rel k r v) ↔ L.IsRel k r ∧ IsUTermVec L k v :=
  ⟨by intro h
      rcases h.case with (⟨k, r, v, hkr, hv, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨hkr, hv⟩,
   by rintro ⟨hkr, hv⟩
      exact mk <| by disj 1; exact ⟨k, r, v, hkr, hv, rfl⟩⟩

set_option linter.flexible false in
@[simp] lemma nrel {k r v : V} :
    IsUFormula L (^nrel k r v) ↔ L.IsRel k r ∧ IsUTermVec L k v :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨k, r, v, hkr, hv, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨hkr, hv⟩,
   by rintro ⟨hkr, hv⟩
      exact mk <| by disj 2; exact ⟨k, r, v, hkr, hv, rfl⟩⟩

@[simp] lemma verum : IsUFormula L (^⊤ : V) :=
  mk <| by disj 3; rfl

@[simp] lemma falsum : IsUFormula L (^⊥ : V) :=
  mk <| by disj 4; rfl

set_option linter.flexible false in
@[simp] lemma and {p q : V} :
    IsUFormula L (p ^⋏ q) ↔ IsUFormula L p ∧ IsUFormula L q :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, hp, hq, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨hp, hq⟩,
   by rintro ⟨hp, hq⟩
      exact mk <| by disj 5; exact ⟨p, q, hp, hq, rfl⟩⟩

set_option linter.flexible false in
@[simp] lemma or {p q : V} :
    IsUFormula L (p ^⋎ q) ↔ IsUFormula L p ∧ IsUFormula L q :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, hp, hq, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨hp, hq⟩,
   by rintro ⟨hp, hq⟩
      exact mk <| by disj 6; exact ⟨p, q, hp, hq, rfl⟩⟩

set_option linter.flexible false in
@[simp] lemma all {p : V} : IsUFormula L (^∀ p) ↔ IsUFormula L p :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, hp, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩
        exact hp,
   by intro hp
      exact mk <| by disj 7; exact ⟨p, hp, rfl⟩⟩

set_option linter.flexible false in
@[simp] lemma ex {p : V} : IsUFormula L (^∃ p) ↔ IsUFormula L p :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, hp, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩
        exact hp,
   by intro hp
      exact mk <| by disj 8; exact ⟨p, hp, rfl⟩⟩

lemma pos {p : V} (h : IsUFormula L p) : 0 < p := by
  rcases h.case with (⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩) <;>
    simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

@[simp] lemma not_zero : ¬IsUFormula L (0 : V) := by
  intro h
  simpa using h.pos

lemma induction {P : V → Prop} (hP : LocallyDelta0Pred P)
    (hrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^nrel k r v))
    (hverum : P ^⊤)
    (hfalsum : P ^⊥)
    (hand : ∀ p q, IsUFormula L p → IsUFormula L q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsUFormula L p → IsUFormula L q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsUFormula L p → P p → P (^∀ p))
    (hexs : ∀ p, IsUFormula L p → P p → P (^∃ p)) :
    ∀ p, IsUFormula L p → P p :=
  (construction L).induction (v := ![]) hP (by
    rintro C hC x (⟨k, r, v, hkr, hv, rfl⟩ | ⟨k, r, v, hkr, hv, rfl⟩ | rfl | rfl |
      ⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact hrel k r v hkr hv
    · exact hnrel k r v hkr hv
    · exact hverum
    · exact hfalsum
    · exact hand p q (hC p hp).1 (hC q hq).1 (hC p hp).2 (hC q hq).2
    · exact hor p q (hC p hp).1 (hC q hq).1 (hC p hp).2 (hC q hq).2
    · exact hall p (hC p hp).1 (hC p hp).2
    · exact hexs p (hC p hp).1 (hC p hp).2)

end IsUFormula

end formula

section rangeList

lemma rangeList_exists (n : V) : ∃ w, len w = n ∧ ∀ i < n, w.[i] = i :=
  sigmaZero_skolem_vec (R := fun i y ↦ y = i) (B := n)
    (LocallyDelta0.eq (LocallyDelta0Function.var 1) (LocallyDelta0Function.var 0))
    fun i hi ↦ ⟨i, hi, rfl⟩

/-- The list `[0, 1, …, n - 1]`. -/
noncomputable def rangeList (n : V) : V := Classical.choose (rangeList_exists n)

@[simp] lemma len_rangeList (n : V) : len (rangeList n) = n :=
  (Classical.choose_spec (rangeList_exists n)).1

@[simp] lemma nth_rangeList {n i : V} (hi : i < n) : (rangeList n).[i] = i :=
  (Classical.choose_spec (rangeList_exists n)).2 i hi

lemma rangeList_eq_iff {n w : V} : w = rangeList n ↔ len w = n ∧ ∀ i < n, w.[i] = i := by
  constructor
  · rintro rfl; exact ⟨len_rangeList n, fun i hi ↦ nth_rangeList hi⟩
  · rintro ⟨hl, hw⟩
    apply nth_ext (by simp [hl])
    intro i hi
    rw [hw i (by simpa [hl] using hi), nth_rangeList (by simpa [hl] using hi)]

lemma rangeList_locallyDelta0 : LocallyDelta0Function₁ (rangeList : V → V) where
  graph := by
    have hentry : LocallyDelta0 fun u : Fin 3 → V ↦ u 0 < u 2 → (u 1).[u 0] = u 0 :=
      (LocallyDelta0.lt (LocallyDelta0Function.var 0) (LocallyDelta0Function.var 2)).imp
        (LocallyDelta0.eq (nth_locallyDelta0.comp₂ (LocallyDelta0Function.var 1)
          (LocallyDelta0Function.var 0)) (LocallyDelta0Function.var 0))
    have hall := LocallyDelta0.ball_le_function (LocallyDelta0Function.var (V := V) (1 : Fin 2))
      hentry
    exact ((LocallyDelta0.eq (len_locallyDelta0.comp₁ (LocallyDelta0Function.var 0))
      (LocallyDelta0Function.var 1)).and hall).of_iff fun w ↦ by
        rw [rangeList_eq_iff]
        simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
        apply and_congr Iff.rfl
        constructor
        · intro h i _ hi; exact h i hi
        · intro h i hi; exact h i hi.le hi
  bounded X := by
    use Exp.exp (Exp.exp (X + X + X + 3))
    intro w hw
    have := le_exp_exp_of_nth_le (B := w 0) (rangeList (w 0)) fun i hi ↦ by
      rw [len_rangeList] at hi
      rw [nth_rangeList hi]; exact hi.le
    refine le_trans (by simpa using this) ?_
    apply exp_monotone_le.mpr
    apply exp_monotone_le.mpr
    gcongr <;> exact hw 0

end rangeList

namespace UformulaRec1

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.UformulaRec1 (Blueprint)

variable (V)

/-- A recursion on formulas in a model of $\mathsf{EA}$. Under a quantifier the parameter
changes by `change`, whose iterates are `iter`, and the values are bounded by `bound`. -/
structure Construction (φ : Blueprint) where
  rel (param k R v : V) : V
  nrel (param k R v : V) : V
  verum (param : V) : V
  falsum (param : V) : V
  and (param p₁ p₂ y₁ y₂ : V) : V
  or (param p₁ p₂ y₁ y₂ : V) : V
  all (param p₁ ys : V) : V
  exs (param p₁ ys : V) : V
  allChanges (param i : V) : V := param
  exsChanges (param i : V) : V := param
  allSize (param p₁ : V) : V := 1
  exsSize (param p₁ : V) : V := 1
  rel_defined : 𝚺ᴬ₁-Function₄ rel via φ.rel
  nrel_defined : 𝚺ᴬ₁-Function₄ nrel via φ.nrel
  verum_defined : 𝚺ᴬ₁-Function₁ verum via φ.verum
  falsum_defined : 𝚺ᴬ₁-Function₁ falsum via φ.falsum
  and_defined : 𝚺ᴬ₁-Function₅ and via φ.and
  or_defined : 𝚺ᴬ₁-Function₅ or via φ.or
  all_defined : 𝚺ᴬ₁-Function₃ all via φ.all
  exs_defined : 𝚺ᴬ₁-Function₃ exs via φ.exs
  allChanges_defined : 𝚺ᴬ₁-Function₂ allChanges via φ.allChanges := by
    exact FFL.FirstOrder.Arithmetic.Bootstrapping.UformulaRec1.param_defined
  exChanges_defined : 𝚺ᴬ₁-Function₂ exsChanges via φ.exsChanges := by
    exact FFL.FirstOrder.Arithmetic.Bootstrapping.UformulaRec1.param_defined
  allSize_defined : 𝚺ᴬ₁-Function₂ allSize via φ.allSize := by
    exact FFL.FirstOrder.Arithmetic.Bootstrapping.UformulaRec1.one_defined
  exsSize_defined : 𝚺ᴬ₁-Function₂ exsSize via φ.exsSize := by
    exact FFL.FirstOrder.Arithmetic.Bootstrapping.UformulaRec1.one_defined
  allChanges_monotone {param i j : V} : i ≤ j → allChanges param i ≤ allChanges param j := by
    intros; exact le_rfl
  exsChanges_monotone {param i j : V} : i ≤ j → exsChanges param i ≤ exsChanges param j := by
    intros; exact le_rfl
  allSize_eq_one : ∀ param p₁, allSize param p₁ = 1 := by intros; rfl
  exsSize_eq_one : ∀ param p₁, exsSize param p₁ = 1 := by intros; rfl
  /-- The change of the parameter under a quantifier. -/
  change (param : V) : V := param
  allChanges_eq_change : ∀ param i, allChanges param i = change param := by intros; rfl
  exsChanges_eq_change : ∀ param i, exsChanges param i = change param := by intros; rfl
  /-- `iter param d` is the `d`-th iterate of `change` at `param`. -/
  iter (param d : V) : V := param
  iter_zero : ∀ param, iter param 0 = param := by intros; rfl
  iter_succ : ∀ param d, iter param (d + 1) = change (iter param d) := by intros; rfl
  iter_monotone : ∀ param {d e}, d ≤ e → iter param d ≤ iter param e := by intros; exact le_rfl
  iter_locallyDelta0 : LocallyDelta0Function fun w : Fin 2 → V ↦ iter (w 0) (w 1) := by
    exact LocallyDelta0Function.var 0
  rel_locallyDelta0 :
    LocallyDelta0Function fun w : Fin 4 → V ↦ rel (w 0) (w 1) (w 2) (w 3)
  nrel_locallyDelta0 :
    LocallyDelta0Function fun w : Fin 4 → V ↦ nrel (w 0) (w 1) (w 2) (w 3)
  verum_locallyDelta0 : LocallyDelta0Function fun w : Fin 1 → V ↦ verum (w 0)
  falsum_locallyDelta0 : LocallyDelta0Function fun w : Fin 1 → V ↦ falsum (w 0)
  and_locallyDelta0 :
    LocallyDelta0Function fun w : Fin 5 → V ↦ and (w 0) (w 1) (w 2) (w 3) (w 4)
  or_locallyDelta0 :
    LocallyDelta0Function fun w : Fin 5 → V ↦ or (w 0) (w 1) (w 2) (w 3) (w 4)
  all_locallyDelta0 : LocallyDelta0Function fun w : Fin 3 → V ↦ all (w 0) (w 1) (w 2)
  exs_locallyDelta0 : LocallyDelta0Function fun w : Fin 3 → V ↦ exs (w 0) (w 1) (w 2)
  /-- `bound param p` bounds the value at the formula `p`. -/
  bound (param p : V) : V
  rel_le_bound : ∀ param k R v, rel param k R v ≤ bound param (^rel k R v)
  nrel_le_bound : ∀ param k R v, nrel param k R v ≤ bound param (^nrel k R v)
  verum_le_bound : ∀ param, verum param ≤ bound param ^⊤
  falsum_le_bound : ∀ param, falsum param ≤ bound param ^⊥
  and_le_bound : ∀ param p₁ p₂ y₁ y₂, y₁ ≤ bound param p₁ → y₂ ≤ bound param p₂ →
    and param p₁ p₂ y₁ y₂ ≤ bound param (p₁ ^⋏ p₂)
  or_le_bound : ∀ param p₁ p₂ y₁ y₂, y₁ ≤ bound param p₁ → y₂ ≤ bound param p₂ →
    or param p₁ p₂ y₁ y₂ ≤ bound param (p₁ ^⋎ p₂)
  all_le_bound : ∀ param p₁ y, y ≤ bound (change param) p₁ →
    all param p₁ ?[y] ≤ bound param (^∀ p₁)
  exs_le_bound : ∀ param p₁ y, y ≤ bound (change param) p₁ →
    exs param p₁ ?[y] ≤ bound param (^∃ p₁)
  bound_monotone : ∀ param {p q}, p ≤ q → bound param p ≤ bound param q
  bound_locallyDelta0 : LocallyDelta0Function fun w : Fin 2 → V ↦ bound (w 0) (w 1)

variable {V}

namespace Construction

variable (L) {β : Blueprint} (c : Construction V β)

/-- The rules generating the graph `⟪param, p, y⟫` of the recursion. -/
def Phi (C : Set V) (pr : V) : Prop :=
  ∃ param p y, pr = ⟪param, p, y⟫ ∧
  IsUFormula L p ∧ (
  (∃ k r v, p = ^rel k r v ∧ y = c.rel param k r v) ∨
  (∃ k r v, p = ^nrel k r v ∧ y = c.nrel param k r v) ∨
  (p = ^⊤ ∧ y = c.verum param) ∨
  (p = ^⊥ ∧ y = c.falsum param) ∨
  (∃ p₁ p₂ y₁ y₂, ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋏ p₂ ∧
    y = c.and param p₁ p₂ y₁ y₂) ∨
  (∃ p₁ p₂ y₁ y₂, ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋎ p₂ ∧
    y = c.or param p₁ p₂ y₁ y₂) ∨
  (∃ p₁ ys : V, (len ys = c.allSize param p₁ ∧
      ∀ i < c.allSize param p₁, ⟪c.allChanges param i, p₁, ys.[i]⟫ ∈ C) ∧
    p = ^∀ p₁ ∧ y = c.all param p₁ ys) ∨
  (∃ p₁ ys : V, (len ys = c.exsSize param p₁ ∧
      ∀ i < c.exsSize param p₁, ⟪c.exsChanges param i, p₁, ys.[i]⟫ ∈ C) ∧
    p = ^∃ p₁ ∧ y = c.exs param p₁ ys) )


private lemma phi_iff (C pr : V) :
    c.Phi L {x | x ∈ C} pr ↔
    ∃ param ≤ pr, ∃ p ≤ pr, ∃ y ≤ pr, pr = ⟪param, p, y⟫ ∧ IsUFormula L p ∧
    ((∃ k < p, ∃ R < p, ∃ v < p, p = ^rel k R v ∧ y = c.rel param k R v) ∨
    (∃ k < p, ∃ R < p, ∃ v < p, p = ^nrel k R v ∧ y = c.nrel param k R v) ∨
    (p = ^⊤ ∧ y = c.verum param) ∨
    (p = ^⊥ ∧ y = c.falsum param) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋏ p₂ ∧ y = c.and param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋎ p₂ ∧ y = c.or param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ ys ≤ repeatVec C (c.allSize param p₁), (c.allSize param p₁ = len ys ∧
        ∀ i < c.allSize param p₁, ⟪c.allChanges param i, p₁, ys.[i]⟫ ∈ C) ∧
      p = ^∀ p₁ ∧ y = c.all param p₁ ys) ∨
    (∃ p₁ < p, ∃ ys ≤ repeatVec C (c.exsSize param p₁), (c.exsSize param p₁ = len ys ∧
        ∀ i < c.exsSize param p₁, ⟪c.exsChanges param i, p₁, ys.[i]⟫ ∈ C) ∧
      p = ^∃ p₁ ∧ y = c.exs param p₁ ys)) := by
  have hrv {g : V → V} {p₁ ys n : V} (hl : len ys = n) (hys : ∀ i < n, ⟪g i, p₁, ys.[i]⟫ ∈ C) :
      ys ≤ repeatVec C n := by
    subst hl
    exact len_repeatVec_of_nth_le fun i hi ↦ le_of_lt <|
      lt_of_le_of_lt ((le_pair_right _ _).trans (le_pair_right _ _)) (lt_of_mem (hys i hi))
  constructor
  · rintro ⟨param, p, y, rfl, hp, H⟩
    refine ⟨param, by simp,
      p, le_trans (le_pair_left p y) (le_pair_right _ _),
      y, le_trans (le_pair_right p y) (le_pair_right _ _), rfl, hp, ?_⟩
    rcases H with (⟨k, r, v, rfl, rfl⟩ | ⟨k, r, v, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ |
      ⟨p₁, ys, ⟨hl, hys⟩, rfl, rfl⟩ | ⟨p₁, ys, ⟨hl, hys⟩, rfl, rfl⟩)
    · disj 1; exact ⟨k, by simp, r, by simp, v, by simp, rfl, rfl⟩;
    · disj 2; exact ⟨k, by simp, r, by simp, v, by simp, rfl, rfl⟩;
    · disj 3; exact ⟨rfl, rfl⟩;
    · disj 4; exact ⟨rfl, rfl⟩;
    · disj 5; exact ⟨p₁, by simp, p₂, by simp,
        y₁, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₁), y₂, lt_of_le_of_lt (by simp)
          (lt_of_mem_rng h₂),
        h₁, h₂, rfl, rfl⟩;
    · disj 6; exact ⟨p₁, by simp, p₂, by simp,
        y₁, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₁), y₂, lt_of_le_of_lt (by simp)
          (lt_of_mem_rng h₂),
        h₁, h₂, rfl, rfl⟩;
    · disj 7; exact ⟨p₁, by simp, ys, hrv hl hys, ⟨hl.symm, hys⟩, rfl, rfl⟩;
    · disj 8; exact ⟨p₁, by simp, ys, hrv hl hys, ⟨hl.symm, hys⟩, rfl, rfl⟩;
  · rintro ⟨param, _, p, _, y, _, rfl, hp, H⟩
    refine ⟨param, p, y, rfl, hp, ?_⟩
    rcases H with (⟨k, _, r, _, v, _, rfl, rfl⟩ | ⟨k, _, r, _, v, _, rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨p₁, _, p₂, _, y₁, _, y₂, _, h₁, h₂, rfl, rfl⟩ |
      ⟨p₁, _, p₂, _, y₁, _, y₂, _, h₁, h₂, rfl, rfl⟩ |
      ⟨p₁, _, ys, _, ⟨hl, hys⟩, rfl, rfl⟩ | ⟨p₁, _, ys, _, ⟨hl, hys⟩, rfl, rfl⟩)
    · disj 1; exact ⟨k, r, v, rfl, rfl⟩;
    · disj 2; exact ⟨k, r, v, rfl, rfl⟩;
    · disj 3; exact ⟨rfl, rfl⟩;
    · disj 4; exact ⟨rfl, rfl⟩;
    · disj 5; exact ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩;
    · disj 6; exact ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩;
    · disj 7; exact ⟨p₁, ys, ⟨hl.symm, hys⟩, rfl, rfl⟩;
    · disj 8; exact ⟨p₁, ys, ⟨hl.symm, hys⟩, rfl, rfl⟩;


private lemma le_pair_pair_right (a b d : V) : d ≤ ⟪a, b, d⟫ :=
  le_trans (le_pair_right _ _) (le_pair_right _ _)

/-- The rules in a form that reads the formula off its code by projections. -/
private lemma phi_iff_decode (C pr : V) :
    c.Phi L {x | x ∈ C} pr ↔ IsUFormula L (π₁ (π₂ pr)) ∧
    ( (π₁ (π₁ (π₂ pr) - 1) = 0 ∧ π₂ (π₂ pr) = c.rel (π₁ pr) (π₁ (π₂ (π₁ (π₂ pr) - 1)))
        (π₁ (π₂ (π₂ (π₁ (π₂ pr) - 1)))) (π₂ (π₂ (π₂ (π₁ (π₂ pr) - 1))))) ∨
      (π₁ (π₁ (π₂ pr) - 1) = 1 ∧ π₂ (π₂ pr) = c.nrel (π₁ pr) (π₁ (π₂ (π₁ (π₂ pr) - 1)))
        (π₁ (π₂ (π₂ (π₁ (π₂ pr) - 1)))) (π₂ (π₂ (π₂ (π₁ (π₂ pr) - 1))))) ∨
      (π₁ (π₁ (π₂ pr) - 1) = 2 ∧ π₂ (π₂ pr) = c.verum (π₁ pr)) ∨
      (π₁ (π₁ (π₂ pr) - 1) = 3 ∧ π₂ (π₂ pr) = c.falsum (π₁ pr)) ∨
      (π₁ (π₁ (π₂ pr) - 1) = 4 ∧ ∃ y₁ < C, ∃ y₂ < C,
        ⟪π₁ pr, π₁ (π₂ (π₁ (π₂ pr) - 1)), y₁⟫ ∈ C ∧ ⟪π₁ pr, π₂ (π₂ (π₁ (π₂ pr) - 1)), y₂⟫ ∈ C ∧
        π₂ (π₂ pr) = c.and (π₁ pr) (π₁ (π₂ (π₁ (π₂ pr) - 1))) (π₂ (π₂ (π₁ (π₂ pr) - 1))) y₁ y₂) ∨
      (π₁ (π₁ (π₂ pr) - 1) = 5 ∧ ∃ y₁ < C, ∃ y₂ < C,
        ⟪π₁ pr, π₁ (π₂ (π₁ (π₂ pr) - 1)), y₁⟫ ∈ C ∧ ⟪π₁ pr, π₂ (π₂ (π₁ (π₂ pr) - 1)), y₂⟫ ∈ C ∧
        π₂ (π₂ pr) = c.or (π₁ pr) (π₁ (π₂ (π₁ (π₂ pr) - 1))) (π₂ (π₂ (π₁ (π₂ pr) - 1))) y₁ y₂) ∨
      (π₁ (π₁ (π₂ pr) - 1) = 6 ∧ ∃ y < C,
        ⟪c.change (π₁ pr), π₂ (π₁ (π₂ pr) - 1), y⟫ ∈ C ∧
        π₂ (π₂ pr) = c.all (π₁ pr) (π₂ (π₁ (π₂ pr) - 1)) ?[y]) ∨
      (π₁ (π₁ (π₂ pr) - 1) = 7 ∧ ∃ y < C,
        ⟪c.change (π₁ pr), π₂ (π₁ (π₂ pr) - 1), y⟫ ∈ C ∧
        π₂ (π₂ pr) = c.exs (π₁ pr) (π₂ (π₁ (π₂ pr) - 1)) ?[y]) ) := by
  have hone (ys : V) (hl : len ys = 1) : ys = ?[ys.[0]] := by
    obtain ⟨x, rfl⟩ := eq_singleton_iff_len_eq_one.mp hl
    simp
  constructor
  · rintro ⟨param, p, y, rfl, hp, H⟩
    refine ⟨by simpa using hp, ?_⟩
    rcases H with (⟨k, r, v, rfl, rfl⟩ | ⟨k, r, v, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ |
      ⟨p₁, ys, ⟨hl, hys⟩, rfl, rfl⟩ | ⟨p₁, ys, ⟨hl, hys⟩, rfl, rfl⟩)
    · disj 1; simp [qqRel]
    · disj 2; simp [qqNRel]
    · disj 3; simp [qqVerum]
    · disj 4; simp [qqFalsum]
    · disj 5
      simp only [pi₁_pair, pi₂_pair, qqAnd, add_tsub_cancel_right, true_and]
      exact ⟨y₁, lt_of_le_of_lt (le_pair_pair_right _ _ _) (lt_of_mem h₁), y₂,
        lt_of_le_of_lt (le_pair_pair_right _ _ _) (lt_of_mem h₂), h₁, h₂, rfl⟩
    · disj 6
      simp only [pi₁_pair, pi₂_pair, qqOr, add_tsub_cancel_right, true_and]
      exact ⟨y₁, lt_of_le_of_lt (le_pair_pair_right _ _ _) (lt_of_mem h₁), y₂,
        lt_of_le_of_lt (le_pair_pair_right _ _ _) (lt_of_mem h₂), h₁, h₂, rfl⟩
    · disj 7
      have hl : len ys = 1 := by rw [hl, c.allSize_eq_one]
      have h0 := hys 0 (by simp [c.allSize_eq_one])
      rw [c.allChanges_eq_change] at h0
      simp only [pi₁_pair, pi₂_pair, qqAll, add_tsub_cancel_right, true_and]
      exact ⟨ys.[0], lt_of_le_of_lt (le_pair_pair_right _ _ _) (lt_of_mem h0), h0,
        by rw [← hone ys hl]⟩
    · disj 8
      have hl : len ys = 1 := by rw [hl, c.exsSize_eq_one]
      have h0 := hys 0 (by simp [c.exsSize_eq_one])
      rw [c.exsChanges_eq_change] at h0
      simp only [pi₁_pair, pi₂_pair, qqExs, add_tsub_cancel_right, true_and]
      exact ⟨ys.[0], lt_of_le_of_lt (le_pair_pair_right _ _ _) (lt_of_mem h0), h0,
        by rw [← hone ys hl]⟩
  · rintro ⟨hp, H⟩
    have hpr : pr = ⟪π₁ pr, π₁ (π₂ pr), π₂ (π₂ pr)⟫ := by simp
    refine ⟨π₁ pr, π₁ (π₂ pr), π₂ (π₂ pr), hpr, hp, ?_⟩
    rcases IsUFormula.case hp with (⟨k, r, v, _, _, e⟩ | ⟨k, r, v, _, _, e⟩ | e | e |
      ⟨p₁, p₂, _, _, e⟩ | ⟨p₁, p₂, _, _, e⟩ | ⟨p₁, _, e⟩ | ⟨p₁, _, e⟩) <;> rw [e] at H ⊢
    · obtain h | h | h | h | h | h | h | h := H
      · exact Or.inl ⟨k, r, v, rfl, by simpa [qqRel] using h.2⟩
      all_goals exact absurd h.1 (by simp [qqRel])
    · obtain h | h | h | h | h | h | h | h := H
      · exact absurd h.1 (by simp [qqNRel])
      · exact Or.inr <| Or.inl ⟨k, r, v, rfl, by simpa [qqNRel] using h.2⟩
      all_goals exact absurd h.1 (by simp [qqNRel])
    · obtain h | h | h | h | h | h | h | h := H
      · exact absurd h.1 (by simp [qqVerum])
      · exact absurd h.1 (by simp [qqVerum])
      · exact Or.inr <| Or.inr <| Or.inl ⟨rfl, h.2⟩
      all_goals exact absurd h.1 (by simp [qqVerum])
    · obtain h | h | h | h | h | h | h | h := H
      · exact absurd h.1 (by simp [qqFalsum])
      · exact absurd h.1 (by simp [qqFalsum])
      · exact absurd h.1 (by simp [qqFalsum])
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, h.2⟩
      all_goals exact absurd h.1 (by simp [qqFalsum])
    · obtain h | h | h | h | h | h | h | h := H
      · exact absurd h.1 (by simp [qqAnd])
      · exact absurd h.1 (by simp [qqAnd])
      · exact absurd h.1 (by simp [qqAnd])
      · exact absurd h.1 (by simp [qqAnd])
      · obtain ⟨_, y₁, _, y₂, _, h₁, h₂, hy⟩ := h
        simp only [qqAnd, add_tsub_cancel_right, pi₁_pair, pi₂_pair] at h₁ h₂ hy
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, hy⟩
      all_goals exact absurd h.1 (by simp [qqAnd])
    · obtain h | h | h | h | h | h | h | h := H
      · exact absurd h.1 (by simp [qqOr])
      · exact absurd h.1 (by simp [qqOr])
      · exact absurd h.1 (by simp [qqOr])
      · exact absurd h.1 (by simp [qqOr])
      · exact absurd h.1 (by simp [qqOr])
      · obtain ⟨_, y₁, _, y₂, _, h₁, h₂, hy⟩ := h
        simp only [qqOr, add_tsub_cancel_right, pi₁_pair, pi₂_pair] at h₁ h₂ hy
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, hy⟩
      all_goals exact absurd h.1 (by simp [qqOr])
    · obtain h | h | h | h | h | h | h | h := H
      · exact absurd h.1 (by simp [qqAll])
      · exact absurd h.1 (by simp [qqAll])
      · exact absurd h.1 (by simp [qqAll])
      · exact absurd h.1 (by simp [qqAll])
      · exact absurd h.1 (by simp [qqAll])
      · exact absurd h.1 (by simp [qqAll])
      · obtain ⟨_, y, _, h₁, hy⟩ := h
        simp only [qqAll, add_tsub_cancel_right, pi₂_pair] at h₁ hy
        refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨p₁, ?[y], ⟨by simp [c.allSize_eq_one], fun i hi ↦ ?_⟩, rfl, hy⟩
        rw [c.allSize_eq_one] at hi
        rcases lt_one_iff_eq_zero.mp hi
        simpa [c.allChanges_eq_change] using h₁
      · exact absurd h.1 (by simp [qqAll])
    · obtain h | h | h | h | h | h | h | h := H
      · exact absurd h.1 (by simp [qqExs])
      · exact absurd h.1 (by simp [qqExs])
      · exact absurd h.1 (by simp [qqExs])
      · exact absurd h.1 (by simp [qqExs])
      · exact absurd h.1 (by simp [qqExs])
      · exact absurd h.1 (by simp [qqExs])
      · exact absurd h.1 (by simp [qqExs])
      · obtain ⟨_, y, _, h₁, hy⟩ := h
        simp only [qqExs, add_tsub_cancel_right, pi₂_pair] at h₁ hy
        refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
          ⟨p₁, ?[y], ⟨by simp [c.exsSize_eq_one], fun i hi ↦ ?_⟩, rfl, hy⟩
        rw [c.exsSize_eq_one] at hi
        rcases lt_one_iff_eq_zero.mp hi
        simpa [c.exsChanges_eq_change] using h₁

lemma change_eq_iter (param : V) : c.change param = c.iter param 1 := by
  simpa [c.iter_zero] using (c.iter_succ param 0).symm

lemma change_locallyDelta0 : LocallyDelta0Function fun w : Fin 1 → V ↦ c.change (w 0) := by
  have := c.iter_locallyDelta0.comp₂ (f := fun w : Fin 1 → V ↦ w 0) (f' := fun _ ↦ 1)
    (LocallyDelta0Function.var 0) (LocallyDelta0Function.const 1)
  simpa [c.change_eq_iter] using this

private lemma fun4 {n : ℕ} {g : V → V → V → V → V} {f₀ f₁ f₂ f₃ : (Fin n → V) → V}
    (hg : LocallyDelta0Function fun w : Fin 4 → V ↦ g (w 0) (w 1) (w 2) (w 3))
    (h₀ : LocallyDelta0Function f₀) (h₁ : LocallyDelta0Function f₁)
    (h₂ : LocallyDelta0Function f₂) (h₃ : LocallyDelta0Function f₃) :
    LocallyDelta0Function fun u ↦ g (f₀ u) (f₁ u) (f₂ u) (f₃ u) := by
  have := hg.comp (f := ![f₀, f₁, f₂, f₃]) <| Fin.forall_fin_succ.mpr ⟨h₀,
    Fin.forall_fin_succ.mpr ⟨h₁, Fin.forall_fin_succ.mpr ⟨h₂,
      Fin.forall_fin_succ.mpr ⟨h₃, finZeroElim⟩⟩⟩⟩
  simpa using this

private lemma fun5 {n : ℕ} {g : V → V → V → V → V → V} {f₀ f₁ f₂ f₃ f₄ : (Fin n → V) → V}
    (hg : LocallyDelta0Function fun w : Fin 5 → V ↦ g (w 0) (w 1) (w 2) (w 3) (w 4))
    (h₀ : LocallyDelta0Function f₀) (h₁ : LocallyDelta0Function f₁)
    (h₂ : LocallyDelta0Function f₂) (h₃ : LocallyDelta0Function f₃)
    (h₄ : LocallyDelta0Function f₄) :
    LocallyDelta0Function fun u ↦ g (f₀ u) (f₁ u) (f₂ u) (f₃ u) (f₄ u) := by
  have := hg.comp (f := ![f₀, f₁, f₂, f₃, f₄]) <| Fin.forall_fin_succ.mpr ⟨h₀,
    Fin.forall_fin_succ.mpr ⟨h₁, Fin.forall_fin_succ.mpr ⟨h₂,
      Fin.forall_fin_succ.mpr ⟨h₃, Fin.forall_fin_succ.mpr ⟨h₄, finZeroElim⟩⟩⟩⟩⟩
  simpa using this

lemma phi_locallyDelta0 :
    LocallyDelta0 fun w : Fin 2 → V ↦ c.Phi L {x | x ∈ w 1} (w 0) := by
  have p₁ {n : ℕ} {g : (Fin n → V) → V} (hg : LocallyDelta0Function g) :
      LocallyDelta0Function fun u ↦ π₁ (g u) := LocallyDelta0Function.pi₁.comp₁ hg
  have p₂ {n : ℕ} {g : (Fin n → V) → V} (hg : LocallyDelta0Function g) :
      LocallyDelta0Function fun u ↦ π₂ (g u) := LocallyDelta0Function.pi₂.comp₁ hg
  have hpred {n : ℕ} {g : (Fin n → V) → V} (hg : LocallyDelta0Function g) :
      LocallyDelta0Function fun u ↦ g u - 1 :=
    LocallyDelta0Function.sub.comp₂ hg (LocallyDelta0Function.const 1)
  -- components of the pair `pr = u j`
  have hparam {n : ℕ} (j : Fin n) := p₁ (LocallyDelta0Function.var (V := V) j)
  have hform {n : ℕ} (j : Fin n) := p₁ (p₂ (LocallyDelta0Function.var (V := V) j))
  have hval {n : ℕ} (j : Fin n) := p₂ (p₂ (LocallyDelta0Function.var (V := V) j))
  have hm {n : ℕ} (j : Fin n) := hpred (hform j)
  have htag {n : ℕ} (j : Fin n) := p₁ (hm j)
  have hb {n : ℕ} (j : Fin n) := p₂ (hm j)
  have htag_eq (t : V) : LocallyDelta0 fun w : Fin 2 → V ↦ π₁ (π₁ (π₂ (w 0)) - 1) = t :=
    LocallyDelta0.eq (htag 0) (LocallyDelta0Function.const t)
  have hrel : LocallyDelta0 fun w : Fin 2 → V ↦ π₂ (π₂ (w 0)) = c.rel (π₁ (w 0))
      (π₁ (π₂ (π₁ (π₂ (w 0)) - 1))) (π₁ (π₂ (π₂ (π₁ (π₂ (w 0)) - 1))))
        (π₂ (π₂ (π₂ (π₁ (π₂ (w 0)) - 1)))) :=
    LocallyDelta0.eq (hval 0) (fun4 c.rel_locallyDelta0 (hparam 0) (p₁ (hb 0)) (p₁ (p₂ (hb 0)))
      (p₂ (p₂ (hb 0))))
  have hnrel : LocallyDelta0 fun w : Fin 2 → V ↦ π₂ (π₂ (w 0)) = c.nrel (π₁ (w 0))
      (π₁ (π₂ (π₁ (π₂ (w 0)) - 1))) (π₁ (π₂ (π₂ (π₁ (π₂ (w 0)) - 1))))
        (π₂ (π₂ (π₂ (π₁ (π₂ (w 0)) - 1)))) :=
    LocallyDelta0.eq (hval 0) (fun4 c.nrel_locallyDelta0 (hparam 0) (p₁ (hb 0))
      (p₁ (p₂ (hb 0))) (p₂ (p₂ (hb 0))))
  have hverum : LocallyDelta0 fun w : Fin 2 → V ↦ π₂ (π₂ (w 0)) = c.verum (π₁ (w 0)) :=
    LocallyDelta0.eq (hval 0) (c.verum_locallyDelta0.comp₁ (f := fun w ↦ π₁ (w 0)) (hparam 0))
  have hfalsum : LocallyDelta0 fun w : Fin 2 → V ↦ π₂ (π₂ (w 0)) = c.falsum (π₁ (w 0)) :=
    LocallyDelta0.eq (hval 0) (c.falsum_locallyDelta0.comp₁ (f := fun w ↦ π₁ (w 0)) (hparam 0))
  have hbin (g : V → V → V → V → V → V)
      (hg : LocallyDelta0Function fun w : Fin 5 → V ↦ g (w 0) (w 1) (w 2) (w 3) (w 4)) :
      LocallyDelta0 fun w : Fin 2 → V ↦ ∃ y₁ < w 1, ∃ y₂ < w 1,
        ⟪π₁ (w 0), π₁ (π₂ (π₁ (π₂ (w 0)) - 1)), y₁⟫ ∈ w 1 ∧
        ⟪π₁ (w 0), π₂ (π₂ (π₁ (π₂ (w 0)) - 1)), y₂⟫ ∈ w 1 ∧
        π₂ (π₂ (w 0)) = g (π₁ (w 0)) (π₁ (π₂ (π₁ (π₂ (w 0)) - 1)))
          (π₂ (π₂ (π₁ (π₂ (w 0)) - 1))) y₁ y₂ := by
    have hpair₃ {n : ℕ} {f₀ f₁ f₂ : (Fin n → V) → V} (h₀ : LocallyDelta0Function f₀)
        (h₁ : LocallyDelta0Function f₁) (h₂ : LocallyDelta0Function f₂) :
        LocallyDelta0Function fun u ↦ ⟪f₀ u, f₁ u, f₂ u⟫ :=
      LocallyDelta0Function.pairing.comp₂ h₀ (LocallyDelta0Function.pairing.comp₂ h₁ h₂)
    have hbody : LocallyDelta0 fun u : Fin 4 → V ↦
        ⟪π₁ (u 2), π₁ (π₂ (π₁ (π₂ (u 2)) - 1)), u 1⟫ ∈ u 3 ∧
        ⟪π₁ (u 2), π₂ (π₂ (π₁ (π₂ (u 2)) - 1)), u 0⟫ ∈ u 3 ∧
        π₂ (π₂ (u 2)) = g (π₁ (u 2)) (π₁ (π₂ (π₁ (π₂ (u 2)) - 1)))
          (π₂ (π₂ (π₁ (π₂ (u 2)) - 1))) (u 1) (u 0) :=
      (LocallyDelta0.mem (hpair₃ (hparam 2) (p₁ (hb 2)) (LocallyDelta0Function.var 1))
        (LocallyDelta0Function.var 3)).and
        ((LocallyDelta0.mem (hpair₃ (hparam 2) (p₂ (hb 2)) (LocallyDelta0Function.var 0))
          (LocallyDelta0Function.var 3)).and
          (LocallyDelta0.eq (hval 2) (fun5 hg (hparam 2) (p₁ (hb 2)) (p₂ (hb 2))
            (LocallyDelta0Function.var 1) (LocallyDelta0Function.var 0))))
    exact (LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 1)
      (LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 2) hbody)).of_iff
        fun w ↦ by simp
  have hquant (g : V → V → V → V)
      (hg : LocallyDelta0Function fun w : Fin 3 → V ↦ g (w 0) (w 1) (w 2)) :
      LocallyDelta0 fun w : Fin 2 → V ↦ ∃ y < w 1,
        ⟪c.change (π₁ (w 0)), π₂ (π₁ (π₂ (w 0)) - 1), y⟫ ∈ w 1 ∧
        π₂ (π₂ (w 0)) = g (π₁ (w 0)) (π₂ (π₁ (π₂ (w 0)) - 1)) ?[y] := by
    have hbody : LocallyDelta0 fun u : Fin 3 → V ↦
        ⟪c.change (π₁ (u 1)), π₂ (π₁ (π₂ (u 1)) - 1), u 0⟫ ∈ u 2 ∧
        π₂ (π₂ (u 1)) = g (π₁ (u 1)) (π₂ (π₁ (π₂ (u 1)) - 1)) ?[u 0] :=
      (LocallyDelta0.mem (LocallyDelta0Function.pairing.comp₂
        (c.change_locallyDelta0.comp₁ (f := fun u ↦ π₁ (u 1)) (hparam 1))
        (LocallyDelta0Function.pairing.comp₂ (hb 1) (LocallyDelta0Function.var 0)))
        (LocallyDelta0Function.var 2)).and
        (LocallyDelta0.eq (hval 1) (LocallyDelta0Function.comp₃ hg (hparam 1) (hb 1)
          (LocallyDelta0Function.adjoin.comp₂ (LocallyDelta0Function.var 0)
            (LocallyDelta0Function.const 0))))
    exact (LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 1) hbody).of_iff
      fun w ↦ by simp
  have hformula : LocallyDelta0 fun w : Fin 2 → V ↦ IsUFormula L (π₁ (π₂ (w 0))) :=
    LocallyDelta0.pred_comp isUFormula_locallyDelta0 (hform 0)
  have := hformula.and <| ((htag_eq 0).and hrel).or <| ((htag_eq 1).and hnrel).or <|
    ((htag_eq 2).and hverum).or <| ((htag_eq 3).and hfalsum).or <|
    ((htag_eq 4).and (hbin c.and c.and_locallyDelta0)).or <|
    ((htag_eq 5).and (hbin c.or c.or_locallyDelta0)).or <|
    ((htag_eq 6).and (hquant c.all c.all_locallyDelta0)).or
    ((htag_eq 7).and (hquant c.exs c.exs_locallyDelta0))
  exact this.of_iff fun w ↦ by simpa using c.phi_iff_decode L (w 1) (w 0)


/-- The construction of the graph of the recursion. -/
def construction : Fixpoint.Construction V (β.blueprint L) where
  Φ := fun _ ↦ c.Phi L
  defined := .mk <| by
    constructor
    · intro v
      simp [_root_.FFL.FirstOrder.Arithmetic.Bootstrapping.UformulaRec1.Blueprint.blueprint,
        c.rel_defined.iff, c.rel_defined.graph_delta.proper.iff',
        c.nrel_defined.iff, c.nrel_defined.graph_delta.proper.iff',
        c.verum_defined.iff, c.verum_defined.graph_delta.proper.iff',
        c.falsum_defined.iff, c.falsum_defined.graph_delta.proper.iff',
        c.and_defined.iff, c.and_defined.graph_delta.proper.iff',
        c.or_defined.iff, c.or_defined.graph_delta.proper.iff',
        c.all_defined.iff, c.all_defined.graph_delta.proper.iff',
        c.exs_defined.iff, c.exs_defined.graph_delta.proper.iff',
        c.allSize_defined.iff, c.exsSize_defined.iff,
        c.allChanges_defined.iff,
        c.exChanges_defined.iff]
    · intro v
      symm
      simpa [_root_.FFL.FirstOrder.Arithmetic.Bootstrapping.UformulaRec1.Blueprint.blueprint,
        c.rel_defined.iff,
        c.nrel_defined.iff,
        c.verum_defined.iff,
        c.falsum_defined.iff,
        c.and_defined.iff,
        c.or_defined.iff,
        c.all_defined.iff,
        c.exs_defined.iff,
        c.allSize_defined.iff,
        c.exsSize_defined.iff,
        c.allChanges_defined.iff,
        c.exChanges_defined.iff] using c.phi_iff L _ _
  monotone := by
    unfold Phi
    rintro C C' hC _ _ ⟨param, p, y, rfl, hp, H⟩
    refine ⟨param, p, y, rfl, hp, ?_⟩
    rcases H with (h | h | h | h | ⟨p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩ |
      ⟨p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩ | ⟨p₁, ys, ⟨hl, hys⟩, rfl, rfl⟩ |
      ⟨p₁, ys, ⟨hl, hys⟩, rfl, rfl⟩)
    · disj 1; exact h
    · disj 2; exact h
    · disj 3; exact h
    · disj 4; exact h
    · disj 5; exact ⟨p₁, p₂, r₁, r₂, hC h₁, hC h₂, rfl, rfl⟩
    · disj 6; exact ⟨p₁, p₂, r₁, r₂, hC h₁, hC h₂, rfl, rfl⟩
    · disj 7; exact ⟨p₁, ys, ⟨hl, fun i hi ↦ hC (hys i hi)⟩, rfl, rfl⟩
    · disj 8; exact ⟨p₁, ys, ⟨hl, fun i hi ↦ hC (hys i hi)⟩, rfl, rfl⟩
  Φ_locallyDelta0 := c.phi_locallyDelta0 L

/-- `c.Graph L param p y` states that the recursion takes the value `y` at `p` with `param`. -/
def Graph (param : V) (x y : V) : Prop := (c.construction L).Fixpoint ![] ⟪param, x, y⟫

open Classical in
/-- The value at depth `d` of the code `n`, read off the table `T` of the lists of values of the
smaller codes; the parameter at depth `d` is `c.iter P d`. -/
noncomputable def depthValue (P n T d : V) : V :=
  if n = 0 then 0
  else if π₁ (n - 1) = 0 then c.rel (c.iter P d) (π₁ (π₂ (n - 1))) (π₁ (π₂ (π₂ (n - 1))))
    (π₂ (π₂ (π₂ (n - 1))))
  else if π₁ (n - 1) = 1 then c.nrel (c.iter P d) (π₁ (π₂ (n - 1))) (π₁ (π₂ (π₂ (n - 1))))
    (π₂ (π₂ (π₂ (n - 1))))
  else if π₁ (n - 1) = 2 then c.verum (c.iter P d)
  else if π₁ (n - 1) = 3 then c.falsum (c.iter P d)
  else if π₁ (n - 1) = 4 then c.and (c.iter P d) (π₁ (π₂ (n - 1))) (π₂ (π₂ (n - 1)))
    (znth T (π₁ (π₂ (n - 1)))).[d] (znth T (π₂ (π₂ (n - 1)))).[d]
  else if π₁ (n - 1) = 5 then c.or (c.iter P d) (π₁ (π₂ (n - 1))) (π₂ (π₂ (n - 1)))
    (znth T (π₁ (π₂ (n - 1)))).[d] (znth T (π₂ (π₂ (n - 1)))).[d]
  else if π₁ (n - 1) = 6 then c.all (c.iter P d) (π₂ (n - 1)) ?[(znth T (π₂ (n - 1))).[d + 1]]
  else if π₁ (n - 1) = 7 then c.exs (c.iter P d) (π₂ (n - 1)) ?[(znth T (π₂ (n - 1))).[d + 1]]
  else 0

lemma depthValue_locallyDelta0 :
    LocallyDelta0Function fun w : Fin 4 → V ↦ c.depthValue (w 0) (w 1) (w 2) (w 3) := by
  have p₁ {n : ℕ} {g : (Fin n → V) → V} (hg : LocallyDelta0Function g) :
      LocallyDelta0Function fun u ↦ π₁ (g u) := LocallyDelta0Function.pi₁.comp₁ hg
  have p₂ {n : ℕ} {g : (Fin n → V) → V} (hg : LocallyDelta0Function g) :
      LocallyDelta0Function fun u ↦ π₂ (g u) := LocallyDelta0Function.pi₂.comp₁ hg
  have hm : LocallyDelta0Function fun w : Fin 4 → V ↦ w 1 - 1 :=
    LocallyDelta0Function.sub.comp₂ (LocallyDelta0Function.var 1) (LocallyDelta0Function.const 1)
  have hb := p₂ hm
  have hpar : LocallyDelta0Function fun w : Fin 4 → V ↦ c.iter (w 0) (w 3) :=
    c.iter_locallyDelta0.comp₂ (LocallyDelta0Function.var 0) (LocallyDelta0Function.var 3)
  have htag (t : V) : LocallyDelta0 fun w : Fin 4 → V ↦ π₁ (w 1 - 1) = t :=
    LocallyDelta0.eq (p₁ hm) (LocallyDelta0Function.const t)
  have hlook {g : (Fin 4 → V) → V} (hg : LocallyDelta0Function g)
      {e : (Fin 4 → V) → V} (he : LocallyDelta0Function e) :
      LocallyDelta0Function fun w : Fin 4 → V ↦ (znth (w 2) (g w)).[e w] :=
    nth_locallyDelta0.comp₂ (LocallyDelta0Function.znth.comp₂ (LocallyDelta0Function.var 2) hg)
      he
  have hsingle {g : (Fin 4 → V) → V} (hg : LocallyDelta0Function g) :
      LocallyDelta0Function fun w : Fin 4 → V ↦ ?[g w] :=
    LocallyDelta0Function.adjoin.comp₂ hg (LocallyDelta0Function.const 0)
  have hrel := fun4 c.rel_locallyDelta0 hpar (p₁ hb) (p₁ (p₂ hb)) (p₂ (p₂ hb))
  have hnrel := fun4 c.nrel_locallyDelta0 hpar (p₁ hb) (p₁ (p₂ hb)) (p₂ (p₂ hb))
  have hverum := c.verum_locallyDelta0.comp₁ (f := fun w : Fin 4 → V ↦ c.iter (w 0) (w 3)) hpar
  have hfalsum := c.falsum_locallyDelta0.comp₁ (f := fun w : Fin 4 → V ↦ c.iter (w 0) (w 3)) hpar
  have hand := fun5 c.and_locallyDelta0 hpar (p₁ hb) (p₂ hb)
    (hlook (p₁ hb) (LocallyDelta0Function.var 3)) (hlook (p₂ hb) (LocallyDelta0Function.var 3))
  have hor := fun5 c.or_locallyDelta0 hpar (p₁ hb) (p₂ hb)
    (hlook (p₁ hb) (LocallyDelta0Function.var 3)) (hlook (p₂ hb) (LocallyDelta0Function.var 3))
  have hall := LocallyDelta0Function.comp₃ c.all_locallyDelta0 hpar hb
    (hsingle (hlook hb (LocallyDelta0Function.add_one (LocallyDelta0Function.var 3))))
  have hexs := LocallyDelta0Function.comp₃ c.exs_locallyDelta0 hpar hb
    (hsingle (hlook hb (LocallyDelta0Function.add_one (LocallyDelta0Function.var 3))))
  unfold depthValue
  exact LocallyDelta0Function.ite
    (LocallyDelta0.eq (LocallyDelta0Function.var 1) (LocallyDelta0Function.const 0))
    (LocallyDelta0Function.const 0) <|
    LocallyDelta0Function.ite (htag 0) hrel <| LocallyDelta0Function.ite (htag 1) hnrel <|
    LocallyDelta0Function.ite (htag 2) hverum <| LocallyDelta0Function.ite (htag 3) hfalsum <|
    LocallyDelta0Function.ite (htag 4) hand <| LocallyDelta0Function.ite (htag 5) hor <|
    LocallyDelta0Function.ite (htag 6) hall <|
    LocallyDelta0Function.ite (htag 7) hexs (LocallyDelta0Function.const 0)

private lemma boundAt_locallyDelta0 :
    LocallyDelta0Function fun w : Fin 3 → V ↦
      (fun (r : Fin 2 → V) d ↦ c.bound (c.iter (r 0) d) (r 1)) (w ·.succ) (w 0) :=
  c.bound_locallyDelta0.comp₂ (c.iter_locallyDelta0.comp₂ (LocallyDelta0Function.var 1)
    (LocallyDelta0Function.var 0)) (LocallyDelta0Function.var 2)

/-- The largest of the bounds at `n` over the depths `d ≤ J`. -/
noncomputable def boundMax (P J n : V) : V :=
  listMax (listMap (fun r d ↦ c.bound (c.iter (r 0) d) (r 1)) ![P, n] (rangeList (J + 1)))

lemma le_boundMax {P J n d : V} (hd : d ≤ J) : c.bound (c.iter P d) n ≤ c.boundMax P J n := by
  have hd' : d < len (rangeList (J + 1)) := by simpa [lt_succ_iff_le] using hd
  have := nth_le_listMax (v := listMap (fun r d ↦ c.bound (c.iter (r 0) d) (r 1)) ![P, n]
    (rangeList (J + 1))) (i := d) (by rwa [len_listMap c.boundAt_locallyDelta0])
  rw [nth_listMap c.boundAt_locallyDelta0 _ _ hd', nth_rangeList (by simpa using hd')] at this
  exact this

lemma boundMax_monotone {P J n m : V} (h : n ≤ m) : c.boundMax P J n ≤ c.boundMax P J m := by
  apply listMaxss_le
  intro i hi
  rw [len_listMap c.boundAt_locallyDelta0] at hi
  rw [nth_listMap c.boundAt_locallyDelta0 _ _ hi, nth_rangeList (by simpa using hi)]
  exact le_trans (c.bound_monotone _ h) (c.le_boundMax (lt_succ_iff_le.mp (by simpa using hi)))

lemma boundMax_locallyDelta0 :
    LocallyDelta0Function fun w : Fin 3 → V ↦ c.boundMax (w 0) (w 1) (w 2) := by
  have := (listMap_locallyDelta0 (g := fun (r : Fin 2 → V) d ↦ c.bound (c.iter (r 0) d) (r 1))
    c.boundAt_locallyDelta0).comp_cons
    (rangeList_locallyDelta0.comp₁ (LocallyDelta0Function.add_one (LocallyDelta0Function.var 1)))
    (u := ![fun w : Fin 3 → V ↦ w 0, fun w ↦ w 2]) <| Fin.forall_fin_succ.mpr
      ⟨LocallyDelta0Function.var 0, Fin.forall_fin_succ.mpr
        ⟨LocallyDelta0Function.var 2, finZeroElim⟩⟩
  convert listMax_locallyDelta0.comp₁ this using 2 with w
  simp only [boundMax]
  congr 2
  funext j
  cases j using Fin.cases with
  | zero => rfl
  | succ j => simp

private lemma depthValueAt_locallyDelta0 :
    LocallyDelta0Function fun w : Fin 4 → V ↦
      (fun (r : Fin 3 → V) d ↦ c.depthValue (r 0) (r 1) (r 2) d) (w ·.succ) (w 0) := by
  simpa using c.depthValue_locallyDelta0.retraction ![1, 2, 3, 0]

/-- The course-of-values recursion computing, for each code, the list of its values at the depths
`d ≤ J`, with the parameter `c.iter P d` at depth `d`. -/
noncomputable def courseOfValues : CourseOfValues.Construction V 2 where
  val q n T := listMap (fun r d ↦ c.depthValue (r 0) (r 1) (r 2) d) ![q 0, n, T]
    (rangeList (q 1 + 1))
  val_locallyDelta0 := by
    have := (listMap_locallyDelta0 (g := fun (r : Fin 3 → V) d ↦ c.depthValue (r 0) (r 1) (r 2) d)
      c.depthValueAt_locallyDelta0).comp_cons
      (rangeList_locallyDelta0.comp₁ (LocallyDelta0Function.add_one (LocallyDelta0Function.var 3)))
      (u := ![fun w : Fin 4 → V ↦ w 2, fun w ↦ w 1, fun w ↦ w 0]) <| Fin.forall_fin_succ.mpr
        ⟨LocallyDelta0Function.var 2, Fin.forall_fin_succ.mpr ⟨LocallyDelta0Function.var 1,
          Fin.forall_fin_succ.mpr ⟨LocallyDelta0Function.var 0, finZeroElim⟩⟩⟩
    convert this using 2 with w
    congr 1
    funext j
    cases j using Fin.cases with
    | zero => rfl
    | succ j =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j => simp
  bound q n := Exp.exp (Exp.exp ((q 1 + 1) + (q 1 + 1) + c.boundMax (q 0) (q 1) n + 3))
  bound_monotone q {_ _} h :=
    exp_monotone_le.mpr (exp_monotone_le.mpr (by gcongr; exact c.boundMax_monotone h))
  bound_locallyDelta0 := by
    have hJ : LocallyDelta0Function fun w : Fin 3 → V ↦ w 2 + 1 :=
      LocallyDelta0Function.add_one (LocallyDelta0Function.var 2)
    exact LocallyDelta0Function.exp.comp₁ <| LocallyDelta0Function.exp.comp₁ <|
      LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.add.comp₂
        (LocallyDelta0Function.add.comp₂ hJ hJ)
        (LocallyDelta0Function.comp₃ c.boundMax_locallyDelta0 (LocallyDelta0Function.var 1)
          (LocallyDelta0Function.var 2) (LocallyDelta0Function.var 0)))
        (LocallyDelta0Function.const 3)

/-- The list of the values of the code `q` at the depths `d ≤ J`. -/
noncomputable def depthList (P J q : V) : V := c.courseOfValues.result ![P, J] q

private lemma qqDecode {q : V} (hq : q ≠ 0) : q = ⟪π₁ (q - 1), π₂ (q - 1)⟫ + 1 := by
  rw [pair_unpair]
  exact (tsub_add_cancel_of_le (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hq))).symm

lemma depthValue_le {P q T d : V}
    (hT : ∀ q' < q, ∀ e, (znth T q').[e] ≤ c.bound (c.iter P e) q') :
    c.depthValue P q T d ≤ c.bound (c.iter P d) q := by
  by_cases h0 : q = 0
  · simp [depthValue, h0]
  have hq := qqDecode h0
  have hb : π₂ (q - 1) < q :=
    lt_of_le_of_lt (pi₂_le_self _) (pred_lt_self_of_pos (pos_iff_ne_zero.mpr h0))
  have hb₁ : π₁ (π₂ (q - 1)) < q := lt_of_le_of_lt (pi₁_le_self _) hb
  have hb₂ : π₂ (π₂ (q - 1)) < q := lt_of_le_of_lt (pi₂_le_self _) hb
  unfold depthValue
  simp only [h0, ↓reduceIte]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · have e : ^rel (π₁ (π₂ (q - 1))) (π₁ (π₂ (π₂ (q - 1)))) (π₂ (π₂ (π₂ (q - 1)))) = q := by
      rw [hq]; simp [qqRel, h1]
    have h := c.rel_le_bound (c.iter P d) (π₁ (π₂ (q - 1))) (π₁ (π₂ (π₂ (q - 1))))
      (π₂ (π₂ (π₂ (q - 1))))
    rwa [e] at h
  · have e : ^nrel (π₁ (π₂ (q - 1))) (π₁ (π₂ (π₂ (q - 1)))) (π₂ (π₂ (π₂ (q - 1)))) = q := by
      rw [hq]; simp [qqNRel, h2]
    have h := c.nrel_le_bound (c.iter P d) (π₁ (π₂ (q - 1))) (π₁ (π₂ (π₂ (q - 1))))
      (π₂ (π₂ (π₂ (q - 1))))
    rwa [e] at h
  · have : ^⊤ ≤ q := by
      rw [hq, qqVerum, h3]; exact add_le_add_left (pair_le_pair_right 2 zero_le) 1
    exact le_trans (c.verum_le_bound _) (c.bound_monotone _ this)
  · have : ^⊥ ≤ q := by
      rw [hq, qqFalsum, h4]; exact add_le_add_left (pair_le_pair_right 3 zero_le) 1
    exact le_trans (c.falsum_le_bound _) (c.bound_monotone _ this)
  · have e : (π₁ (π₂ (q - 1))) ^⋏ (π₂ (π₂ (q - 1))) = q := by rw [hq]; simp [qqAnd, h5]
    have h := c.and_le_bound _ _ _ _ _ (hT _ hb₁ d) (hT _ hb₂ d)
    rwa [e] at h
  · have e : (π₁ (π₂ (q - 1))) ^⋎ (π₂ (π₂ (q - 1))) = q := by rw [hq]; simp [qqOr, h6]
    have h := c.or_le_bound _ _ _ _ _ (hT _ hb₁ d) (hT _ hb₂ d)
    rwa [e] at h
  · have e : ^∀ π₂ (q - 1) = q := by rw [hq]; simp [qqAll, h7]
    have h := c.all_le_bound (c.iter P d) (π₂ (q - 1)) (znth T (π₂ (q - 1))).[d + 1]
      (by rw [← c.iter_succ]; exact hT _ hb _)
    rwa [e] at h
  · have e : ^∃ π₂ (q - 1) = q := by rw [hq]; simp [qqExs, h8]
    have h := c.exs_le_bound (c.iter P d) (π₂ (q - 1)) (znth T (π₂ (q - 1))).[d + 1]
      (by rw [← c.iter_succ]; exact hT _ hb _)
    rwa [e] at h
  · exact zero_le

private lemma depthValueList_locallyDelta0 (P J : V) :
    LocallyDelta0Function fun w : Fin 1 → V ↦
      listMap (fun r d ↦ c.depthValue (r 0) (r 1) (r 2) d)
        ![P, w 0, c.courseOfValues.table ![P, J] (w 0)] (rangeList (J + 1)) := by
  have htable : LocallyDelta0Function fun w : Fin 1 → V ↦ c.courseOfValues.table ![P, J] (w 0) := by
    have := c.courseOfValues.table_locallyDelta0.comp_cons (LocallyDelta0Function.var 0)
      (u := ![fun _ : Fin 1 → V ↦ P, fun _ ↦ J]) <| Fin.forall_fin_succ.mpr
        ⟨LocallyDelta0Function.const P, Fin.forall_fin_succ.mpr
          ⟨LocallyDelta0Function.const J, finZeroElim⟩⟩
    convert this using 2 with w
    congr 1
    funext j
    cases j using Fin.cases with
    | zero => rfl
    | succ j => simp
  have := (listMap_locallyDelta0 (g := fun (r : Fin 3 → V) d ↦ c.depthValue (r 0) (r 1) (r 2) d)
    c.depthValueAt_locallyDelta0).comp_cons (LocallyDelta0Function.const (rangeList (J + 1)))
    (u := ![fun _ : Fin 1 → V ↦ P, fun w ↦ w 0, fun w ↦ c.courseOfValues.table ![P, J] (w 0)]) <|
      Fin.forall_fin_succ.mpr ⟨LocallyDelta0Function.const P, Fin.forall_fin_succ.mpr
        ⟨LocallyDelta0Function.var 0, Fin.forall_fin_succ.mpr ⟨htable, finZeroElim⟩⟩⟩
  convert this using 2 with w
  congr 1
  funext j
  cases j using Fin.cases with
  | zero => rfl
  | succ j =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j => simp

lemma depthList_locallyDelta0 :
    LocallyDelta0Function fun w : Fin 3 → V ↦ c.depthList (w 0) (w 1) (w 2) := by
  have := c.courseOfValues.result_locallyDelta0.comp_cons
    (LocallyDelta0Function.var (V := V) (2 : Fin 3))
    (u := ![fun w : Fin 3 → V ↦ w 0, fun w ↦ w 1]) <| Fin.forall_fin_succ.mpr
      ⟨LocallyDelta0Function.var 0, Fin.forall_fin_succ.mpr
        ⟨LocallyDelta0Function.var 1, finZeroElim⟩⟩
  convert this using 2 with w
  simp only [depthList]
  congr 1
  funext j
  cases j using Fin.cases with
  | zero => rfl
  | succ j =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j => exact j.elim0

lemma depthList_spec (P J q : V) :
    c.depthList P J q = listMap (fun r d ↦ c.depthValue (r 0) (r 1) (r 2) d)
        ![P, q, c.courseOfValues.table ![P, J] q] (rangeList (J + 1)) ∧
      ∀ e < len (c.depthList P J q), (c.depthList P J q).[e] ≤ c.bound (c.iter P e) q := by
  have hdl : LocallyDelta0Function fun w : Fin 1 → V ↦ c.depthList P J (w 0) :=
    c.depthList_locallyDelta0.comp₃ (LocallyDelta0Function.const P)
      (LocallyDelta0Function.const J) (LocallyDelta0Function.var 0)
  have hP : LocallyDelta0Pred fun q ↦ c.depthList P J q =
        listMap (fun r d ↦ c.depthValue (r 0) (r 1) (r 2) d)
          ![P, q, c.courseOfValues.table ![P, J] q] (rangeList (J + 1)) ∧
      ∀ e < len (c.depthList P J q), (c.depthList P J q).[e] ≤ c.bound (c.iter P e) q := by
    have hentry : LocallyDelta0 fun u : Fin 2 → V ↦
        (c.depthList P J (u 1)).[u 0] ≤ c.bound (c.iter P (u 0)) (u 1) :=
      LocallyDelta0.le (nth_locallyDelta0.comp₂ (hdl.comp₁ (LocallyDelta0Function.var 1))
        (LocallyDelta0Function.var 0))
        (c.bound_locallyDelta0.comp₂ (c.iter_locallyDelta0.comp₂ (LocallyDelta0Function.const P)
          (LocallyDelta0Function.var 0)) (LocallyDelta0Function.var 1))
    exact (LocallyDelta0.eq hdl (c.depthValueList_locallyDelta0 P J)).and
      (LocallyDelta0.ball_lt_function (len_locallyDelta0.comp₁ hdl) hentry)
  revert q
  apply LocallyDelta0Pred.order_induction hP
  intro q ih
  set T := c.courseOfValues.table ![P, J] q
  have hg : LocallyDelta0Function fun w : Fin 4 → V ↦
      (fun (r : Fin 3 → V) d ↦ c.depthValue (r 0) (r 1) (r 2) d) (w ·.succ) (w 0) :=
    c.depthValueAt_locallyDelta0
  have hT : ∀ q' < q, ∀ e, (znth T q').[e] ≤ c.bound (c.iter P e) q' := by
    intro q' hq' e
    have hz : znth T q' = c.depthList P J q' := c.courseOfValues.znth_table hq'
    rw [hz]
    by_cases he : e < len (c.depthList P J q')
    · exact (ih q' hq').2 e he
    · rw [nth_lt_len (not_lt.mp he)]; exact zero_le
  have hentries : ∀ i < len (listMap (fun r d ↦ c.depthValue (r 0) (r 1) (r 2) d) ![P, q, T]
      (rangeList (J + 1))), (listMap (fun r d ↦ c.depthValue (r 0) (r 1) (r 2) d) ![P, q, T]
      (rangeList (J + 1))).[i] ≤ c.boundMax P J q := by
    intro i hi
    rw [len_listMap hg] at hi
    rw [nth_listMap hg _ _ hi, nth_rangeList (by simpa using hi)]
    exact le_trans (c.depthValue_le hT) (c.le_boundMax (lt_succ_iff_le.mp (by simpa using hi)))
  have hval_le : c.courseOfValues.val ![P, J] q T ≤ c.courseOfValues.bound ![P, J] q := by
    have := le_exp_exp_of_nth_le _ hentries
    rw [len_listMap hg, len_rangeList] at this
    exact this
  have heq : c.depthList P J q = listMap (fun r d ↦ c.depthValue (r 0) (r 1) (r 2) d) ![P, q, T]
      (rangeList (J + 1)) :=
    c.courseOfValues.result_eq_val hval_le
  refine ⟨heq, fun e he ↦ ?_⟩
  rw [heq] at he ⊢
  rw [len_listMap hg] at he
  rw [nth_listMap hg _ _ he, nth_rangeList (by simpa using he)]
  exact c.depthValue_le hT

lemma iter_add (P a d : V) : c.iter (c.iter P a) d = c.iter P (a + d) := by
  have hP : LocallyDelta0Pred fun d ↦ c.iter (c.iter P a) d = c.iter P (a + d) :=
    LocallyDelta0.eq (c.iter_locallyDelta0.comp₂ (LocallyDelta0Function.const _)
        (LocallyDelta0Function.var 0))
      (c.iter_locallyDelta0.comp₂ (LocallyDelta0Function.const P)
        (LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.const a)
          (LocallyDelta0Function.var 0)))
  revert d
  apply LocallyDelta0Pred.succ_induction hP
  · simp [c.iter_zero]
  · intro d ih
    rw [c.iter_succ, ih, ← add_assoc, c.iter_succ]

lemma nth_depthList {P J q d : V} (hd : d ≤ J) :
    (c.depthList P J q).[d] = c.depthValue P q (c.courseOfValues.table ![P, J] q) d := by
  have hg : LocallyDelta0Function fun w : Fin 4 → V ↦
      (fun (r : Fin 3 → V) d ↦ c.depthValue (r 0) (r 1) (r 2) d) (w ·.succ) (w 0) :=
    c.depthValueAt_locallyDelta0
  have hd' : d < len (rangeList (J + 1)) := by simpa using lt_succ_iff_le.mpr hd
  rw [(c.depthList_spec P J q).1, nth_listMap hg _ _ hd', nth_rangeList (by simpa using hd')]
  simp

lemma depthValue_congr {P P' q T T' d e : V} (hP : c.iter P d = c.iter P' e)
    (hT : ∀ q' < q, (znth T q').[d] = (znth T' q').[e] ∧
      (znth T q').[d + 1] = (znth T' q').[e + 1]) :
    c.depthValue P q T d = c.depthValue P' q T' e := by
  by_cases h0 : q = 0
  · simp [depthValue, h0]
  have hb : π₂ (q - 1) < q :=
    lt_of_le_of_lt (pi₂_le_self _) (pred_lt_self_of_pos (pos_iff_ne_zero.mpr h0))
  have hb₁ : π₁ (π₂ (q - 1)) < q := lt_of_le_of_lt (pi₁_le_self _) hb
  have hb₂ : π₂ (π₂ (q - 1)) < q := lt_of_le_of_lt (pi₂_le_self _) hb
  have hP' : c.iter P (d + 1) = c.iter P' (e + 1) := by rw [c.iter_succ, c.iter_succ, hP]
  unfold depthValue
  simp only [h0, ↓reduceIte]
  split_ifs <;> simp only [hP, (hT _ hb₁).1, (hT _ hb₂).1, (hT _ hb).2]

/-- The entries of the lists of values do not depend on the depth bound, and an entry at a
depth depends only on the parameter at that depth. -/
lemma nth_depthList_eq (P M J J' : V) (hJ : J ≤ M) (hJ' : J' ≤ M) :
    ∀ q, ∀ a ≤ M, ∀ d ≤ M, ∀ b ≤ M, ∀ e ≤ M, a + d = b + e → d + q ≤ J → e + q ≤ J' →
      (c.depthList (c.iter P a) J q).[d] = (c.depthList (c.iter P b) J' q).[e] := by
  have hP : LocallyDelta0Pred fun q ↦ ∀ a ≤ M, ∀ d ≤ M, ∀ b ≤ M, ∀ e ≤ M,
      a + d = b + e → d + q ≤ J → e + q ≤ J' →
        (c.depthList (c.iter P a) J q).[d] = (c.depthList (c.iter P b) J' q).[e] := by
    have v5 : ∀ i : Fin 5, LocallyDelta0Function fun w : Fin 5 → V ↦ w i :=
      LocallyDelta0Function.var
    have hX : ∀ (i j : Fin 5) (K : V), LocallyDelta0Function fun w : Fin 5 → V ↦
        (c.depthList (c.iter P (w i)) K (w 4)).[w j] := fun i j K ↦
      nth_locallyDelta0.comp₂ (c.depthList_locallyDelta0.comp₃
        (c.iter_locallyDelta0.comp₂ (LocallyDelta0Function.const P) (v5 i))
        (LocallyDelta0Function.const K) (v5 4)) (v5 j)
    have hR : LocallyDelta0 fun w : Fin 5 → V ↦ w 3 + w 2 = w 1 + w 0 → w 2 + w 4 ≤ J →
        w 0 + w 4 ≤ J' → (c.depthList (c.iter P (w 3)) J (w 4)).[w 2] =
          (c.depthList (c.iter P (w 1)) J' (w 4)).[w 0] :=
      (LocallyDelta0.eq (LocallyDelta0Function.add.comp₂ (v5 3) (v5 2))
          (LocallyDelta0Function.add.comp₂ (v5 1) (v5 0))).imp <|
        (LocallyDelta0.le (LocallyDelta0Function.add.comp₂ (v5 2) (v5 4))
          (LocallyDelta0Function.const J)).imp <|
        (LocallyDelta0.le (LocallyDelta0Function.add.comp₂ (v5 0) (v5 4))
          (LocallyDelta0Function.const J')).imp <|
        LocallyDelta0.eq (hX 3 2 J) (hX 1 0 J')
    have := LocallyDelta0.ball_le_function (LocallyDelta0Function.const M) <|
      LocallyDelta0.ball_le_function (LocallyDelta0Function.const M) <|
      LocallyDelta0.ball_le_function (LocallyDelta0Function.const M) <|
      LocallyDelta0.ball_le_function (LocallyDelta0Function.const M) hR
    exact this.of_iff fun v ↦ by simp
  apply LocallyDelta0Pred.order_induction hP
  intro q ih a ha d hd b hb e he hsum hdJ heJ
  rw [c.nth_depthList (le_trans le_self_add hdJ), c.nth_depthList (le_trans le_self_add heJ)]
  apply c.depthValue_congr (by rw [c.iter_add, c.iter_add, hsum])
  intro q' hq'
  have hq1 : q' + 1 ≤ q := lt_iff_succ_le.mp hq'
  have hd1 : d + 1 + q' ≤ J := le_trans (by rw [add_assoc, add_comm 1 q']; gcongr) hdJ
  have he1 : e + 1 + q' ≤ J' := le_trans (by rw [add_assoc, add_comm 1 q']; gcongr) heJ
  rw [c.courseOfValues.znth_table hq', c.courseOfValues.znth_table hq']
  exact ⟨ih q' hq' a ha d hd b hb e he hsum (le_trans (by gcongr; exact le_self_add) hd1)
      (le_trans (by gcongr; exact le_self_add) he1),
    ih q' hq' a ha (d + 1) (le_trans (le_trans le_self_add hd1) hJ) b hb (e + 1)
      (le_trans (le_trans le_self_add he1) hJ') (by rw [← add_assoc, ← add_assoc, hsum]) hd1 he1⟩

lemma len_depthList (P J q : V) : len (c.depthList P J q) = J + 1 := by
  have hg : LocallyDelta0Function fun w : Fin 4 → V ↦
      (fun (r : Fin 3 → V) d ↦ c.depthValue (r 0) (r 1) (r 2) d) (w ·.succ) (w 0) :=
    c.depthValueAt_locallyDelta0
  rw [(c.depthList_spec P J q).1, len_listMap hg, len_rangeList]

/-- The value of the recursion at the code `q` with the parameter `P`. -/
noncomputable def courseOfValuesResult (P q : V) : V := (c.depthList P q q).[0]

lemma courseOfValuesResult_locallyDelta0 :
    LocallyDelta0Function fun w : Fin 2 → V ↦ c.courseOfValuesResult (w 0) (w 1) :=
  nth_locallyDelta0.comp₂ (c.depthList_locallyDelta0.comp₃ (LocallyDelta0Function.var 0)
    (LocallyDelta0Function.var 1) (LocallyDelta0Function.var 1)) (LocallyDelta0Function.const 0)

lemma courseOfValuesResult_le_bound (P q : V) : c.courseOfValuesResult P q ≤ c.bound P q := by
  simpa [c.iter_zero, courseOfValuesResult] using
    (c.depthList_spec P q q).2 0 (by simp [c.len_depthList])

lemma nth_depthList_eq_courseOfValuesResult {P J p d : V} (h : d + p ≤ J) :
    (c.depthList P J p).[d] = c.courseOfValuesResult (c.iter P d) p := by
  have hd : d ≤ J := le_trans le_self_add h
  have := c.nth_depthList_eq P J J p le_rfl (le_trans le_add_self h) p 0 zero_le d hd d hd 0
    zero_le (by simp) h (by simp)
  simpa [c.iter_zero, courseOfValuesResult] using this

private lemma courseOfValuesResult_eq_depthValue (P q : V) :
    c.courseOfValuesResult P q = c.depthValue P q (c.courseOfValues.table ![P, q] q) 0 :=
  c.nth_depthList zero_le

private lemma znth_table_eq {P q p d : V} (hp : p < q) (hd : d ≤ 1) :
    (znth (c.courseOfValues.table ![P, q] q) p).[d] = c.courseOfValuesResult (c.iter P d) p := by
  rw [c.courseOfValues.znth_table hp]
  refine c.nth_depthList_eq_courseOfValuesResult ?_
  calc d + p ≤ 1 + p := by gcongr
    _ = p + 1 := add_comm _ _
    _ ≤ q := lt_iff_succ_le.mp hp

lemma courseOfValuesResult_rel (P k R v : V) :
    c.courseOfValuesResult P (^rel k R v) = c.rel P k R v := by
  simp [courseOfValuesResult_eq_depthValue, depthValue, qqRel, c.iter_zero]

lemma courseOfValuesResult_nrel (P k R v : V) :
    c.courseOfValuesResult P (^nrel k R v) = c.nrel P k R v := by
  simp [courseOfValuesResult_eq_depthValue, depthValue, qqNRel, c.iter_zero]

lemma courseOfValuesResult_verum (P : V) : c.courseOfValuesResult P ^⊤ = c.verum P := by
  simp [courseOfValuesResult_eq_depthValue, depthValue, qqVerum, c.iter_zero]

lemma courseOfValuesResult_falsum (P : V) : c.courseOfValuesResult P ^⊥ = c.falsum P := by
  simp [courseOfValuesResult_eq_depthValue, depthValue, qqFalsum, c.iter_zero]

private lemma depthValue_and (P p₁ p₂ T d : V) :
    c.depthValue P (p₁ ^⋏ p₂) T d =
      c.and (c.iter P d) p₁ p₂ (znth T p₁).[d] (znth T p₂).[d] := by
  simp [depthValue, qqAnd]

private lemma depthValue_or (P p₁ p₂ T d : V) :
    c.depthValue P (p₁ ^⋎ p₂) T d =
      c.or (c.iter P d) p₁ p₂ (znth T p₁).[d] (znth T p₂).[d] := by
  simp [depthValue, qqOr]

private lemma depthValue_all (P p₁ T d : V) :
    c.depthValue P (^∀ p₁) T d = c.all (c.iter P d) p₁ ?[(znth T p₁).[d + 1]] := by
  simp [depthValue, qqAll]

private lemma depthValue_exs (P p₁ T d : V) :
    c.depthValue P (^∃ p₁) T d = c.exs (c.iter P d) p₁ ?[(znth T p₁).[d + 1]] := by
  simp [depthValue, qqExs]

lemma courseOfValuesResult_and (P p₁ p₂ : V) :
    c.courseOfValuesResult P (p₁ ^⋏ p₂) =
      c.and P p₁ p₂ (c.courseOfValuesResult P p₁) (c.courseOfValuesResult P p₂) := by
  rw [courseOfValuesResult_eq_depthValue, depthValue_and, c.znth_table_eq (by simp) zero_le,
    c.znth_table_eq (by simp) zero_le]
  simp only [c.iter_zero]

lemma courseOfValuesResult_or (P p₁ p₂ : V) :
    c.courseOfValuesResult P (p₁ ^⋎ p₂) =
      c.or P p₁ p₂ (c.courseOfValuesResult P p₁) (c.courseOfValuesResult P p₂) := by
  rw [courseOfValuesResult_eq_depthValue, depthValue_or, c.znth_table_eq (by simp) zero_le,
    c.znth_table_eq (by simp) zero_le]
  simp only [c.iter_zero]

lemma courseOfValuesResult_all (P p₁ : V) :
    c.courseOfValuesResult P (^∀ p₁) = c.all P p₁ ?[c.courseOfValuesResult (c.change P) p₁] := by
  rw [courseOfValuesResult_eq_depthValue, depthValue_all, zero_add,
    c.znth_table_eq (by simp) le_rfl, ← c.change_eq_iter, c.iter_zero]

lemma courseOfValuesResult_exs (P p₁ : V) :
    c.courseOfValuesResult P (^∃ p₁) = c.exs P p₁ ?[c.courseOfValuesResult (c.change P) p₁] := by
  rw [courseOfValuesResult_eq_depthValue, depthValue_exs, zero_add,
    c.znth_table_eq (by simp) le_rfl, ← c.change_eq_iter, c.iter_zero]

private lemma limSeq_comp {n : ℕ} {f : (Fin n → V) → V} (hf : LocallyDelta0Function f) :
    LocallyDelta0Function fun w : Fin n → V ↦ (c.construction L).limSeq ![] (f w) := by
  have := (c.construction L).limSeq_locallyDelta0.comp_cons hf (u := fun j ↦ j.elim0)
    fun j ↦ j.elim0
  convert this using 2 with w
  congr 1
  funext j
  exact j.elim0

lemma isUFormula_and_eq_of_mem_limSeq {s z : V} (h : z ∈ (c.construction L).limSeq ![] s) :
    IsUFormula L (π₁ (π₂ z)) ∧ π₂ (π₂ z) = c.courseOfValuesResult (π₁ z) (π₁ (π₂ z)) := by
  have hz : LocallyDelta0Function fun y : Fin 2 → V ↦ y 0 := LocallyDelta0Function.var 0
  have hR : LocallyDelta0 fun y : Fin 2 → V ↦ y 0 ∈ (c.construction L).limSeq ![] (y 1) →
      IsUFormula L (π₁ (π₂ (y 0))) ∧
        π₂ (π₂ (y 0)) = c.courseOfValuesResult (π₁ (y 0)) (π₁ (π₂ (y 0))) :=
    (LocallyDelta0.mem hz (c.limSeq_comp L (LocallyDelta0Function.var 1))).imp
      ((isUFormula_locallyDelta0.pred_comp
          (LocallyDelta0Function.pi₁.comp₁ (LocallyDelta0Function.pi₂.comp₁ hz))).and
        (LocallyDelta0.eq (LocallyDelta0Function.pi₂.comp₁ (LocallyDelta0Function.pi₂.comp₁ hz))
          (c.courseOfValuesResult_locallyDelta0.comp₂ (LocallyDelta0Function.pi₁.comp₁ hz)
            (LocallyDelta0Function.pi₁.comp₁ (LocallyDelta0Function.pi₂.comp₁ hz)))))
  have hP : LocallyDelta0Pred fun s ↦ ∀ z < (c.construction L).limSeq ![] s,
      z ∈ (c.construction L).limSeq ![] s →
        IsUFormula L (π₁ (π₂ z)) ∧ π₂ (π₂ z) = c.courseOfValuesResult (π₁ z) (π₁ (π₂ z)) :=
    (LocallyDelta0.ball_lt_function
      (c.limSeq_comp L (LocallyDelta0Function.var (V := V) (0 : Fin 1))) hR).of_iff
        fun w ↦ by simp
  have : ∀ s, ∀ z < (c.construction L).limSeq ![] s, z ∈ (c.construction L).limSeq ![] s →
      IsUFormula L (π₁ (π₂ z)) ∧ π₂ (π₂ z) = c.courseOfValuesResult (π₁ z) (π₁ (π₂ z)) := by
    apply LocallyDelta0Pred.succ_induction hP
    · intro z _ hz
      simp at hz
    · intro s ih z _ hz
      have ih' {param p y : V} (h : ⟪param, p, y⟫ ∈ (c.construction L).limSeq ![] s) :
          y = c.courseOfValuesResult param p := by
        simpa using (ih _ (lt_of_mem h) h).2
      obtain ⟨param, p, y, rfl, hp, H⟩ := ((c.construction L).mem_limSeq_succ_iff.mp hz).2
      simp only [pi₁_pair, pi₂_pair]
      refine ⟨hp, ?_⟩
      rcases H with (⟨k, R, v, rfl, rfl⟩ | ⟨k, R, v, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ |
        ⟨p₁, ys, ⟨hl, hys⟩, rfl, rfl⟩ | ⟨p₁, ys, ⟨hl, hys⟩, rfl, rfl⟩)
      · rw [c.courseOfValuesResult_rel]
      · rw [c.courseOfValuesResult_nrel]
      · rw [c.courseOfValuesResult_verum]
      · rw [c.courseOfValuesResult_falsum]
      · rw [c.courseOfValuesResult_and, ← ih' h₁, ← ih' h₂]
      · rw [c.courseOfValuesResult_or, ← ih' h₁, ← ih' h₂]
      · have h₀ := hys 0 (by simp [c.allSize_eq_one])
        rw [c.allChanges_eq_change] at h₀
        have hys₁ : ys = ?[ys.[0]] := nth_ext (by simp [hl, c.allSize_eq_one]) fun i hi ↦ by
          rw [hl, c.allSize_eq_one] at hi
          rcases lt_one_iff_eq_zero.mp hi
          simp
        rw [c.courseOfValuesResult_all, ← ih' h₀, ← hys₁]
      · have h₀ := hys 0 (by simp [c.exsSize_eq_one])
        rw [c.exsChanges_eq_change] at h₀
        have hys₁ : ys = ?[ys.[0]] := nth_ext (by simp [hl, c.exsSize_eq_one]) fun i hi ↦ by
          rw [hl, c.exsSize_eq_one] at hi
          rcases lt_one_iff_eq_zero.mp hi
          simp
        rw [c.courseOfValuesResult_exs, ← ih' h₀, ← hys₁]
  exact this s z (lt_of_mem h) h

lemma mem_limSeq_of_isUFormula {P p : V} (hp : IsUFormula L p) :
    ⟪P, p, c.courseOfValuesResult P p⟫ ∈
      (c.construction L).limSeq ![] (⟪c.iter P p, p, c.boundMax P p p⟫ + p + 1) := by
  set K := ⟪c.iter P p, p, c.boundMax P p p⟫
  have hP : LocallyDelta0Pred fun p' ↦ ∀ d ≤ p, d + p' ≤ p → IsUFormula L p' →
      ⟪c.iter P d, p', c.courseOfValuesResult (c.iter P d) p'⟫ ∈
        (c.construction L).limSeq ![] (K + p' + 1) := by
    have v2 : ∀ i : Fin 2, LocallyDelta0Function fun w : Fin 2 → V ↦ w i :=
      LocallyDelta0Function.var
    have hi : LocallyDelta0Function fun w : Fin 2 → V ↦ c.iter P (w 0) :=
      c.iter_locallyDelta0.comp₂ (LocallyDelta0Function.const P) (v2 0)
    have hmem := LocallyDelta0.mem
      (LocallyDelta0Function.pairing.comp₂ hi (LocallyDelta0Function.pairing.comp₂ (v2 1)
        (c.courseOfValuesResult_locallyDelta0.comp₂ hi (v2 1))))
      (c.limSeq_comp L <| LocallyDelta0Function.add_one <|
        LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.const K) (v2 1))
    have := LocallyDelta0.ball_le_function (LocallyDelta0Function.const p) <|
      (LocallyDelta0.le (LocallyDelta0Function.add.comp₂ (v2 0) (v2 1))
        (LocallyDelta0Function.const p)).imp <|
      ((isUFormula_locallyDelta0 (L := L)).pred_comp (v2 1)).imp hmem
    exact this.of_iff fun w ↦ by simp
  have : ∀ p', ∀ d ≤ p, d + p' ≤ p → IsUFormula L p' →
      ⟪c.iter P d, p', c.courseOfValuesResult (c.iter P d) p'⟫ ∈
        (c.construction L).limSeq ![] (K + p' + 1) := by
    apply LocallyDelta0Pred.order_induction hP
    intro p' ih d hd hdp hu
    have hp' : p' ≤ p := le_trans le_add_self hdp
    have hle : ⟪c.iter P d, p', c.courseOfValuesResult (c.iter P d) p'⟫ ≤ K :=
      pair_le_pair (c.iter_monotone P hd) <| pair_le_pair hp' <|
        le_trans (c.courseOfValuesResult_le_bound _ _)
          (le_trans (c.bound_monotone _ hp') (c.le_boundMax hd))
    have hsub {p₁ e : V} (hp₁ : p₁ < p') (he : e ≤ 1) (hu₁ : IsUFormula L p₁) :
        ⟪c.iter P (d + e), p₁, c.courseOfValuesResult (c.iter P (d + e)) p₁⟫ ∈
          (c.construction L).limSeq ![] (K + p') := by
      have h₁ : d + e + p₁ ≤ p := by
        refine le_trans ?_ hdp
        calc d + e + p₁ ≤ d + (1 + p₁) := by rw [add_assoc]; gcongr
          _ = d + (p₁ + 1) := by rw [add_comm 1 p₁]
          _ ≤ d + p' := by gcongr; exact lt_iff_succ_le.mp hp₁
      exact (c.construction L).limSeq_cumulative
        (by rw [add_assoc]; exact add_le_add_right (succ_le_iff_lt.mpr hp₁) K)
        (ih p₁ hp₁ (d + e) (le_trans le_self_add h₁) h₁ hu₁)
    apply (c.construction L).mem_limSeq_succ_iff.mpr
    refine ⟨le_trans hle le_self_add, ?_⟩
    change c.Phi L _ _
    refine ⟨c.iter P d, p', _, rfl, hu, ?_⟩
    rcases IsUFormula.case hu with (⟨k, R, v, _, _, rfl⟩ | ⟨k, R, v, _, _, rfl⟩ | rfl | rfl |
      ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩)
    · disj 1; exact ⟨k, R, v, rfl, c.courseOfValuesResult_rel _ _ _ _⟩
    · disj 2; exact ⟨k, R, v, rfl, c.courseOfValuesResult_nrel _ _ _ _⟩
    · disj 3; exact ⟨rfl, c.courseOfValuesResult_verum _⟩
    · disj 4; exact ⟨rfl, c.courseOfValuesResult_falsum _⟩
    · disj 5
      exact ⟨p₁, p₂, c.courseOfValuesResult (c.iter P d) p₁,
        c.courseOfValuesResult (c.iter P d) p₂, by simpa using hsub (by simp) zero_le hp₁,
        by simpa using hsub (by simp) zero_le hp₂, rfl, c.courseOfValuesResult_and _ _ _⟩
    · disj 6
      exact ⟨p₁, p₂, c.courseOfValuesResult (c.iter P d) p₁,
        c.courseOfValuesResult (c.iter P d) p₂, by simpa using hsub (by simp) zero_le hp₁,
        by simpa using hsub (by simp) zero_le hp₂, rfl, c.courseOfValuesResult_or _ _ _⟩
    · disj 7
      refine ⟨p₁, ?[c.courseOfValuesResult (c.change (c.iter P d)) p₁],
        ⟨by simp [c.allSize_eq_one], fun i hi ↦ ?_⟩, rfl, c.courseOfValuesResult_all _ _⟩
      rw [c.allSize_eq_one] at hi
      rcases lt_one_iff_eq_zero.mp hi
      have := hsub (by simp) le_rfl hp₁
      rw [c.iter_succ] at this
      simpa [c.allChanges_eq_change] using this
    · disj 8
      refine ⟨p₁, ?[c.courseOfValuesResult (c.change (c.iter P d)) p₁],
        ⟨by simp [c.exsSize_eq_one], fun i hi ↦ ?_⟩, rfl, c.courseOfValuesResult_exs _ _⟩
      rw [c.exsSize_eq_one] at hi
      rcases lt_one_iff_eq_zero.mp hi
      have := hsub (by simp) le_rfl hp₁
      rw [c.iter_succ] at this
      simpa [c.exsChanges_eq_change] using this
  have := this p 0 zero_le (by simp) hp
  rwa [c.iter_zero] at this

lemma graph_iff {param p y : V} :
    c.Graph L param p y ↔ IsUFormula L p ∧ y = c.courseOfValuesResult param p := by
  constructor
  · rintro ⟨s, h⟩
    simpa using c.isUFormula_and_eq_of_mem_limSeq L h
  · rintro ⟨hp, rfl⟩
    exact ⟨_, c.mem_limSeq_of_isUFormula L hp⟩

variable {param : V}

variable {L c}

lemma Graph.case_iff {p y : V} :
    c.Graph L param p y ↔
    IsUFormula L p ∧ (
    (∃ k R v, p = ^rel k R v ∧ y = c.rel param k R v) ∨
    (∃ k R v, p = ^nrel k R v ∧ y = c.nrel param k R v) ∨
    (p = ^⊤ ∧ y = c.verum param) ∨
    (p = ^⊥ ∧ y = c.falsum param) ∨
    (∃ p₁ p₂ y₁ y₂, c.Graph L param p₁ y₁ ∧ c.Graph L param p₂ y₂ ∧ p = p₁ ^⋏ p₂ ∧ y = c.and param
      p₁ p₂ y₁ y₂) ∨
    (∃ p₁ p₂ y₁ y₂, c.Graph L param p₁ y₁ ∧ c.Graph L param p₂ y₂ ∧ p = p₁ ^⋎ p₂ ∧ y = c.or param
      p₁ p₂ y₁ y₂) ∨
    (∃ p₁ ys, (len ys = c.allSize param p₁ ∧
        ∀ i < c.allSize param p₁, c.Graph L (c.allChanges param i) p₁ ys.[i]) ∧
      p = ^∀ p₁ ∧ y = c.all param p₁ ys) ∨
    (∃ p₁ ys, (len ys = c.exsSize param p₁ ∧
        ∀ i < c.exsSize param p₁, c.Graph L (c.exsChanges param i) p₁ ys.[i]) ∧
      p = ^∃ p₁ ∧ y = c.exs param p₁ ys) ) := by
  rw [c.graph_iff L]
  constructor
  · rintro ⟨hp, rfl⟩
    refine ⟨hp, ?_⟩
    rcases IsUFormula.case hp with (⟨k, R, v, _, _, rfl⟩ | ⟨k, R, v, _, _, rfl⟩ | rfl | rfl |
      ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩)
    · disj 1; exact ⟨k, R, v, rfl, c.courseOfValuesResult_rel _ _ _ _⟩
    · disj 2; exact ⟨k, R, v, rfl, c.courseOfValuesResult_nrel _ _ _ _⟩
    · disj 3; exact ⟨rfl, c.courseOfValuesResult_verum _⟩
    · disj 4; exact ⟨rfl, c.courseOfValuesResult_falsum _⟩
    · disj 5
      exact ⟨p₁, p₂, _, _, (c.graph_iff L).mpr ⟨hp₁, rfl⟩, (c.graph_iff L).mpr ⟨hp₂, rfl⟩, rfl,
        c.courseOfValuesResult_and _ _ _⟩
    · disj 6
      exact ⟨p₁, p₂, _, _, (c.graph_iff L).mpr ⟨hp₁, rfl⟩, (c.graph_iff L).mpr ⟨hp₂, rfl⟩, rfl,
        c.courseOfValuesResult_or _ _ _⟩
    · disj 7
      refine ⟨p₁, _, ⟨by simp [c.allSize_eq_one], fun i hi ↦ ?_⟩, rfl,
        c.courseOfValuesResult_all _ _⟩
      rw [c.allSize_eq_one] at hi
      rcases lt_one_iff_eq_zero.mp hi
      exact (c.graph_iff L).mpr ⟨hp₁, by simp [c.allChanges_eq_change]⟩
    · disj 8
      refine ⟨p₁, _, ⟨by simp [c.exsSize_eq_one], fun i hi ↦ ?_⟩, rfl,
        c.courseOfValuesResult_exs _ _⟩
      rw [c.exsSize_eq_one] at hi
      rcases lt_one_iff_eq_zero.mp hi
      exact (c.graph_iff L).mpr ⟨hp₁, by simp [c.exsChanges_eq_change]⟩
  · rintro ⟨hp, H⟩
    refine ⟨hp, ?_⟩
    rcases H with (⟨k, R, v, rfl, rfl⟩ | ⟨k, R, v, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ |
      ⟨p₁, ys, ⟨hl, hys⟩, rfl, rfl⟩ | ⟨p₁, ys, ⟨hl, hys⟩, rfl, rfl⟩)
    · rw [c.courseOfValuesResult_rel]
    · rw [c.courseOfValuesResult_nrel]
    · rw [c.courseOfValuesResult_verum]
    · rw [c.courseOfValuesResult_falsum]
    · rw [c.courseOfValuesResult_and, ((c.graph_iff L).mp h₁).2, ((c.graph_iff L).mp h₂).2]
    · rw [c.courseOfValuesResult_or, ((c.graph_iff L).mp h₁).2, ((c.graph_iff L).mp h₂).2]
    · have h₀ := ((c.graph_iff L).mp (hys 0 (by simp [c.allSize_eq_one]))).2
      rw [c.allChanges_eq_change] at h₀
      have hys₁ : ys = ?[ys.[0]] := nth_ext (by simp [hl, c.allSize_eq_one]) fun i hi ↦ by
        rw [hl, c.allSize_eq_one] at hi
        rcases lt_one_iff_eq_zero.mp hi
        simp
      rw [c.courseOfValuesResult_all, ← h₀, ← hys₁]
    · have h₀ := ((c.graph_iff L).mp (hys 0 (by simp [c.exsSize_eq_one]))).2
      rw [c.exsChanges_eq_change] at h₀
      have hys₁ : ys = ?[ys.[0]] := nth_ext (by simp [hl, c.exsSize_eq_one]) fun i hi ↦ by
        rw [hl, c.exsSize_eq_one] at hi
        rcases lt_one_iff_eq_zero.mp hi
        simp
      rw [c.courseOfValuesResult_exs, ← h₀, ← hys₁]

variable (c β)

lemma graph_defined : 𝚺ᴬ₁-Relation₃ c.Graph L via β.graph L := .mk fun v ↦ by
  simp [Blueprint.graph, (c.construction L).fixpoint_defined.iff, Matrix.empty_eq]; rfl

@[simp] lemma eval_graphDef (v : Fin 3 → V) :
    (β.graph L).val.Evalb v ↔ c.Graph L (v 0) (v 1) (v 2) := (graph_defined β c).iff

instance graph_definable : 𝚺ᴬ_[0 + 1]-Relation₃ c.Graph L := c.graph_defined.to_definable

variable {β}

lemma graph_dom_uformula {p r} :
    c.Graph L param p r → IsUFormula L p := fun h ↦ Graph.case_iff.mp h |>.1

lemma graph_rel_iff {k r v y} (hkr : L.IsRel k r) (hv : IsUTermVec L k v) :
    c.Graph L param (^rel k r v) y ↔ y = c.rel param k r v := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨k, r, v, H, rfl⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
      ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
    · rcases (by simpa [qqRel] using H) with ⟨rfl, rfl, rfl, rfl⟩; rfl
    · simp [qqRel, qqNRel] at H
    · simp [qqRel, qqVerum] at H
    · simp [qqRel, qqFalsum] at H
    · simp [qqRel, qqAnd] at H
    · simp [qqRel, qqOr] at H
    · simp [qqRel, qqAll] at H
    · simp [qqRel, qqExs] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp [hkr, hv], by disj 1; exact ⟨k, r, v, rfl, rfl⟩⟩

lemma graph_nrel_iff {k r v y} (hkr : L.IsRel k r) (hv : IsUTermVec L k v) :
    c.Graph L param (^nrel k r v) y ↔ y = c.nrel param k r v := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, rfl⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
      ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
    · simp [qqNRel, qqRel] at H
    · rcases (by simpa [qqNRel] using H) with ⟨rfl, rfl, rfl, rfl⟩; rfl
    · simp [qqNRel, qqVerum] at H
    · simp [qqNRel, qqFalsum] at H
    · simp [qqNRel, qqAnd] at H
    · simp [qqNRel, qqOr] at H
    · simp [qqNRel, qqAll] at H
    · simp [qqNRel, qqExs] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp [hkr, hv], by disj 2; exact ⟨k, r, v, rfl, rfl⟩⟩

lemma graph_verum_iff {y} :
    c.Graph L param ^⊤ y ↔ y = c.verum param := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, rfl⟩ | ⟨H, _⟩ |
      ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
    · simp [qqVerum, qqRel] at H
    · simp [qqVerum, qqNRel] at H
    · rcases (by simpa [qqVerum] using H); rfl
    · simp [qqVerum, qqFalsum] at H
    · simp [qqVerum, qqAnd] at H
    · simp [qqVerum, qqOr] at H
    · simp [qqVerum, qqAll] at H
    · simp [qqVerum, qqExs] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp, by disj 3; exact ⟨rfl, rfl⟩⟩

lemma graph_falsum_iff {y} :
    c.Graph L param ^⊥ y ↔ y = c.falsum param := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, rfl⟩ |
      ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
    · simp [qqFalsum, qqRel] at H
    · simp [qqFalsum, qqNRel] at H
    · simp [qqFalsum, qqVerum] at H
    · rcases (by simpa [qqFalsum] using H); rfl
    · simp [qqFalsum, qqAnd] at H
    · simp [qqFalsum, qqOr] at H
    · simp [qqFalsum, qqAll] at H
    · simp [qqFalsum, qqExs] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp, by disj 4; exact ⟨rfl, rfl⟩⟩

lemma graph_rel {k r v} (hkr : L.IsRel k r) (hv : IsUTermVec L k v) :
    c.Graph L param (^rel k r v) (c.rel param k r v) :=
  (Graph.case_iff).mpr ⟨by simp [hkr, hv], by disj 1; exact ⟨k, r, v, rfl, rfl⟩⟩

lemma graph_nrel {k r v} (hkr : L.IsRel k r) (hv : IsUTermVec L k v) :
    c.Graph L param (^nrel k r v) (c.nrel param k r v) :=
  (Graph.case_iff).mpr ⟨by simp [hkr, hv], by disj 2; exact ⟨k, r, v, rfl, rfl⟩⟩

lemma graph_verum :
    c.Graph L param ^⊤ (c.verum param) :=
  (Graph.case_iff).mpr ⟨by simp, by disj 3; exact ⟨rfl, rfl⟩⟩

lemma graph_falsum :
    c.Graph L param ^⊥ (c.falsum param) :=
  (Graph.case_iff).mpr ⟨by simp, by disj 4; exact ⟨rfl, rfl⟩⟩

lemma graph_and {p₁ p₂ r₁ r₂ : V} (hp₁ : IsUFormula L p₁) (hp₂ : IsUFormula L p₂)
    (h₁ : c.Graph L param p₁ r₁) (h₂ : c.Graph L param p₂ r₂) :
    c.Graph L param (p₁ ^⋏ p₂) (c.and param p₁ p₂ r₁ r₂) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁, hp₂], by disj 5; exact ⟨p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩⟩

lemma graph_and_inv {p₁ p₂ r : V} :
    c.Graph L param (p₁ ^⋏ p₂) r → ∃ r₁ r₂, c.Graph L param p₁ r₁ ∧ c.Graph L param p₂ r₂ ∧ r =
      c.and param p₁ p₂ r₁ r₂ := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
    ⟨_, _, _, _, _, _, H, rfl⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
  · simp [qqAnd, qqRel] at H
  · simp [qqAnd, qqNRel] at H
  · simp [qqAnd, qqVerum] at H
  · simp [qqAnd, qqFalsum] at H
  · rcases (by simpa [qqAnd] using H) with ⟨rfl, rfl, rfl⟩
    exact ⟨_, _, by assumption, by assumption, rfl⟩
  · simp [qqAnd, qqOr] at H
  · simp [qqAnd, qqAll] at H
  · simp [qqAnd, qqExs] at H

lemma graph_or {p₁ p₂ r₁ r₂ : V} (hp₁ : IsUFormula L p₁) (hp₂ : IsUFormula L p₂)
    (h₁ : c.Graph L param p₁ r₁) (h₂ : c.Graph L param p₂ r₂) :
    c.Graph L param (p₁ ^⋎ p₂) (c.or param p₁ p₂ r₁ r₂) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁, hp₂], by disj 6; exact ⟨p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩⟩

lemma graph_or_inv {p₁ p₂ r : V} :
    c.Graph L param (p₁ ^⋎ p₂) r → ∃ r₁ r₂, c.Graph L param p₁ r₁ ∧ c.Graph L param p₂ r₂ ∧ r =
      c.or param p₁ p₂ r₁ r₂ := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
    ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, rfl⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
  · simp [qqOr, qqRel] at H
  · simp [qqOr, qqNRel] at H
  · simp [qqOr, qqVerum] at H
  · simp [qqOr, qqFalsum] at H
  · simp [qqOr, qqAnd] at H
  · rcases (by simpa [qqOr] using H) with ⟨rfl, rfl, rfl⟩
    exact ⟨_, _, by assumption, by assumption, rfl⟩
  · simp [qqOr, qqAll] at H
  · simp [qqOr, qqExs] at H

lemma graph_all {p₁ ys : V} (hp₁ : IsUFormula L p₁) (hl : len ys = c.allSize param p₁)
    (h₁ : ∀ i < c.allSize param p₁, c.Graph L (c.allChanges param i) p₁ ys.[i]) :
    c.Graph L param (^∀ p₁) (c.all param p₁ ys) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁], by disj 7; exact ⟨p₁, ys, ⟨hl, h₁⟩, rfl, rfl⟩⟩

lemma graph_all_inv {p₁ r : V} :
    c.Graph L param (^∀ p₁) r → ∃ ys, (len ys = c.allSize param p₁ ∧
      ∀ i < c.allSize param p₁, c.Graph L (c.allChanges param i) p₁ ys.[i]) ∧ r = c.all param p₁ ys
      := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
    ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, rfl⟩ | ⟨_, _, _, H, _⟩)⟩
  · simp [qqAll, qqRel] at H
  · simp [qqAll, qqNRel] at H
  · simp [qqAll, qqVerum] at H
  · simp [qqAll, qqFalsum] at H
  · simp [qqAll, qqAnd] at H
  · simp [qqAll, qqOr] at H
  · rcases (by simpa [qqAll] using H) with ⟨rfl, rfl⟩
    exact ⟨_, by assumption, rfl⟩
  · simp [qqAll, qqExs] at H

lemma graph_ex {p₁ ys : V} (hp₁ : IsUFormula L p₁) (hl : len ys = c.exsSize param p₁)
    (h₁ : ∀ i < c.exsSize param p₁, c.Graph L (c.exsChanges param i) p₁ ys.[i]) :
    c.Graph L param (^∃ p₁) (c.exs param p₁ ys) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁], by disj 8; exact ⟨p₁, ys, ⟨hl, h₁⟩, rfl, rfl⟩⟩

lemma graph_ex_inv {p₁ r : V} :
    c.Graph L param (^∃ p₁) r → ∃ ys, (len ys = c.exsSize param p₁ ∧
      ∀ i < c.exsSize param p₁, c.Graph L (c.exsChanges param i) p₁ ys.[i]) ∧ r = c.exs param p₁ ys
      := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
    ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, rfl⟩)⟩
  · simp [qqExs, qqRel] at H
  · simp [qqExs, qqNRel] at H
  · simp [qqExs, qqVerum] at H
  · simp [qqExs, qqFalsum] at H
  · simp [qqExs, qqAnd] at H
  · simp [qqExs, qqOr] at H
  · simp [qqExs, qqAll] at H
  · rcases (by simpa [qqExs] using H) with ⟨rfl, rfl⟩
    exact ⟨_, by assumption, rfl⟩

variable (param)

lemma graph_exists {p : V} : IsUFormula L p → ∃ y, c.Graph L param p y := fun hp ↦
  ⟨_, (c.graph_iff L).mpr ⟨hp, rfl⟩⟩

lemma graph_unique {p : V} : IsUFormula L p → ∀ {param r r'}, c.Graph L param p r → c.Graph L param
    p r' → r = r' := by
  intro _ _ _ _ h h'
  rw [((c.graph_iff L).mp h).2, ((c.graph_iff L).mp h').2]

lemma exists_unique {p : V} (hp : IsUFormula L p) : ∃! r, c.Graph L param p r := by
  rcases c.graph_exists param hp with ⟨r, hr⟩
  exact ExistsUnique.intro r hr (fun r' hr' ↦ c.graph_unique hp hr' hr)

variable (L)

lemma exists_unique_all (p : V) : ∃! r, (IsUFormula L p → c.Graph L param p r) ∧ (¬IsUFormula L p →
  r = 0) := by
  by_cases hp : IsUFormula L p <;> simp [hp, exists_unique]

noncomputable def result (p : V) : V := Classical.choose! (c.exists_unique_all L param p)

variable {L}

lemma result_prop {p : V} (hp : IsUFormula L p) : c.Graph L param p (c.result L param p) :=
  Classical.choose!_spec (c.exists_unique_all L param p) |>.1 hp

lemma result_prop_not {p : V} (hp : ¬IsUFormula L p) : c.result L param p = 0 :=
  Classical.choose!_spec (c.exists_unique_all L param p) |>.2 hp

variable {param}

lemma result_eq_of_graph {p r} (h : c.Graph L param p r) : c.result L param p = r := Eq.symm <|
  Classical.choose_uniq (c.exists_unique_all L param p) (by simp [c.graph_dom_uformula h, h])

@[simp] lemma result_rel {k R v} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    c.result L param (^rel k R v) = c.rel param k R v :=
  c.result_eq_of_graph (c.graph_rel hR hv)

@[simp] lemma result_nrel {k R v} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    c.result L param (^nrel k R v) = c.nrel param k R v :=
  c.result_eq_of_graph (c.graph_nrel hR hv)

@[simp] lemma result_verum : c.result L param ^⊤ = c.verum param := c.result_eq_of_graph
  c.graph_verum

@[simp] lemma result_falsum : c.result L param ^⊥ = c.falsum param := c.result_eq_of_graph
  c.graph_falsum

@[simp] lemma result_and {p q}
    (hp : IsUFormula L p) (hq : IsUFormula L q) :
    c.result L param (p ^⋏ q) = c.and param p q (c.result L param p) (c.result L param q) :=
  c.result_eq_of_graph (c.graph_and hp hq (c.result_prop param hp) (c.result_prop param hq))

@[simp] lemma result_or {p q}
    (hp : IsUFormula L p) (hq : IsUFormula L q) :
    c.result L param (p ^⋎ q) = c.or param p q (c.result L param p) (c.result L param q) :=
  c.result_eq_of_graph (c.graph_or hp hq (c.result_prop param hp) (c.result_prop param hq))

@[simp] lemma result_all {p} (hp : IsUFormula L p) (hs : c.allSize param p = 1) :
    c.result L param (^∀ p) = c.all param p ?[c.result L (c.allChanges param 0) p] :=
  c.result_eq_of_graph (c.graph_all hp (by simp [hs]) fun i hi ↦ by
    rcases lt_one_iff_eq_zero.mp (hs ▸ hi); simpa using c.result_prop _ hp)

@[simp] lemma result_exs {p} (hp : IsUFormula L p) (hs : c.exsSize param p = 1) :
    c.result L param (^∃ p) = c.exs param p ?[c.result L (c.exsChanges param 0) p] :=
  c.result_eq_of_graph (c.graph_ex hp (by simp [hs]) fun i hi ↦ by
    rcases lt_one_iff_eq_zero.mp (hs ▸ hi); simpa using c.result_prop _ hp)

open Classical in
lemma result_eq_ite (param p : V) :
    c.result L param p = if IsUFormula L p then c.courseOfValuesResult param p else 0 := by
  by_cases hp : IsUFormula L p
  · simp [hp, ((c.graph_iff L).mp (c.result_prop param hp)).2]
  · simp [hp, c.result_prop_not param hp]

open Classical in
variable (L) in
lemma result_locallyDelta0 :
    LocallyDelta0Function fun w : Fin 2 → V ↦ c.result L (w 0) (w 1) := by
  have : (fun w : Fin 2 → V ↦ c.result L (w 0) (w 1)) = fun w ↦
      if IsUFormula L (w 1) then c.courseOfValuesResult (w 0) (w 1) else 0 :=
    funext fun w ↦ c.result_eq_ite _ _
  rw [this]
  exact LocallyDelta0Function.ite
    ((isUFormula_locallyDelta0 (L := L)).pred_comp (LocallyDelta0Function.var 1))
    c.courseOfValuesResult_locallyDelta0 (LocallyDelta0Function.const 0)

section

lemma result_defined : 𝚺ᴬ₁-Function₂ c.result L via β.result L := .mk fun v ↦ by
  simp [Blueprint.result, result, c.eval_graphDef]

instance result_definable : 𝚺ᴬ_[0 + 1]-Function₂ c.result L := c.result_defined.to_definable

end

lemma uformula_result_induction {P : V → V → V → Prop}
    (hP : LocallyDelta0 fun w : Fin 3 → V ↦ P (w 0) (w 1) (w 2))
    (hRel : ∀ param k R v, L.IsRel k R → IsUTermVec L k v → P param (^rel k R v) (c.rel param k R
      v))
    (hNRel : ∀ param k R v, L.IsRel k R → IsUTermVec L k v → P param (^nrel k R v) (c.nrel param k
      R v))
    (hverum : ∀ param, P param ^⊤ (c.verum param))
    (hfalsum : ∀ param, P param ^⊥ (c.falsum param))
    (hand : ∀ param p q, IsUFormula L p → IsUFormula L q →
      P param p (c.result L param p) → P param q (c.result L param q) → P param (p ^⋏ q) (c.and
        param p q (c.result L param p) (c.result L param q)))
    (hor : ∀ param p q, IsUFormula L p → IsUFormula L q →
      P param p (c.result L param p) → P param q (c.result L param q) → P param (p ^⋎ q) (c.or
        param p q (c.result L param p) (c.result L param q)))
    (hall : ∀ param p, IsUFormula L p →
      (∀ i < c.allSize param p,
        P (c.allChanges param i) p (c.result L (c.allChanges param i) p)) →
      P param (^∀ p) (c.result L param (^∀ p)))
    (hexs : ∀ param p, IsUFormula L p →
      (∀ i < c.exsSize param p,
        P (c.exsChanges param i) p (c.result L (c.exsChanges param i) p)) →
      P param (^∃ p) (c.result L param (^∃ p))) :
    ∀ {param p : V}, IsUFormula L p → P param p (c.result L param p) := by
  intro param p hp
  have hQ : LocallyDelta0Pred fun p' ↦ ∀ d ≤ p, d + p' ≤ p → IsUFormula L p' →
      P (c.iter param d) p' (c.result L (c.iter param d) p') := by
    have v2 : ∀ i : Fin 2, LocallyDelta0Function fun w : Fin 2 → V ↦ w i :=
      LocallyDelta0Function.var
    have hi : LocallyDelta0Function fun w : Fin 2 → V ↦ c.iter param (w 0) :=
      c.iter_locallyDelta0.comp₂ (LocallyDelta0Function.const param) (v2 0)
    have hR := hP.comp₃ hi (v2 1) ((c.result_locallyDelta0 L).comp₂ hi (v2 1))
    have := LocallyDelta0.ball_le_function (LocallyDelta0Function.const p) <|
      (LocallyDelta0.le (LocallyDelta0Function.add.comp₂ (v2 0) (v2 1))
        (LocallyDelta0Function.const p)).imp <|
      ((isUFormula_locallyDelta0 (L := L)).pred_comp (v2 1)).imp hR
    exact this.of_iff fun w ↦ by simp
  have : ∀ p', ∀ d ≤ p, d + p' ≤ p → IsUFormula L p' →
      P (c.iter param d) p' (c.result L (c.iter param d) p') := by
    apply LocallyDelta0Pred.order_induction hQ
    intro p' ih d hd hdp hu
    have hsub {p₁ e : V} (hp₁ : p₁ < p') (he : e ≤ 1) (hu₁ : IsUFormula L p₁) :
        P (c.iter param (d + e)) p₁ (c.result L (c.iter param (d + e)) p₁) := by
      have h₁ : d + e + p₁ ≤ p := by
        refine le_trans ?_ hdp
        calc d + e + p₁ ≤ d + (1 + p₁) := by rw [add_assoc]; gcongr
          _ = d + (p₁ + 1) := by rw [add_comm 1 p₁]
          _ ≤ d + p' := by gcongr; exact lt_iff_succ_le.mp hp₁
      exact ih p₁ hp₁ (d + e) (le_trans le_self_add h₁) h₁ hu₁
    rcases IsUFormula.case hu with
      (⟨k, R, v, hkR, hv, rfl⟩ | ⟨k, R, v, hkR, hv, rfl⟩ | rfl | rfl |
        ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩)
    · simpa [hkR, hv] using hRel (c.iter param d) k R v hkR hv
    · simpa [hkR, hv] using hNRel (c.iter param d) k R v hkR hv
    · simpa using hverum (c.iter param d)
    · simpa using hfalsum (c.iter param d)
    · simpa [c.result_and hp₁ hp₂] using hand (c.iter param d) p₁ p₂ hp₁ hp₂
        (by simpa using hsub (by simp) zero_le hp₁) (by simpa using hsub (by simp) zero_le hp₂)
    · simpa [c.result_or hp₁ hp₂] using hor (c.iter param d) p₁ p₂ hp₁ hp₂
        (by simpa using hsub (by simp) zero_le hp₁) (by simpa using hsub (by simp) zero_le hp₂)
    · refine hall (c.iter param d) p₁ hp₁ fun i hi ↦ ?_
      rw [c.allSize_eq_one] at hi
      rcases lt_one_iff_eq_zero.mp hi
      have := hsub (by simp) le_rfl hp₁
      rwa [c.iter_succ, ← c.allChanges_eq_change _ 0] at this
    · refine hexs (c.iter param d) p₁ hp₁ fun i hi ↦ ?_
      rw [c.exsSize_eq_one] at hi
      rcases lt_one_iff_eq_zero.mp hi
      have := hsub (by simp) le_rfl hp₁
      rwa [c.iter_succ, ← c.exsChanges_eq_change _ 0] at this
  have := this p 0 zero_le (by simp) hp
  rwa [c.iter_zero] at this

end Construction

end UformulaRec1

section bv

variable {Γ : Polarity} {m : ℕ}

lemma termBVVec_of_not {k v : V} (h : ¬IsUTermVec L k v) : termBVVec L k v = 0 :=
  IsUTerm.BV.construction.resultVec_of_not L _ h

lemma termBV_le {t : V} : termBV L t ≤ t := by
  by_cases ht : IsUTerm L t
  · have h : IsUTerm.BV.construction.courseOfValuesResult ![] t ≤ t :=
      IsUTerm.BV.construction.courseOfValuesResult_le_bound ![] t
    simpa [termBV, IsUTerm.BV.construction.result_eq_ite (L := L) (param := ![]) t, ht] using h
  · simp [termBV, IsUTerm.BV.construction.result_prop_not L _ ht]

lemma termBVVec_eq_listMap {k v : V} (hv : IsUTermVec L k v) :
    termBVVec L k v = listMap (fun (_ : Fin 0 → V) t ↦ termBV L t) ![] v := by
  have hg : LocallyDelta0Function fun w : Fin (0 + 1) → V ↦ termBV L (w 0) :=
    termBV_locallyDelta0.comp₁ (LocallyDelta0Function.var 0)
  rw [listMap_eq_iff hg]
  refine ⟨by rw [len_termBVVec hv, hv.lh], fun i hi ↦ ?_⟩
  rw [nth_termBVVec hv (by simpa [hv.lh] using hi)]

open Classical in
lemma termBVVec_locallyDelta0 : LocallyDelta0Function₂ (termBVVec (V := V) L) := by
  have hg : LocallyDelta0Function fun w : Fin (0 + 1) → V ↦ termBV L (w 0) :=
    termBV_locallyDelta0.comp₁ (LocallyDelta0Function.var 0)
  have : (fun w : Fin 2 → V ↦ termBVVec L (w 0) (w 1)) = fun w ↦
      if IsUTermVec L (w 0) (w 1) then
        listMap (fun (_ : Fin 0 → V) t ↦ termBV L t) ![] (w 1) else 0 := by
    funext w
    by_cases h : IsUTermVec L (w 0) (w 1)
    · simp only [h, ↓reduceIte, termBVVec_eq_listMap h]
    · simp [h, termBVVec_of_not h]
  change LocallyDelta0Function fun w : Fin 2 → V ↦ termBVVec L (w 0) (w 1)
  have hlm : LocallyDelta0Function fun w : Fin 2 → V ↦
      listMap (fun (_ : Fin 0 → V) t ↦ termBV L t) ![] (w 1) := by
    have := (listMap_locallyDelta0 (g := fun (_ : Fin 0 → V) t ↦ termBV L t) hg).comp_cons
      (LocallyDelta0Function.var (1 : Fin 2)) (u := fun j : Fin 0 ↦ j.elim0)
    simpa [Matrix.empty_eq] using this
  rw [this]
  exact LocallyDelta0Function.ite
    (isUTermVec_locallyDelta0.rel_comp₂ (LocallyDelta0Function.var 0) (LocallyDelta0Function.var 1))
    hlm (LocallyDelta0Function.const 0)


namespace BV

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.BV (blueprint) in
variable (L) in
/-- The recursion on formulas computing the least bound for their bound variables. -/
noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel {_} := fun k _ v ↦ listMax (termBVVec L k v)
  nrel {_} := fun k _ v ↦ listMax (termBVVec L k v)
  verum {_} := 0
  falsum {_} := 0
  and {_} := fun _ _ y₁ y₂ ↦ Max.max y₁ y₂
  or {_} := fun _ _ y₁ y₂ ↦ Max.max y₁ y₂
  all {_} := fun _ ys ↦ ys.[0] - 1
  exs {_} := fun _ ys ↦ ys.[0] - 1
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  rel_locallyDelta0 := listMax_locallyDelta0.comp₁ (termBVVec_locallyDelta0.comp₂
    (LocallyDelta0Function.var (1 : Fin 4)) (LocallyDelta0Function.var (3 : Fin 4)))
  nrel_locallyDelta0 := listMax_locallyDelta0.comp₁ (termBVVec_locallyDelta0.comp₂
    (LocallyDelta0Function.var (1 : Fin 4)) (LocallyDelta0Function.var (3 : Fin 4)))
  verum_locallyDelta0 := LocallyDelta0Function.const 0
  falsum_locallyDelta0 := LocallyDelta0Function.const 0
  and_locallyDelta0 := LocallyDelta0Function.max.comp₂ (LocallyDelta0Function.var (3 : Fin 5))
    (LocallyDelta0Function.var (4 : Fin 5))
  or_locallyDelta0 := LocallyDelta0Function.max.comp₂ (LocallyDelta0Function.var (3 : Fin 5))
    (LocallyDelta0Function.var (4 : Fin 5))
  all_locallyDelta0 := LocallyDelta0Function.sub.comp₂ (nth_locallyDelta0.comp₂
    (LocallyDelta0Function.var (2 : Fin 3)) (LocallyDelta0Function.const 0))
    (LocallyDelta0Function.const 1)
  exs_locallyDelta0 := LocallyDelta0Function.sub.comp₂ (nth_locallyDelta0.comp₂
    (LocallyDelta0Function.var (2 : Fin 3)) (LocallyDelta0Function.const 0))
    (LocallyDelta0Function.const 1)
  bound _ p := p
  rel_le_bound _ k R v := by
    refine listMaxss_le fun i hi ↦ ?_
    by_cases hv : IsUTermVec L k v
    · have hi : i < k := by simpa [hv] using hi
      rw [nth_termBVVec hv hi]
      exact termBV_le.trans (nth_lt_qqRel_of_lt (by rw [← hv.lh]; exact hi)).le
    · simp [termBVVec_of_not hv] at hi
  nrel_le_bound _ k R v := by
    refine listMaxss_le fun i hi ↦ ?_
    by_cases hv : IsUTermVec L k v
    · have hi : i < k := by simpa [hv] using hi
      rw [nth_termBVVec hv hi]
      exact termBV_le.trans (nth_lt_qqNRel_of_lt (by rw [← hv.lh]; exact hi)).le
    · simp [termBVVec_of_not hv] at hi
  verum_le_bound _ := zero_le
  falsum_le_bound _ := zero_le
  and_le_bound _ p₁ p₂ _ _ h₁ h₂ :=
    max_le (h₁.trans (lt_K!_left p₁ p₂).le) (h₂.trans (lt_K!_right p₁ p₂).le)
  or_le_bound _ p₁ p₂ _ _ h₁ h₂ :=
    max_le (h₁.trans (lt_or_left p₁ p₂).le) (h₂.trans (lt_or_right p₁ p₂).le)
  all_le_bound _ p₁ y h := by simpa using (sub_le_self y 1).trans (h.trans (lt_forall p₁).le)
  exs_le_bound _ p₁ y h := by simpa using (sub_le_self y 1).trans (h.trans (lt_exists p₁).le)
  bound_monotone _ _ _ h := h
  bound_locallyDelta0 := LocallyDelta0Function.var (1 : Fin 2)

end BV


open BV

variable (L)

/-- The least `n` such that all bound variables in the code `p` of a formula are below `n`. -/
noncomputable def bv (p : V) : V := (BV.construction L).result L 0 p

variable {L}

section

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (bvGraph)

instance bv.defined : 𝚺ᴬ₁-Function₁ bv (V := V) L via bvGraph L := .mk fun v ↦ by
  simpa [bvGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using! (BV.construction
    L).result_defined.defined ![v 0, 0, v 1]

instance bv.definable : 𝚺ᴬ₁-Function₁ bv (V := V) L := bv.defined.to_definable

instance bv.definable' : Γᴬ_[m + 1]-Function₁ bv (V := V) L := bv.definable.of_sigmaOne

end

lemma bv_locallyDelta0 : LocallyDelta0Function₁ (bv (V := V) L) :=
  ((BV.construction L).result_locallyDelta0 L).comp₂ (LocallyDelta0Function.const 0)
    (LocallyDelta0Function.var 0)

@[simp] lemma bv_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    bv L (^rel k R v) = listMax (termBVVec L k v) := by simp [bv, hR, hv, BV.construction]

@[simp] lemma bv_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    bv L (^nrel k R v) = listMax (termBVVec L k v) := by simp [bv, hR, hv, BV.construction]

@[simp] lemma bv_verum : bv L (^⊤ : V) = 0 := by simp [bv, BV.construction]

@[simp] lemma bv_falsum : bv L (^⊥ : V) = 0 := by simp [bv, BV.construction]

@[simp] lemma bv_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    bv L (p ^⋏ q) = Max.max (bv L p) (bv L q) := by simp [bv, hp, hq, BV.construction]

@[simp] lemma bv_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    bv L (p ^⋎ q) = Max.max (bv L p) (bv L q) := by simp [bv, hp, hq, construction]

@[simp] lemma bv_all {p : V} (hp : IsUFormula L p) : bv L (^∀ p) = bv L p - 1 := by
  simp [bv, hp, construction]

@[simp] lemma bv_ex {p : V} (hp : IsUFormula L p) : bv L (^∃ p) = bv L p - 1 := by
  simp [bv, hp, construction]

lemma bv_eq_of_not_isUFormula {p : V} (h : ¬IsUFormula L p) : bv L p = 0 :=
  (construction L).result_prop_not _ h

end bv

section isSemiformula

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (isSemiformula)

variable {Γ : Polarity} {m : ℕ}

variable (L)

/-- The code `p` is a formula of the language `L` whose bound variables are all below `n`. -/
structure IsSemiformula (n p : V) : Prop where
  isUFormula : IsUFormula L p
  bv_le : bv L p ≤ n

/-- The code `p` is a formula of the language `L` without free bound variables. -/
abbrev IsFormula (p : V) : Prop := IsSemiformula L 0 p

variable {L}

lemma isSemiformula_iff {n p : V} :
    IsSemiformula L n p ↔ IsUFormula L p ∧ bv L p ≤ n :=
  ⟨fun h ↦ ⟨h.isUFormula, h.bv_le⟩, by rintro ⟨hp, h⟩; exact ⟨hp, h⟩⟩

lemma isSemiformula_locallyDelta0 : LocallyDelta0Rel (IsSemiformula (V := V) L) := by
  have h : LocallyDelta0 fun w : Fin 2 → V ↦ IsUFormula L (w 1) ∧ bv L (w 1) ≤ w 0 :=
    (isUFormula_locallyDelta0.pred_comp (LocallyDelta0Function.var 1)).and
      (LocallyDelta0.le (bv_locallyDelta0.comp₁ (LocallyDelta0Function.var 1))
        (LocallyDelta0Function.var 0))
  exact h.of_iff fun w ↦ isSemiformula_iff

section

instance IsSemiformula.defined : 𝚫ᴬ₁-Relation IsSemiformula (V := V) L via isSemiformula L := .mk <|
  by
  constructor
  · intro v; simp [isSemiformula, Bounding.HierarchySymbol.Semiformula.val_sigma, bv.defined.iff]
  · intro v; simp [isSemiformula, Bounding.HierarchySymbol.Semiformula.val_sigma, bv.defined.iff,
    isSemiformula_iff]

instance IsSemiformula.definable : 𝚫ᴬ₁-Relation IsSemiformula (V := V) L :=
  IsSemiformula.defined.to_definable

instance IsSemiformula.definable' : Γᴬ_[m + 1]-Relation IsSemiformula (V := V) L :=
  IsSemiformula.definable.of_deltaOne

end

@[simp] lemma IsUFormula.isSemiformula {p : V} (h : IsUFormula L p) : IsSemiformula L (bv L p) p
  where
  isUFormula := h
  bv_le := by rfl

@[simp] lemma IsSemiformula.rel {n k r v : V} :
    IsSemiformula L n (^rel k r v) ↔ L.IsRel k r ∧ IsSemitermVec L k n v := by
  constructor
  · intro h
    have hrv : L.IsRel k r ∧ IsUTermVec L k v := by simpa using h.isUFormula
    exact ⟨hrv.1, hrv.2, fun {i} hi ↦ by
      have : listMax (termBVVec L k v) ≤ n := by simpa [hrv] using h.bv_le
      exact le_trans (le_trans (by simp_all) (nth_le_listMax (i := i) (by simp_all))) this⟩
  · rintro ⟨hr, hv⟩
    exact ⟨by simp [hr, hv.isUTerm], by
      rw [bv_rel hr hv.isUTerm]
      apply listMaxss_le
      intro i hi
      have := hv.bv (i := i) (by simpa [hv.isUTerm] using hi)
      rwa [nth_termBVVec hv.isUTerm (by simpa [hv.isUTerm] using hi)]⟩

@[simp] lemma IsSemiformula.nrel {n k r v : V} :
    IsSemiformula L n (^nrel k r v) ↔ L.IsRel k r ∧ IsSemitermVec L k n v := by
  constructor
  · intro h
    have hrv : L.IsRel k r ∧ IsUTermVec L k v := by simpa using h.isUFormula
    exact ⟨hrv.1, hrv.2, fun {i} hi ↦ by
      have : listMax (termBVVec L k v) ≤ n := by simpa [hrv] using h.bv_le
      exact le_trans (le_trans (by simp_all) (nth_le_listMax (i := i) (by simp_all))) this⟩
  · rintro ⟨hr, hv⟩
    exact ⟨by simp [hr, hv.isUTerm], by
      rw [bv_nrel hr hv.isUTerm]
      apply listMaxss_le
      intro i hi
      have := hv.bv (i := i) (by simpa [hv.isUTerm] using hi)
      rwa [nth_termBVVec hv.isUTerm (by simpa [hv.isUTerm] using hi)]⟩

@[simp] lemma IsSemiformula.verum {n : V} : IsSemiformula L n ^⊤ := ⟨by simp, by simp⟩

@[simp] lemma IsSemiformula.falsum {n : V} : IsSemiformula L n ^⊥ := ⟨by simp, by simp⟩

@[simp] lemma IsSemiformula.and {n p q : V} :
    IsSemiformula L n (p ^⋏ q) ↔ IsSemiformula L n p ∧ IsSemiformula L n q := by
  constructor
  · intro h
    have hpq : IsUFormula L p ∧ IsUFormula L q := by simpa using h.isUFormula
    have hbv : bv L p ≤ n ∧ bv L q ≤ n := by simpa [hpq] using h.bv_le
    exact ⟨⟨hpq.1, hbv.1⟩, ⟨hpq.2, hbv.2⟩⟩
  · rintro ⟨hp, hq⟩
    exact ⟨by simp [hp.isUFormula, hq.isUFormula], by simp [hp.isUFormula, hq.isUFormula, hp.bv_le,
      hq.bv_le]⟩

@[simp] lemma IsSemiformula.or {n p q : V} :
    IsSemiformula L n (p ^⋎ q) ↔ IsSemiformula L n p ∧ IsSemiformula L n q := by
  constructor
  · intro h
    have hpq : IsUFormula L p ∧ IsUFormula L q := by simpa using h.isUFormula
    have hbv : bv L p ≤ n ∧ bv L q ≤ n := by simpa [hpq] using h.bv_le
    exact ⟨⟨hpq.1, hbv.1⟩, ⟨hpq.2, hbv.2⟩⟩
  · rintro ⟨hp, hq⟩
    exact ⟨by simp [hp.isUFormula, hq.isUFormula], by simp [hp.isUFormula, hq.isUFormula, hp.bv_le,
      hq.bv_le]⟩

@[simp] lemma IsSemiformula.all {n p : V} :
    IsSemiformula L n (^∀ p) ↔ IsSemiformula L (n + 1) p := by
  constructor
  · intro h
    exact ⟨by simpa using h.isUFormula, by
      simpa [show IsUFormula L p by simpa using h.isUFormula] using h.bv_le⟩
  · intro h
    exact ⟨by simp [h.isUFormula], by simp [h.isUFormula, h.bv_le]⟩

@[simp] lemma IsSemiformula.exs {n p : V} :
    IsSemiformula L n (^∃ p) ↔ IsSemiformula L (n + 1) p := by
  constructor
  · intro h
    exact ⟨by simpa using h.isUFormula, by
      simpa [show IsUFormula L p by simpa using h.isUFormula] using h.bv_le⟩
  · intro h
    exact ⟨by simp [h.isUFormula], by simp [h.isUFormula, h.bv_le]⟩

lemma IsSemiformula.case_iff {n p : V} :
    IsSemiformula L n p ↔
    (∃ k R v, L.IsRel k R ∧ IsSemitermVec L k n v ∧ p = ^rel k R v) ∨
    (∃ k R v, L.IsRel k R ∧ IsSemitermVec L k n v ∧ p = ^nrel k R v) ∨
    (p = ^⊤) ∨
    (p = ^⊥) ∨
    (∃ p₁ p₂, IsSemiformula L n p₁ ∧ IsSemiformula L n p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, IsSemiformula L n p₁ ∧ IsSemiformula L n p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (∃ p₁, IsSemiformula L (n + 1) p₁ ∧ p = ^∀ p₁) ∨
    (∃ p₁, IsSemiformula L (n + 1) p₁ ∧ p = ^∃ p₁) := by
  constructor
  · intro h
    rcases h.isUFormula.case with
      (⟨k, r, v, _, _, rfl⟩ | ⟨k, r, v, _, _, rfl⟩ | rfl | rfl | ⟨p₁, p₂, _, _, rfl⟩ | ⟨p₁, p₂, _,
        _, rfl⟩ | ⟨p₁, _, rfl⟩ | ⟨p₁, _, rfl⟩)
    · have : L.IsRel k r ∧ IsSemitermVec L k n v := by simpa using h
      disj 1; exact ⟨k, r, v, by simp [this]⟩;
    · have : L.IsRel k r ∧ IsSemitermVec L k n v := by simpa using h
      disj 2; exact ⟨k, r, v, by simp [this]⟩;
    · disj 3; rfl;
    · disj 4; rfl;
    · have : IsSemiformula L n p₁ ∧ IsSemiformula L n p₂ := by simpa using h
      disj 5; exact ⟨p₁, p₂, by simp [this]⟩;
    · have : IsSemiformula L n p₁ ∧ IsSemiformula L n p₂ := by simpa using h
      disj 6; exact ⟨p₁, p₂, by simp [this]⟩;
    · have : IsSemiformula L (n + 1) p₁ := by simpa using h
      disj 7; exact ⟨p₁, by simp [this]⟩;
    · have : IsSemiformula L (n + 1) p₁ := by simpa using h
      disj 8; exact ⟨p₁, by simp [this]⟩;
  · rintro (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ |
    ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩) <;> simp [*]

lemma IsSemiformula.case {P : V → V → Prop} {n p} (hp : IsSemiformula L n p)
    (hrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^rel k r v))
    (hnrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^nrel k r v))
    (hverum : ∀ n, P n ^⊤)
    (hfalsum : ∀ n, P n ^⊥)
    (hand : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n (p ^⋏ q))
    (hor : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n (p ^⋎ q))
    (hall : ∀ n p, IsSemiformula L (n + 1) p → P n (^∀ p))
    (hexs : ∀ n p, IsSemiformula L (n + 1) p → P n (^∃ p)) : P n p := by
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂,
      h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · exact hrel _ _ _ _ hR hv
  · exact hnrel _ _ _ _ hR hv
  · exact hverum n
  · exact hfalsum n
  · exact hand _ _ _ h₁ h₂
  · exact hor _ _ _ h₁ h₂
  · exact hall _ _ h₁
  · exact hexs _ _ h₁

/-- Structural induction on semiformulas for locally $\Delta_0$ predicates. -/
lemma IsSemiformula.induction {P : V → V → Prop} (hP : LocallyDelta0Rel P)
    (hrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^rel k r v))
    (hnrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^nrel k r v))
    (hverum : ∀ n, P n ^⊤)
    (hfalsum : ∀ n, P n ^⊥)
    (hand : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, IsSemiformula L (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hexs : ∀ n p, IsSemiformula L (n + 1) p → P (n + 1) p → P n (^∃ p)) {n p} :
    IsSemiformula L n p → P n p := by
  intro hnp
  have hQ : LocallyDelta0Pred fun p' ↦
      ∀ m ≤ n + p, m + p' ≤ n + p → IsSemiformula L m p' → P m p' := by
    have v2 : ∀ i : Fin 2, LocallyDelta0Function fun w : Fin 2 → V ↦ w i :=
      LocallyDelta0Function.var
    have := LocallyDelta0.ball_le_function (LocallyDelta0Function.const (n + p)) <|
      (LocallyDelta0.le (LocallyDelta0Function.add.comp₂ (v2 0) (v2 1))
        (LocallyDelta0Function.const (n + p))).imp <|
      (((isSemiformula_locallyDelta0 (L := L)).rel_comp₂ (v2 0) (v2 1)).imp
        (hP.comp₂ (v2 0) (v2 1)))
    exact this.of_iff fun w ↦ by simp
  have : ∀ p', ∀ m ≤ n + p, m + p' ≤ n + p → IsSemiformula L m p' → P m p' := by
    apply LocallyDelta0Pred.order_induction hQ
    intro p' ih m hm hmp h
    have hsub {p₁ e : V} (hp₁ : p₁ < p') (he : e ≤ 1) (h₁ : IsSemiformula L (m + e) p₁) :
        P (m + e) p₁ := by
      have h₂ : m + e + p₁ ≤ n + p := by
        refine le_trans ?_ hmp
        calc m + e + p₁ ≤ m + (1 + p₁) := by rw [add_assoc]; gcongr
          _ = m + (p₁ + 1) := by rw [add_comm 1 p₁]
          _ ≤ m + p' := by gcongr; exact lt_iff_succ_le.mp hp₁
      exact ih p₁ hp₁ (m + e) (le_trans le_self_add h₂) h₂ h₁
    rcases IsSemiformula.case_iff.mp h with
      (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ |
        ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
    · exact hrel _ _ _ _ hR hv
    · exact hnrel _ _ _ _ hR hv
    · exact hverum m
    · exact hfalsum m
    · exact hand _ _ _ h₁ h₂ (by simpa using hsub (by simp) zero_le (by simpa using h₁))
        (by simpa using hsub (by simp) zero_le (by simpa using h₂))
    · exact hor _ _ _ h₁ h₂ (by simpa using hsub (by simp) zero_le (by simpa using h₁))
        (by simpa using hsub (by simp) zero_le (by simpa using h₂))
    · exact hall _ _ h₁ (hsub (by simp) le_rfl h₁)
    · exact hexs _ _ h₁ (hsub (by simp) le_rfl h₁)
  exact this p n le_self_add le_rfl hnp

lemma IsSemiformula.pos {n p : V} (h : IsSemiformula L n p) : 0 < p := h.isUFormula.pos

@[simp] lemma IsSemiformula.not_zero (m : V) : ¬IsSemiformula L m (0 : V) := by intro h; simpa
  using h.pos

end isSemiformula

namespace UformulaRec1.Construction

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.UformulaRec1 (Blueprint)

variable {β : Blueprint} {c : Construction V β} {param : V}

lemma semiformula_result_induction {P : V → V → V → V → Prop}
    (hP : LocallyDelta0 fun w : Fin 4 → V ↦ P (w 0) (w 1) (w 2) (w 3))
    (hRel : ∀ n param k R v, L.IsRel k R → IsSemitermVec L k n v → P param n (^rel k R v) (c.rel
      param k R v))
    (hNRel : ∀ n param k R v, L.IsRel k R → IsSemitermVec L k n v → P param n (^nrel k R v) (c.nrel
      param k R v))
    (hverum : ∀ n param, P param n ^⊤ (c.verum param))
    (hfalsum : ∀ n param, P param n ^⊥ (c.falsum param))
    (hand : ∀ n param p q, IsSemiformula L n p → IsSemiformula L n q →
      P param n p (c.result L param p) → P param n q (c.result L param q) → P param n (p ^⋏ q)
        (c.and param p q (c.result L param p) (c.result L param q)))
    (hor : ∀ n param p q, IsSemiformula L n p → IsSemiformula L n q →
      P param n p (c.result L param p) → P param n q (c.result L param q) → P param n (p ^⋎ q)
        (c.or param p q (c.result L param p) (c.result L param q)))
    (hall : ∀ n param p, IsSemiformula L (n + 1) p →
      (∀ i < c.allSize param p,
        P (c.allChanges param i) (n + 1) p (c.result L (c.allChanges param i) p)) →
      P param n (^∀ p) (c.result L param (^∀ p)))
    (hexs : ∀ n param p, IsSemiformula L (n + 1) p →
      (∀ i < c.exsSize param p,
        P (c.exsChanges param i) (n + 1) p (c.result L (c.exsChanges param i) p)) →
      P param n (^∃ p) (c.result L param (^∃ p))) :
    ∀ {param n p : V}, IsSemiformula L n p → P param n p (c.result L param p) := by
  intro param n p hnp
  have hQ : LocallyDelta0Pred fun p' ↦ ∀ d ≤ p, ∀ m ≤ n + p, d + p' ≤ p → m + p' ≤ n + p →
      IsSemiformula L m p' → P (c.iter param d) m p' (c.result L (c.iter param d) p') := by
    have v3 : ∀ i : Fin 3, LocallyDelta0Function fun w : Fin 3 → V ↦ w i :=
      LocallyDelta0Function.var
    have hi : LocallyDelta0Function fun w : Fin 3 → V ↦ c.iter param (w 1) :=
      c.iter_locallyDelta0.comp₂ (LocallyDelta0Function.const param) (v3 1)
    have hR : LocallyDelta0 fun w : Fin 3 → V ↦
        P (c.iter param (w 1)) (w 0) (w 2) (c.result L (c.iter param (w 1)) (w 2)) :=
      (hP.comp (f := ![fun w : Fin 3 → V ↦ c.iter param (w 1), fun w ↦ w 0, fun w ↦ w 2,
        fun w ↦ c.result L (c.iter param (w 1)) (w 2)])
        (Fin.forall_fin_succ.mpr ⟨hi, Fin.forall_fin_succ.mpr ⟨v3 0, Fin.forall_fin_succ.mpr
          ⟨v3 2, Fin.forall_fin_succ.mpr ⟨(c.result_locallyDelta0 L).comp₂ hi (v3 2),
            finZeroElim⟩⟩⟩⟩)).of_iff fun w ↦ by simp
    have h1 : LocallyDelta0 fun w : Fin 3 → V ↦ w 1 + w 2 ≤ p :=
      LocallyDelta0.le (LocallyDelta0Function.add.comp₂ (v3 1) (v3 2))
        (LocallyDelta0Function.const p)
    have h2 : LocallyDelta0 fun w : Fin 3 → V ↦ w 0 + w 2 ≤ n + p :=
      LocallyDelta0.le (LocallyDelta0Function.add.comp₂ (v3 0) (v3 2))
        (LocallyDelta0Function.const (n + p))
    have h3 : LocallyDelta0 fun w : Fin 3 → V ↦ IsSemiformula L (w 0) (w 2) :=
      (isSemiformula_locallyDelta0 (L := L)).rel_comp₂ (v3 0) (v3 2)
    have := LocallyDelta0.ball_le_function (LocallyDelta0Function.const p) <|
      LocallyDelta0.ball_le_function (LocallyDelta0Function.const (n + p)) <|
      h1.imp <| h2.imp <| h3.imp hR
    exact this.of_iff fun w ↦ by simp
  have : ∀ p', ∀ d ≤ p, ∀ m ≤ n + p, d + p' ≤ p → m + p' ≤ n + p →
      IsSemiformula L m p' → P (c.iter param d) m p' (c.result L (c.iter param d) p') := by
    apply LocallyDelta0Pred.order_induction hQ
    intro p' ih d hd m hm hdp hmp h
    have hsub {p₁ e : V} (hp₁ : p₁ < p') (he : e ≤ 1) (h₁ : IsSemiformula L (m + e) p₁) :
        P (c.iter param (d + e)) (m + e) p₁ (c.result L (c.iter param (d + e)) p₁) := by
      have hle : e + p₁ ≤ p' := by
        calc e + p₁ ≤ 1 + p₁ := by gcongr
          _ = p₁ + 1 := add_comm 1 p₁
          _ ≤ p' := lt_iff_succ_le.mp hp₁
      have h₂ : d + e + p₁ ≤ p := by
        refine le_trans ?_ hdp
        rw [add_assoc]; gcongr
      have h₃ : m + e + p₁ ≤ n + p := by
        refine le_trans ?_ hmp
        rw [add_assoc]; gcongr
      exact ih p₁ hp₁ (d + e) (le_trans le_self_add h₂) (m + e) (le_trans le_self_add h₃) h₂ h₃ h₁
    rcases IsSemiformula.case_iff.mp h with
      (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ |
        ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
    · simpa [hR, hv.isUTerm] using hRel m (c.iter param d) k R v hR hv
    · simpa [hR, hv.isUTerm] using hNRel m (c.iter param d) k R v hR hv
    · simpa using hverum m (c.iter param d)
    · simpa using hfalsum m (c.iter param d)
    · simpa [h₁.isUFormula, h₂.isUFormula] using hand m (c.iter param d) p₁ p₂ h₁ h₂
        (by simpa using hsub (by simp) zero_le (by simpa using h₁))
        (by simpa using hsub (by simp) zero_le (by simpa using h₂))
    · simpa [h₁.isUFormula, h₂.isUFormula] using hor m (c.iter param d) p₁ p₂ h₁ h₂
        (by simpa using hsub (by simp) zero_le (by simpa using h₁))
        (by simpa using hsub (by simp) zero_le (by simpa using h₂))
    · refine hall m (c.iter param d) p₁ h₁ fun i hi ↦ ?_
      rw [c.allSize_eq_one] at hi
      rcases lt_one_iff_eq_zero.mp hi
      have := hsub (by simp) le_rfl h₁
      rwa [c.iter_succ, ← c.allChanges_eq_change _ 0] at this
    · refine hexs m (c.iter param d) p₁ h₁ fun i hi ↦ ?_
      rw [c.exsSize_eq_one] at hi
      rcases lt_one_iff_eq_zero.mp hi
      have := hsub (by simp) le_rfl h₁
      rwa [c.iter_succ, ← c.exsChanges_eq_change _ 0] at this
  have := this p 0 zero_le n le_self_add (by simp) le_rfl hnp
  rwa [c.iter_zero] at this

end UformulaRec1.Construction

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping
