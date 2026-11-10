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
`qqRelDef`, …, `qqExsDef` and `isUFormula`.

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

end Construction

end UformulaRec1

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping
