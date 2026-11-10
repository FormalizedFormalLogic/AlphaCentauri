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

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping
