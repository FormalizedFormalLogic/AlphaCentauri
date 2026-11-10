module

public import AlphaCentauri.ToFoundation.ElementaryArithmetic.Bootstrapping.Syntax.Language
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Basic

/-!
# Codes of terms in models of $\mathsf{EA}$

The part of `Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Basic.lean` on codes of
terms, ported to models of $\mathsf{EA}$: the codes `qqBvar`, `qqFvar` and `qqFunc` of bound
variables, free variables and function applications, the predicate `IsUTerm L` of codes of
terms with induction on locally $\Delta_0$ predicates, and the predicate `IsUTermVec L` of
lists of terms. The formulas are Foundation's `qqBvarDef`, `qqFvarDef`, `qqFuncDef`,
`isUTerm` and `isUTermVec`.

- [HP98, §V.3]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (isUTerm isUTermVec)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]
  {L : Language} [L.Encodable] [L.LORDefinable]

section term

/-- The code of the bound variable `z`. -/
noncomputable def qqBvar (z : V) : V := ⟪0, z⟫ + 1

/-- The code of the free variable `x`. -/
noncomputable def qqFvar (x : V) : V := ⟪1, x⟫ + 1

/-- The code of the application of the function symbol `f` of arity `k` to the list `v`. -/
noncomputable def qqFunc (k f v : V) : V := ⟪2, k, f, v⟫ + 1

def qqFuncN (k f v : ℕ) : ℕ := (Nat.pair 2 <| Nat.pair k <| Nat.pair f v) + 1

scoped prefix:max "^#" => qqBvar

scoped prefix:max "^&" => qqFvar

scoped prefix:max "^func " => qqFunc

lemma qqFuncN_eq_qqFunc (k f v : ℕ) : qqFuncN k f v = qqFunc k f v := by
  simp [qqFunc, qqFuncN, nat_pair_eq]

@[simp] lemma var_lt_qqBvar (z : V) : z < ^#z := lt_succ_iff_le.mpr <| le_pair_right 0 z

@[simp] lemma var_lt_qqFvar (x : V) : x < ^&x := lt_succ_iff_le.mpr <| le_pair_right 1 x

@[simp] lemma arity_lt_qqFunc (k f v : V) : k < ^func k f v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right 2 k) <| pair_le_pair_right 2 <| le_pair_left k ⟪f, v⟫

@[simp] lemma func_lt_qqFunc (k f v : V) : f < ^func k f v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left f v) <|
    le_trans (le_pair_right k ⟪f, v⟫) <| le_pair_right 2 ⟪k, ⟪f, v⟫⟫

@[simp] lemma terms_lt_qqFunc (k f v : V) : v < ^func k f v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right f v) <|
    le_trans (le_pair_right k ⟪f, v⟫) <| le_pair_right 2 ⟪k, ⟪f, v⟫⟫

lemma nth_lt_qqFunc_of_lt {i k f v : V} (hi : i < len v) : v.[i] < ^func k f v :=
  lt_trans (nth_lt_self hi) (terms_lt_qqFunc _ _ _)

@[simp] lemma qqBvar_inj {z z' : V} : ^#z = ^#z' ↔ z = z' := by simp [qqBvar]

@[simp] lemma qqFvar_inj {x x' : V} : ^&x = ^&x' ↔ x = x' := by simp [qqFvar]

@[simp] lemma qqFunc_inj {k f v k' f' w : V} :
    ^func k f v = ^func k' f' w ↔ k = k' ∧ f = f' ∧ v = w := by simp [qqFunc]

instance qqBvar_defined : 𝚺ᴬ₀-Function₁ (qqBvar : V → V) via qqBvarDef :=
  .mk fun _ ↦ by simp_all [qqBvarDef, qqBvar]

instance qqFvar_defined : 𝚺ᴬ₀-Function₁ (qqFvar : V → V) via qqFvarDef :=
  .mk fun v ↦ by simp_all [qqFvarDef, qqFvar]

private lemma qqFunc_graph {x k f v : V} :
    x = ^func k f v ↔
      ∃ fv < x, fv = ⟪f, v⟫ ∧ ∃ kfv < x, kfv = ⟪k, fv⟫ ∧ ∃ x' < x, x' = ⟪2, kfv⟫ ∧ x = x' + 1 :=
  ⟨by rintro rfl
      exact ⟨⟪f, v⟫, lt_succ_iff_le.mpr <| le_trans (le_pair_right _ _) (le_pair_right _ _), rfl,
        ⟪k, f, v⟫, lt_succ_iff_le.mpr <| by simp, rfl,
        ⟪2, k, f, v⟫, by simp [qqFunc], rfl, rfl⟩,
   by rintro ⟨_, _, rfl, _, _, rfl, _, _, rfl, rfl⟩; rfl⟩

instance qqFunc_defined : 𝚺ᴬ₀-Function₃ (qqFunc : V → V → V → V) via qqFuncDef :=
  .mk fun v ↦ by simp [qqFuncDef, qqFunc_graph]

instance qqBvar_definable : 𝚺ᴬ₀-Function₁ (qqBvar : V → V) := qqBvar_defined.to_definable

instance qqFvar_definable : 𝚺ᴬ₀-Function₁ (qqFvar : V → V) := qqFvar_defined.to_definable

instance qqFunc_definable : 𝚺ᴬ₀-Function₃ (qqFunc : V → V → V → V) := qqFunc_defined.to_definable

instance qqBvar_bounded : Bounded₁ (qqBvar : V → V) :=
  ⟨‘z. (z + 1) * (z + 1) + 1’, fun w ↦ by
    simpa [qqBvar, sq] using pair_polybound 0 (w 0)⟩

instance qqFvar_bounded : Bounded₁ (qqFvar : V → V) :=
  ⟨‘x. (1 + x + 1) * (1 + x + 1) + 1’, fun w ↦ by
    simpa [qqFvar, sq] using pair_polybound 1 (w 0)⟩

instance qqFunc_bounded : Bounded₃ (qqFunc : V → V → V → V) :=
  ⟨‘k f v. (2 + (k + (f + v + 1) * (f + v + 1) + 1) * (k + (f + v + 1) * (f + v + 1) + 1) + 1) *
      (2 + (k + (f + v + 1) * (f + v + 1) + 1) * (k + (f + v + 1) * (f + v + 1) + 1) + 1) + 1’,
    fun w ↦ by
      have key (a b : V) : ⟪a, b⟫ ≤ (a + b + 1) * (a + b + 1) := by
        simpa [sq] using pair_polybound a b
      have h₁ := key (w 1) (w 2)
      have h₂ := le_trans (pair_le_pair_right (w 0) h₁)
        (key (w 0) ((w 1 + w 2 + 1) * (w 1 + w 2 + 1)))
      have h₃ := le_trans (pair_le_pair_right 2 h₂) (key 2 _)
      simpa [qqFunc] using add_le_add_right h₃ 1⟩

lemma qqBvar_locallyDelta0 : LocallyDelta0Function₁ (qqBvar : V → V) :=
  LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, qqBvar_definable⟩

lemma qqFvar_locallyDelta0 : LocallyDelta0Function₁ (qqFvar : V → V) :=
  LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, qqFvar_definable⟩

lemma qqFunc_locallyDelta0 :
    LocallyDelta0Function (k := 3) fun w : Fin 3 → V ↦ qqFunc (w 0) (w 1) (w 2) :=
  LocallyDelta0Function.of_definableBoundedFunction ⟨inferInstance, qqFunc_definable⟩

namespace FormalizedTerm

variable (L)

/-- The operator generating the codes of terms. -/
def Phi (C : Set V) (t : V) : Prop :=
  (∃ z, t = ^#z) ∨ (∃ x, t = ^&x) ∨
  (∃ k f v : V, L.IsFunc k f ∧ k = len v ∧ (∀ i < k, v.[i] ∈ C) ∧ t = ^func k f v)

private lemma phi_iff (C : V) (t : V) :
    Phi L {x | x ∈ C} t ↔
    (∃ z < t, t = ^#z) ∨
    (∃ x < t, t = ^&x) ∨
    (∃ k < t, ∃ f < t, ∃ v < t,
      L.IsFunc k f ∧ k = len v ∧ (∀ i < k, v.[i] ∈ C) ∧ t = ^func k f v) where
  mp := by
    rintro (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hkf, hk, hv, rfl⟩)
    · disj 1; exact ⟨z, lt_succ_iff_le.mpr <| by simp, rfl⟩
    · disj 2; exact ⟨x, lt_succ_iff_le.mpr <| by simp, rfl⟩
    · disj 3; exact ⟨k, by simp, f, by simp, v, by simp, hkf, hk, hv, rfl⟩
  mpr := by
    unfold Phi
    rintro (⟨z, _, rfl⟩ | ⟨x, _, rfl⟩ | ⟨k, _, f, _, v, _, hkf, hk, hv, rfl⟩)
    · disj 1; exact ⟨z, rfl⟩
    · disj 2; exact ⟨x, rfl⟩
    · disj 3; exact ⟨k, f, v, hkf, hk, hv, rfl⟩

lemma phi_locallyDelta0 :
    LocallyDelta0 fun w : Fin 2 → V ↦ Phi L {x | x ∈ w 1} (w 0) := by
  have hbvar : LocallyDelta0 fun y : Fin 3 → V ↦ y 1 = qqBvar (y 0) :=
    LocallyDelta0.eq (LocallyDelta0Function.var 1) <|
      qqBvar_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 3))
  have hfvar : LocallyDelta0 fun y : Fin 3 → V ↦ y 1 = qqFvar (y 0) :=
    LocallyDelta0.eq (LocallyDelta0Function.var 1) <|
      qqFvar_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 3))
  have hisFunc : LocallyDelta0 fun y : Fin 5 → V ↦ L.IsFunc (y 2) (y 1) :=
    (LocallyDelta0.of_definable (R := fun w : Fin 2 → V ↦ L.IsFunc (w 0) (w 1))
      (by definability)).comp₂ (LocallyDelta0Function.var 2) (LocallyDelta0Function.var 1)
  have hlen : LocallyDelta0 fun y : Fin 5 → V ↦ y 2 = len (y 0) :=
    LocallyDelta0.eq (LocallyDelta0Function.var 2) <|
      len_locallyDelta0.comp₁ (LocallyDelta0Function.var (0 : Fin 5))
  have hmem : LocallyDelta0 fun y : Fin 6 → V ↦ nth (y 1) (y 0) ∈ y 5 :=
    LocallyDelta0.mem (nth_locallyDelta0.comp₂ (LocallyDelta0Function.var 1)
      (LocallyDelta0Function.var 0)) (LocallyDelta0Function.var 5)
  have hall : LocallyDelta0 fun y : Fin 5 → V ↦ ∀ i < y 2, nth (y 0) i ∈ y 4 :=
    (LocallyDelta0.ball_lt_function (LocallyDelta0Function.var 2) hmem).of_iff
      fun y ↦ by simp
  have hfunc : LocallyDelta0 fun y : Fin 5 → V ↦ y 3 = qqFunc (y 2) (y 1) (y 0) :=
    LocallyDelta0.eq (LocallyDelta0Function.var 3) <|
      qqFunc_locallyDelta0.comp (f := ![fun y : Fin 5 → V ↦ y 2, fun y ↦ y 1, fun y ↦ y 0]) <|
        Fin.forall_fin_succ.mpr ⟨LocallyDelta0Function.var 2, Fin.forall_fin_succ.mpr
          ⟨LocallyDelta0Function.var 1, Fin.forall_fin_succ.mpr
            ⟨LocallyDelta0Function.var 0, finZeroElim⟩⟩⟩
  have hex₁ := LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var (0 : Fin 2)) hbvar
  have hex₂ := LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var (0 : Fin 2)) hfvar
  have hex₃ := LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var (0 : Fin 2)) <|
    LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 1) <|
      LocallyDelta0.bexs_lt_function (LocallyDelta0Function.var 2) <|
        hisFunc.and <| hlen.and <| hall.and hfunc
  exact (hex₁.or <| hex₂.or hex₃).of_iff fun w ↦ by simpa using phi_iff L (w 1) (w 0)

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.FormalizedTerm (blueprint) in
/-- The construction of the codes of terms. -/
def construction : Fixpoint.Construction V (blueprint L) where
  Φ := fun _ ↦ Phi L
  defined := ⟨by intro v; simp [blueprint], by intro v; simp [blueprint, phi_iff]⟩
  monotone := by
    rintro C C' hC _ x (h | h | ⟨k, f, v, hkf, hk, h, rfl⟩)
    · disj 1; exact h
    · disj 2; exact h
    · disj 3; exact ⟨k, f, v, hkf, hk, fun i hi ↦ hC (h i hi), rfl⟩
  Φ_locallyDelta0 := phi_locallyDelta0 L

instance : (construction L).StrongFinite V where
  strong_finite := by
    rintro C v x (h | h | ⟨k, f, v, hkf, hk, h, rfl⟩)
    · disj 1; exact h
    · disj 2; exact h
    · disj 3
      exact ⟨k, f, v, hkf, hk, fun i hi ↦ ⟨h i hi, lt_of_le_of_lt (nth_le _ _) (by simp)⟩, rfl⟩

end FormalizedTerm

open FormalizedTerm

variable (L)

/-- The predicate that `t` is the code of a term in the language `L`, possibly with
dangling bound variables. -/
def IsUTerm : V → Prop := (construction L).Fixpoint ![]

variable {L}

namespace IsUTerm

variable {Γ : Polarity} {m : ℕ}

instance defined : 𝚫ᴬ₁-Predicate (IsUTerm L (V := V)) via (isUTerm L) :=
  (construction L).fixpoint_definedΔ₁

instance definable : 𝚫ᴬ₁-Predicate (IsUTerm L (V := V)) := defined.to_definable

instance definable' (Γ) : Γᴬ_[m + 1]-Predicate (IsUTerm L (V := V)) := definable.of_deltaOne

end IsUTerm

lemma isUTerm_locallyDelta0 : LocallyDelta0Pred (IsUTerm L (V := V)) :=
  (construction L).fixpoint_locallyDelta0.of_iff fun w ↦
    iff_of_eq <| congrArg (fun u ↦ (construction L).Fixpoint u (w 0)) (Subsingleton.elim _ _)

variable (L)

/-- The predicate that `w` is the code of a list of `n` terms in the language `L`. -/
def IsUTermVec (n w : V) : Prop := n = len w ∧ ∀ i < n, IsUTerm L w.[i]

variable {L}

lemma isUTermVec_locallyDelta0 : LocallyDelta0Rel (IsUTermVec L (V := V)) := by
  have hlen : LocallyDelta0 fun w : Fin 2 → V ↦ w 0 = len (w 1) :=
    LocallyDelta0.eq (LocallyDelta0Function.var 0) <|
      len_locallyDelta0.comp₁ (LocallyDelta0Function.var (1 : Fin 2))
  have hterm : LocallyDelta0 fun y : Fin 3 → V ↦ IsUTerm L (nth (y 2) (y 0)) := by
    simpa using isUTerm_locallyDelta0.comp_cons
      (nth_locallyDelta0.comp₂ (LocallyDelta0Function.var (2 : Fin 3))
        (LocallyDelta0Function.var (0 : Fin 3))) (u := fun j ↦ j.elim0) fun j ↦ j.elim0
  exact hlen.and <| (LocallyDelta0.ball_lt_function (LocallyDelta0Function.var 0) hterm).of_iff
    fun w ↦ by simp

namespace IsUTermVec

variable {v : V}

protected lemma lh {n w : V} (h : IsUTermVec L n w) : n = len w := h.1

lemma nth {n w : V} (h : IsUTermVec L n w) {i} : i < n → IsUTerm L w.[i] := h.2 i

@[simp] lemma empty : IsUTermVec (V := V) L 0 0 := ⟨by simp, by simp⟩

@[simp] lemma empty_iff : IsUTermVec L 0 v ↔ v = 0 := by
  constructor
  · intro h
    exact len_zero_iff_eq_nil.mp h.lh.symm
  · rintro rfl
    simp

lemma two_iff {v : V} :
    IsUTermVec L 2 v ↔ ∃ t₁ t₂, IsUTerm L t₁ ∧ IsUTerm L t₂ ∧ v = ?[t₁, t₂] := by
  constructor
  · intro h
    rcases eq_doubleton_of_len_eq_two.mp h.lh.symm with ⟨t₁, t₂, rfl⟩
    exact ⟨t₁, t₂, by simpa using h.nth (show 0 < 2 by simp),
      by simpa using h.nth (show 1 < 2 by simp), rfl⟩
  · rintro ⟨t₁, t₂, h₁, h₂, rfl⟩
    exact ⟨by simp [one_add_one_eq_two],
      by simp [lt_two_iff_le_one, le_one_iff_eq_zero_or_one, h₁, h₂]⟩

@[simp] lemma adjoin {n w t : V} (h : IsUTermVec L n w) (ht : IsUTerm L t) :
    IsUTermVec L (n + 1) (t ∷ w) :=
  ⟨by simp [h.lh], fun i hi ↦ by
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simpa
    · simpa using h.nth (by simpa using hi)⟩

@[simp] lemma adjoin₁_iff {t : V} :
    IsUTermVec L 1 (?[t] : V) ↔ IsUTerm L t := by
  constructor
  · intro h
    simpa using h.nth (i := 0) (by simp)
  · intro h
    simpa using empty.adjoin h

@[simp] lemma mkSeq₂_iff {t₁ t₂ : V} :
    IsUTermVec L 2 (?[t₁, t₂] : V) ↔ IsUTerm L t₁ ∧ IsUTerm L t₂ := by
  constructor
  · intro h
    exact ⟨by simpa using h.nth (i := 0) (by simp), by simpa using h.nth (i := 1) (by simp)⟩
  · rintro ⟨h₁, h₂⟩
    simpa [one_add_one_eq_two] using (adjoin₁_iff.mpr h₂).adjoin h₁

section

instance defined : 𝚫ᴬ₁-Relation (IsUTermVec (V := V) L) via (isUTermVec L) :=
  ⟨by intro v; simp [isUTermVec, Bounding.HierarchySymbol.Semiformula.val_sigma,
    IsUTerm.defined.proper.iff'],
   by intro v; simp [isUTermVec, Bounding.HierarchySymbol.Semiformula.val_sigma, IsUTermVec]⟩

instance definable : 𝚫ᴬ₁-Relation (IsUTermVec (V := V) L) := defined.to_definable

instance definable' (Γ) {m : ℕ} : Γᴬ_[m + 1]-Relation (IsUTermVec (V := V) L) :=
  definable.of_deltaOne

end

end IsUTermVec

namespace IsUTerm

lemma case_iff {t : V} :
    IsUTerm L t ↔
    (∃ z, t = ^#z) ∨
    (∃ x, t = ^&x) ∨
    (∃ k f v : V, L.IsFunc k f ∧ IsUTermVec L k v ∧ t = ^func k f v) := by
  simpa [construction, Phi, IsUTermVec, and_assoc] using! (construction L).case

alias ⟨case, mk⟩ := case_iff

@[simp] lemma bvar {z : V} : IsUTerm L ^#z :=
  mk (by disj 1; exact ⟨z, rfl⟩)

@[simp] lemma fvar (x : V) : IsUTerm L ^&x :=
  mk (by disj 2; exact ⟨x, rfl⟩)

@[simp] lemma func_iff {k f v : V} :
    IsUTerm L (^func k f v) ↔ L.IsFunc k f ∧ IsUTermVec L k v :=
  ⟨by intro h
      rcases h.case with (⟨_, h⟩ | ⟨x, h⟩ | ⟨k', f', w, hkf, ⟨hk, hv⟩, h⟩)
      · simp [qqFunc, qqBvar] at h
      · simp [qqFunc, qqFvar] at h
      · rcases (show k = k' ∧ f = f' ∧ v = w by simpa [qqFunc] using h) with ⟨rfl, rfl, rfl⟩
        exact ⟨hkf, hk, hv⟩,
   by rintro ⟨hkf, hk, hv⟩; apply mk; disj 3; exact ⟨k, f, v, hkf, ⟨hk, hv⟩, rfl⟩⟩

lemma func {k f v : V} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    IsUTerm L (^func k f v) := func_iff.mpr ⟨hkf, hv⟩

lemma induction {P : V → Prop} (hP : LocallyDelta0Pred P)
    (hbvar : ∀ z, P (^#z)) (hfvar : ∀ x, P (^&x))
    (hfunc : ∀ k f v, L.IsFunc k f → IsUTermVec L k v → (∀ i < k, P v.[i]) → P (^func k f v)) :
    ∀ t, IsUTerm L t → P t :=
  (construction L).induction (v := ![]) hP (by
    rintro C hC x (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hkf, hk, h, rfl⟩)
    · exact hbvar z
    · exact hfvar x
    · exact hfunc k f v hkf ⟨hk, fun i hi ↦ hC _ (h i hi) |>.1⟩ (fun i hi ↦ hC _ (h i hi) |>.2))

end IsUTerm

end term

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping
