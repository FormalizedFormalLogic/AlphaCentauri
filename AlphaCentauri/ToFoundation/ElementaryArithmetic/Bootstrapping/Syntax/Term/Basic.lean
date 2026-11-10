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
`isUTerm` and `isUTermVec`. The recursion `termBV` computing the least bound of the bound
variables and the predicates `IsSemiterm` and `IsSemitermVec` follow, with the formulas
`termBVGraph`, `isSemiterm` and `isSemitermVec`.

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

section structuralBound

variable {c : V}

private lemma exp_exp_le_of_le {m n : V} (h : m ≤ n) :
    Exp.exp (Exp.exp m) ≤ Exp.exp (Exp.exp n) :=
  exp_monotone_le.mpr (exp_monotone_le.mpr h)

/-- A list whose elements are bounded by `Exp.exp (Exp.exp (8 * vᵢ + c))` for the elements `vᵢ`
of a list `v` of the same length is bounded by `Exp.exp (Exp.exp (8 * v + c))`. -/
lemma le_exp_exp_of_nth_le_exp_exp (hc : 1 ≤ c) {v w : V} (hl : len w = len v)
    (h : ∀ i < len v, w.[i] ≤ Exp.exp (Exp.exp (8 * v.[i] + c))) :
    w ≤ Exp.exp (Exp.exp (8 * v + c)) := by
  have hG' {n : ℕ} {g : (Fin n → V) → V} (hg : LocallyDelta0Function g) :
      LocallyDelta0Function fun u ↦ Exp.exp (Exp.exp (8 * g u + c)) :=
    LocallyDelta0Function.exp.comp₁ <| LocallyDelta0Function.exp.comp₁ <|
      LocallyDelta0Function.add.comp₂
        (LocallyDelta0Function.mul.comp₂ (LocallyDelta0Function.const 8) hg)
        (LocallyDelta0Function.const c)
  set W := w
  have hP : LocallyDelta0Pred fun v ↦ ∀ w ≤ W, len w = len v →
      (∀ i < len v, w.[i] ≤ Exp.exp (Exp.exp (8 * v.[i] + c))) →
        w ≤ Exp.exp (Exp.exp (8 * v + c)) := by
    have hentry : LocallyDelta0 fun x : Fin 3 → V ↦
        x 0 < len (x 2) → (x 1).[x 0] ≤ Exp.exp (Exp.exp (8 * (x 2).[x 0] + c)) :=
      (LocallyDelta0.lt (LocallyDelta0Function.var 0)
        (len_locallyDelta0.comp₁ (LocallyDelta0Function.var 2))).imp
        (LocallyDelta0.le (nth_locallyDelta0.comp₂ (LocallyDelta0Function.var 1)
          (LocallyDelta0Function.var 0))
          (hG' (nth_locallyDelta0.comp₂ (LocallyDelta0Function.var 2)
            (LocallyDelta0Function.var 0))))
    have hall := LocallyDelta0.ball_le_function
      (len_locallyDelta0.comp₁ (LocallyDelta0Function.var (V := V) (1 : Fin 2))) hentry
    have hbody : LocallyDelta0 fun y : Fin 2 → V ↦ len (y 0) = len (y 1) →
        (∀ i ≤ len (y 1), i < len (y 1) →
          (y 0).[i] ≤ Exp.exp (Exp.exp (8 * (y 1).[i] + c))) →
        y 0 ≤ Exp.exp (Exp.exp (8 * y 1 + c)) :=
      (LocallyDelta0.eq (len_locallyDelta0.comp₁ (LocallyDelta0Function.var 0))
        (len_locallyDelta0.comp₁ (LocallyDelta0Function.var 1))).imp
        (hall.imp (LocallyDelta0.le (LocallyDelta0Function.var 0)
          (hG' (LocallyDelta0Function.var 1))))
    exact (LocallyDelta0.ball_le_function (LocallyDelta0Function.const W) hbody).of_iff
      fun u ↦ by
        simp only [Matrix.cons_val_zero]
        constructor
        · intro H w hw hl h; exact H w hw hl fun i hi ↦ h i hi.le hi
        · intro H w hw hl h; exact H w hw hl fun i _ hi ↦ h i hi
  have : ∀ v, ∀ w ≤ W, len w = len v →
      (∀ i < len v, w.[i] ≤ Exp.exp (Exp.exp (8 * v.[i] + c))) →
        w ≤ Exp.exp (Exp.exp (8 * v + c)) := by
    apply adjoin_induction hP
    · intro w _ hl _
      simp [show w = 0 by simpa using hl]
    · intro x v ih w hw hl h
      rcases nil_or_adjoin w with (rfl | ⟨a, w', rfl⟩)
      · exact zero_le
      have hl' : len w' = len v := by simpa using hl
      have ha : a ≤ Exp.exp (Exp.exp (8 * x + c)) := by simpa using h 0 (by simp)
      have hw' : w' ≤ Exp.exp (Exp.exp (8 * v + c)) :=
        ih w' (le_trans (lt_adjoin' a w').le hw) hl' fun i hi ↦ by
          simpa using h (i + 1) (by simpa using hi)
      set m := max x v
      have hm : 8 * m + c + 2 ≤ 8 * (x ∷ v) + c := by
        have : m + 1 ≤ x ∷ v := succ_le_iff_lt.mpr (max_lt (by simp) (by simp))
        have h28 : (2 : V) ≤ 8 := by
          have : ((2 : ℕ) : V) ≤ ((8 : ℕ) : V) := by exact_mod_cast (by norm_num : 2 ≤ 8)
          simpa using this
        calc 8 * m + c + 2 ≤ 8 * m + c + 8 := add_le_add_right h28 _
          _ = 8 * (m + 1) + c := by grind
          _ ≤ 8 * (x ∷ v) + c := by gcongr
      apply le_trans _ (exp_exp_le_of_le hm)
      apply adjoin_le_exp_exp (le_trans hc le_add_self)
      · exact le_trans ha (exp_exp_le_of_le (by gcongr; exact le_max_left x v))
      · exact le_trans hw' (exp_exp_le_of_le (by gcongr; exact le_max_right x v))
  exact this v w le_rfl hl h

/-- `^func k f w` is bounded by `Exp.exp (Exp.exp (8 * ^func k f v + c))` when `w` is bounded by
`Exp.exp (Exp.exp (8 * v + c))`. -/
lemma qqFunc_le_exp_exp (hc : 1 ≤ c) {k f v w : V} (hw : w ≤ Exp.exp (Exp.exp (8 * v + c))) :
    ^func k f w ≤ Exp.exp (Exp.exp (8 * ^func k f v + c)) := by
  set m := max k (max f v)
  set E := Exp.exp (Exp.exp (8 * m + c))
  have hpa (a b : V) : ⟪a, b⟫ ≤ a ∷ b := by rw [adjoin_def]; exact le_self_add
  have hn : (1 : V) ≤ 8 * m + c := le_trans hc le_add_self
  have hmle : m ≤ 8 * m + c :=
    le_trans (le_mul_of_one_le_left (by simp) (by norm_num)) le_self_add
  have hk : k ≤ E := le_exp_exp (le_trans (le_max_left _ _) hmle)
  have hf : f ≤ E := le_exp_exp (le_trans (le_trans (le_max_left f v) (le_max_right _ _)) hmle)
  have hw' : w ≤ E :=
    le_trans hw (exp_exp_le_of_le (by gcongr; exact le_trans (le_max_right f v) (le_max_right _ _)))
  have h₁ : ⟪f, w⟫ ≤ Exp.exp (Exp.exp (8 * m + c + 2)) :=
    le_trans (hpa f w) (adjoin_le_exp_exp hn hf hw')
  have h₂ : ⟪k, ⟪f, w⟫⟫ ≤ Exp.exp (Exp.exp (8 * m + c + 2 + 2)) :=
    le_trans (hpa _ _) (adjoin_le_exp_exp (le_trans hn le_self_add)
      (le_trans hk (exp_exp_le_of_le le_self_add)) h₁)
  have h₃ : ^func k f w ≤ Exp.exp (Exp.exp (8 * m + c + 2 + 2 + 2)) := by
    have : ^func k f w = 2 ∷ ⟪k, ⟪f, w⟫⟫ := rfl
    rw [this]
    apply adjoin_le_exp_exp (le_trans hn (le_trans le_self_add le_self_add))
    · exact le_exp_exp le_add_self
    · exact h₂
  apply le_trans h₃ (exp_exp_le_of_le _)
  have : m + 1 ≤ ^func k f v :=
    succ_le_iff_lt.mpr (max_lt (by simp) (max_lt (by simp) (by simp)))
  have h68 : (2 : V) + 2 + 2 ≤ 8 := by
    rw [show (2 : V) + 2 + 2 = 6 by norm_num]
    exact_mod_cast (by norm_num : (6 : ℕ) ≤ 8)
  calc 8 * m + c + 2 + 2 + 2 = (8 * m + c) + (2 + 2 + 2) := by simp only [add_assoc]
    _ ≤ (8 * m + c) + 8 := add_le_add_right h68 _
    _ = 8 * (m + 1) + c := by grind
    _ ≤ 8 * ^func k f v + c := by gcongr

lemma qqFunc_le_exp_exp_of_nth_le (hc : 1 ≤ c) {k f v w : V} (hv : k = len v) (hw : k = len w)
    (h : ∀ i < k, w.[i] ≤ Exp.exp (Exp.exp (8 * v.[i] + c))) :
    ^func k f w ≤ Exp.exp (Exp.exp (8 * ^func k f v + c)) :=
  qqFunc_le_exp_exp hc <| le_exp_exp_of_nth_le_exp_exp hc (by rw [← hw, ← hv]) fun i hi ↦
    h i (by rwa [hv])

lemma le_exp_exp_eight_mul_add (a c : V) : a ≤ Exp.exp (Exp.exp (8 * a + c)) :=
  le_exp_exp <| le_trans (le_mul_of_one_le_left (by simp) (by norm_num)) le_self_add

end structuralBound

end term

namespace Language.TermRec

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.Language.TermRec (Blueprint)

variable (V)

/-- A recursion on terms in a model of $\mathsf{EA}$, with a monotone bound on its values. -/
structure Construction {k : ℕ} (φ : Blueprint k) where
  bvar : (Fin k → V) → V → V
  fvar : (Fin k → V) → V → V
  func : (Fin k → V) → V → V → V → V → V
  bvar_defined : 𝚺ᴬ₁.DefinedFunction (fun v ↦ bvar (v ·.succ) (v 0)) φ.bvar
  fvar_defined : 𝚺ᴬ₁.DefinedFunction (fun v ↦ fvar (v ·.succ) (v 0)) φ.fvar
  func_defined :
    𝚺ᴬ₁.DefinedFunction (fun v ↦ func (v ·.succ.succ.succ.succ) (v 0) (v 1) (v 2) (v 3)) φ.func
  bvar_locallyDelta0 : LocallyDelta0Function fun v : Fin (k + 1) → V ↦ bvar (v ·.succ) (v 0)
  fvar_locallyDelta0 : LocallyDelta0Function fun v : Fin (k + 1) → V ↦ fvar (v ·.succ) (v 0)
  func_locallyDelta0 : LocallyDelta0Function fun v : Fin (k + 4) → V ↦
    func (v ·.succ.succ.succ.succ) (v 0) (v 1) (v 2) (v 3)
  /-- `c.bound param t` bounds the value at the term `t`. -/
  bound : (Fin k → V) → V → V
  bvar_le_bound : ∀ param z, bvar param z ≤ bound param (^#z)
  fvar_le_bound : ∀ param x, fvar param x ≤ bound param (^&x)
  func_le_bound : ∀ param (k f v w : V), k = len v → k = len w →
    (∀ i < k, w.[i] ≤ bound param v.[i]) → func param k f v w ≤ bound param (^func k f v)
  bound_monotone : ∀ param {s t}, s ≤ t → bound param s ≤ bound param t
  bound_locallyDelta0 : LocallyDelta0Function fun v : Fin (k + 1) → V ↦ bound (v ·.succ) (v 0)

variable {V} (L)

namespace Construction

variable {arity : ℕ} {β : Blueprint arity} (c : Construction V β)

/-- The rules generating the graph `⟪t, y⟫` of the recursion. -/
def Phi (param : Fin arity → V) (C : Set V) (pr : V) : Prop :=
  IsUTerm L (π₁ pr) ∧
  ( (∃ z, pr = ⟪^#z, c.bvar param z⟫) ∨
    (∃ x, pr = ⟪^&x, c.fvar param x⟫) ∨
    (∃ k f v w : V,
      (k = len w ∧ ∀ i < k, ⟪v.[i], w.[i]⟫ ∈ C) ∧ pr = ⟪^func k f v, c.func param k f v w⟫) )

private lemma phi_iff (param : Fin arity → V) (C pr : V) :
    c.Phi L param {x | x ∈ C} pr ↔
    ∃ t ≤ pr, ∃ y ≤ pr, pr = ⟪t, y⟫ ∧ IsUTerm L t ∧
    ( (∃ z < t, t = ^#z ∧ y = c.bvar param z) ∨
      (∃ x < t, t = ^&x ∧ y = c.fvar param x) ∨
      (∃ k < t, ∃ f < t, ∃ v < t, ∃ w ≤ repeatVec C k,
        (k = len w ∧ ∀ i < k, ⟪v.[i], w.[i]⟫ ∈ C) ∧
        t = ^func k f v ∧ y = c.func param k f v w) ) := by
  constructor
  · rintro ⟨ht, H⟩
    refine ⟨π₁ pr, by simp, π₂ pr, by simp, by simp, ht, ?_⟩
    rcases H with (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, w, ⟨hk, hw⟩, hk, rfl⟩)
    · disj 1; exact ⟨z, by simp⟩
    · disj 2; exact ⟨x, by simp⟩
    · disj 3
      refine ⟨k, by simp, f, by simp, v, by simp, w, ?_, ⟨hk, hw⟩, by simp⟩
      rcases hk
      exact len_repeatVec_of_nth_le fun i hi ↦ le_of_lt <| lt_of_mem_rng <| hw i hi
  · rintro ⟨t, _, y, _, rfl, ht, H⟩
    refine ⟨by simpa using ht, ?_⟩
    rcases H with
      (⟨z, _, rfl, rfl⟩ | ⟨x, _, rfl, rfl⟩ | ⟨k, _, f, _, v, _, w, _, ⟨hk, hw⟩, rfl, rfl⟩)
    · disj 1; exact ⟨z, rfl⟩
    · disj 2; exact ⟨x, rfl⟩
    · disj 3; exact ⟨k, f, v, w, ⟨hk, fun i hi ↦ hw i hi⟩, rfl⟩

/-- The rules in a form that reads the term off its code by projections. -/
private lemma phi_iff_decode (param : Fin arity → V) (C pr : V) :
    c.Phi L param {x | x ∈ C} pr ↔ IsUTerm L (π₁ pr) ∧
    ( (π₁ (π₁ pr - 1) = 0 ∧ π₂ pr = c.bvar param (π₂ (π₁ pr - 1))) ∨
      (π₁ (π₁ pr - 1) = 1 ∧ π₂ pr = c.fvar param (π₂ (π₁ pr - 1))) ∨
      (π₁ (π₁ pr - 1) = 2 ∧ ∃ w ≤ repeatVec C (π₁ (π₂ (π₁ pr - 1))),
        (π₁ (π₂ (π₁ pr - 1)) = len w ∧ ∀ i < π₁ (π₂ (π₁ pr - 1)),
          ⟪(π₂ (π₂ (π₂ (π₁ pr - 1)))).[i], w.[i]⟫ ∈ C) ∧
        π₂ pr = c.func param (π₁ (π₂ (π₁ pr - 1))) (π₁ (π₂ (π₂ (π₁ pr - 1))))
          (π₂ (π₂ (π₂ (π₁ pr - 1)))) w) ) := by
  constructor
  · rintro ⟨ht, H⟩
    refine ⟨ht, ?_⟩
    rcases H with (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, w, ⟨hk, hw⟩, rfl⟩)
    · disj 1; simp [qqBvar]
    · disj 2; simp [qqFvar]
    · disj 3
      simp only [pi₁_pair, qqFunc, add_tsub_cancel_right, pi₂_pair, true_and]
      refine ⟨w, ?_, ⟨hk, hw⟩, rfl⟩
      rcases hk
      exact len_repeatVec_of_nth_le fun i hi ↦ le_of_lt <| lt_of_mem_rng <| hw i hi
  · rintro ⟨ht, H⟩
    refine ⟨ht, ?_⟩
    have hpr : pr = ⟪π₁ pr, π₂ pr⟫ := by simp
    rcases IsUTerm.case ht with (⟨z, hz⟩ | ⟨x, hx⟩ | ⟨k, f, v, _, _, hkfv⟩)
    · rw [hz] at H
      rcases H with (⟨_, hy⟩ | ⟨h, _⟩ | ⟨h, _⟩)
      · disj 1; exact ⟨z, by rw [hpr, hz, hy]; simp [qqBvar]⟩
      · simp [qqBvar] at h
      · simp [qqBvar] at h
    · rw [hx] at H
      rcases H with (⟨h, _⟩ | ⟨_, hy⟩ | ⟨h, _⟩)
      · simp [qqFvar] at h
      · disj 2; exact ⟨x, by rw [hpr, hx, hy]; simp [qqFvar]⟩
      · simp [qqFvar] at h
    · rw [hkfv] at H
      rcases H with (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, w, _, ⟨hk, hw⟩, hy⟩)
      · simp [qqFunc] at h
      · simp [qqFunc] at h
      · simp only [qqFunc, add_tsub_cancel_right, pi₂_pair, pi₁_pair] at hk hw hy
        disj 3
        exact ⟨k, f, v, w, ⟨hk, hw⟩, by rw [hpr, hkfv, hy]⟩

private lemma pred_comp {n : ℕ} {P : V → Prop} {g : (Fin n → V) → V} (hP : LocallyDelta0Pred P)
    (hg : LocallyDelta0Function g) : LocallyDelta0 fun u ↦ P (g u) :=
  (hP.comp (f := fun _ ↦ g) fun _ ↦ hg).of_iff fun _ ↦ Iff.rfl

private lemma pi₁_comp {n : ℕ} {g : (Fin n → V) → V} (hg : LocallyDelta0Function g) :
    LocallyDelta0Function fun u ↦ π₁ (g u) := LocallyDelta0Function.pi₁.comp₁ hg

private lemma pi₂_comp {n : ℕ} {g : (Fin n → V) → V} (hg : LocallyDelta0Function g) :
    LocallyDelta0Function fun u ↦ π₂ (g u) := LocallyDelta0Function.pi₂.comp₁ hg

private lemma pred_sub_comp {n : ℕ} {g : (Fin n → V) → V} (hg : LocallyDelta0Function g) :
    LocallyDelta0Function fun u ↦ g u - 1 :=
  LocallyDelta0Function.sub.comp₂ hg (LocallyDelta0Function.const 1)

lemma phi_locallyDelta0 :
    LocallyDelta0 fun w : Fin (arity + 2) → V ↦ c.Phi L (w ·.succ.succ) {x | x ∈ w 1} (w 0) := by
  -- the code of the term, its tag, and its body, as functions of the pair `pr`
  have hm {n : ℕ} (j : Fin n) : LocallyDelta0Function fun u : Fin n → V ↦ π₁ (u j) - 1 :=
    pred_sub_comp (pi₁_comp (LocallyDelta0Function.var j))
  have hb {n : ℕ} (j : Fin n) : LocallyDelta0Function fun u : Fin n → V ↦ π₂ (π₁ (u j) - 1) :=
    pi₂_comp (hm j)
  have hk {n : ℕ} (j : Fin n) :
      LocallyDelta0Function fun u : Fin n → V ↦ π₁ (π₂ (π₁ (u j) - 1)) := pi₁_comp (hb j)
  have hf {n : ℕ} (j : Fin n) :
      LocallyDelta0Function fun u : Fin n → V ↦ π₁ (π₂ (π₂ (π₁ (u j) - 1))) :=
    pi₁_comp (pi₂_comp (hb j))
  have hv {n : ℕ} (j : Fin n) :
      LocallyDelta0Function fun u : Fin n → V ↦ π₂ (π₂ (π₂ (π₁ (u j) - 1))) :=
    pi₂_comp (pi₂_comp (hb j))
  have hterm : LocallyDelta0 fun w : Fin (arity + 2) → V ↦ IsUTerm L (π₁ (w 0)) :=
    pred_comp isUTerm_locallyDelta0 (pi₁_comp (LocallyDelta0Function.var 0))
  have hbvar : LocallyDelta0 fun w : Fin (arity + 2) → V ↦
      π₁ (π₁ (w 0) - 1) = 0 ∧ π₂ (w 0) = c.bvar (w ·.succ.succ) (π₂ (π₁ (w 0) - 1)) := by
    apply LocallyDelta0.and
    · exact LocallyDelta0.eq (pi₁_comp (hm 0)) (LocallyDelta0Function.const 0)
    · apply LocallyDelta0.eq (pi₂_comp (LocallyDelta0Function.var 0))
      simpa using c.bvar_locallyDelta0.comp_cons (hb 0) fun j ↦
        LocallyDelta0Function.var j.succ.succ
  have hfvar : LocallyDelta0 fun w : Fin (arity + 2) → V ↦
      π₁ (π₁ (w 0) - 1) = 1 ∧ π₂ (w 0) = c.fvar (w ·.succ.succ) (π₂ (π₁ (w 0) - 1)) := by
    apply LocallyDelta0.and
    · exact LocallyDelta0.eq (pi₁_comp (hm 0)) (LocallyDelta0Function.const 1)
    · apply LocallyDelta0.eq (pi₂_comp (LocallyDelta0Function.var 0))
      simpa using c.fvar_locallyDelta0.comp_cons (hb 0) fun j ↦
        LocallyDelta0Function.var j.succ.succ
  have hentry : LocallyDelta0 fun x : Fin (arity + 4) → V ↦
      ⟪(π₂ (π₂ (π₂ (π₁ (x 2) - 1)))).[x 0], (x 1).[x 0]⟫ ∈ x 3 :=
    LocallyDelta0.mem (LocallyDelta0Function.pairing.comp₂
      (nth_locallyDelta0.comp₂ (hv 2) (LocallyDelta0Function.var 0))
      (nth_locallyDelta0.comp₂ (LocallyDelta0Function.var 1) (LocallyDelta0Function.var 0)))
      (LocallyDelta0Function.var 3)
  have hfunc' : LocallyDelta0Function fun u : Fin (arity + 3) → V ↦
      c.func (fun j ↦ u j.succ.succ.succ) (π₁ (π₂ (π₁ (u 1) - 1))) (π₁ (π₂ (π₂ (π₁ (u 1) - 1))))
        (π₂ (π₂ (π₂ (π₁ (u 1) - 1)))) (u 0) := by
    have := c.func_locallyDelta0.comp
      (f := (fun u : Fin (arity + 3) → V ↦ π₁ (π₂ (π₁ (u 1) - 1))) :>
        (fun u ↦ π₁ (π₂ (π₂ (π₁ (u 1) - 1)))) :> (fun u ↦ π₂ (π₂ (π₂ (π₁ (u 1) - 1)))) :>
          (fun u ↦ u 0) :> fun j u ↦ u j.succ.succ.succ) fun i ↦ by
        cases i using Fin.cases with
        | zero => exact hk 1
        | succ i =>
          cases i using Fin.cases with
          | zero => exact hf 1
          | succ i =>
            cases i using Fin.cases with
            | zero => exact hv 1
            | succ i =>
              cases i using Fin.cases with
              | zero => exact LocallyDelta0Function.var 0
              | succ i => exact LocallyDelta0Function.var i.succ.succ.succ
    simpa using this
  have hbody : LocallyDelta0 fun u : Fin (arity + 3) → V ↦
      (π₁ (π₂ (π₁ (u 1) - 1)) = len (u 0) ∧ ∀ i < π₁ (π₂ (π₁ (u 1) - 1)),
        ⟪(π₂ (π₂ (π₂ (π₁ (u 1) - 1)))).[i], (u 0).[i]⟫ ∈ u 2) ∧
      π₂ (u 1) = c.func (fun j ↦ u j.succ.succ.succ) (π₁ (π₂ (π₁ (u 1) - 1)))
        (π₁ (π₂ (π₂ (π₁ (u 1) - 1)))) (π₂ (π₂ (π₂ (π₁ (u 1) - 1)))) (u 0) := by
    apply LocallyDelta0.and
    · apply LocallyDelta0.and
      · exact LocallyDelta0.eq (hk 1) (len_locallyDelta0.comp₁ (LocallyDelta0Function.var 0))
      · exact LocallyDelta0.ball_lt_function (hk 1) hentry
    · exact LocallyDelta0.eq (pi₂_comp (LocallyDelta0Function.var 1)) hfunc'
  have hfunc : LocallyDelta0 fun w : Fin (arity + 2) → V ↦
      π₁ (π₁ (w 0) - 1) = 2 ∧ ∃ w' ≤ repeatVec (w 1) (π₁ (π₂ (π₁ (w 0) - 1))),
        (π₁ (π₂ (π₁ (w 0) - 1)) = len w' ∧ ∀ i < π₁ (π₂ (π₁ (w 0) - 1)),
          ⟪(π₂ (π₂ (π₂ (π₁ (w 0) - 1)))).[i], w'.[i]⟫ ∈ w 1) ∧
        π₂ (w 0) = c.func (w ·.succ.succ) (π₁ (π₂ (π₁ (w 0) - 1)))
          (π₁ (π₂ (π₂ (π₁ (w 0) - 1)))) (π₂ (π₂ (π₂ (π₁ (w 0) - 1)))) w' :=
    (LocallyDelta0.eq (pi₁_comp (hm 0)) (LocallyDelta0Function.const 2)).and
      (LocallyDelta0.bexs_le_function
        (repeatVec_locallyDelta0.comp₂ (LocallyDelta0Function.var 1) (hk 0)) hbody)
  exact (hterm.and (hbvar.or (hfvar.or hfunc))).of_iff fun w ↦ by
    simpa using c.phi_iff_decode L (w ·.succ.succ) (w 1) (w 0)

/-- The construction of the graph of the recursion. -/
def construction : Fixpoint.Construction V (β.blueprint L) where
  Φ := c.Phi L
  defined := .mk <| by
    constructor
    · intro v
      simp [Blueprint.blueprint,
        c.bvar_defined.iff,
        c.bvar_defined.graph_delta.iff_delta_pi,
        c.fvar_defined.iff,
        c.fvar_defined.graph_delta.iff_delta_pi,
        c.func_defined.iff,
        c.func_defined.graph_delta.iff_delta_pi]
    · intro v
      symm
      simpa [Blueprint.blueprint, c.bvar_defined.iff, c.fvar_defined.iff, c.func_defined.iff]
        using c.phi_iff L _ _ _
  monotone := by
    unfold Phi
    rintro C C' hC v pr ⟨ht, H⟩
    refine ⟨ht, ?_⟩
    rcases H with (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, w, ⟨hk, hw⟩, rfl⟩)
    · disj 1; exact ⟨z, rfl⟩
    · disj 2; exact ⟨x, rfl⟩
    · disj 3; exact ⟨k, f, v, w, ⟨hk, fun i hi ↦ hC (hw i hi)⟩, rfl⟩
  Φ_locallyDelta0 := c.phi_locallyDelta0 L

/-- `c.Graph L param t y` states that the recursion takes the value `y` at the term `t`. -/
def Graph (param : Fin arity → V) (x y : V) : Prop := (c.construction L).Fixpoint param ⟪x, y⟫

/-- The lookup of the values of the elements of `v` in the table `q 0`. -/
noncomputable def tableLookup (q : Fin 1 → V) (x : V) : V := znth (q 0) x

lemma tableLookup_locallyDelta0 :
    LocallyDelta0Function fun w : Fin 2 → V ↦ tableLookup (V := V) (w ·.succ) (w 0) :=
  LocallyDelta0Function.znth.comp₂ (LocallyDelta0Function.var 1) (LocallyDelta0Function.var 0)

open Classical in
/-- The course-of-values recursion computing the values. -/
noncomputable def courseOfValues : CourseOfValues.Construction V arity where
  val param n T :=
    if n = 0 then 0
    else if π₁ (n - 1) = 0 then c.bvar param (π₂ (n - 1))
    else if π₁ (n - 1) = 1 then c.fvar param (π₂ (n - 1))
    else c.func param (π₁ (π₂ (n - 1))) (π₁ (π₂ (π₂ (n - 1)))) (π₂ (π₂ (π₂ (n - 1))))
      (listMap tableLookup (fun _ ↦ T) (π₂ (π₂ (π₂ (n - 1)))))
  val_locallyDelta0 := by
    have hm : LocallyDelta0Function fun w : Fin (arity + 2) → V ↦ w 1 - 1 :=
      pred_sub_comp (LocallyDelta0Function.var 1)
    have hb := pi₂_comp hm
    have hk := pi₁_comp hb
    have hf := pi₁_comp (pi₂_comp hb)
    have hv := pi₂_comp (pi₂_comp hb)
    have hlist : LocallyDelta0Function fun w : Fin (arity + 2) → V ↦
        listMap tableLookup (fun _ ↦ w 0) (π₂ (π₂ (π₂ (w 1 - 1)))) := by
      have := (listMap_locallyDelta0 tableLookup_locallyDelta0).comp_cons hv
        fun _ ↦ LocallyDelta0Function.var 0
      simpa using this
    have hfunc : LocallyDelta0Function fun w : Fin (arity + 2) → V ↦
        c.func (w ·.succ.succ) (π₁ (π₂ (w 1 - 1))) (π₁ (π₂ (π₂ (w 1 - 1))))
          (π₂ (π₂ (π₂ (w 1 - 1))))
          (listMap tableLookup (fun _ ↦ w 0) (π₂ (π₂ (π₂ (w 1 - 1))))) := by
      have := c.func_locallyDelta0.comp
        (f := (fun w : Fin (arity + 2) → V ↦ π₁ (π₂ (w 1 - 1))) :>
          (fun w ↦ π₁ (π₂ (π₂ (w 1 - 1)))) :> (fun w ↦ π₂ (π₂ (π₂ (w 1 - 1)))) :>
            (fun w ↦ listMap tableLookup (fun _ ↦ w 0) (π₂ (π₂ (π₂ (w 1 - 1))))) :>
              fun j w ↦ w j.succ.succ) fun i ↦ by
          cases i using Fin.cases with
          | zero => exact hk
          | succ i =>
            cases i using Fin.cases with
            | zero => exact hf
            | succ i =>
              cases i using Fin.cases with
              | zero => exact hv
              | succ i =>
                cases i using Fin.cases with
                | zero => exact hlist
                | succ i => exact LocallyDelta0Function.var i.succ.succ
      simpa using this
    exact LocallyDelta0Function.ite
      (LocallyDelta0.eq (LocallyDelta0Function.var 1) (LocallyDelta0Function.const 0))
      (LocallyDelta0Function.const 0) <|
      LocallyDelta0Function.ite (LocallyDelta0.eq (pi₁_comp hm) (LocallyDelta0Function.const 0))
        (by simpa using c.bvar_locallyDelta0.comp_cons hb fun j ↦
          LocallyDelta0Function.var j.succ.succ) <|
        LocallyDelta0Function.ite (LocallyDelta0.eq (pi₁_comp hm) (LocallyDelta0Function.const 1))
          (by simpa using c.fvar_locallyDelta0.comp_cons hb fun j ↦
            LocallyDelta0Function.var j.succ.succ) hfunc
  bound := c.bound
  bound_monotone := c.bound_monotone
  bound_locallyDelta0 := c.bound_locallyDelta0

variable (param : Fin arity → V)

/-- The value of the course-of-values recursion at `t`. -/
noncomputable def courseOfValuesResult (t : V) : V := c.courseOfValues.result param t

lemma courseOfValuesResult_le_bound (t : V) :
    c.courseOfValuesResult param t ≤ c.bound param t :=
  c.courseOfValues.result_le_bound (v := param) t

lemma courseOfValuesResult_locallyDelta0 :
    LocallyDelta0Function fun w : Fin (arity + 1) → V ↦ c.courseOfValuesResult (w ·.succ) (w 0) :=
  c.courseOfValues.result_locallyDelta0

lemma courseOfValuesResult_bvar (z : V) : c.courseOfValuesResult param (^#z) = c.bvar param z := by
  have e : c.courseOfValues.val param (^#z) (c.courseOfValues.table param (^#z)) =
      c.bvar param z := by simp [courseOfValues, qqBvar]
  have hle := c.bvar_le_bound param z
  rw [← e] at hle
  rw [courseOfValuesResult, c.courseOfValues.result_eq_val hle, e]

lemma courseOfValuesResult_fvar (x : V) : c.courseOfValuesResult param (^&x) = c.fvar param x := by
  have e : c.courseOfValues.val param (^&x) (c.courseOfValues.table param (^&x)) =
      c.fvar param x := by simp [courseOfValues, qqFvar]
  have hle := c.fvar_le_bound param x
  rw [← e] at hle
  rw [courseOfValuesResult, c.courseOfValues.result_eq_val hle, e]

lemma courseOfValuesResult_func {k f v : V} (hk : k = len v) :
    ∃ w, len w = k ∧ (∀ i < k, w.[i] = c.courseOfValuesResult param v.[i]) ∧
      c.courseOfValuesResult param (^func k f v) = c.func param k f v w := by
  set w := listMap tableLookup (fun _ ↦ c.courseOfValues.table param (^func k f v)) v
  have hw : len w = k := by rw [len_listMap tableLookup_locallyDelta0, hk]
  have hwv : ∀ i < k, w.[i] = c.courseOfValuesResult param v.[i] := by
    intro i hi
    rw [nth_listMap tableLookup_locallyDelta0 _ _ (by simpa [hk] using hi), tableLookup,
      c.courseOfValues.znth_table (nth_lt_qqFunc_of_lt (by simpa [hk] using hi))]
    rfl
  have e : c.courseOfValues.val param (^func k f v) (c.courseOfValues.table param (^func k f v)) =
      c.func param k f v w := by simp [courseOfValues, qqFunc, w]
  have hle := c.func_le_bound param k f v w hk hw.symm fun i hi ↦ by
    rw [hwv i hi]; exact c.courseOfValuesResult_le_bound param _
  rw [← e] at hle
  exact ⟨w, hw, hwv, by rw [courseOfValuesResult, c.courseOfValues.result_eq_val hle, e]⟩

private lemma limSeq_comp {n : ℕ} {f : (Fin n → V) → V} (hf : LocallyDelta0Function f) :
    LocallyDelta0Function fun w : Fin n → V ↦ (c.construction L).limSeq param (f w) := by
  simpa using (c.construction L).limSeq_locallyDelta0.comp_cons hf fun j ↦
    LocallyDelta0Function.const (param j)

private lemma courseOfValuesResult_comp {n : ℕ} {f : (Fin n → V) → V}
    (hf : LocallyDelta0Function f) :
    LocallyDelta0Function fun w : Fin n → V ↦ c.courseOfValuesResult param (f w) := by
  simpa using c.courseOfValuesResult_locallyDelta0.comp_cons hf fun j ↦
    LocallyDelta0Function.const (param j)

lemma isUTerm_and_eq_of_mem_limSeq {s z : V} (h : z ∈ (c.construction L).limSeq param s) :
    IsUTerm L (π₁ z) ∧ π₂ z = c.courseOfValuesResult param (π₁ z) := by
  have hR : LocallyDelta0 fun y : Fin 2 → V ↦ y 0 ∈ (c.construction L).limSeq param (y 1) →
      IsUTerm L (π₁ (y 0)) ∧ π₂ (y 0) = c.courseOfValuesResult param (π₁ (y 0)) :=
    (LocallyDelta0.mem (LocallyDelta0Function.var 0)
      (c.limSeq_comp L param (LocallyDelta0Function.var 1))).imp
      ((pred_comp isUTerm_locallyDelta0 (pi₁_comp (LocallyDelta0Function.var 0))).and
        (LocallyDelta0.eq (pi₂_comp (LocallyDelta0Function.var 0))
          (c.courseOfValuesResult_comp param (pi₁_comp (LocallyDelta0Function.var 0)))))
  have hP : LocallyDelta0Pred fun s ↦ ∀ z < (c.construction L).limSeq param s,
      z ∈ (c.construction L).limSeq param s →
        IsUTerm L (π₁ z) ∧ π₂ z = c.courseOfValuesResult param (π₁ z) :=
    (LocallyDelta0.ball_lt_function
      (c.limSeq_comp L param (LocallyDelta0Function.var (V := V) (0 : Fin 1))) hR).of_iff
        fun w ↦ by simp
  have : ∀ s, ∀ z < (c.construction L).limSeq param s,
      z ∈ (c.construction L).limSeq param s →
        IsUTerm L (π₁ z) ∧ π₂ z = c.courseOfValuesResult param (π₁ z) := by
    apply LocallyDelta0Pred.succ_induction hP
    · intro z _ hz
      simp at hz
    · intro s ih z _ hz
      have hΦ : c.Phi L param {z | z ∈ (c.construction L).limSeq param s} z :=
        ((c.construction L).mem_limSeq_succ_iff.mp hz).2
      obtain ⟨ht, H⟩ := hΦ
      refine ⟨ht, ?_⟩
      rcases H with (⟨z', rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, w, ⟨hk, hw⟩, rfl⟩)
      · simp [courseOfValuesResult_bvar]
      · simp [courseOfValuesResult_fvar]
      · have hkv : k = len v := (IsUTerm.func_iff.mp (by simpa using ht)).2.lh
        obtain ⟨w', hw', hw'v, he⟩ := c.courseOfValuesResult_func param (f := f) hkv
        have : w = w' := by
          apply nth_ext (by rw [← hk, hw'])
          intro i hi
          have hi' : i < k := by simpa [← hk] using hi
          have hmem : ⟪v.[i], w.[i]⟫ ∈ (c.construction L).limSeq param s := hw i hi'
          have := (ih _ (lt_of_mem hmem) hmem).2
          simp only [pi₂_pair, pi₁_pair] at this
          rw [this, hw'v i hi']
        simp [he, this]
  exact this s z (lt_of_mem h) h

lemma mem_limSeq_of_isUTerm {t : V} (ht : IsUTerm L t) :
    ⟪t, c.courseOfValuesResult param t⟫ ∈
      (c.construction L).limSeq param (⟪t, c.bound param t⟫ + t + 1) := by
  set K := ⟪t, c.bound param t⟫
  have hP : LocallyDelta0Pred fun t' ↦ t' ≤ t → IsUTerm L t' →
      ⟪t', c.courseOfValuesResult param t'⟫ ∈ (c.construction L).limSeq param (K + t' + 1) := by
    have hmem := LocallyDelta0.mem
      (LocallyDelta0Function.pairing.comp₂ (LocallyDelta0Function.var (V := V) (0 : Fin 1))
        (c.courseOfValuesResult_comp param (LocallyDelta0Function.var (V := V) (0 : Fin 1))))
      (c.limSeq_comp L param <| LocallyDelta0Function.add_one <|
        LocallyDelta0Function.add.comp₂ (LocallyDelta0Function.const K)
          (LocallyDelta0Function.var (V := V) (0 : Fin 1)))
    exact (LocallyDelta0.le (LocallyDelta0Function.var 0) (LocallyDelta0Function.const t)).imp
      ((pred_comp isUTerm_locallyDelta0 (LocallyDelta0Function.var 0)).imp hmem)
  have : ∀ t', t' ≤ t → IsUTerm L t' →
      ⟪t', c.courseOfValuesResult param t'⟫ ∈ (c.construction L).limSeq param (K + t' + 1) := by
    apply LocallyDelta0Pred.order_induction hP
    intro t' ih ht' hu
    have hle : ⟪t', c.courseOfValuesResult param t'⟫ ≤ K :=
      pair_le_pair ht' (le_trans (c.courseOfValuesResult_le_bound param t')
        (c.bound_monotone param ht'))
    apply (c.construction L).mem_limSeq_succ_iff.mpr
    refine ⟨le_trans hle le_self_add, ?_⟩
    change c.Phi L param _ _
    refine ⟨by simpa using hu, ?_⟩
    rcases IsUTerm.case hu with (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, _, hv, rfl⟩)
    · disj 1; exact ⟨z, by rw [courseOfValuesResult_bvar]⟩
    · disj 2; exact ⟨x, by rw [courseOfValuesResult_fvar]⟩
    · disj 3
      obtain ⟨w, hw, hwv, he⟩ := c.courseOfValuesResult_func param (f := f) hv.lh
      refine ⟨k, f, v, w, ⟨hw.symm, fun i hi ↦ ?_⟩, by rw [he]⟩
      have hvi : v.[i] < ^func k f v := nth_lt_qqFunc_of_lt (by simpa [← hv.lh] using hi)
      rw [hwv i hi]
      exact (c.construction L).limSeq_cumulative
        (by rw [add_assoc]; exact add_le_add_right (succ_le_iff_lt.mpr hvi) K)
        (ih _ hvi (le_trans hvi.le ht') (hv.nth hi))
  exact this t le_rfl ht

variable {param}

lemma graph_iff {t y : V} :
    c.Graph L param t y ↔ IsUTerm L t ∧ y = c.courseOfValuesResult param t := by
  constructor
  · rintro ⟨s, h⟩
    simpa using c.isUTerm_and_eq_of_mem_limSeq L param h
  · rintro ⟨ht, rfl⟩
    exact ⟨_, c.mem_limSeq_of_isUTerm L param ht⟩

variable {L c} {y : V}

lemma Graph.case_iff {t y : V} :
    c.Graph L param t y ↔
    IsUTerm L t ∧
    ( (∃ z, t = ^#z ∧ y = c.bvar param z) ∨
      (∃ x, t = ^&x ∧ y = c.fvar param x) ∨
      (∃ k f v w, (k = len w ∧ ∀ i < k, c.Graph L param v.[i] w.[i]) ∧
      t = ^func k f v ∧ y = c.func param k f v w) ) := by
  rw [c.graph_iff L]
  constructor
  · rintro ⟨ht, rfl⟩
    refine ⟨ht, ?_⟩
    rcases IsUTerm.case ht with (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, _, hv, rfl⟩)
    · disj 1; exact ⟨z, rfl, by rw [courseOfValuesResult_bvar]⟩
    · disj 2; exact ⟨x, rfl, by rw [courseOfValuesResult_fvar]⟩
    · disj 3
      obtain ⟨w, hw, hwv, he⟩ := c.courseOfValuesResult_func param (f := f) hv.lh
      exact ⟨k, f, v, w, ⟨hw.symm, fun i hi ↦
        (c.graph_iff L).mpr ⟨hv.nth hi, hwv i hi⟩⟩, rfl, he⟩
  · rintro ⟨ht, H⟩
    refine ⟨ht, ?_⟩
    rcases H with (⟨z, rfl, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨k, f, v, w, ⟨hk, hw⟩, rfl, rfl⟩)
    · rw [courseOfValuesResult_bvar]
    · rw [courseOfValuesResult_fvar]
    · have hv := (IsUTerm.func_iff.mp ht).2
      obtain ⟨w', hw', hw'v, he⟩ := c.courseOfValuesResult_func param (f := f) hv.lh
      have : w = w' := by
        apply nth_ext (by rw [← hk, hw'])
        intro i hi
        have hi' : i < k := by simpa [← hk] using hi
        rw [((c.graph_iff L).mp (hw i hi')).2, hw'v i hi']
      rw [he, this]

variable (c)

lemma graph_defined : 𝚺ᴬ₁.Defined (fun v ↦ c.Graph L (v ·.succ.succ) (v 0) (v 1)) (β.graph L) :=
  .mk fun v ↦ by
  simp [Blueprint.graph, (c.construction L).fixpoint_defined.iff, Graph]

@[simp] lemma eval_graphDef (v : Fin (arity + 2) → V) :
    (β.graph L).val.Evalb v ↔ c.Graph L (v ·.succ.succ) (v 0) (v 1) := (graph_defined c).iff

instance graph_definable : 𝚺ᴬ₁.Definable fun v ↦ c.Graph L (v ·.succ.succ) (v 0) (v 1) :=
  (graph_defined c).to_definable

instance graph_definable₂ (param) : 𝚺ᴬ_[0 + 1]-Relation (c.Graph L param) := by
  simpa using Bounding.HierarchySymbol.Definable.retractiont (n := 2) (graph_definable
    c) (#0 :> #1 :> fun i ↦ &(param i))

lemma graph_dom_isUTerm {t y} :
    c.Graph L param t y → IsUTerm L t := fun h ↦ Graph.case_iff.mp h |>.1

lemma graph_bvar_iff {z} :
    c.Graph L param ^#z y ↔ y = c.bvar param z := by
  constructor
  · intro H
    rcases Graph.case_iff.mp H with ⟨_, (⟨_, h, rfl⟩ | ⟨_, h, _⟩ | ⟨_, _, _, _, _, h, _⟩)⟩
    · rcases (by simpa using h); rfl
    · simp [qqBvar, qqFvar] at h
    · simp [qqBvar, qqFunc] at h
  · rintro rfl; exact Graph.case_iff.mpr ⟨by simp, by disj 1; exact ⟨z, by simp⟩⟩

lemma graph_fvar_iff (x) :
    c.Graph L param ^&x y ↔ y = c.fvar param x := by
  constructor
  · intro H
    rcases Graph.case_iff.mp H with ⟨_, (⟨_, h, _⟩ | ⟨_, h, rfl⟩ | ⟨_, _, _, _, _, h, _⟩)⟩
    · simp [qqFvar, qqBvar] at h
    · rcases (by simpa using h); rfl
    · simp [qqFvar, qqFunc] at h
  · rintro rfl; exact Graph.case_iff.mpr ⟨by simp, by disj 2; exact ⟨x, by simp⟩⟩

lemma graph_func {k f v w} (hkr : L.IsFunc k f) (hv : IsUTermVec L k v)
    (hkw : k = len w) (hw : ∀ i < k, c.Graph L param v.[i] w.[i]) :
    c.Graph L param (^func k f v) (c.func param k f v w) := by
  exact Graph.case_iff.mpr
    ⟨by simp [hkr, hv], by disj 3; exact ⟨k, f, v, w, ⟨hkw, hw⟩, by simp⟩⟩

lemma graph_func_inv {k f v y} :
    c.Graph L param (^func k f v) y → ∃ w,
      (k = len w ∧ ∀ i < k, c.Graph L param v.[i] w.[i]) ∧
      y = c.func param k f v w := by
  intro H
  rcases Graph.case_iff.mp H with ⟨_, (⟨_, h, _⟩ | ⟨_, h, rfl⟩ | ⟨k', f', v', w, hw, h, rfl⟩)⟩
  · simp [qqFunc, qqBvar] at h
  · simp [qqFunc, qqFvar] at h
  · rcases show k = k' ∧ f = f' ∧ v = v' by simpa [qqFunc, qqFunc] using h with ⟨rfl, rfl, rfl⟩
    exact ⟨w, hw, by rfl⟩

variable {c} (param n)

lemma graph_exists {t : V} : IsUTerm L t → ∃ y, c.Graph L param t y := fun ht ↦
  ⟨_, (c.graph_iff L).mpr ⟨ht, rfl⟩⟩

lemma graph_unique {t y₁ y₂ : V} : c.Graph L param t y₁ → c.Graph L param t y₂ → y₁ = y₂ := by
  intro h₁ h₂
  rw [((c.graph_iff L).mp h₁).2, ((c.graph_iff L).mp h₂).2]

variable (L c)

lemma graph_existsUnique {t : V} (ht : IsUTerm L t) : ∃! y, c.Graph L param t y := by
  rcases graph_exists param ht with ⟨y, hy⟩
  exact ExistsUnique.intro y hy (fun y' h' ↦ graph_unique param h' hy)

lemma graph_existsUnique_total (t : V) : ∃! y,
    (IsUTerm L t → c.Graph L param t y) ∧ (¬IsUTerm L t → y = 0) := by
  by_cases ht : IsUTerm L t <;> simp [ht, c.graph_existsUnique L param]

noncomputable def result (t : V) : V := Classical.choose! (c.graph_existsUnique_total L param t)

theorem result_prop {t : V} (ht : IsUTerm L t) : c.Graph L param t (c.result L param t) :=
  Classical.choose!_spec (c.graph_existsUnique_total L param t) |>.1 ht

theorem result_prop_not {t : V} (ht : ¬IsUTerm L t) : c.result L param t = 0 :=
  Classical.choose!_spec (c.graph_existsUnique_total L param t) |>.2 ht

variable {L c param}

lemma result_eq_of_graph {t y} (ht : IsUTerm L t) (h : c.Graph L param t y) :
    c.result L param t = y :=
  Eq.symm <| Classical.choose_uniq (c.graph_existsUnique_total L param t) (by simp [h, ht])

@[simp] lemma result_bvar (z) : c.result L param (^#z) = c.bvar param z :=
  c.result_eq_of_graph (by simp) (by simp [c.graph_bvar_iff])

@[simp] lemma result_fvar (x) : c.result L param (^&x) = c.fvar param x :=
  c.result_eq_of_graph (by simp) (by simp [c.graph_fvar_iff])

lemma result_func {k f v w} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v)
    (hkw : k = len w) (hw : ∀ i < k, c.result L param v.[i] = w.[i]) :
    c.result L param (^func k f v) = c.func param k f v w :=
  c.result_eq_of_graph (by simp [hkf, hv]) (c.graph_func hkf hv hkw (fun i hi ↦ by
    simpa [hw i hi] using c.result_prop L param (hv.nth hi)))

open Classical in
lemma result_eq_ite (t : V) :
    c.result L param t = if IsUTerm L t then c.courseOfValuesResult param t else 0 := by
  by_cases ht : IsUTerm L t
  · simp [ht, ((c.graph_iff L).mp (c.result_prop L param ht)).2]
  · simp [ht, c.result_prop_not L param ht]

open Classical in
variable (L c) in
lemma result_locallyDelta0 :
    LocallyDelta0Function fun w : Fin (arity + 1) → V ↦ c.result L (w ·.succ) (w 0) := by
  have : (fun w : Fin (arity + 1) → V ↦ c.result L (w ·.succ) (w 0)) = fun w ↦
      if IsUTerm L (w 0) then c.courseOfValuesResult (w ·.succ) (w 0) else 0 :=
    funext fun w ↦ c.result_eq_ite _
  rw [this]
  exact LocallyDelta0Function.ite (pred_comp isUTerm_locallyDelta0 (LocallyDelta0Function.var 0))
    c.courseOfValuesResult_locallyDelta0 (LocallyDelta0Function.const 0)

section vec

lemma graph_existsUnique_vec {k w : V} (hw : IsUTermVec L k w) :
    ∃! w' : V, k = len w' ∧ ∀ i < k, c.Graph L param w.[i] w'.[i] := by
  have hres := c.result_locallyDelta0 (L := L)
  apply ExistsUnique.intro (listMap (fun p x ↦ c.result L p x) param w)
  · refine ⟨by rw [len_listMap hres, hw.lh], fun i hi ↦ ?_⟩
    rw [nth_listMap hres _ _ (by simpa [← hw.lh] using hi)]
    exact c.result_prop L param (hw.nth hi)
  · rintro w'' ⟨hkw'', hw''⟩
    apply nth_ext (by rw [len_listMap hres, ← hkw'', hw.lh])
    intro i hi
    have hi' : i < k := by simpa [hkw''] using hi
    rw [nth_listMap hres _ _ (by simpa [← hw.lh] using hi')]
    exact (c.result_eq_of_graph (hw.nth hi') (hw'' i hi')).symm

variable (L c param)

lemma graph_existsUnique_vec_total (k w : V) : ∃! w',
    (IsUTermVec L k w → k = len w' ∧ ∀ i < k, c.Graph L param w.[i] w'.[i]) ∧
    (¬IsUTermVec L k w → w' = 0) := by
  by_cases h : IsUTermVec L k w <;> simp [h, c.graph_existsUnique_vec]

noncomputable def resultVec (k w : V) : V :=
  Classical.choose! (c.graph_existsUnique_vec_total L param k w)

@[simp] lemma resultVec_lh {k w : V} (hw : IsUTermVec L k w) : len (c.resultVec L param k w) = k :=
  Eq.symm <| Classical.choose!_spec (c.graph_existsUnique_vec_total L param k w) |>.1 hw |>.1

lemma graph_of_mem_resultVec {k w : V} (hw : IsUTermVec L k w) {i : V} (hi : i < k) :
    c.Graph L param w.[i] (c.resultVec L param k w).[i] :=
  Classical.choose!_spec (c.graph_existsUnique_vec_total L param k w) |>.1 hw |>.2 i hi

lemma nth_resultVec {k w i : V} (hw : IsUTermVec L k w) (hi : i < k) :
    (c.resultVec L param k w).[i] = c.result L param w.[i] :=
  c.result_eq_of_graph (hw.nth hi) (c.graph_of_mem_resultVec L param hw hi) |>.symm

@[simp] theorem resultVec_of_not {k w : V} (hw : ¬IsUTermVec L k w) : c.resultVec L param k w = 0 :=
  Classical.choose!_spec (c.graph_existsUnique_vec_total L param k w) |>.2 hw

@[simp] lemma resultVec_nil :
    c.resultVec L param 0 0 = 0 := len_zero_iff_eq_nil.mp (by simp)

lemma resultVec_cons {k w t : V} (hw : IsUTermVec L k w) (ht : IsUTerm L t) :
    c.resultVec L param (k + 1) (t ∷ w) = c.result L param t ∷ c.resultVec L param k w :=
  nth_ext (by simp [hw, hw.adjoin ht]) (by
    intro i hi
    have hi : i < k + 1 := by simpa [hw.adjoin ht, resultVec_lh] using hi
    rw [c.nth_resultVec L param (hw.adjoin ht) hi]
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simp [c.nth_resultVec L param hw (by simpa using hi)])

end vec

variable (c)

@[simp] lemma result_func' {k f v} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    c.result L param (^func k f v) = c.func param k f v (c.resultVec L param k v) :=
  c.result_func hkf hv (by simp [hv]) (fun i hi ↦ c.nth_resultVec L param hv hi |>.symm)

section

lemma result_defined : 𝚺ᴬ₁.DefinedFunction (fun v ↦ c.result L (v ·.succ) (v 0))
  (β.result L) := .mk fun v ↦ by
  simp [Blueprint.result, Bounding.HierarchySymbol.Semiformula.val_sigma,
    IsUTerm.defined.proper.iff',
    c.eval_graphDef, result, Classical.choose!_eq_iff_right]

@[simp] lemma result_graphDef (v : Fin (arity + 2) → V) :
    (β.result L).val.Evalb v ↔ v 0 = c.result L (v ·.succ.succ) (v 1) := (result_defined c).iff

private lemma resultVec_graph {w' k w} :
    w' = c.resultVec L param k w ↔
    ( (IsUTermVec L k w → k = len w' ∧ ∀ i < k, c.Graph L param w.[i] w'.[i]) ∧
      (¬IsUTermVec L k w → w' = 0) ) :=
  Classical.choose!_eq_iff_right (c.graph_existsUnique_vec_total L param k w)

lemma resultVec_defined :
    𝚺ᴬ₁.DefinedFunction (fun v ↦ c.resultVec L (v ·.succ.succ) (v 0) (v 1)) (β.resultVec L) :=
  .mk fun v ↦ by
  symm
  simpa [Blueprint.resultVec, Bounding.HierarchySymbol.Semiformula.val_sigma,
    IsUTermVec.defined.proper.iff',
    c.eval_graphDef] using c.resultVec_graph

lemma eval_resultVec (v : Fin (arity + 3) → V) :
    (β.resultVec L).val.Evalb v ↔ v 0 = c.resultVec L (v ·.succ.succ.succ) (v 1) (v 2) :=
  c.resultVec_defined.iff

end

end Construction

end Language.TermRec

namespace IsUTerm.BV

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV (blueprint) in
/-- The recursion on terms computing the least bound for their bound variables. -/
noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar _ z := z + 1
  fvar _ _ := 0
  func _ _ _ _ v' := listMax v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by simp [blueprint]
  bvar_locallyDelta0 := LocallyDelta0Function.add_one (LocallyDelta0Function.var 0)
  fvar_locallyDelta0 := LocallyDelta0Function.const 0
  func_locallyDelta0 := listMax_locallyDelta0.comp₁ (LocallyDelta0Function.var 3)
  bound _ t := t
  bvar_le_bound _ z := succ_le_iff_lt.mpr (var_lt_qqBvar z)
  fvar_le_bound _ _ := zero_le
  func_le_bound _ k f v w _ hk h :=
    listMaxss_le fun i hi ↦ le_trans (le_trans (h i (hk ▸ hi)) (nth_le _ _))
      (terms_lt_qqFunc k f v).le
  bound_monotone _ _ _ h := h
  bound_locallyDelta0 := LocallyDelta0Function.var 0

end IsUTerm.BV

section bv

open IsUTerm.BV

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (termBVGraph termBVVecGraph)

variable (L)

/-- The least `n` such that all bound variables in the code `t` of a term are below `n`. -/
noncomputable def termBV (t : V) : V := construction.result L ![] t

/-- The list of the values of `termBV` on the list `v` of `k` terms. -/
noncomputable def termBVVec (k v : V) : V := construction.resultVec L ![] k v

variable {L}
variable {k : V}

@[simp] lemma termBV_bvar (z : V) :
    termBV L ^#z = z + 1 := by simp [termBV, construction]

@[simp] lemma termBV_fvar (x : V) :
    termBV L ^&x = 0 := by simp [termBV, construction]

@[simp] lemma termBV_func {k f v : V} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    termBV L (^func k f v) = listMax (termBVVec L k v) := by
  simp [termBV, construction, hkf, hv]; rfl

@[simp] lemma len_termBVVec {v : V} (hv : IsUTermVec L k v) :
    len (termBVVec L k v) = k := construction.resultVec_lh L _ hv

@[simp] lemma nth_termBVVec {v : V} (hv : IsUTermVec L k v) {i} (hi : i < k) :
    (termBVVec L k v).[i] = termBV L v.[i] := construction.nth_resultVec L _ hv hi

@[simp] lemma termBVVec_nil : termBVVec L 0 0 = 0 := construction.resultVec_nil L _

lemma termBVVec_cons {k t ts : V} (ht : IsUTerm L t) (hts : IsUTermVec L k ts) :
    termBVVec L (k + 1) (t ∷ ts) = termBV L t ∷ termBVVec L k ts :=
  construction.resultVec_cons L ![] hts ht

section

instance termBV.defined : 𝚺ᴬ₁-Function₁ (termBV (V := V) L) via (termBVGraph L) :=
  construction.result_defined

instance termBV.definable : 𝚺ᴬ₁-Function₁ (termBV (V := V) L) := termBV.defined.to_definable

instance termBV.definable' {k : ℕ} (Γ) : Γᴬ_[k + 1]-Function₁ (termBV (V := V) L) :=
  termBV.definable.of_sigmaOne

instance termBVVec.defined : 𝚺ᴬ₁-Function₂ (termBVVec (V := V) L) via (termBVVecGraph L) :=
  construction.resultVec_defined

instance termBVVec.definable : 𝚺ᴬ₁-Function₂ (termBVVec (V := V) L) :=
  termBVVec.defined.to_definable

instance termBVVec.definable' {i : ℕ} (Γ) : Γᴬ_[i + 1]-Function₂ (termBVVec (V := V) L) :=
  termBVVec.definable.of_sigmaOne

end

lemma termBV_locallyDelta0 : LocallyDelta0Function₁ (termBV L : V → V) := by
  convert construction.result_locallyDelta0 (V := V) L using 3
  simp [termBV, Matrix.empty_eq]

end bv

section isSemiterm

open _root_.FFL.FirstOrder.Arithmetic.Bootstrapping (isSemiterm isSemitermVec)

variable (L)
variable {n k w t : V}

/-- The code `t` is a term of the language `L` whose bound variables are all below `n`. -/
class IsSemiterm (n t : V) : Prop where
  isUTerm : IsUTerm L t
  bv : termBV L t ≤ n

/-- The list `v` of `k` semiterms with bound variables below `n`. -/
class IsSemitermVec (k n v : V) : Prop where
  isUTermVec : IsUTermVec L k v
  bv : ∀  {i}, i < k → termBV L v.[i] ≤ n

abbrev IsTerm (t : V) : Prop := IsSemiterm L 0 t

abbrev IsTermVec (k v : V) : Prop := IsSemitermVec L k 0 v

variable {L}

lemma IsSemiterm.def {n} {t : V} : IsSemiterm L n t ↔ IsUTerm L t ∧ termBV L t ≤ n :=
  ⟨by rintro ⟨h, bv⟩; exact ⟨h, bv⟩, by rintro ⟨h, bv⟩; exact ⟨h, bv⟩⟩

lemma IsSemitermVec.def {v : V} :
    IsSemitermVec L k n v ↔ IsUTermVec L k v ∧ ∀ i < k, termBV (V := V) L v.[i] ≤ n :=
  ⟨by rintro ⟨h, bv⟩; exact ⟨h, fun _ ↦ bv⟩, by rintro ⟨h, bv⟩; exact ⟨h, bv _⟩⟩

lemma isSemiterm_locallyDelta0 : LocallyDelta0Rel (IsSemiterm (V := V) L) := by
  have h : LocallyDelta0 fun w : Fin 2 → V ↦ IsUTerm L (w 1) ∧ termBV L (w 1) ≤ w 0 :=
    (isUTerm_locallyDelta0.pred_comp (LocallyDelta0Function.var 1)).and
      (LocallyDelta0.le (termBV_locallyDelta0.comp₁ (LocallyDelta0Function.var 1))
        (LocallyDelta0Function.var 0))
  exact h.of_iff fun w ↦ IsSemiterm.def

lemma isSemitermVec_locallyDelta0 :
    LocallyDelta0 fun w : Fin 3 → V ↦ IsSemitermVec L (w 0) (w 1) (w 2) := by
  have hbv : LocallyDelta0 fun w : Fin 4 → V ↦ termBV L (nth (w 3) (w 0)) ≤ w 2 :=
    LocallyDelta0.le (termBV_locallyDelta0.comp₁ (nth_locallyDelta0.comp₂
      (LocallyDelta0Function.var 3) (LocallyDelta0Function.var 0))) (LocallyDelta0Function.var 2)
  have hvec : LocallyDelta0 fun w : Fin 3 → V ↦ IsUTermVec L (w 0) (w 2) :=
    isUTermVec_locallyDelta0.rel_comp₂ (LocallyDelta0Function.var 0) (LocallyDelta0Function.var 2)
  exact (hvec.and (LocallyDelta0.ball_lt_function (LocallyDelta0Function.var 0)
    (hbv.of_iff fun w ↦ Iff.rfl))).of_iff fun w ↦ IsSemitermVec.def

@[simp] lemma IsSemitermVec.isUTerm {k n v : V} (h : IsSemitermVec L k n v) :
    IsUTermVec L k v := h.1

lemma IsSemitermVec.lh {k n v : V} (h : IsSemitermVec L k n v) : len v = k := h.isUTerm.lh.symm

lemma IsSemitermVec.nth {k n v : V} (h : IsSemitermVec L k n v) {i} (hi : i < k) :
    IsSemiterm L n v.[i] := ⟨h.isUTerm.nth hi, h.bv hi⟩

lemma IsUTerm.isSemiterm {t : V} (h : IsUTerm L t) : IsSemiterm L (termBV L t) t := ⟨h, by simp⟩

lemma IsUTermVec.isSemitermVec {k v : V} (h : IsUTermVec L k v) :
    IsSemitermVec L k (listMax (termBVVec L k v)) v :=
  ⟨h, fun {i} hi ↦
    le_trans (by rw [nth_termBVVec h hi]) (nth_le_listMax (i := i) (by simp [h, hi]))⟩

lemma IsSemitermVec.iff {k n v : V} :
    IsSemitermVec L k n v ↔ (len v = k ∧ ∀ i < k, IsSemiterm L n v.[i]) := by
  constructor
  · intro h; exact ⟨h.lh, fun i hi ↦ h.nth hi⟩
  · intro ⟨hk, h⟩; exact ⟨⟨hk.symm, fun i hi ↦ h i hi |>.isUTerm⟩, fun hi ↦ h _ hi |>.bv⟩

@[simp] lemma IsSemiterm.bvar {n z : V} :
    IsSemiterm L n ^#z ↔ z < n := by simp [IsSemiterm.def, succ_le_iff_lt]

@[simp] lemma IsSemiterm.fvar (n x : V) :
    IsSemiterm L n ^&x := by simp [IsSemiterm.def]

@[simp] lemma IsSemiterm.func {n k f v : V} :
    IsSemiterm L n (^func k f v) ↔ L.IsFunc k f ∧ IsSemitermVec L k n v := by
  simp only [IsSemiterm.def, IsUTerm.func_iff]
  constructor
  · rintro ⟨⟨hf, hbv⟩, hv⟩
    exact ⟨hf, hbv, by
      intro i hi
      have : listMax (termBVVec L k v) ≤ n := by simpa [termBV_func, hf, hbv] using hv
      simpa [hbv, hi] using listMaxss_le_iff.mp this i (by simp [hbv, hi])⟩
  · rintro ⟨hf, h⟩
    exact ⟨⟨hf, h.isUTerm⟩, by
      simp only [hf, h.isUTerm, termBV_func]
      apply listMaxss_le_iff.mpr
      intro i hi
      have hi : i < k := by simpa [hf, h.isUTerm] using hi
      simpa [hf, h.isUTerm, hi] using (h.nth hi).bv⟩

@[simp] lemma IsSemitermVec.empty (n : V) : IsSemitermVec L 0 n 0 := ⟨by simp, by simp⟩

@[simp] lemma IsSemitermVec.empty_iff {v : V} : IsSemitermVec L 0 n v ↔ v = 0 := by
  constructor
  · intro h; exact len_zero_iff_eq_nil.mp h.lh
  · rintro rfl; simp

@[simp] lemma IsSemitermVec.cons_iff :
    IsSemitermVec L (k + 1) n (t ∷ w) ↔ IsSemiterm L n t ∧ IsSemitermVec L k n w := by
  constructor
  · intro h
    exact ⟨by simpa using h.nth (i := 0) (by simp),
      IsSemitermVec.iff.mpr
        ⟨by simpa using h.lh, fun i hi ↦ by simpa using h.nth (show i + 1 < k + 1 by simp [hi])⟩⟩
  · rintro ⟨ht, hw⟩
    exact ⟨hw.isUTerm.adjoin ht.isUTerm, by
    intro i hi
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp [ht.bv]
    · simpa using hw.nth (by simpa using hi) |>.bv⟩

lemma SemitermVec.adjoin {n m w t : V} (h : IsSemitermVec L n m w) (ht : IsSemiterm L m t) :
    IsSemitermVec L (n + 1) m (t ∷ w) :=
  IsSemitermVec.cons_iff.mpr ⟨ht, h⟩

@[simp] lemma IsSemitermVec.singleton {n t : V} :
    IsSemitermVec L 1 n ?[t] ↔ IsSemiterm L n t := by
  rw [show (1 : V) = 0 + 1 by simp, IsSemitermVec.cons_iff]; simp

@[simp] lemma IsSemitermVec.doubleton {n t₁ t₂ : V} :
    IsSemitermVec L 2 n ?[t₁, t₂] ↔ IsSemiterm L n t₁ ∧ IsSemiterm L n t₂ := by
  rw [show (2 : V) = 1 + 1 by simp [one_add_one_eq_two], IsSemitermVec.cons_iff]; simp

section

instance IsSemiterm.defined : 𝚫ᴬ₁-Relation (IsSemiterm (V := V) L) via (isSemiterm L) := .mk <| by
  refine ⟨?_, ?_⟩
  · intro v
    simp [isSemiterm, Bounding.HierarchySymbol.Semiformula.val_sigma]
  · intro v
    simp [isSemiterm, IsSemiterm.def, Bounding.HierarchySymbol.Semiformula.val_sigma]

instance IsSemiterm.definable : 𝚫ᴬ₁-Relation (IsSemiterm (V := V) L) :=
  IsSemiterm.defined.to_definable

instance IsSemiterm.definable' (Γ : Polarity) (m : ℕ) :
    Γᴬ_[m + 1]-Relation (IsSemiterm (V := V) L) := IsSemiterm.definable.of_deltaOne

instance IsSemitermVec.defined : 𝚫ᴬ₁-Relation₃ (IsSemitermVec (V := V) L) via (isSemitermVec L) :=
  .mk <| by
  refine ⟨?_, ?_⟩
  · intro v
    simp [isSemitermVec, Bounding.HierarchySymbol.Semiformula.val_sigma]
  · intro v
    simp [isSemitermVec, IsSemitermVec.def, Bounding.HierarchySymbol.Semiformula.val_sigma]

instance IsSemitermVec.definable : 𝚫ᴬ₁-Relation₃ (IsSemitermVec (V := V) L) :=
  IsSemitermVec.defined.to_definable

instance IsSemitermVec.definable' (Γ : Polarity) (m : ℕ) :
    Γᴬ_[m + 1]-Relation₃ (IsSemitermVec (V := V) L) := IsSemitermVec.definable.of_deltaOne

end

lemma IsSemiterm.case_iff {n t : V} :
    IsSemiterm L n t ↔
    (∃ z < n, t = ^#z) ∨
    (∃ x, t = ^&x) ∨
    (∃ k f v : V, L.IsFunc k f ∧ IsSemitermVec L k n v ∧ t = ^func k f v) := by
  constructor
  · intro h
    rcases h.isUTerm.case with (⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hf, _, rfl⟩)
    · disj 1; exact ⟨z, by simpa [succ_le_iff_lt] using h.bv, rfl⟩;
    · disj 2; exact ⟨x, rfl⟩;
    · disj 3; exact ⟨k, f, v, hf, by simp_all, rfl⟩;
  · rintro (⟨z, hz, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hf, hv, rfl⟩)
    · simp [hz]
    · simp
    · simp [hf, hv]

alias ⟨IsSemiterm.case, IsSemiterm.mk'⟩ := IsSemiterm.case_iff

lemma IsSemiterm.induction {P : V → Prop} (hP : LocallyDelta0Pred P)
    (hbvar : ∀ z < n, P (^#z)) (hfvar : ∀ x, P (^&x))
    (hfunc : ∀ k f v, L.IsFunc k f → IsSemitermVec L k n v → (∀ i < k, P v.[i]) → P (^func k f v)) :
    ∀ t, IsSemiterm L n t → P t := by
  intro t ht
  suffices IsSemiterm L n t → P t by exact this ht
  apply IsUTerm.induction ?_ ?_ ?_ ?_ t ht.isUTerm
  · exact (isSemiterm_locallyDelta0.rel_comp₂ (LocallyDelta0Function.const n)
      (LocallyDelta0Function.var (0 : Fin 1))).imp hP
  · intro z; simp only [bvar]; exact hbvar z
  · intro x _; exact hfvar x
  · intro k f v hf _ ih h
    have hv : IsSemitermVec L k n v := by simp_all
    exact hfunc k f v hf hv (fun i hi ↦ ih i hi (hv.nth hi))

@[simp] lemma IsSemitermVec.nil (k : V) : IsSemitermVec L 0 k 0 := ⟨by simp, by simp⟩

@[simp] lemma IsSemitermVec.adjoin {k n w t : V} (h : IsSemitermVec L n k w)
    (ht : IsSemiterm L k t) : IsSemitermVec L (n + 1) k (t ∷ w) :=
  ⟨h.isUTerm.adjoin ht.isUTerm, by
    intro i hi
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp [ht.bv]
    · simp [h.bv (by simpa using hi)]⟩

end isSemiterm

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping
