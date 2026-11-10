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
  func_le_bound : ∀ param (k f v w : V), k = len w → (∀ i < k, w.[i] ≤ bound param v.[i]) →
    func param k f v w ≤ bound param (^func k f v)
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
  have hle := c.func_le_bound param k f v w hw.symm fun i hi ↦ by
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

end Construction

end Language.TermRec

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping
