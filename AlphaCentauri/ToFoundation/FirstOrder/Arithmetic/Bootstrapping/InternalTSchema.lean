module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.PairingAssignment
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Provable
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Hierarchy
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.General
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.Bounded
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.General

/-!
# Gaps in Foundation's `PartialTruth.Bounded`: the internal T-schema

The internal T-schema for prenex $\Sigma_1$ partial truth.

`psatDef` and `tvDef` express $\Delta_0$ satisfaction and the values of terms under an assignment
coded by iterated `ppair`s. Their Tarski conditions are theorems of `𝗜𝚺₁`, so every internal
theory containing `𝗜𝚺₁` proves their instances at arbitrary internal terms. Under the assignment
term `assignment n`, which gives each bound variable `#i` the value `&i`, the internal theory proves
that every internal $\Delta_0$ formula without free variables is equivalent to its satisfaction,
and hence that every internal prenex $\Sigma_1$ sentence is equivalent to its partial truth.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open FirstOrder FFL.Entailment Bootstrapping.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def _root_.FFL.FirstOrder.Arithmetic.psatDef : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “a p. ∃ s, !decGraph s a ∧ !boundedSatisfied.sigma s p”

noncomputable def _root_.FFL.FirstOrder.Arithmetic.tvDef : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “y a t. ∃ s, !decGraph s a ∧ !termValGraph y s t”

@[simp] lemma eval_psatDef (v : Fin 2 → V) :
    V ⊧/v psatDef.val ↔ BoundedSatisfied (dec (v 0)) (v 1) := by
  simp [psatDef]

@[simp] lemma eval_tvDef (v : Fin 3 → V) :
    V ⊧/v tvDef.val ↔ v 0 = termVal (dec (v 1)) (v 2) := by
  simp [tvDef]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private lemma add_mul_add_eq_ppair (x a : V) : (x + a) * (x + a) + a + 1 = ppair x a := rfl

/-- The internal term `(t + u) * (t + u) + u + 1`. -/
noncomputable def pTerm {n : ℕ} (t u : Semiterm V ℒₒᵣ n) : Semiterm V ℒₒᵣ n :=
  (t + u) * (t + u) + u + 𝕹 1

/-- The internal sentence that the code `p` is satisfied under the assignment coded by `a`. -/
noncomputable def psatF {n : ℕ} (a : Semiterm V ℒₒᵣ n) (p : V) : Semiformula V ℒₒᵣ n :=
  (⌜psatDef.val⌝ : Semiformula V ℒₒᵣ 2).subst ![a, 𝕹 p]

/-- The internal sentence that `y` is the value of the code `t` under the assignment coded by
`a`. -/
noncomputable def tvF {n : ℕ} (y a : Semiterm V ℒₒᵣ n) (t : V) : Semiformula V ℒₒᵣ n :=
  (⌜tvDef.val⌝ : Semiformula V ℒₒᵣ 3).subst ![y, a, 𝕹 t]

section

variable {n m : ℕ}

@[simp] lemma subst_pTerm (w : SemitermVec V ℒₒᵣ n m) (t u : Semiterm V ℒₒᵣ n) :
    (pTerm t u).subst w = pTerm (t.subst w) (u.subst w) := by
  simp [pTerm]

@[simp] lemma shift_pTerm (t u : Semiterm V ℒₒᵣ n) :
    (pTerm t u).shift = pTerm t.shift u.shift := by
  simp [pTerm]

@[simp] lemma bShift_pTerm (t u : Semiterm V ℒₒᵣ n) :
    (pTerm t u).bShift = pTerm t.bShift u.bShift := by
  simp [pTerm]

@[simp] lemma subst_psatF (w : SemitermVec V ℒₒᵣ n m) (a : Semiterm V ℒₒᵣ n) (p : V) :
    (psatF a p).subst w = psatF (a.subst w) p := by
  simp [psatF, Semiformula.substs_substs]

@[simp] lemma shift_psatF (a : Semiterm V ℒₒᵣ n) (p : V) :
    (psatF a p).shift = psatF a.shift p := by
  simp [psatF, Semiformula.shift_substs, typed_quote_shift]

@[simp] lemma subst_tvF (w : SemitermVec V ℒₒᵣ n m) (y a : Semiterm V ℒₒᵣ n) (t : V) :
    (tvF y a t).subst w = tvF (y.subst w) (a.subst w) t := by
  simp [tvF, Semiformula.substs_substs]

@[simp] lemma shift_tvF (y a : Semiterm V ℒₒᵣ n) (t : V) :
    (tvF y a t).shift = tvF y.shift a.shift t := by
  simp [tvF, Semiformula.shift_substs, typed_quote_shift]

end

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

lemma numeral_vec_two (a b : V) :
    (fun i ↦ (𝕹 (![a, b] i) : Term V ℒₒᵣ)) = ![𝕹 a, 𝕹 b] := by
  funext i; match i with | 0 => rfl | 1 => rfl

lemma numeral_vec_three (a b c : V) :
    (fun i ↦ (𝕹 (![a, b, c] i) : Term V ℒₒᵣ)) = ![𝕹 a, 𝕹 b, 𝕹 c] := by
  funext i; match i with | 0 => rfl | 1 => rfl | 2 => rfl

lemma numeral_vec_four (a b c d : V) :
    (fun i ↦ (𝕹 (![a, b, c, d] i) : Term V ℒₒᵣ)) = ![𝕹 a, 𝕹 b, 𝕹 c, 𝕹 d] := by
  funext i; match i with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl

/-! ### Terms -/

private noncomputable def tvBvarZeroClause : ArithmeticSemisentence 3 :=
  qqBvarDef.val/[#2, ‘0’] 🡒 tvDef.val/[#0, ‘(#0 + #1) * (#0 + #1) + #1 + 1’, #2]

lemma tprovable_tvF_bvar_zero (x a : Term V ℒₒᵣ) :
    T.internalize V ⊢ tvF x (pTerm x a) (^#0) := by
  have h₁ := tprovable_subst_of_models (T := T) (φ := tvBvarZeroClause) (by
    intro W _ _ e;
    simpa [tvBvarZeroClause, add_mul_add_eq_ppair] using fun (h : e 2 = ^#0) ↦ by
      simp [h]) ![x, a, 𝕹 (^#0)];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (φ := qqBvarDef.val) (by simp)
    (w := ![(^#0 : V), 0]) (by simp);
  rw [numeral_vec_two] at h₂;
  have h₃ : T.internalize V ⊢ (⌜qqBvarDef.val⌝ : Semiformula V ℒₒᵣ 2).subst ![𝕹 (^#0), 𝕹 0] 🡒
      tvF x (pTerm x a) (^#0) := by
    simpa [tvBvarZeroClause, tvF, pTerm, typed_quote_rew_subst, Semiformula.substs_substs,
      Matrix.vecHead, Matrix.vecTail] using h₁;
  exact h₃ ⨀ h₂

private noncomputable def bvarSuccCond : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “z z' i. !qqBvarDef z i ∧ !qqBvarDef z' (i + 1)”

private noncomputable def tvBvarSuccClause : ArithmeticSemisentence 6 :=
  bvarSuccCond.val/[#3, #4, #5] 🡒 tvDef.val/[#0, #2, #3] 🡒
    tvDef.val/[#0, ‘(#1 + #2) * (#1 + #2) + #2 + 1’, #4]

lemma tprovable_tvF_bvar_succ (y x a : Term V ℒₒᵣ) (i : V) :
    T.internalize V ⊢ tvF y a (^#i) 🡒 tvF y (pTerm x a) (^#(i + 1)) := by
  have h₁ := tprovable_subst_of_models (T := T) (φ := tvBvarSuccClause) (by
    intro W _ _ e;
    simpa [tvBvarSuccClause, bvarSuccCond, add_mul_add_eq_ppair] using
      fun (h₁ : e 3 = ^#(e 5)) (h₂ : e 4 = ^#(e 5 + 1)) ↦ by simp [h₁, h₂])
    ![y, x, a, 𝕹 (^#i), 𝕹 (^#(i + 1)), 𝕹 i];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (φ := bvarSuccCond.val) (by simp)
    (w := ![(^#i : V), ^#(i + 1), i]) (by simp [bvarSuccCond]);
  rw [numeral_vec_three] at h₂;
  have h₃ : T.internalize V ⊢
      (⌜bvarSuccCond.val⌝ : Semiformula V ℒₒᵣ 3).subst ![𝕹 (^#i), 𝕹 (^#(i + 1)), 𝕹 i] 🡒
        tvF y a (^#i) 🡒 tvF y (pTerm x a) (^#(i + 1)) := by
    simpa [tvBvarSuccClause, tvF, pTerm, typed_quote_rew_subst, Semiformula.substs_substs,
      Matrix.vecHead, Matrix.vecTail] using h₁;
  exact h₃ ⨀ h₂

private noncomputable def zeroCond : 𝚺ᴬ₁.Semisentence 1 := .mkSigma “t. t = ↑Arithmetic.zero”

private noncomputable def oneCond : 𝚺ᴬ₁.Semisentence 1 := .mkSigma “t. t = ↑Arithmetic.one”

private noncomputable def tvZeroClause : ArithmeticSemisentence 2 :=
  zeroCond.val/[#1] 🡒 tvDef.val/[‘0’, #0, #1]

private noncomputable def tvOneClause : ArithmeticSemisentence 2 :=
  oneCond.val/[#1] 🡒 tvDef.val/[‘1’, #0, #1]

lemma tprovable_tvF_zero (a : Term V ℒₒᵣ) : T.internalize V ⊢ tvF (𝕹 0) a 𝟎 := by
  have h₁ := tprovable_subst_of_models (T := T) (φ := tvZeroClause) (by
    intro W _ _ e;
    simpa [tvZeroClause, zeroCond, numeral_eq_natCast] using fun (h : e 1 = 𝟎) ↦ by simp [h])
    ![a, 𝕹 (𝟎 : V)];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (φ := zeroCond.val) (by simp)
    (w := ![(𝟎 : V)]) (by simp [zeroCond, numeral_eq_natCast]);
  have h₃ : T.internalize V ⊢ (⌜zeroCond.val⌝ : Semiformula V ℒₒᵣ 1).subst ![𝕹 (𝟎 : V)] 🡒
      tvF (𝕹 0) a 𝟎 := by
    simpa [tvZeroClause, tvF, typed_quote_rew_subst, Semiformula.substs_substs,
      Matrix.vecHead, Matrix.vecTail, Matrix.constant_eq_singleton] using h₁;
  exact h₃ ⨀ (by simpa [Matrix.constant_eq_singleton] using h₂)

lemma tprovable_tvF_one (a : Term V ℒₒᵣ) : T.internalize V ⊢ tvF (𝕹 1) a 𝟏 := by
  have h₁ := tprovable_subst_of_models (T := T) (φ := tvOneClause) (by
    intro W _ _ e;
    simpa [tvOneClause, oneCond, numeral_eq_natCast] using fun (h : e 1 = 𝟏) ↦ by simp [h])
    ![a, 𝕹 (𝟏 : V)];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (φ := oneCond.val) (by simp)
    (w := ![(𝟏 : V)]) (by simp [oneCond, numeral_eq_natCast]);
  have h₃ : T.internalize V ⊢ (⌜oneCond.val⌝ : Semiformula V ℒₒᵣ 1).subst ![𝕹 (𝟏 : V)] 🡒
      tvF (𝕹 1) a 𝟏 := by
    simpa [tvOneClause, tvF, typed_quote_rew_subst, Semiformula.substs_substs,
      Matrix.vecHead, Matrix.vecTail, Matrix.constant_eq_singleton] using h₁;
  exact h₃ ⨀ (by simpa [Matrix.constant_eq_singleton] using h₂)

private noncomputable def addCond : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “c t u. !qqAddGraph c t u ∧ !(isUTerm ℒₒᵣ).sigma t ∧ !(isUTerm ℒₒᵣ).sigma u”

private noncomputable def mulCond : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “c t u. !qqMulGraph c t u ∧ !(isUTerm ℒₒᵣ).sigma t ∧ !(isUTerm ℒₒᵣ).sigma u”

private noncomputable def tvAddClause : ArithmeticSemisentence 6 :=
  addCond.val/[#5, #3, #4] 🡒 tvDef.val/[#0, #2, #3] 🡒 tvDef.val/[#1, #2, #4] 🡒
    tvDef.val/[‘#0 + #1’, #2, #5]

private noncomputable def tvMulClause : ArithmeticSemisentence 6 :=
  mulCond.val/[#5, #3, #4] 🡒 tvDef.val/[#0, #2, #3] 🡒 tvDef.val/[#1, #2, #4] 🡒
    tvDef.val/[‘#0 * #1’, #2, #5]

lemma tprovable_tvF_add (y₁ y₂ a : Term V ℒₒᵣ) {t u : V} (ht : IsUTerm ℒₒᵣ t)
    (hu : IsUTerm ℒₒᵣ u) :
    T.internalize V ⊢ tvF y₁ a t 🡒 tvF y₂ a u 🡒 tvF (y₁ + y₂) a (t ^+ u) := by
  have h₁ := tprovable_subst_of_models (T := T) (φ := tvAddClause) (by
    intro W _ _ e;
    simpa [tvAddClause, addCond] using
      fun (h : e 5 = e 3 ^+ e 4) (ht : IsUTerm ℒₒᵣ (e 3)) (hu : IsUTerm ℒₒᵣ (e 4))
        (h₁ : e 0 = termVal (dec (e 2)) (e 3)) (h₂ : e 1 = termVal (dec (e 2)) (e 4)) ↦ by
        simp [h, h₁, h₂, termVal_add ht hu])
    ![y₁, y₂, a, 𝕹 t, 𝕹 u, 𝕹 (t ^+ u)];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (φ := addCond.val) (by simp)
    (w := ![t ^+ u, t, u]) (by simp [addCond, ht, hu]);
  rw [numeral_vec_three] at h₂;
  have h₃ : T.internalize V ⊢
      (⌜addCond.val⌝ : Semiformula V ℒₒᵣ 3).subst ![𝕹 (t ^+ u), 𝕹 t, 𝕹 u] 🡒
        tvF y₁ a t 🡒 tvF y₂ a u 🡒 tvF (y₁ + y₂) a (t ^+ u) := by
    simpa [tvAddClause, tvF, typed_quote_rew_subst, Semiformula.substs_substs,
      Matrix.vecHead, Matrix.vecTail] using h₁;
  exact h₃ ⨀ h₂

lemma tprovable_tvF_mul (y₁ y₂ a : Term V ℒₒᵣ) {t u : V} (ht : IsUTerm ℒₒᵣ t)
    (hu : IsUTerm ℒₒᵣ u) :
    T.internalize V ⊢ tvF y₁ a t 🡒 tvF y₂ a u 🡒 tvF (y₁ * y₂) a (t ^* u) := by
  have h₁ := tprovable_subst_of_models (T := T) (φ := tvMulClause) (by
    intro W _ _ e;
    simpa [tvMulClause, mulCond] using
      fun (h : e 5 = e 3 ^* e 4) (ht : IsUTerm ℒₒᵣ (e 3)) (hu : IsUTerm ℒₒᵣ (e 4))
        (h₁ : e 0 = termVal (dec (e 2)) (e 3)) (h₂ : e 1 = termVal (dec (e 2)) (e 4)) ↦ by
        simp [h, h₁, h₂, termVal_mul ht hu])
    ![y₁, y₂, a, 𝕹 t, 𝕹 u, 𝕹 (t ^* u)];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (φ := mulCond.val) (by simp)
    (w := ![t ^* u, t, u]) (by simp [mulCond, ht, hu]);
  rw [numeral_vec_three] at h₂;
  have h₃ : T.internalize V ⊢
      (⌜mulCond.val⌝ : Semiformula V ℒₒᵣ 3).subst ![𝕹 (t ^* u), 𝕹 t, 𝕹 u] 🡒
        tvF y₁ a t 🡒 tvF y₂ a u 🡒 tvF (y₁ * y₂) a (t ^* u) := by
    simpa [tvMulClause, tvF, typed_quote_rew_subst, Semiformula.substs_substs,
      Matrix.vecHead, Matrix.vecTail] using h₁;
  exact h₃ ⨀ h₂

/-! ### Formulas -/

private noncomputable def verumCond : 𝚺ᴬ₁.Semisentence 1 := .mkSigma “c. !qqVerumDef c”

private noncomputable def falsumCond : 𝚺ᴬ₁.Semisentence 1 := .mkSigma “c. !qqFalsumDef c”

private noncomputable def psatVerumClause : ArithmeticSemisentence 2 :=
  verumCond.val/[#1] 🡒 psatDef.val/[#0, #1]

private noncomputable def psatFalsumClause : ArithmeticSemisentence 2 :=
  falsumCond.val/[#1] 🡒 ∼psatDef.val/[#0, #1]

lemma tprovable_psatF_verum (a : Term V ℒₒᵣ) : T.internalize V ⊢ psatF a ^⊤ := by
  have h₁ := tprovable_subst_of_models (T := T) (φ := psatVerumClause) (by
    intro W _ _ e;
    simpa [psatVerumClause, verumCond] using fun (h : e 1 = ^⊤) ↦ by simp [h]) ![a, 𝕹 ^⊤];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (φ := verumCond.val) (by simp)
    (w := ![(^⊤ : V)]) (by simp [verumCond]);
  have h₃ : T.internalize V ⊢ (⌜verumCond.val⌝ : Semiformula V ℒₒᵣ 1).subst ![𝕹 (^⊤ : V)] 🡒
      psatF a ^⊤ := by
    simpa [psatVerumClause, psatF, typed_quote_rew_subst, Semiformula.substs_substs,
      Matrix.vecHead, Matrix.vecTail, Matrix.constant_eq_singleton] using h₁;
  exact h₃ ⨀ (by simpa [Matrix.constant_eq_singleton] using h₂)

lemma tprovable_psatF_falsum (a : Term V ℒₒᵣ) : T.internalize V ⊢ ∼psatF a ^⊥ := by
  have h₁ := tprovable_subst_of_models (T := T) (φ := psatFalsumClause) (by
    intro W _ _ e;
    simpa [psatFalsumClause, falsumCond] using fun (h : e 1 = ^⊥) ↦ by simp [h]) ![a, 𝕹 ^⊥];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (φ := falsumCond.val) (by simp)
    (w := ![(^⊥ : V)]) (by simp [falsumCond]);
  have h₃ : T.internalize V ⊢ (⌜falsumCond.val⌝ : Semiformula V ℒₒᵣ 1).subst ![𝕹 (^⊥ : V)] 🡒
      ∼psatF a ^⊥ := by
    simpa [psatFalsumClause, psatF, typed_quote_rew_subst, Semiformula.substs_substs,
      Matrix.vecHead, Matrix.vecTail, Matrix.constant_eq_singleton] using h₁;
  exact h₃ ⨀ (by simpa [Matrix.constant_eq_singleton] using h₂)

private noncomputable def andCond : 𝚺ᴬ₁.Semisentence 3 := .mkSigma “c p q. !qqAndDef c p q”

private noncomputable def psatAndClause : ArithmeticSemisentence 4 :=
  andCond.val/[#3, #1, #2] 🡒
    (psatDef.val/[#0, #3] 🡘 psatDef.val/[#0, #1] ⋏ psatDef.val/[#0, #2])

lemma tprovable_psatF_and (a : Term V ℒₒᵣ) (p q : V) :
    T.internalize V ⊢ psatF a (p ^⋏ q) 🡘 psatF a p ⋏ psatF a q := by
  have h₁ := tprovable_subst_of_models (T := T) (φ := psatAndClause) (by
    intro W _ _ e;
    simpa [psatAndClause, andCond] using fun (h : e 3 = e 1 ^⋏ e 2) ↦ by
      rw [h, BoundedSatisfied.and_iff]) ![a, 𝕹 p, 𝕹 q, 𝕹 (p ^⋏ q)];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (φ := andCond.val) (by simp)
    (w := ![p ^⋏ q, p, q]) (by simp [andCond]);
  rw [numeral_vec_three] at h₂;
  have h₃ : T.internalize V ⊢
      (⌜andCond.val⌝ : Semiformula V ℒₒᵣ 3).subst ![𝕹 (p ^⋏ q), 𝕹 p, 𝕹 q] 🡒
        (psatF a (p ^⋏ q) 🡘 psatF a p ⋏ psatF a q) := by
    simpa [psatAndClause, psatF, typed_quote_rew_subst, Semiformula.substs_substs,
      Matrix.vecHead, Matrix.vecTail] using h₁;
  exact h₃ ⨀ h₂

private noncomputable def orCond : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “c p q. !qqOrDef c p q ∧ !isBounded.sigma p ∧ !(isUFormula ℒₒᵣ).sigma p ∧
    !isBounded.sigma q ∧ !(isUFormula ℒₒᵣ).sigma q”

private noncomputable def psatOrClause : ArithmeticSemisentence 4 :=
  orCond.val/[#3, #1, #2] 🡒
    (psatDef.val/[#0, #3] 🡘 psatDef.val/[#0, #1] ⋎ psatDef.val/[#0, #2])

lemma tprovable_psatF_or (a : Term V ℒₒᵣ) {p q : V} (hp : IsBounded p) (hp' : IsUFormula ℒₒᵣ p)
    (hq : IsBounded q) (hq' : IsUFormula ℒₒᵣ q) :
    T.internalize V ⊢ psatF a (p ^⋎ q) 🡘 psatF a p ⋎ psatF a q := by
  have h₁ := tprovable_subst_of_models (T := T) (φ := psatOrClause) (by
    intro W _ _ e;
    simpa [psatOrClause, orCond] using
      fun (h : e 3 = e 1 ^⋎ e 2) (hp : IsBounded (e 1)) (hp' : IsUFormula ℒₒᵣ (e 1))
        (hq : IsBounded (e 2)) (hq' : IsUFormula ℒₒᵣ (e 2)) ↦ by
      rw [h, BoundedSatisfied.or_iff hp hp' hq hq']) ![a, 𝕹 p, 𝕹 q, 𝕹 (p ^⋎ q)];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (φ := orCond.val) (by simp)
    (w := ![p ^⋎ q, p, q]) (by simp [orCond, hp, hp', hq, hq']);
  rw [numeral_vec_three] at h₂;
  have h₃ : T.internalize V ⊢
      (⌜orCond.val⌝ : Semiformula V ℒₒᵣ 3).subst ![𝕹 (p ^⋎ q), 𝕹 p, 𝕹 q] 🡒
        (psatF a (p ^⋎ q) 🡘 psatF a p ⋎ psatF a q) := by
    simpa [psatOrClause, psatF, typed_quote_rew_subst, Semiformula.substs_substs,
      Matrix.vecHead, Matrix.vecTail] using h₁;
  exact h₃ ⨀ h₂

private noncomputable def eqCond : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “c t u. !qqEQDef c t u ∧ !(isUTerm ℒₒᵣ).sigma t ∧ !(isUTerm ℒₒᵣ).sigma u”

private noncomputable def psatEqClause : ArithmeticSemisentence 6 :=
  eqCond.val/[#5, #3, #4] 🡒 tvDef.val/[#0, #2, #3] 🡒 tvDef.val/[#1, #2, #4] 🡒
    (psatDef.val/[#2, #5] 🡘 “#0 = #1”)

lemma tprovable_psatF_eq (y z a : Term V ℒₒᵣ) {t u : V} (ht : IsUTerm ℒₒᵣ t)
    (hu : IsUTerm ℒₒᵣ u) :
    T.internalize V ⊢ tvF y a t 🡒 tvF z a u 🡒 (psatF a (t ^= u) 🡘 (Semiformula.equal y z)) := by
  have h₁ := tprovable_subst_of_models (T := T) (φ := psatEqClause) (by
    intro W _ _ e;
    simpa [psatEqClause, eqCond] using
      fun (h : e 5 = e 3 ^= e 4) (ht : IsUTerm ℒₒᵣ (e 3)) (hu : IsUTerm ℒₒᵣ (e 4))
        (h₁ : e 0 = termVal (dec (e 2)) (e 3)) (h₂ : e 1 = termVal (dec (e 2)) (e 4)) ↦ by
        simp [h, h₁, h₂, ht, hu])
    ![y, z, a, 𝕹 t, 𝕹 u, 𝕹 (t ^= u)];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (φ := eqCond.val) (by simp)
    (w := ![t ^= u, t, u]) (by simp [eqCond, ht, hu]);
  rw [numeral_vec_three] at h₂;
  have h₃ : T.internalize V ⊢
      (⌜eqCond.val⌝ : Semiformula V ℒₒᵣ 3).subst ![𝕹 (t ^= u), 𝕹 t, 𝕹 u] 🡒
        tvF y a t 🡒 tvF z a u 🡒 (psatF a (t ^= u) 🡘 (Semiformula.equal y z)) := by
    simpa [psatEqClause, psatF, tvF, typed_quote_rew_subst, Semiformula.substs_substs,
      Matrix.vecHead, Matrix.vecTail] using h₁;
  exact h₃ ⨀ h₂

private noncomputable def neqCond : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “c t u. !qqNEQDef c t u ∧ !(isUTerm ℒₒᵣ).sigma t ∧ !(isUTerm ℒₒᵣ).sigma u”

private noncomputable def psatNeqClause : ArithmeticSemisentence 6 :=
  neqCond.val/[#5, #3, #4] 🡒 tvDef.val/[#0, #2, #3] 🡒 tvDef.val/[#1, #2, #4] 🡒
    (psatDef.val/[#2, #5] 🡘 “#0 ≠ #1”)

lemma tprovable_psatF_neq (y z a : Term V ℒₒᵣ) {t u : V} (ht : IsUTerm ℒₒᵣ t)
    (hu : IsUTerm ℒₒᵣ u) :
    T.internalize V ⊢ tvF y a t 🡒 tvF z a u 🡒 (psatF a (t ^≠ u) 🡘 (∼Semiformula.equal y z)) := by
  have h₁ := tprovable_subst_of_models (T := T) (φ := psatNeqClause) (by
    intro W _ _ e;
    simpa [psatNeqClause, neqCond] using
      fun (h : e 5 = e 3 ^≠ e 4) (ht : IsUTerm ℒₒᵣ (e 3)) (hu : IsUTerm ℒₒᵣ (e 4))
        (h₁ : e 0 = termVal (dec (e 2)) (e 3)) (h₂ : e 1 = termVal (dec (e 2)) (e 4)) ↦ by
        simp [h, h₁, h₂, ht, hu])
    ![y, z, a, 𝕹 t, 𝕹 u, 𝕹 (t ^≠ u)];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (φ := neqCond.val) (by simp)
    (w := ![t ^≠ u, t, u]) (by simp [neqCond, ht, hu]);
  rw [numeral_vec_three] at h₂;
  have h₃ : T.internalize V ⊢
      (⌜neqCond.val⌝ : Semiformula V ℒₒᵣ 3).subst ![𝕹 (t ^≠ u), 𝕹 t, 𝕹 u] 🡒
        tvF y a t 🡒 tvF z a u 🡒 (psatF a (t ^≠ u) 🡘 (∼Semiformula.equal y z)) := by
    simpa [psatNeqClause, psatF, tvF, typed_quote_rew_subst, Semiformula.substs_substs,
      Matrix.vecHead, Matrix.vecTail] using h₁;
  exact h₃ ⨀ h₂

private noncomputable def ltCond : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “c t u. !qqLTDef c t u ∧ !(isUTerm ℒₒᵣ).sigma t ∧ !(isUTerm ℒₒᵣ).sigma u”

private noncomputable def psatLtClause : ArithmeticSemisentence 6 :=
  ltCond.val/[#5, #3, #4] 🡒 tvDef.val/[#0, #2, #3] 🡒 tvDef.val/[#1, #2, #4] 🡒
    (psatDef.val/[#2, #5] 🡘 “#0 < #1”)

lemma tprovable_psatF_lt (y z a : Term V ℒₒᵣ) {t u : V} (ht : IsUTerm ℒₒᵣ t)
    (hu : IsUTerm ℒₒᵣ u) :
    T.internalize V ⊢ tvF y a t 🡒 tvF z a u 🡒 (psatF a (t ^< u) 🡘 (Semiterm.lessThan y z)) := by
  have h₁ := tprovable_subst_of_models (T := T) (φ := psatLtClause) (by
    intro W _ _ e;
    simpa [psatLtClause, ltCond] using
      fun (h : e 5 = e 3 ^< e 4) (ht : IsUTerm ℒₒᵣ (e 3)) (hu : IsUTerm ℒₒᵣ (e 4))
        (h₁ : e 0 = termVal (dec (e 2)) (e 3)) (h₂ : e 1 = termVal (dec (e 2)) (e 4)) ↦ by
        simp [h, h₁, h₂, ht, hu])
    ![y, z, a, 𝕹 t, 𝕹 u, 𝕹 (t ^< u)];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (φ := ltCond.val) (by simp)
    (w := ![t ^< u, t, u]) (by simp [ltCond, ht, hu]);
  rw [numeral_vec_three] at h₂;
  have h₃ : T.internalize V ⊢
      (⌜ltCond.val⌝ : Semiformula V ℒₒᵣ 3).subst ![𝕹 (t ^< u), 𝕹 t, 𝕹 u] 🡒
        tvF y a t 🡒 tvF z a u 🡒 (psatF a (t ^< u) 🡘 (Semiterm.lessThan y z)) := by
    simpa [psatLtClause, psatF, tvF, typed_quote_rew_subst, Semiformula.substs_substs,
      Matrix.vecHead, Matrix.vecTail] using h₁;
  exact h₃ ⨀ h₂

private noncomputable def nltCond : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “c t u. !qqNLTDef c t u ∧ !(isUTerm ℒₒᵣ).sigma t ∧ !(isUTerm ℒₒᵣ).sigma u”

private noncomputable def psatNltClause : ArithmeticSemisentence 6 :=
  nltCond.val/[#5, #3, #4] 🡒 tvDef.val/[#0, #2, #3] 🡒 tvDef.val/[#1, #2, #4] 🡒
    (psatDef.val/[#2, #5] 🡘 “¬#0 < #1”)

lemma tprovable_psatF_nlt (y z a : Term V ℒₒᵣ) {t u : V} (ht : IsUTerm ℒₒᵣ t)
    (hu : IsUTerm ℒₒᵣ u) :
    T.internalize V ⊢ tvF y a t 🡒 tvF z a u 🡒
      (psatF a (Arithmetic.qqNLT t u) 🡘 (Semiterm.notLessThan y z)) := by
  have h₁ := tprovable_subst_of_models (T := T) (φ := psatNltClause) (by
    intro W _ _ e;
    simpa [psatNltClause, nltCond] using
      fun (h : e 5 = Arithmetic.qqNLT (e 3) (e 4)) (ht : IsUTerm ℒₒᵣ (e 3)) (hu : IsUTerm ℒₒᵣ (e 4))
        (h₁ : e 0 = termVal (dec (e 2)) (e 3)) (h₂ : e 1 = termVal (dec (e 2)) (e 4)) ↦ by
        simp [h, h₁, h₂, ht, hu])
    ![y, z, a, 𝕹 t, 𝕹 u, 𝕹 (Arithmetic.qqNLT t u)];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (φ := nltCond.val) (by simp)
    (w := ![Arithmetic.qqNLT t u, t, u]) (by simp [nltCond, ht, hu]);
  rw [numeral_vec_three] at h₂;
  have h₃ : T.internalize V ⊢
      (⌜nltCond.val⌝ : Semiformula V ℒₒᵣ 3).subst ![𝕹 (Arithmetic.qqNLT t u), 𝕹 t, 𝕹 u] 🡒
        tvF y a t 🡒 tvF z a u 🡒 (psatF a (Arithmetic.qqNLT t u) 🡘 (Semiterm.notLessThan y z)) := by
    simpa [psatNltClause, psatF, tvF, typed_quote_rew_subst, Semiformula.substs_substs,
      Matrix.vecHead, Matrix.vecTail] using h₁;
  exact h₃ ⨀ h₂

private noncomputable def ballCond : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “c t q u. !(termBShiftGraph ℒₒᵣ) u t ∧ !qqBallDef c u q ∧ !(isUTerm ℒₒᵣ).sigma t ∧
    !isBounded.sigma q ∧ !(isUFormula ℒₒᵣ).sigma q”

private noncomputable def psatBallClause : ArithmeticSemisentence 6 :=
  ballCond.val/[#4, #2, #3, #5] 🡒 tvDef.val/[#0, #1, #2] 🡒
    (psatDef.val/[#1, #4] 🡘 ∀¹ (“#0 < #1” 🡒 psatDef.val/[‘(#0 + #2) * (#0 + #2) + #2 + 1’, #4]))

lemma tprovable_psatF_ball (y a : Term V ℒₒᵣ) {t q : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsBounded q)
    (hq' : IsUFormula ℒₒᵣ q) :
    T.internalize V ⊢ tvF y a t 🡒
      (psatF a (qqBall (termBShift ℒₒᵣ t) q) 🡘
        ∀¹ (Semiterm.lessThan (Semiterm.bvar 0) y.bShift 🡒
          psatF (pTerm (Semiterm.bvar 0) a.bShift) q)) := by
  have h₁ := tprovable_subst_of_models (T := T) (φ := psatBallClause) (by
    intro W _ _ e;
    simpa [psatBallClause, ballCond, add_mul_add_eq_ppair] using
      fun (hu : e 5 = termBShift ℒₒᵣ (e 2)) (h : e 4 = qqBall (e 5) (e 3)) (ht : IsUTerm ℒₒᵣ (e 2))
        (hq : IsBounded (e 3)) (hq' : IsUFormula ℒₒᵣ (e 3))
        (h₁ : e 0 = termVal (dec (e 1)) (e 2)) ↦ by
        simp [h, hu, h₁, ht, hq, hq'])
    ![y, a, 𝕹 t, 𝕹 q, 𝕹 (qqBall (termBShift ℒₒᵣ t) q), 𝕹 (termBShift ℒₒᵣ t)];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (φ := ballCond.val) (by simp)
    (w := ![qqBall (termBShift ℒₒᵣ t) q, t, q, termBShift ℒₒᵣ t]) (by simp [ballCond, ht, hq, hq']);
  rw [numeral_vec_four] at h₂;
  have h₃ : T.internalize V ⊢
      (⌜ballCond.val⌝ : Semiformula V ℒₒᵣ 4).subst
          ![𝕹 (qqBall (termBShift ℒₒᵣ t) q), 𝕹 t, 𝕹 q, 𝕹 (termBShift ℒₒᵣ t)] 🡒
        tvF y a t 🡒
          (psatF a (qqBall (termBShift ℒₒᵣ t) q) 🡘
            ∀¹ (Semiterm.lessThan (Semiterm.bvar 0) y.bShift 🡒
              psatF (pTerm (Semiterm.bvar 0) a.bShift) q)) := by
    simpa [psatBallClause, psatF, tvF, pTerm, typed_quote_rew_subst, Semiformula.substs_substs,
      SemitermVec.q, Matrix.vecHead, Matrix.vecTail] using h₁;
  exact h₃ ⨀ h₂

private noncomputable def bexCond : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “c t q u. !(termBShiftGraph ℒₒᵣ) u t ∧ !qqBexDef c u q ∧ !(isUTerm ℒₒᵣ).sigma t ∧
    !isBounded.sigma q ∧ !(isUFormula ℒₒᵣ).sigma q”

private noncomputable def psatBexClause : ArithmeticSemisentence 6 :=
  bexCond.val/[#4, #2, #3, #5] 🡒 tvDef.val/[#0, #1, #2] 🡒
    (psatDef.val/[#1, #4] 🡘 ∃¹ (“#0 < #1” ⋏ psatDef.val/[‘(#0 + #2) * (#0 + #2) + #2 + 1’, #4]))

lemma tprovable_psatF_bex (y a : Term V ℒₒᵣ) {t q : V} (ht : IsUTerm ℒₒᵣ t) (hq : IsBounded q)
    (hq' : IsUFormula ℒₒᵣ q) :
    T.internalize V ⊢ tvF y a t 🡒
      (psatF a (qqBex (termBShift ℒₒᵣ t) q) 🡘
        ∃¹ (Semiterm.lessThan (Semiterm.bvar 0) y.bShift ⋏
          psatF (pTerm (Semiterm.bvar 0) a.bShift) q)) := by
  have h₁ := tprovable_subst_of_models (T := T) (φ := psatBexClause) (by
    intro W _ _ e;
    simpa [psatBexClause, bexCond, add_mul_add_eq_ppair] using
      fun (hu : e 5 = termBShift ℒₒᵣ (e 2)) (h : e 4 = qqBex (e 5) (e 3)) (ht : IsUTerm ℒₒᵣ (e 2))
        (hq : IsBounded (e 3)) (hq' : IsUFormula ℒₒᵣ (e 3))
        (h₁ : e 0 = termVal (dec (e 1)) (e 2)) ↦ by
        simp [h, hu, h₁, ht])
    ![y, a, 𝕹 t, 𝕹 q, 𝕹 (qqBex (termBShift ℒₒᵣ t) q), 𝕹 (termBShift ℒₒᵣ t)];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (φ := bexCond.val) (by simp)
    (w := ![qqBex (termBShift ℒₒᵣ t) q, t, q, termBShift ℒₒᵣ t]) (by simp [bexCond, ht, hq, hq']);
  rw [numeral_vec_four] at h₂;
  have h₃ : T.internalize V ⊢
      (⌜bexCond.val⌝ : Semiformula V ℒₒᵣ 4).subst
          ![𝕹 (qqBex (termBShift ℒₒᵣ t) q), 𝕹 t, 𝕹 q, 𝕹 (termBShift ℒₒᵣ t)] 🡒
        tvF y a t 🡒
          (psatF a (qqBex (termBShift ℒₒᵣ t) q) 🡘
            ∃¹ (Semiterm.lessThan (Semiterm.bvar 0) y.bShift ⋏
              psatF (pTerm (Semiterm.bvar 0) a.bShift) q)) := by
    simpa [psatBexClause, psatF, tvF, pTerm, typed_quote_rew_subst, Semiformula.substs_substs,
      SemitermVec.q, Matrix.vecHead, Matrix.vecTail] using h₁;
  exact h₃ ⨀ h₂

/-! ### The assignment terms -/

section assignment

/-- The code of the term `(t + u) * (t + u) + u + 1`. -/
noncomputable def pTermCode (t u : V) : V := (t ^+ u) ^* (t ^+ u) ^+ u ^+ numeral 1

noncomputable def _root_.FFL.FirstOrder.Arithmetic.pTermCodeGraph : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “y t u. ∃ a, !qqAddGraph a t u ∧ ∃ m, !qqMulGraph m a a ∧ ∃ b, !qqAddGraph b m u ∧
    ∃ o, !numeralGraph o 1 ∧ !qqAddGraph y b o”

instance pTermCode_defined : 𝚺ᴬ₁-Function₂ (pTermCode : V → V → V) via pTermCodeGraph :=
  .mk fun v ↦ by simp [pTermCodeGraph, pTermCode]

instance pTermCode_definable : 𝚺ᴬ₁-Function₂ (pTermCode : V → V → V) :=
  pTermCode_defined.to_definable

@[simp] lemma val_pTerm {n : ℕ} (t u : Semiterm V ℒₒᵣ n) :
    (pTerm t u).val = pTermCode t.val u.val := by
  simp [pTerm, pTermCode]

namespace AssignmentCode

noncomputable def blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. !numeralGraph y 0”
  succ := .mkSigma “y ih n. ∃ f, !qqFvarDef f 0 ∧ ∃ s, !(termShiftGraph ℒₒᵣ) s ih ∧
    !pTermCodeGraph y f s”

noncomputable def construction : PR.Construction V blueprint where
  zero _ := numeral 0
  succ _ _ ih := pTermCode (^&0) (termShift ℒₒᵣ ih)
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]

end AssignmentCode

/-- The code of the term assigning `^&i` to the bound variable `^#i` for `i < n`. -/
noncomputable def assignmentCode (n : V) : V := AssignmentCode.construction.result ![] n

@[simp] lemma assignmentCode_zero : assignmentCode (0 : V) = numeral 0 := by
  simp [assignmentCode, AssignmentCode.construction]

@[simp] lemma assignmentCode_succ (n : V) :
    assignmentCode (n + 1) = pTermCode (^&0) (termShift ℒₒᵣ (assignmentCode n)) := by
  simp [assignmentCode, AssignmentCode.construction]

noncomputable def _root_.FFL.FirstOrder.Arithmetic.assignmentCodeGraph : 𝚺ᴬ₁.Semisentence 2 :=
  AssignmentCode.blueprint.resultDef

instance assignmentCode_defined : 𝚺ᴬ₁-Function₁ (assignmentCode : V → V) via assignmentCodeGraph :=
  .mk fun v ↦ by
    simp [AssignmentCode.construction.result_defined_iff, assignmentCodeGraph]; rfl

instance assignmentCode_definable : 𝚺ᴬ₁-Function₁ (assignmentCode : V → V) :=
  assignmentCode_defined.to_definable

instance assignmentCode_definable' {Γ : Polarity} {m : ℕ} :
    Γᴬ_[m + 1]-Function₁ (assignmentCode : V → V) := assignmentCode_definable.of_sigmaOne

lemma isSemiterm_assignmentCode (n : V) : IsSemiterm ℒₒᵣ 0 (assignmentCode n) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    simpa using (pTerm (Semiterm.fvar 0) (⟨assignmentCode n, ih⟩ : Term V ℒₒᵣ).shift).isSemiterm

/-- The internal term assigning `&i` to the bound variable `#i` for `i < n`. -/
noncomputable def assignment (n : V) : Term V ℒₒᵣ :=
  ⟨assignmentCode n, isSemiterm_assignmentCode n⟩

@[simp] lemma val_assignment (n : V) : (assignment n).val = assignmentCode n := rfl

lemma assignment_zero : assignment (0 : V) = 𝕹 0 := by ext; simp [assignment]

lemma assignment_succ (n : V) :
    assignment (n + 1) = pTerm (Semiterm.fvar 0) (assignment n).shift := by
  ext; simp [assignment]

lemma val_tvF (y a : Term V ℒₒᵣ) (t : V) :
    (tvF y a t).val = subst ℒₒᵣ ?[y.val, a.val, numeral t] (⌜tvDef.val⌝ : V) := by
  simp [tvF, Sentence.quote_eq]

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

lemma tprovable_tvF_fvar_assignment (n : V) :
    ∀ i < n, T.internalize V ⊢ tvF (Semiterm.fvar i) (assignment n) (^#i) := by
  suffices ∀ i < n,
      Provable T (subst ℒₒᵣ ?[^&i, assignmentCode n, numeral (^#i)] (⌜tvDef.val⌝ : V)) by
    intro i hi;
    apply tprovable_iff_provable.mpr;
    simpa [val_tvF] using this i hi;
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    intro i hi;
    rcases zero_or_succ i with rfl | ⟨i, rfl⟩
    · have h := tprovable_tvF_bvar_zero (T := T) (Semiterm.fvar 0) (assignment n).shift;
      rw [← assignment_succ] at h;
      simpa [val_tvF] using tprovable_iff_provable.mp h;
    · have h₁ : T.internalize V ⊢ tvF (Semiterm.fvar i) (assignment n) (^#i) :=
        tprovable_iff_provable.mpr <| by simpa [val_tvF] using ih i (by simpa using hi);
      have h₂ := tprovable_tvF_bvar_succ (T := T) (Semiterm.fvar (i + 1)) (Semiterm.fvar 0)
        (assignment n).shift i;
      have h₃ : T.internalize V ⊢ tvF (Semiterm.fvar (i + 1)) (assignment n).shift (^#i) := by
        simpa using TProof.shift! h₁;
      have h₄ := h₂ ⨀ h₃;
      rw [← assignment_succ] at h₄;
      simpa [val_tvF] using tprovable_iff_provable.mp h₄

end assignment

/-! ### Disquotation for terms -/

section termDisquotation

lemma LOR_func_cases {k f v : V} (hf : (ℒₒᵣ).IsFunc k f) (hv : IsUTermVec ℒₒᵣ k v) :
    (k = 0 ∧ ^func k f v = (𝟎 : V)) ∨ (k = 0 ∧ ^func k f v = (𝟏 : V)) ∨
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ k = 2 ∧ v = ?[t, u] ∧ ^func k f v = t ^+ u) ∨
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ k = 2 ∧ v = ?[t, u] ∧ ^func k f v = t ^* u) := by
  rcases Arithmetic.isFunc_iff_LOR.mp hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; simp at hv; simp [hv, qqZero_eq_qqFunc]; rfl
  · right; left; simp at hv; simp [hv, qqOne_eq_qqFunc]; rfl
  · obtain ⟨a, b, ha, hb, rfl⟩ := IsUTermVec.two_iff.mp hv
    right; right; left; use a, b; simp [ha, hb, qqAdd]; rfl
  · obtain ⟨a, b, ha, hb, rfl⟩ := IsUTermVec.two_iff.mp hv
    right; right; right; use a, b; simp [ha, hb, qqMul]; rfl

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

omit [𝗜𝚺₁ ⪯ T] in
lemma tprovable_tvF_iff (y a : Term V ℒₒᵣ) (t : V) :
    T.internalize V ⊢ tvF y a t ↔
      Provable T (subst ℒₒᵣ ?[y.val, a.val, numeral t] (⌜tvDef.val⌝ : V)) := by
  rw [tprovable_iff_provable, val_tvF]

/-- The value of a term without free variables under `assignment n` is the term obtained by
replacing each bound variable `#i` by `&i`. -/
lemma provable_tvF_termSubst (n : V) :
    ∀ t, IsSemiterm ℒₒᵣ n t → termShift ℒₒᵣ t = t →
      Provable T (subst ℒₒᵣ ?[termSubst ℒₒᵣ (fvarVec n) t, assignmentCode n, numeral t]
        (⌜tvDef.val⌝ : V)) := by
  intro t ht;
  apply IsSemiterm.induction 𝚺 (P := fun t ↦ termShift ℒₒᵣ t = t →
    Provable T (subst ℒₒᵣ ?[termSubst ℒₒᵣ (fvarVec n) t, assignmentCode n, numeral t]
      (⌜tvDef.val⌝ : V))) ?_ ?_ ?_ ?_ t ht;
  · definability
  · intro z hz _;
    rw [termSubst_bvar, nth_fvarVec n z hz];
    simpa using (tprovable_tvF_iff _ _ _).mp (tprovable_tvF_fvar_assignment (T := T) n z hz);
  · intro x h;
    simp at h;
  · intro k f v hf hv ih hs;
    have hvn := isSemitermVec_fvarVec (L := ℒₒᵣ) n 0;
    rcases LOR_func_cases hf hv.isUTerm with
      ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨a, b, ha, hb, rfl, rfl, h⟩ | ⟨a, b, ha, hb, rfl, rfl, h⟩
    · rw [h];
      simpa [qqZero_eq_qqFunc] using
        (tprovable_tvF_iff _ _ _).mp (tprovable_tvF_zero (T := T) (assignment n));
    · rw [h];
      simpa [qqOne_eq_qqFunc] using
        (tprovable_tvF_iff _ _ _).mp (tprovable_tvF_one (T := T) (assignment n));
    · rw [h] at hs ⊢;
      have hab : termShift ℒₒᵣ a = a ∧ termShift ℒₒᵣ b = b := by simpa [qqAdd, ha, hb] using hs;
      have ha' : IsSemiterm ℒₒᵣ n a := by simpa using hv.nth (i := 0) (by simp);
      have hb' : IsSemiterm ℒₒᵣ n b := by simpa using hv.nth (i := 1) (by simp);
      let a' : Term V ℒₒᵣ := ⟨termSubst ℒₒᵣ (fvarVec n) a, hvn.termSubst ha'⟩;
      let b' : Term V ℒₒᵣ := ⟨termSubst ℒₒᵣ (fvarVec n) b, hvn.termSubst hb'⟩;
      have h₁ : T.internalize V ⊢ tvF a' (assignment n) a :=
        (tprovable_tvF_iff _ _ _).mpr <| by simpa using ih 0 (by simp) (by simpa using hab.1);
      have h₂ : T.internalize V ⊢ tvF b' (assignment n) b :=
        (tprovable_tvF_iff _ _ _).mpr <| by simpa using ih 1 (by simp) (by simpa using hab.2);
      simpa [a', b', qqAdd, ha, hb] using
        (tprovable_tvF_iff _ _ _).mp
          (tprovable_tvF_add (T := T) a' b' (assignment n) ha hb ⨀ h₁ ⨀ h₂);
    · rw [h] at hs ⊢;
      have hab : termShift ℒₒᵣ a = a ∧ termShift ℒₒᵣ b = b := by simpa [qqMul, ha, hb] using hs;
      have ha' : IsSemiterm ℒₒᵣ n a := by simpa using hv.nth (i := 0) (by simp);
      have hb' : IsSemiterm ℒₒᵣ n b := by simpa using hv.nth (i := 1) (by simp);
      let a' : Term V ℒₒᵣ := ⟨termSubst ℒₒᵣ (fvarVec n) a, hvn.termSubst ha'⟩;
      let b' : Term V ℒₒᵣ := ⟨termSubst ℒₒᵣ (fvarVec n) b, hvn.termSubst hb'⟩;
      have h₁ : T.internalize V ⊢ tvF a' (assignment n) a :=
        (tprovable_tvF_iff _ _ _).mpr <| by simpa using ih 0 (by simp) (by simpa using hab.1);
      have h₂ : T.internalize V ⊢ tvF b' (assignment n) b :=
        (tprovable_tvF_iff _ _ _).mpr <| by simpa using ih 1 (by simp) (by simpa using hab.2);
      simpa [a', b', qqMul, ha, hb] using
        (tprovable_tvF_iff _ _ _).mp
          (tprovable_tvF_mul (T := T) a' b' (assignment n) ha hb ⨀ h₁ ⨀ h₂)

/-- The term obtained from `t` by replacing each bound variable `#i` by `&i`. -/
noncomputable def instTerm (n t : V) (ht : IsSemiterm ℒₒᵣ n t) : Term V ℒₒᵣ :=
  ⟨termSubst ℒₒᵣ (fvarVec n) t, (isSemitermVec_fvarVec n 0).termSubst ht⟩

lemma tprovable_tvF_instTerm {n t : V} (ht : IsSemiterm ℒₒᵣ n t) (hs : termShift ℒₒᵣ t = t) :
    T.internalize V ⊢ tvF (instTerm n t ht) (assignment n) t :=
  (tprovable_tvF_iff _ _ _).mpr <| by simpa [instTerm] using provable_tvF_termSubst n t ht hs

end termDisquotation

/-! ### Disquotation for $\Delta_0$ formulas -/

section formulaDisquotation

lemma adjoin_termShiftVec_fvarVec (n : V) :
    ^&0 ∷ termShiftVec ℒₒᵣ n (fvarVec n) = fvarVec (n + 1) := by
  have hv := (isSemitermVec_fvarVec (L := ℒₒᵣ) n 0).isUTerm
  apply nth_ext' (n + 1) (by simp [hv]) (by simp)
  intro i hi
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · rw [nth_fvarVec (n + 1) 0 (by simp)]; simp
  · have hi' : i < n := by simpa using hi
    rw [nth_fvarVec (n + 1) (i + 1) hi]; simp [nth_termShiftVec hv hi', nth_fvarVec n i hi']

lemma free_subst_qVec_fvarVec {n q : V} (hq : IsSemiformula ℒₒᵣ (n + 1) q)
    (hs : shift ℒₒᵣ q = q) :
    free ℒₒᵣ (subst ℒₒᵣ (qVec ℒₒᵣ (fvarVec n)) q) = subst ℒₒᵣ (fvarVec (n + 1)) q := by
  have hw := isSemitermVec_fvarVec (L := ℒₒᵣ) n 0
  rw [free, shift_substs hq hw.qVec, hs, termShift_qVec hw,
    substs1_subst_qVec hw.termShiftVec hq (by simp), adjoin_termShiftVec_fvarVec]


/-- The formula obtained from `p` by replacing each bound variable `#i` by `&i`. -/
noncomputable def instFormula (n p : V) (hp : IsSemiformula ℒₒᵣ n p) : Formula V ℒₒᵣ :=
  ⟨subst ℒₒᵣ (fvarVec n) p, hp.subst (isSemitermVec_fvarVec n 0)⟩

lemma equal_eq_equals (t u : Term V ℒₒᵣ) : Semiformula.equal t u = Semiterm.equals t u := by
  ext; simp [Semiformula.equal, Arithmetic.qqEQ]

lemma neg_equals (t u : Term V ℒₒᵣ) : ∼Semiterm.equals t u = Semiterm.notEquals t u := by
  ext; simp [Arithmetic.qqNEQ]

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

lemma tprovable_instTerm_eq_iff {n t u : V} (ht : IsSemiterm ℒₒᵣ n t) (hu : IsSemiterm ℒₒᵣ n u)
    (hts : termShift ℒₒᵣ t = t) (hus : termShift ℒₒᵣ u = u) :
    T.internalize V ⊢ Semiterm.equals (instTerm n t ht) (instTerm n u hu) 🡘
      psatF (assignment n) (t ^= u) := by
  have h₁ := tprovable_tvF_instTerm (T := T) ht hts;
  have h₂ := tprovable_tvF_instTerm (T := T) hu hus;
  have h₃ := tprovable_psatF_eq (T := T) (instTerm n t ht) (instTerm n u hu) (assignment n)
    ht.isUTerm hu.isUTerm;
  rw [equal_eq_equals] at h₃;
  exact E_symm (h₃ ⨀ h₁ ⨀ h₂)

lemma tprovable_instTerm_neq_iff {n t u : V} (ht : IsSemiterm ℒₒᵣ n t) (hu : IsSemiterm ℒₒᵣ n u)
    (hts : termShift ℒₒᵣ t = t) (hus : termShift ℒₒᵣ u = u) :
    T.internalize V ⊢ Semiterm.notEquals (instTerm n t ht) (instTerm n u hu) 🡘
      psatF (assignment n) (t ^≠ u) := by
  have h₁ := tprovable_tvF_instTerm (T := T) ht hts;
  have h₂ := tprovable_tvF_instTerm (T := T) hu hus;
  have h₃ := tprovable_psatF_neq (T := T) (instTerm n t ht) (instTerm n u hu) (assignment n)
    ht.isUTerm hu.isUTerm;
  rw [equal_eq_equals, neg_equals] at h₃;
  exact E_symm (h₃ ⨀ h₁ ⨀ h₂)

lemma tprovable_instTerm_lt_iff {n t u : V} (ht : IsSemiterm ℒₒᵣ n t) (hu : IsSemiterm ℒₒᵣ n u)
    (hts : termShift ℒₒᵣ t = t) (hus : termShift ℒₒᵣ u = u) :
    T.internalize V ⊢ Semiterm.lessThan (instTerm n t ht) (instTerm n u hu) 🡘
      psatF (assignment n) (t ^< u) := by
  have h₁ := tprovable_tvF_instTerm (T := T) ht hts;
  have h₂ := tprovable_tvF_instTerm (T := T) hu hus;
  have h₃ := tprovable_psatF_lt (T := T) (instTerm n t ht) (instTerm n u hu) (assignment n)
    ht.isUTerm hu.isUTerm;
  exact E_symm (h₃ ⨀ h₁ ⨀ h₂)

lemma tprovable_instTerm_nlt_iff {n t u : V} (ht : IsSemiterm ℒₒᵣ n t) (hu : IsSemiterm ℒₒᵣ n u)
    (hts : termShift ℒₒᵣ t = t) (hus : termShift ℒₒᵣ u = u) :
    T.internalize V ⊢ Semiterm.notLessThan (instTerm n t ht) (instTerm n u hu) 🡘
      psatF (assignment n) (Arithmetic.qqNLT t u) := by
  have h₁ := tprovable_tvF_instTerm (T := T) ht hts;
  have h₂ := tprovable_tvF_instTerm (T := T) hu hus;
  have h₃ := tprovable_psatF_nlt (T := T) (instTerm n t ht) (instTerm n u hu) (assignment n)
    ht.isUTerm hu.isUTerm;
  exact E_symm (h₃ ⨀ h₁ ⨀ h₂)

omit [𝗜𝚺₁ ⪯ T] in
lemma tprovable_instFormula_iff {n p : V} (hp : IsSemiformula ℒₒᵣ n p) :
    T.internalize V ⊢ instFormula n p hp 🡘 psatF (assignment n) p ↔
      Provable T (iff ℒₒᵣ (subst ℒₒᵣ (fvarVec n) p)
        (subst ℒₒᵣ ?[assignmentCode n, numeral p] (⌜psatDef.val⌝ : V))) := by
  rw [tprovable_iff_provable];
  simp [instFormula, psatF, Sentence.quote_eq]

lemma tprovable_instFormula_and {n p q : V} (hp : IsSemiformula ℒₒᵣ n p)
    (hq : IsSemiformula ℒₒᵣ n q)
    (h₁ : T.internalize V ⊢ instFormula n p hp 🡘 psatF (assignment n) p)
    (h₂ : T.internalize V ⊢ instFormula n q hq 🡘 psatF (assignment n) q) :
    T.internalize V ⊢ instFormula n (p ^⋏ q) (by simp [hp, hq]) 🡘
      psatF (assignment n) (p ^⋏ q) := by
  have e : instFormula n (p ^⋏ q) (by simp [hp, hq]) = instFormula n p hp ⋏ instFormula n q hq := by
    ext; simp [instFormula, hp.isUFormula, hq.isUFormula];
  have h₃ := tprovable_psatF_and (T := T) (assignment n) p q;
  rw [e];
  generalize instFormula n p hp = A at h₁ ⊢;
  generalize instFormula n q hq = B at h₂ ⊢;
  generalize psatF (assignment n) p = X at h₁ h₃;
  generalize psatF (assignment n) q = Y at h₂ h₃;
  generalize psatF (assignment n) (p ^⋏ q) = Z at h₃ ⊢;
  cl_prover [h₁, h₂, h₃]

lemma tprovable_instFormula_or {n p q : V} (hp : IsSemiformula ℒₒᵣ n p)
    (hq : IsSemiformula ℒₒᵣ n q) (hpb : IsBounded p) (hqb : IsBounded q)
    (h₁ : T.internalize V ⊢ instFormula n p hp 🡘 psatF (assignment n) p)
    (h₂ : T.internalize V ⊢ instFormula n q hq 🡘 psatF (assignment n) q) :
    T.internalize V ⊢ instFormula n (p ^⋎ q) (by simp [hp, hq]) 🡘
      psatF (assignment n) (p ^⋎ q) := by
  have e : instFormula n (p ^⋎ q) (by simp [hp, hq]) = instFormula n p hp ⋎ instFormula n q hq := by
    ext; simp [instFormula, hp.isUFormula, hq.isUFormula];
  have h₃ := tprovable_psatF_or (T := T) (assignment n) hpb hp.isUFormula hqb hq.isUFormula;
  rw [e];
  generalize instFormula n p hp = A at h₁ ⊢;
  generalize instFormula n q hq = B at h₂ ⊢;
  generalize psatF (assignment n) p = X at h₁ h₃;
  generalize psatF (assignment n) q = Y at h₂ h₃;
  generalize psatF (assignment n) (p ^⋎ q) = Z at h₃ ⊢;
  cl_prover [h₁, h₂, h₃]

lemma tprovable_instFormula_ball {n t q : V} (ht : IsSemiterm ℒₒᵣ n t)
    (hts : termShift ℒₒᵣ t = t) (hq : IsSemiformula ℒₒᵣ (n + 1) q) (hqs : shift ℒₒᵣ q = q)
    (hqb : IsBounded q)
    (ih : T.internalize V ⊢ instFormula (n + 1) q hq 🡘 psatF (assignment (n + 1)) q)
    (hp : IsSemiformula ℒₒᵣ n (qqBall (termBShift ℒₒᵣ t) q)) :
    T.internalize V ⊢ instFormula n (qqBall (termBShift ℒₒᵣ t) q) hp 🡘
      psatF (assignment n) (qqBall (termBShift ℒₒᵣ t) q) := by
  have hw := isSemitermVec_fvarVec (L := ℒₒᵣ) n 0;
  let B : Semiformula V ℒₒᵣ 1 :=
    ⟨subst ℒₒᵣ (qVec ℒₒᵣ (fvarVec n)) q, by simpa using hq.subst hw.qVec⟩;
  have e₁ : instFormula n (qqBall (termBShift ℒₒᵣ t) q) hp =
      ∀¹ (Semiterm.lessThan (Semiterm.bvar 0) (instTerm n t ht).bShift 🡒 B) := by
    have e : instFormula n (qqBall (termBShift ℒₒᵣ t) q) hp = B.ball (instTerm n t ht) := by
      ext;
      simp only [instFormula, instTerm, B, Arithmetic.val_ball];
      rw [subst_qqBall hw ht hq.isUFormula];
      rfl;
    rw [e, Semiformula.ball_eqss_imp];
  have hB : B.free = instFormula (n + 1) q hq := by
    ext; simp [B, instFormula, free_subst_qVec_fvarVec hq hqs];
  have hF : (psatF (pTerm (Semiterm.bvar 0) (assignment n).bShift) q).free =
      psatF (assignment (n + 1)) q := by
    rw [assignment_succ]; simp [Semiformula.free, ← Semiterm.bShift_shift_comm];
  have h₁ : T.internalize V ⊢ ∀¹ (B 🡘 psatF (pTerm (Semiterm.bvar 0) (assignment n).bShift) q) :=
    TProof.all! <| by simpa [hB, hF] using ih;
  have h₂ := tprovable_all_iff_all_domain (T := T)
    (Semiterm.lessThan (Semiterm.bvar 0) (instTerm n t ht).bShift) B
    (psatF (pTerm (Semiterm.bvar 0) (assignment n).bShift) q);
  have h₃ := tprovable_psatF_ball (T := T) (instTerm n t ht) (assignment n) ht.isUTerm hqb
    hq.isUFormula;
  have h₄ := tprovable_tvF_instTerm (T := T) ht hts;
  rw [e₁];
  generalize ∀¹ (Semiterm.lessThan (Semiterm.bvar 0) (instTerm n t ht).bShift 🡒 B) = X at h₂ ⊢;
  generalize ∀¹ (Semiterm.lessThan (Semiterm.bvar 0) (instTerm n t ht).bShift 🡒
    psatF (pTerm (Semiterm.bvar 0) (assignment n).bShift) q) = Y at h₂ h₃;
  generalize ∀¹ (B 🡘 psatF (pTerm (Semiterm.bvar 0) (assignment n).bShift) q) = H at h₁ h₂;
  generalize tvF (instTerm n t ht) (assignment n) t = S at h₃ h₄;
  generalize psatF (assignment n) (qqBall (termBShift ℒₒᵣ t) q) = P at h₃ ⊢;
  cl_prover [h₁, h₂, h₃, h₄]

lemma tprovable_instFormula_bex {n t q : V} (ht : IsSemiterm ℒₒᵣ n t)
    (hts : termShift ℒₒᵣ t = t) (hq : IsSemiformula ℒₒᵣ (n + 1) q) (hqs : shift ℒₒᵣ q = q)
    (hqb : IsBounded q)
    (ih : T.internalize V ⊢ instFormula (n + 1) q hq 🡘 psatF (assignment (n + 1)) q)
    (hp : IsSemiformula ℒₒᵣ n (qqBex (termBShift ℒₒᵣ t) q)) :
    T.internalize V ⊢ instFormula n (qqBex (termBShift ℒₒᵣ t) q) hp 🡘
      psatF (assignment n) (qqBex (termBShift ℒₒᵣ t) q) := by
  have hw := isSemitermVec_fvarVec (L := ℒₒᵣ) n 0;
  let B : Semiformula V ℒₒᵣ 1 :=
    ⟨subst ℒₒᵣ (qVec ℒₒᵣ (fvarVec n)) q, by simpa using hq.subst hw.qVec⟩;
  have e₁ : instFormula n (qqBex (termBShift ℒₒᵣ t) q) hp =
      ∃¹ (Semiterm.lessThan (Semiterm.bvar 0) (instTerm n t ht).bShift ⋏ B) := by
    have e : instFormula n (qqBex (termBShift ℒₒᵣ t) q) hp = B.bexs (instTerm n t ht) := by
      ext;
      simp only [instFormula, instTerm, B, Arithmetic.val_bexs];
      rw [subst_qqBex hw ht hq.isUFormula];
      rfl;
    rw [e];
    rfl;
  have hB : B.free = instFormula (n + 1) q hq := by
    ext; simp [B, instFormula, free_subst_qVec_fvarVec hq hqs];
  have hF : (psatF (pTerm (Semiterm.bvar 0) (assignment n).bShift) q).free =
      psatF (assignment (n + 1)) q := by
    rw [assignment_succ]; simp [Semiformula.free, ← Semiterm.bShift_shift_comm];
  have h₁ : T.internalize V ⊢ ∀¹ (B 🡘 psatF (pTerm (Semiterm.bvar 0) (assignment n).bShift) q) :=
    TProof.all! <| by simpa [hB, hF] using ih;
  have h₂ := tprovable_all_iff_exs_domain (T := T)
    (Semiterm.lessThan (Semiterm.bvar 0) (instTerm n t ht).bShift) B
    (psatF (pTerm (Semiterm.bvar 0) (assignment n).bShift) q);
  have h₃ := tprovable_psatF_bex (T := T) (instTerm n t ht) (assignment n) ht.isUTerm hqb
    hq.isUFormula;
  have h₄ := tprovable_tvF_instTerm (T := T) ht hts;
  rw [e₁];
  generalize ∃¹ (Semiterm.lessThan (Semiterm.bvar 0) (instTerm n t ht).bShift ⋏ B) = X at h₂ ⊢;
  generalize ∃¹ (Semiterm.lessThan (Semiterm.bvar 0) (instTerm n t ht).bShift ⋏
    psatF (pTerm (Semiterm.bvar 0) (assignment n).bShift) q) = Y at h₂ h₃;
  generalize ∀¹ (B 🡘 psatF (pTerm (Semiterm.bvar 0) (assignment n).bShift) q) = H at h₁ h₂;
  generalize tvF (instTerm n t ht) (assignment n) t = S at h₃ h₄;
  generalize psatF (assignment n) (qqBex (termBShift ℒₒᵣ t) q) = P at h₃ ⊢;
  cl_prover [h₁, h₂, h₃, h₄]

omit [𝗜𝚺₁ ⪯ T] in
lemma termBShift_inj {n t t' : V} (ht : IsSemiterm ℒₒᵣ n t) (ht' : IsSemiterm ℒₒᵣ n t')
    (h : termBShift ℒₒᵣ t = termBShift ℒₒᵣ t') : t = t' := by
  have H : ∀ i < n, (bvarVec 0 n).[i] = ^#i := by
    intro i hi
    simp [nth_bvarVec _ _ _ hi]
  have := congrArg (termSubst ℒₒᵣ (0 ∷ bvarVec 0 n)) h
  rwa [substs_cons_bShift ht, substs_cons_bShift ht', termSubst_eq_self ht H,
    termSubst_eq_self ht' H] at this

lemma provable_iff_psat_of_isBounded (N : V) :
    ∀ p, IsBounded p → ∀ n ≤ N, n + p ≤ N → IsSemiformula ℒₒᵣ n p → shift ℒₒᵣ p = p →
      Provable T (iff ℒₒᵣ (subst ℒₒᵣ (fvarVec n) p)
        (subst ℒₒᵣ ?[assignmentCode n, numeral p] (⌜psatDef.val⌝ : V))) := by
  apply IsBounded.induction 𝚺 (P := fun p ↦ ∀ n ≤ N, n + p ≤ N → IsSemiformula ℒₒᵣ n p →
    shift ℒₒᵣ p = p → Provable T (iff ℒₒᵣ (subst ℒₒᵣ (fvarVec n) p)
      (subst ℒₒᵣ ?[assignmentCode n, numeral p] (⌜psatDef.val⌝ : V))))
  · definability
  · intro n _ _ hp _
    apply (tprovable_instFormula_iff hp).mp
    have e : instFormula n ^⊤ hp = ⊤ := by ext; simp [instFormula]
    have h := tprovable_psatF_verum (T := T) (assignment n)
    rw [e]
    generalize psatF (assignment n) ^⊤ = X at h ⊢
    cl_prover [h]
  · intro n _ _ hp _
    apply (tprovable_instFormula_iff hp).mp
    have e : instFormula n ^⊥ hp = ⊥ := by ext; simp [instFormula]
    have h := tprovable_psatF_falsum (T := T) (assignment n)
    rw [e]
    generalize psatF (assignment n) ^⊥ = X at h ⊢
    cl_prover [h]
  · intro k r v n _ _ hp hs
    rcases IsUFormula.rel_cases hp.isUFormula with ⟨t, u, ht, hu, e⟩ | ⟨t, u, ht, hu, e⟩
    · rw [e] at hp hs ⊢
      have htu : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by simpa [Arithmetic.qqEQ] using hp
      have hs' : termShift ℒₒᵣ t = t ∧ termShift ℒₒᵣ u = u := by
        simpa [Arithmetic.qqEQ, ht, hu] using hs
      apply (tprovable_instFormula_iff hp).mp
      have e' : instFormula n (t ^= u) hp =
          Semiterm.equals (instTerm n t htu.1) (instTerm n u htu.2) := by
        ext; simp [instFormula, instTerm, Semiterm.equals, subst_qqEQ ht hu]
      rw [e']
      exact tprovable_instTerm_eq_iff htu.1 htu.2 hs'.1 hs'.2
    · rw [e] at hp hs ⊢
      have htu : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by simpa [Arithmetic.qqLT] using hp
      have hs' : termShift ℒₒᵣ t = t ∧ termShift ℒₒᵣ u = u := by
        simpa [Arithmetic.qqLT, ht, hu] using hs
      apply (tprovable_instFormula_iff hp).mp
      have e' : instFormula n (t ^< u) hp =
          Semiterm.lessThan (instTerm n t htu.1) (instTerm n u htu.2) := by
        ext; simp [instFormula, instTerm, Semiterm.lessThan, subst_qqLT ht hu]
      rw [e']
      exact tprovable_instTerm_lt_iff htu.1 htu.2 hs'.1 hs'.2
  · intro k r v n _ _ hp hs
    rcases IsUFormula.nrel_cases hp.isUFormula with ⟨t, u, ht, hu, e⟩ | ⟨t, u, ht, hu, e⟩
    · rw [e] at hp hs ⊢
      have htu : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by simpa [Arithmetic.qqNEQ] using hp
      have hs' : termShift ℒₒᵣ t = t ∧ termShift ℒₒᵣ u = u := by
        simpa [Arithmetic.qqNEQ, ht, hu] using hs
      apply (tprovable_instFormula_iff hp).mp
      have e' : instFormula n (t ^≠ u) hp =
          Semiterm.notEquals (instTerm n t htu.1) (instTerm n u htu.2) := by
        ext; simp [instFormula, instTerm, Semiterm.notEquals, subst_qqNEQ ht hu]
      rw [e']
      exact tprovable_instTerm_neq_iff htu.1 htu.2 hs'.1 hs'.2
    · rw [e] at hp hs ⊢
      have htu : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by simpa [Arithmetic.qqNLT] using hp
      have hs' : termShift ℒₒᵣ t = t ∧ termShift ℒₒᵣ u = u := by
        simpa [Arithmetic.qqNLT, ht, hu] using hs
      apply (tprovable_instFormula_iff hp).mp
      have e' : instFormula n (Arithmetic.qqNLT t u) hp =
          Semiterm.notLessThan (instTerm n t htu.1) (instTerm n u htu.2) := by
        ext; simp [instFormula, instTerm, Semiterm.notLessThan, subst_qqNLT ht hu]
      rw [e']
      exact tprovable_instTerm_nlt_iff htu.1 htu.2 hs'.1 hs'.2
  · intro p q hpb hqb ihp ihq n hn hnpq hpq hs
    have hpq' := IsSemiformula.and.mp hpq
    have hs' : shift ℒₒᵣ p = p ∧ shift ℒₒᵣ q = q := by
      simpa [hpq'.1.isUFormula, hpq'.2.isUFormula] using hs
    have h₁ := (tprovable_instFormula_iff hpq'.1).mpr <| ihp n hn
      (le_trans (by simpa using (lt_K!_left p q).le) hnpq) hpq'.1 hs'.1
    have h₂ := (tprovable_instFormula_iff hpq'.2).mpr <| ihq n hn
      (le_trans (by simpa using (lt_K!_right p q).le) hnpq) hpq'.2 hs'.2
    exact (tprovable_instFormula_iff hpq).mp <| tprovable_instFormula_and hpq'.1 hpq'.2 h₁ h₂
  · intro p q hpb hqb ihp ihq n hn hnpq hpq hs
    have hpq' := IsSemiformula.or.mp hpq
    have hs' : shift ℒₒᵣ p = p ∧ shift ℒₒᵣ q = q := by
      simpa [hpq'.1.isUFormula, hpq'.2.isUFormula] using hs
    have h₁ := (tprovable_instFormula_iff hpq'.1).mpr <| ihp n hn
      (le_trans (by simpa using (lt_or_left p q).le) hnpq) hpq'.1 hs'.1
    have h₂ := (tprovable_instFormula_iff hpq'.2).mpr <| ihq n hn
      (le_trans (by simpa using (lt_or_right p q).le) hnpq) hpq'.2 hs'.2
    exact (tprovable_instFormula_iff hpq).mp <|
      tprovable_instFormula_or hpq'.1 hpq'.2 hpb hqb h₁ h₂
  · intro t q ht hqb ihq n hn hnp hp hs
    have hp' : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t) ∧ IsSemiformula ℒₒᵣ (n + 1) q := by
      simpa [qqBall, Arithmetic.qqNLT] using hp
    have htn : IsSemiterm ℒₒᵣ n t := IsSemiterm.of_termBShift ht hp'.1
    have hs₁ : termShift ℒₒᵣ (termBShift ℒₒᵣ t) = termBShift ℒₒᵣ t ∧ shift ℒₒᵣ q = q := by
      rw [shift_qqBall ht.termBShift hp'.2.isUFormula] at hs
      simpa [qqBall, Arithmetic.qqNLT] using hs
    have hts : termShift ℒₒᵣ t = t :=
      termBShift_inj htn.termShift htn <| by rw [termBShift_termShift htn, hs₁.1]
    have hq : q + 1 ≤ qqBall (termBShift ℒₒᵣ t) q := by
      simpa [qqBall, lt_iff_succ_le] using lt_trans (lt_or_right _ q) (lt_forall _)
    have hb : n + (q + 1) ≤ N := le_trans (by gcongr) hnp
    have ih := (tprovable_instFormula_iff hp'.2).mpr <| ihq (n + 1)
      (le_trans (by gcongr; exact le_add_self) hb)
      (by rw [add_assoc, add_comm 1 q]; exact hb) hp'.2 hs₁.2
    exact (tprovable_instFormula_iff hp).mp <|
      tprovable_instFormula_ball htn hts hp'.2 hs₁.2 hqb ih hp
  · intro t q ht hqb ihq n hn hnp hp hs
    have hp' : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t) ∧ IsSemiformula ℒₒᵣ (n + 1) q := by
      simpa [qqBex, Arithmetic.qqLT] using hp
    have htn : IsSemiterm ℒₒᵣ n t := IsSemiterm.of_termBShift ht hp'.1
    have hs₁ : termShift ℒₒᵣ (termBShift ℒₒᵣ t) = termBShift ℒₒᵣ t ∧ shift ℒₒᵣ q = q := by
      rw [shift_qqBex ht.termBShift hp'.2.isUFormula] at hs
      simpa [qqBex, Arithmetic.qqLT] using hs
    have hts : termShift ℒₒᵣ t = t :=
      termBShift_inj htn.termShift htn <| by rw [termBShift_termShift htn, hs₁.1]
    have hq : q + 1 ≤ qqBex (termBShift ℒₒᵣ t) q := by
      simpa [qqBex, lt_iff_succ_le] using lt_trans (lt_K!_right _ q) (lt_exists _)
    have hb : n + (q + 1) ≤ N := le_trans (by gcongr) hnp
    have ih := (tprovable_instFormula_iff hp'.2).mpr <| ihq (n + 1)
      (le_trans (by gcongr; exact le_add_self) hb)
      (by rw [add_assoc, add_comm 1 q]; exact hb) hp'.2 hs₁.2
    exact (tprovable_instFormula_iff hp).mp <|
      tprovable_instFormula_bex htn hts hp'.2 hs₁.2 hqb ih hp

end formulaDisquotation

/-! ### The internal T-schema for prenex $\Sigma_1$ partial truth -/

section tSchema

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

private noncomputable def exsCond : 𝚺ᴬ₁.Semisentence 2 := .mkSigma “z θ. !qqExsDef z θ”

private noncomputable def partialTrueClause : ArithmeticSemisentence 2 :=
  exsCond.val/[#0, #1] 🡒
    ((partialTrue 𝚺 1).val/[#0] 🡘 ∃¹ psatDef.val/[‘(#0 + 0) * (#0 + 0) + 0 + 1’, #2])

lemma tprovable_partialTrue_iff_exs_psatF (θ : V) :
    T.internalize V ⊢ (⌜(partialTrue 𝚺 1).val⌝ : Semiformula V ℒₒᵣ 1).subst ![𝕹 (^∃ θ)] 🡘
      ∃¹ psatF (pTerm (Semiterm.bvar 0) (𝕹 0)) θ := by
  have h₁ := tprovable_subst_of_models (T := T) (φ := partialTrueClause) (by
    intro W _ _ e;
    simpa [partialTrueClause, exsCond, add_mul_add_eq_ppair] using
      fun (h : e 0 = ^∃ (e 1)) ↦ by
        have hdec (x : W) : dec (x * x + 1) = x ∷ 0 := by simpa [ppair] using dec_ppair x 0;
        have hpt := (PartialTrue.sigma_defined (V := W) 1).df ![^∃ e 1];
        simp only [Matrix.cons_val_zero] at hpt;
        rw [h];
        simp only [hdec];
        exact hpt.trans (by simp [PartialTrue, (lt_exists (e 1)).le])) ![𝕹 (^∃ θ), 𝕹 θ];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (φ := exsCond.val) (by simp)
    (w := ![^∃ θ, θ]) (by simp [exsCond]);
  rw [numeral_vec_two] at h₂;
  have h₃ : T.internalize V ⊢ (⌜exsCond.val⌝ : Semiformula V ℒₒᵣ 2).subst ![𝕹 (^∃ θ), 𝕹 θ] 🡒
      ((⌜(partialTrue 𝚺 1).val⌝ : Semiformula V ℒₒᵣ 1).subst ![𝕹 (^∃ θ)] 🡘
        ∃¹ psatF (pTerm (Semiterm.bvar 0) (𝕹 0)) θ) := by
    simpa [partialTrueClause, psatF, pTerm, typed_quote_rew_subst, Semiformula.substs_substs,
      SemitermVec.q, Matrix.vecHead, Matrix.vecTail, Matrix.constant_eq_singleton] using h₁;
  exact h₃ ⨀ h₂

/-- Every internal prenex $\Sigma_1$ sentence is internally equivalent to its partial truth. -/
theorem tprovable_iff_partialTrue (φ : Formula V ℒₒᵣ) (hφ : IsPrenexHierarchy 𝚺 1 φ.val)
    (hs : φ.shift = φ) :
    T.internalize V ⊢ φ 🡘 (⌜(partialTrue 𝚺 1).val⌝ : Semiformula V ℒₒᵣ 1).subst ![𝕹 φ.val] := by
  obtain ⟨θ, hφθ, hθb⟩ := isPrenexHierarchy_iff_exists_qqToPrenex.mp hφ;
  simp only [qqToPrenex_succ, qqQuant_sigma, qqToPrenex_zero] at hφθ;
  have hθ : IsSemiformula ℒₒᵣ ((1 : ℕ) : V) θ := by simpa [hφθ] using φ.isSemiformula;
  let Θ : Semiformula V ℒₒᵣ 1 := ⟨θ, hθ⟩;
  have hφΘ : φ = ∃¹ Θ := by ext; simp [Θ, hφθ];
  have hΘs : Θ.shift = Θ := by
    rw [hφΘ, Semiformula.shift_exs] at hs;
    ext; simpa using congrArg (·.val) hs;
  have hθs : shift ℒₒᵣ θ = θ := by simpa [Θ] using congrArg (·.val) hΘs;
  have hdq := (tprovable_instFormula_iff (T := T) (by simpa using hθ)).mpr <|
    provable_iff_psat_of_isBounded (T := T) (θ + 1) θ hθb 1 (by simp) (by rw [add_comm])
      (by simpa using hθ) hθs;
  let F : Semiformula V ℒₒᵣ 1 := psatF (pTerm (Semiterm.bvar 0) (𝕹 0)) θ;
  have hFs : F.shift = F := by simp [F];
  have hfv : fvarVec (1 : V) = ?[^&0] := by
    rw [show (1 : V) = 0 + 1 from (zero_add 1).symm, fvarVec_succ]; simp;
  have e₁ : instFormula 1 θ (by simpa using hθ) = Θ.free := by
    ext; simp [instFormula, Θ, free, substs1, hθs, hfv];
  have e₂ : psatF (assignment 1) θ = F.free := by
    rw [show (1 : V) = 0 + 1 from (zero_add 1).symm, assignment_succ, assignment_zero];
    simp [F, Semiformula.free];
  rw [e₁, e₂] at hdq;
  have h₁ : T.internalize V ⊢ ∃¹ Θ 🡒 ∃¹ F := by
    apply TProof.exs_imp_of_free;
    have h := TProof.subst_imp_exs (T := T) F (Semiterm.fvar 0);
    rw [Semiformula.shift_exs, hFs];
    have e : F.free = F.subst ![Semiterm.fvar 0] := by simp [Semiformula.free, hFs];
    rw [← e] at h;
    cl_prover [hdq, h];
  have h₂ : T.internalize V ⊢ ∃¹ F 🡒 ∃¹ Θ := by
    apply TProof.exs_imp_of_free;
    have h := TProof.subst_imp_exs (T := T) Θ (Semiterm.fvar 0);
    rw [Semiformula.shift_exs, hΘs];
    have e : Θ.free = Θ.subst ![Semiterm.fvar 0] := by simp [Semiformula.free, hΘs];
    rw [← e] at h;
    cl_prover [hdq, h];
  have h₃ := tprovable_partialTrue_iff_exs_psatF (T := T) θ;
  rw [hφΘ];
  have e₃ : (∃¹ Θ).val = ^∃ θ := by simp [Θ];
  rw [e₃];
  cl_prover [h₁, h₂, h₃]

end tSchema

end FFL.FirstOrder.Arithmetic.Bootstrapping
