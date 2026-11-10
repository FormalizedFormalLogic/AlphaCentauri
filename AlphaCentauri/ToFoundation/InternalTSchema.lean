module

public import AlphaCentauri.ToFoundation.PairingAssignment
public import AlphaCentauri.ToFoundation.Provable
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.Bounded

/-!
# Internal Tarski conditions for $\Delta_0$ satisfaction

`psatDef` and `tvDef` express $\Delta_0$ satisfaction and the values of terms under an assignment
coded by iterated `ppair`s. Their Tarski conditions are theorems of `𝗜𝚺₁`, so every internal
theory containing `𝗜𝚺₁` proves their instances at arbitrary internal terms.
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
noncomputable def pTerm (t u : Term V ℒₒᵣ) : Term V ℒₒᵣ := (t + u) * (t + u) + u + 𝕹 1

/-- The internal sentence that the code `p` is satisfied under the assignment coded by `a`. -/
noncomputable def psatF (a : Term V ℒₒᵣ) (p : V) : Formula V ℒₒᵣ :=
  (⌜psatDef.val⌝ : Semiformula V ℒₒᵣ 2).subst ![a, 𝕹 p]

/-- The internal sentence that `y` is the value of the code `t` under the assignment coded by
`a`. -/
noncomputable def tvF (y a : Term V ℒₒᵣ) (t : V) : Formula V ℒₒᵣ :=
  (⌜tvDef.val⌝ : Semiformula V ℒₒᵣ 3).subst ![y, a, 𝕹 t]

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

lemma tprovable_subst_of_models {k : ℕ} {φ : ArithmeticSemisentence k}
    (h : ∀ (W : Type) [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin k → W), W ⊧/e φ)
    (w : SemitermVec V ℒₒᵣ k 0) :
    T.internalize V ⊢ (⌜φ⌝ : Semiformula V ℒₒᵣ k).subst w :=
  tprovable_subst_of_allClosure T w <| internal_provable_of_outer_provable <|
    Entailment.WeakerThan.pbl <| complete 𝗜𝚺₁ _ fun W _ _ ↦ by simpa [models_iff] using h W

lemma numeral_vec_two (a b : V) :
    (fun i ↦ (𝕹 (![a, b] i) : Term V ℒₒᵣ)) = ![𝕹 a, 𝕹 b] := by
  funext i; match i with | 0 => rfl | 1 => rfl

lemma numeral_vec_three (a b c : V) :
    (fun i ↦ (𝕹 (![a, b, c] i) : Term V ℒₒᵣ)) = ![𝕹 a, 𝕹 b, 𝕹 c] := by
  funext i; match i with | 0 => rfl | 1 => rfl | 2 => rfl

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

end FFL.FirstOrder.Arithmetic.Bootstrapping
