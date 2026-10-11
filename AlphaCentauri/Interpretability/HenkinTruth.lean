module

public import AlphaCentauri.Bootstrapping.Completeness.HenkinCongruence
public import AlphaCentauri.Interpretability.HenkinTranslation

/-!
# The truth lemma of the Henkin translation

In the model of the Henkin translation, a formula is true of representatives of free variables
exactly when the formula with those free variables substituted is in the Henkin set.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] (S : Theory L) [S.Δ₁]
  [Theory.Δ₁.Sentential S] [𝗘𝗤 L ⪯ S] (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
  {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] [V↓[ℒₒᵣ] ⊧* T ∪ S.Con]

theorem henkinTranslation_term {n : ℕ} (t : ClosedSemiterm L n)
    {e : Fin n → (henkinTranslation S T).Model V} {u : Fin n → V}
    (h : ∀ i, HenkinEq S (e i : V) (u i)) :
    HenkinSet S (Bootstrapping.Semiformula.equal
      ((⌜t⌝ : Bootstrapping.Semiterm V L n).subst
        (fun i ↦ Bootstrapping.Semiterm.fvar (u i) : Bootstrapping.SemitermVec V L n 0))
      (Bootstrapping.Semiterm.fvar
        ((t.val e Empty.elim : (henkinTranslation S T).Model V) : V)) :
        Bootstrapping.Formula V L).val := by
  have hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p := fun _ hp ↦
    Theory.Δ₁.Sentential.shift_eq hp
  have hcons : S.Consistent V := consistent_of_models_con S T
  induction t with
  | bvar i =>
    simp only [Semiterm.empty_typed_quote_bvar, Semiterm.substs_bvar, Semiterm.val_bvar]
    exact HenkinEq.symm S hS hcons (h i)
  | fvar x => exact x.elim
  | func f v ih =>
    have h₁ := DirectTranslation.Model.eval_func (π := henkinTranslation S T) (M := V) f
      fun i ↦ (v i).val e Empty.elim
    have h₂ := (henkinFunc_val S f _ _).mp h₁
    simp only [Semiterm.empty_typed_quote_func, Semiterm.substs_func, Semiterm.val_func]
    exact henkinSet_equal_trans S hS hcons (henkinSet_equal_func S hS hcons f ih) h₂

section quote

omit [L.Eq]

variable {n : ℕ}

private lemma sentence_typed_quote_rel {k : ℕ} (R : L.Rel k) (v : Fin k → ClosedSemiterm L n) :
    (⌜(Semiformula.rel R v : Semisentence L n)⌝ : Bootstrapping.Semiformula V L n) =
      Bootstrapping.Semiformula.rel R fun i ↦ ⌜v i⌝ :=
  rfl

private lemma sentence_typed_quote_nrel {k : ℕ} (R : L.Rel k) (v : Fin k → ClosedSemiterm L n) :
    (⌜(Semiformula.nrel R v : Semisentence L n)⌝ : Bootstrapping.Semiformula V L n) =
      Bootstrapping.Semiformula.nrel R fun i ↦ ⌜v i⌝ :=
  rfl

private lemma sentence_typed_quote_and (φ ψ : Semisentence L n) :
    (⌜φ ⋏ ψ⌝ : Bootstrapping.Semiformula V L n) = ⌜φ⌝ ⋏ ⌜ψ⌝ :=
  rfl

private lemma sentence_typed_quote_or (φ ψ : Semisentence L n) :
    (⌜φ ⋎ ψ⌝ : Bootstrapping.Semiformula V L n) = ⌜φ⌝ ⋎ ⌜ψ⌝ :=
  rfl

private lemma sentence_typed_quote_all (φ : Semisentence L (n + 1)) :
    (⌜∀¹ φ⌝ : Bootstrapping.Semiformula V L n) = ∀¹ ⌜φ⌝ := by
  simp only [LCWQIsoGödelQuote.all, Sentence.typed_quote_def]

private lemma sentence_typed_quote_exs (φ : Semisentence L (n + 1)) :
    (⌜∃¹ φ⌝ : Bootstrapping.Semiformula V L n) = ∃¹ ⌜φ⌝ := by
  simp only [LCWQIsoGödelQuote.exs, Sentence.typed_quote_def]

private lemma subst_q_subst_single (w : Bootstrapping.SemitermVec V L n 0)
    (t : Bootstrapping.Term V L) (φ : Bootstrapping.Semiformula V L (n + 1)) :
    (φ.subst w.q).subst ![t] = φ.subst (t :> w) := by
  rw [Bootstrapping.Semiformula.substs_substs]
  congr 1
  funext i
  cases i using Fin.cases
  · simp only [Matrix.vecMap_app, Bootstrapping.SemitermVec.q_zero,
      Bootstrapping.Semiterm.substs_bvar, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
  · simp only [Matrix.vecMap_app, Bootstrapping.SemitermVec.q_succ,
      Bootstrapping.Semiterm.bShift_substs_sing, Matrix.cons_val_succ]

private lemma subst_fvar_cons (x : V) (u : Fin n → V) (φ : Bootstrapping.Semiformula V L (n + 1)) :
    (φ.subst (Bootstrapping.SemitermVec.q fun i ↦ Bootstrapping.Semiterm.fvar (u i) :
        Bootstrapping.SemitermVec V L (n + 1) 1)).subst ![Bootstrapping.Semiterm.fvar x] =
      φ.subst (fun i ↦ Bootstrapping.Semiterm.fvar ((x :> u) i) :
        Bootstrapping.SemitermVec V L (n + 1) 0) := by
  rw [subst_q_subst_single]
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

end quote

section model

omit [V↓[ℒₒᵣ] ⊧* T ∪ S.Con] in
private lemma exists_model_henkinEq (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hcons : S.Consistent V) (x : V) :
    ∃ a : (henkinTranslation S T).Model V, HenkinEq S (a : V) x := by
  obtain ⟨r, hr, hrx⟩ := exists_isRepresentative S hS hcons x
  exact ⟨⟨r, (henkinDomain_val S r).mpr hr⟩, hrx⟩

omit [V↓[ℒₒᵣ] ⊧* T ∪ S.Con] in
private lemma henkinEq_cons {n : ℕ} {e : Fin n → (henkinTranslation S T).Model V} {u : Fin n → V}
    {a : (henkinTranslation S T).Model V} {x : V} (ha : HenkinEq S (a : V) x)
    (h : ∀ i, HenkinEq S (e i : V) (u i)) : ∀ i, HenkinEq S ((a :> e) i : V) ((x :> u) i) :=
  Fin.cases ha h

end model

theorem henkinTranslation_truth {n : ℕ} (β : Semisentence L n)
    {e : Fin n → (henkinTranslation S T).Model V} {u : Fin n → V}
    (h : ∀ i, HenkinEq S (e i : V) (u i)) :
    ((henkinTranslation S T).Model V) ⊧/e β ↔
      HenkinSet S ((⌜β⌝ : Bootstrapping.Semiformula V L n).subst
        (fun i ↦ Bootstrapping.Semiterm.fvar (u i) : Bootstrapping.SemitermVec V L n 0)).val := by
  have hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p := fun _ hp ↦
    Theory.Δ₁.Sentential.shift_eq hp
  have hcons : S.Consistent V := consistent_of_models_con S T
  induction β using Semiformula.rec' with
  | hrel R v =>
    rw [sentence_typed_quote_rel, Bootstrapping.Semiformula.substs_rel, Semiformula.eval_rel]
    exact (henkinRel_val S R _).trans
      (henkinSet_rel_iff S hS hcons R fun i ↦ henkinTranslation_term S T (v i) h).symm
  | hnrel R v =>
    rw [sentence_typed_quote_nrel, Bootstrapping.Semiformula.substs_nrel, Semiformula.eval_nrel,
      ← Bootstrapping.Semiformula.neg_rel, henkinSet_neg_iff S hS hcons]
    exact not_congr <| (henkinRel_val S R _).trans
      (henkinSet_rel_iff S hS hcons R fun i ↦ henkinTranslation_term S T (v i) h).symm
  | hverum =>
    simp only [LogicalConnective.HomClass.map_top, «Prop».top_eq_true, LCWQIsoGödelQuote.top,
      Bootstrapping.Semiformula.substs_verum, true_iff]
    exact henkinSet_of_tprovable S (φ := (⊤ : Bootstrapping.Formula V L)) (by simp)
  | hfalsum =>
    simp only [LogicalConnective.HomClass.map_bot, «Prop».bot_eq_false, LCWQIsoGödelQuote.bot,
      Bootstrapping.Semiformula.substs_falsum, false_iff]
    exact henkinSet_not_falsum S hS hcons
  | hand φ ψ ihφ ihψ =>
    rw [sentence_typed_quote_and, Bootstrapping.Semiformula.substs_and,
      henkinSet_and_iff S hS hcons, LogicalConnective.HomClass.map_and,
      LogicalConnective.Prop.and_eq]
    exact and_congr (ihφ h) (ihψ h)
  | hor φ ψ ihφ ihψ =>
    rw [sentence_typed_quote_or, Bootstrapping.Semiformula.substs_or,
      henkinSet_or_iff S hS hcons, LogicalConnective.HomClass.map_or,
      LogicalConnective.Prop.or_eq]
    exact or_congr (ihφ h) (ihψ h)
  | hall φ ih =>
    rw [sentence_typed_quote_all, Bootstrapping.Semiformula.substs_all,
      henkinSet_all_iff S hS hcons, Semiformula.eval_all]
    simp only [subst_fvar_cons]
    constructor
    · intro hφ x
      obtain ⟨a, ha⟩ := exists_model_henkinEq S T hS hcons x
      exact (ih (henkinEq_cons S T ha h)).mp (hφ a)
    · intro hφ a
      exact (ih (henkinEq_cons S T (HenkinEq.refl S _) h)).mpr (hφ a)
  | hexs φ ih =>
    rw [sentence_typed_quote_exs, Bootstrapping.Semiformula.substs_ex,
      henkinSet_exs_iff S hS hcons, Semiformula.eval_ex]
    simp only [subst_fvar_cons]
    constructor
    · rintro ⟨a, hφ⟩
      exact ⟨a, (ih (henkinEq_cons S T (HenkinEq.refl S _) h)).mp hφ⟩
    · rintro ⟨x, hφ⟩
      obtain ⟨a, ha⟩ := exists_model_henkinEq S T hS hcons x
      exact ⟨a, (ih (henkinEq_cons S T ha h)).mpr hφ⟩

end FFL.FirstOrder.Arithmetic
