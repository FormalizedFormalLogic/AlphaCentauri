module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1

/-!
# Equality in the internal calculus

The typed equality formula of a language with equality, and the internal proofs of reflexivity,
symmetry, transitivity and the congruence of function and relation symbols from $\mathsf{EQ}$.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq]

/-- The formula saying that two terms are equal. -/
noncomputable def Semiformula.equal {n : ℕ} (s t : Semiterm V L n) : Semiformula V L n :=
  Semiformula.rel Language.Eq.eq ![s, t]

lemma quote_eqop {n : ℕ} (t u : ClosedSemiterm L n) :
    (⌜(op(=).operator ![t, u] : Semisentence L n)⌝ : Semiformula V L n) =
      Semiformula.equal ⌜t⌝ ⌜u⌝ := by
  simp only [Semiformula.Operator.operator, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.rew_rel_eq_comp, Rew.emb_eq_id, Semiformula.equal]
  rw [Sentence.typed_quote_def]
  simp only [Semiformula.rew_rel_eq_comp, Semiformula.typed_quote_rel, Function.comp_apply,
    Rew.id_app, Rew.subst_bvar]
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

omit [L.Eq] in
lemma quote_rel_sentence {n k : ℕ} (R : L.Rel k) (v : Fin k → ClosedSemiterm L n) :
    (⌜(FirstOrder.Semiformula.rel R v : Semisentence L n)⌝ : Semiformula V L n) =
      Semiformula.rel R fun i ↦ ⌜v i⌝ := by
  rw [Sentence.typed_quote_def]
  simp
  rfl

lemma Semiformula.substs_equal {n m : ℕ} (w : SemitermVec V L n m) (s t : Semiterm V L n) :
    (Semiformula.equal s t).subst w = Semiformula.equal (s.subst w) (t.subst w) := by
  simp only [Semiformula.equal, Semiformula.substs_rel]
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

omit [L.Eq] in
lemma Semiformula.substs_conj {n m k : ℕ} (w : SemitermVec V L n m)
    (v : Fin k → Semiformula V L n) :
    (Matrix.conj v).subst w = Matrix.conj fun i ↦ (v i).subst w := by
  induction k with
  | zero => simp
  | succ k ih => simp [Matrix.conj, ih]; rfl

omit [L.Eq] in
lemma quote_conj {n k : ℕ} (v : Fin k → Semisentence L n) :
    (⌜Matrix.conj v⌝ : Semiformula V L n) = Matrix.conj fun i ↦ ⌜v i⌝ := by
  induction k with
  | zero => simp
  | succ k ih => simp [Matrix.conj, ih]; rfl

private lemma append_addCast {α : Type*} {k : ℕ} (s u : Fin k → α) (i : Fin k) :
    Fin.append s u (Fin.addCast k i) = s i := by
  simp [Fin.addCast]

private lemma append_addNat {α : Type*} {k : ℕ} (s u : Fin k → α) (i : Fin k) :
    Fin.append s u (i.addNat k) = u i := by
  have : i.addNat k = Fin.natAdd k i := Fin.ext (Nat.add_comm _ _)
  rw [this, Fin.append_right]

variable (S : Theory L) [S.Δ₁]

omit [L.Eq] in
lemma tprovable_conj {k : ℕ} {v : Fin k → Formula V L}
    (h : ∀ i, S.internalize V ⊢ v i) : S.internalize V ⊢ Matrix.conj v := by
  induction k with
  | zero => simp
  | succ k ih => exact _root_.FFL.Entailment.K_intro (h 0) (ih fun i ↦ h i.succ)

omit [L.Eq] in
lemma tprovable_subst_of_allClosure :
    ∀ {n : ℕ} {σ : Semisentence L n} (w : SemitermVec V L n 0),
      S.internalize V ⊢ (⌜∀¹* σ⌝ : Formula V L) →
        S.internalize V ⊢ (⌜σ⌝ : Semiformula V L n).subst w
  | 0, σ, w, h => by simpa using h
  | n + 1, σ, w, h => by
    have h₁ := tprovable_subst_of_allClosure (σ := ∀¹ σ) (Matrix.vecTail w) h
    simp only [LCWQIsoGödelQuote.all, Semiformula.substs_all] at h₁
    have h₂ := TProof.specialize! h₁ (w 0)
    rw [Semiformula.substs_substs] at h₂
    convert h₂ using 2
    funext i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · simp
    · simp [Semiterm.bShift_substs_sing]; rfl

lemma tprovable_quote_eqAxiom [𝗘𝗤 L ⪯ S] {σ : Sentence L} (h : 𝗘𝗤 L σ) :
    S.internalize V ⊢ (⌜σ⌝ : Formula V L) := by
  have h₁ : S ⊢ σ :=
    _root_.FFL.Entailment.WeakerThan.pbl (𝓢 := 𝗘𝗤 L) (_root_.FFL.Entailment.by_axm h)
  exact tprovable_tquote_iff_provable_quote_sentence.mpr (internalize_provability h₁)

theorem tprovable_equal_refl [𝗘𝗤 L ⪯ S] (t : Semiterm V L 0) :
    S.internalize V ⊢ Semiformula.equal t t := by
  have h₁ := tprovable_subst_of_allClosure S (σ := (op(=).operator ![#0, #0] : Semisentence L 1))
    ![t] (tprovable_quote_eqAxiom S Theory.eqAxiom.refl)
  rw [quote_eqop] at h₁
  simpa [Semiformula.substs_equal] using h₁

theorem tprovable_equal_symm_imp [𝗘𝗤 L ⪯ S] (s t : Semiterm V L 0) :
    S.internalize V ⊢ Semiformula.equal s t 🡒 Semiformula.equal t s := by
  have h₁ := tprovable_subst_of_allClosure S
    (σ := (op(=).operator ![#1, #0] 🡒 op(=).operator ![#0, #1] : Semisentence L 2))
    ![t, s] (tprovable_quote_eqAxiom S Theory.eqAxiom.symm)
  simp only [LCWQIsoGödelQuote.imply, quote_eqop, Semiformula.substs_imp,
    Semiformula.substs_equal] at h₁
  simpa using h₁

theorem tprovable_equal_trans_imp [𝗘𝗤 L ⪯ S] (s t u : Semiterm V L 0) :
    S.internalize V ⊢ Semiformula.equal s t ⋏ Semiformula.equal t u 🡒 Semiformula.equal s u := by
  have h₁ := tprovable_subst_of_allClosure S
    (σ := (op(=).operator ![#2, #1] 🡒 op(=).operator ![#1, #0] 🡒 op(=).operator ![#2, #0] :
      Semisentence L 3))
    ![u, t, s] (tprovable_quote_eqAxiom S Theory.eqAxiom.trans)
  simp only [LCWQIsoGödelQuote.imply, quote_eqop, Semiformula.substs_imp,
    Semiformula.substs_equal] at h₁
  simpa using _root_.FFL.Entailment.CK_of_CC h₁

theorem tprovable_equal_symm [𝗘𝗤 L ⪯ S] {s t : Semiterm V L 0}
    (h : S.internalize V ⊢ Semiformula.equal s t) :
    S.internalize V ⊢ Semiformula.equal t s :=
  tprovable_equal_symm_imp S s t ⨀ h

theorem tprovable_equal_trans [𝗘𝗤 L ⪯ S] {s t u : Semiterm V L 0}
    (h₁ : S.internalize V ⊢ Semiformula.equal s t)
    (h₂ : S.internalize V ⊢ Semiformula.equal t u) :
    S.internalize V ⊢ Semiformula.equal s u :=
  tprovable_equal_trans_imp S s t u ⨀ _root_.FFL.Entailment.K_intro h₁ h₂

theorem tprovable_equal_func_imp [𝗘𝗤 L ⪯ S] {k : ℕ} (f : L.Func k) (s u : SemitermVec V L k 0) :
    S.internalize V ⊢ Matrix.conj (fun i ↦ Semiformula.equal (s i) (u i)) 🡒
      Semiformula.equal (Semiterm.func f s) (Semiterm.func f u) := by
  have h₁ := tprovable_subst_of_allClosure S (n := k + k) (w := Fin.append s u)
    (tprovable_quote_eqAxiom S (Theory.eqAxiom.funcExt f))
  simp only [LCWQIsoGödelQuote.imply, quote_conj, quote_eqop, Semiformula.substs_imp,
    Semiformula.substs_equal, Semiformula.substs_conj] at h₁
  simp only [Semiterm.empty_typed_quote_bvar, Semiterm.substs_bvar, append_addCast,
    append_addNat, Semiterm.empty_typed_quote_func, Semiterm.substs_func] at h₁
  have e₁ : (Semiterm.subst (Fin.append s u))⨟ (fun i ↦ Semiterm.bvar (Fin.addCast k i)) = s := by
    funext i
    simp [append_addCast]
  have e₂ : (Semiterm.subst (Fin.append s u))⨟ (fun i ↦ Semiterm.bvar (i.addNat k)) = u := by
    funext i
    simp [append_addNat]
  rw [e₁, e₂] at h₁
  exact h₁

theorem tprovable_rel_congr_imp [𝗘𝗤 L ⪯ S] {k : ℕ} (R : L.Rel k) (s u : SemitermVec V L k 0) :
    S.internalize V ⊢ Matrix.conj (fun i ↦ Semiformula.equal (s i) (u i)) 🡒
      (Semiformula.rel R s 🡒 Semiformula.rel R u) := by
  have h₁ := tprovable_subst_of_allClosure S (n := k + k) (w := Fin.append s u)
    (tprovable_quote_eqAxiom S (Theory.eqAxiom.relExt R))
  simp only [LCWQIsoGödelQuote.imply, quote_conj, quote_eqop, quote_rel_sentence,
    Semiformula.substs_imp, Semiformula.substs_equal, Semiformula.substs_conj,
    Semiformula.substs_rel] at h₁
  simp only [Semiterm.empty_typed_quote_bvar, Semiterm.substs_bvar, append_addCast,
    append_addNat] at h₁
  have e₁ : (Semiterm.subst (Fin.append s u))⨟ (fun i ↦ Semiterm.bvar (Fin.addCast k i)) = s := by
    funext i
    simp [append_addCast]
  have e₂ : (Semiterm.subst (Fin.append s u))⨟ (fun i ↦ Semiterm.bvar (i.addNat k)) = u := by
    funext i
    simp [append_addNat]
  rw [e₁, e₂] at h₁
  exact h₁

theorem tprovable_equal_func [𝗘𝗤 L ⪯ S] {k : ℕ} (f : L.Func k) {s u : SemitermVec V L k 0}
    (h : ∀ i, S.internalize V ⊢ Semiformula.equal (s i) (u i)) :
    S.internalize V ⊢ Semiformula.equal (Semiterm.func f s) (Semiterm.func f u) :=
  tprovable_equal_func_imp S f s u ⨀ tprovable_conj S h

theorem tprovable_rel_congr [𝗘𝗤 L ⪯ S] {k : ℕ} (R : L.Rel k) {s u : SemitermVec V L k 0}
    (h : ∀ i, S.internalize V ⊢ Semiformula.equal (s i) (u i))
    (hs : S.internalize V ⊢ Semiformula.rel R s) : S.internalize V ⊢ Semiformula.rel R u :=
  tprovable_rel_congr_imp S R s u ⨀ tprovable_conj S h ⨀ hs

end FFL.FirstOrder.Arithmetic.Bootstrapping
