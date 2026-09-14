module

public import AlphaCentauri.Bootstrapping.PartialTruth.Tarski
public import AlphaCentauri.Vorspiel.Absoluteness

/-!
# Partial truth definitions agree with truth

This module proves the “it's snowing” agreement between partial satisfaction and semantics,
both in every model of `𝗜𝚺₁` and, uniformly, over `𝗣𝗔⁻` together with the finite Tarski theory.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Codes of quoted semisentences

Foundation's `quote_*` lemmas compute the code of a `Semiproposition`. A `Semisentence` is
quoted through its embedding (`Sentence.quote_def`), so each of them has a counterpart here.

- [HP98, 1.66]
- [HP98, 0.30] -/

private lemma isUTerm_quote {k : ℕ} (t : ClosedSemiterm ℒₒᵣ k) : IsUTerm ℒₒᵣ (⌜t⌝ : V) := by
  simp [Semiterm.empty_quote_eq]

private lemma isUFormula_quote {k : ℕ} (φ : ArithmeticSemisentence k) :
    IsUFormula ℒₒᵣ (⌜φ⌝ : V) := (Sentence.quote_isSemiformula φ).isUFormula

section
variable {k : ℕ} (t u : ClosedSemiterm ℒₒᵣ k)

private lemma quote_eq_sentence :
    (⌜(.rel Language.Eq.eq ![t, u] : ArithmeticSemisentence k)⌝ : V)
      = Arithmetic.qqEQ (⌜t⌝ : V) (⌜u⌝ : V) := by
  simpa [Sentence.quote_def, Semiformula.quote_rel, Arithmetic.qqEQ, Semiterm.empty_quote_eq,
    Semiterm.empty_typed_quote_def, Matrix.vecHead, Matrix.vecTail] using coe_quote_eq (V := V)

private lemma quote_neq_sentence :
    (⌜(.nrel Language.Eq.eq ![t, u] : ArithmeticSemisentence k)⌝ : V)
      = Arithmetic.qqNEQ (⌜t⌝ : V) (⌜u⌝ : V) := by
  simpa [Sentence.quote_def, Semiformula.quote_nrel, Arithmetic.qqNEQ, Semiterm.empty_quote_eq,
    Semiterm.empty_typed_quote_def, Matrix.vecHead, Matrix.vecTail] using coe_quote_eq (V := V)

private lemma quote_lt_sentence :
    (⌜(.rel Language.LT.lt ![t, u] : ArithmeticSemisentence k)⌝ : V)
      = Arithmetic.qqLT (⌜t⌝ : V) (⌜u⌝ : V) := by
  simpa [Sentence.quote_def, Semiformula.quote_rel, Arithmetic.qqLT, Semiterm.empty_quote_eq,
    Semiterm.empty_typed_quote_def, Matrix.vecHead, Matrix.vecTail] using coe_quote_lt (V := V)

private lemma quote_nlt_sentence :
    (⌜(.nrel Language.LT.lt ![t, u] : ArithmeticSemisentence k)⌝ : V)
      = Arithmetic.qqNLT (⌜t⌝ : V) (⌜u⌝ : V) := by
  simpa [Sentence.quote_def, Semiformula.quote_nrel, Arithmetic.qqNLT, Semiterm.empty_quote_eq,
    Semiterm.empty_typed_quote_def, Matrix.vecHead, Matrix.vecTail] using coe_quote_lt (V := V)

end

private lemma quote_and_sentence {k : ℕ} (φ ψ : ArithmeticSemisentence k) :
    (⌜φ ⋏ ψ⌝ : V) = (⌜φ⌝ : V) ^⋏ (⌜ψ⌝ : V) := by simp [Sentence.quote_def]

private lemma quote_or_sentence {k : ℕ} (φ ψ : ArithmeticSemisentence k) :
    (⌜φ ⋎ ψ⌝ : V) = (⌜φ⌝ : V) ^⋎ (⌜ψ⌝ : V) := by simp [Sentence.quote_def]

private lemma quote_all_sentence {k : ℕ} (φ : ArithmeticSemisentence (k + 1)) :
    (⌜(∀¹ φ : ArithmeticSemisentence k)⌝ : V) = ^∀ (⌜φ⌝ : V) := by simp [Sentence.quote_def]

private lemma quote_ex_sentence {k : ℕ} (φ : ArithmeticSemisentence (k + 1)) :
    (⌜(∃¹ φ : ArithmeticSemisentence k)⌝ : V) = ^∃ (⌜φ⌝ : V) := by simp [Sentence.quote_def]

section
variable {k : ℕ} (t : ClosedSemiterm ℒₒᵣ k) (φ : ArithmeticSemisentence (k + 1))

private lemma quote_ball_sentence :
    (⌜(∀¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemisentence k)⌝ : V)
      = qqBall (termBShift ℒₒᵣ (⌜t⌝ : V)) (⌜φ⌝ : V) := by
  rw [Semiformula.ball_eq, Semiformula.imp_eq]
  simpa [Sentence.quote_def, Semiformula.Operator.lt_def, Semiformula.neg_rel, qqBall,
    Semiformula.quote_nrel, Arithmetic.qqNLT, Semiterm.empty_quote_eq, Matrix.vecHead,
    Matrix.vecTail, ← Rew.emb_bShift_term,
    ← Semiterm.empty_typed_quote_def] using coe_quote_lt (V := V)

private lemma quote_bex_sentence :
    (⌜(∃¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemisentence k)⌝ : V)
      = qqBex (termBShift ℒₒᵣ (⌜t⌝ : V)) (⌜φ⌝ : V) := by
  rw [Semiformula.bexs_eq]
  simpa [Sentence.quote_def, Semiformula.Operator.lt_def, qqBex, Semiformula.quote_rel,
    Arithmetic.qqLT, Semiterm.empty_quote_eq, Matrix.vecHead, Matrix.vecTail,
    ← Rew.emb_bShift_term, ← Semiterm.empty_typed_quote_def] using coe_quote_lt (V := V)

end

private lemma quote_bvar_sentence {k : ℕ} (i : Fin k) :
    (⌜(#i : ClosedSemiterm ℒₒᵣ k)⌝ : V) = qqBvar (i.val : V) := by
  simp [Semiterm.empty_quote_eq]

private lemma quote_zeroTerm_sentence {k : ℕ} (w : Fin 0 → ClosedSemiterm ℒₒᵣ k) :
    (⌜(Semiterm.func Language.ORing.Func.zero w : ClosedSemiterm ℒₒᵣ k)⌝ : V) = (𝟎 : V) := by
  rw [Arithmetic.coe_zero_eq,
    show (⌜(Language.Zero.zero : (ℒₒᵣ).Func 0)⌝ : V) = 0 from quote_zeroIndex_eq]
  simp [Semiterm.empty_quote_eq, quote_zeroIndex_eq]

private lemma quote_oneTerm_sentence {k : ℕ} (w : Fin 0 → ClosedSemiterm ℒₒᵣ k) :
    (⌜(Semiterm.func Language.ORing.Func.one w : ClosedSemiterm ℒₒᵣ k)⌝ : V) = (𝟏 : V) := by
  rw [Arithmetic.coe_one_eq,
    show (⌜(Language.One.one : (ℒₒᵣ).Func 0)⌝ : V) = 1 from quote_oneIndex_eq]
  simp [Semiterm.empty_quote_eq, quote_oneIndex_eq]

private lemma quote_addTerm_sentence {k : ℕ} (w : Fin 2 → ClosedSemiterm ℒₒᵣ k) :
    (⌜(Semiterm.func Language.ORing.Func.add w : ClosedSemiterm ℒₒᵣ k)⌝ : V)
      = (⌜w 0⌝ : V) ^+ ⌜w 1⌝ := by
  simp [Semiterm.empty_quote_eq, Arithmetic.qqAdd, quote_addIndex_eq,
    Arithmetic.coe_addIndex_eq, Matrix.vecHead, Matrix.vecTail]

private lemma quote_mulTerm_sentence {k : ℕ} (w : Fin 2 → ClosedSemiterm ℒₒᵣ k) :
    (⌜(Semiterm.func Language.ORing.Func.mul w : ClosedSemiterm ℒₒᵣ k)⌝ : V)
      = (⌜w 0⌝ : V) ^* ⌜w 1⌝ := by
  simp [Semiterm.empty_quote_eq, Arithmetic.qqMul, quote_mulIndex_eq,
    Arithmetic.coe_mulIndex_eq, Matrix.vecHead, Matrix.vecTail]

/-! ## Agreement of satisfaction with truth

- [HP98, Theorem I.1.70]
- [HP98, Corollary I.1.76]
- [HP98, Definition I.1.74]
- [HP98, Remark I.1.80] -/

theorem boundedSatisfaction_quote_iff {k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : φ.Bounded) (v : Fin k → V) :
    BoundedSatisfaction (⌜φ⌝ : V) (matrixToVec v) ↔ V ⊧/v φ := by
  revert v
  refine bounded_induction (ξ := Empty)
    (P := fun k φ ↦ ∀ v : Fin k → V, BoundedSatisfaction (⌜φ⌝ : V) (matrixToVec v) ↔ V ⊧/v φ)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ k φ hφ
  · intro n v; simp [Sentence.quote_def]
  · intro n v; simp [Sentence.quote_def]
  · intro n t u v
    simp [quote_eq_sentence, isUTerm_quote, termVal_quote, Semiformula.eval_rel]
  · intro n t u v
    simp [quote_neq_sentence, isUTerm_quote, termVal_quote, Semiformula.eval_nrel]
  · intro n t u v
    simp [quote_lt_sentence, isUTerm_quote, termVal_quote, Semiformula.eval_rel]
  · intro n t u v
    simp [quote_nlt_sentence, isUTerm_quote, termVal_quote, Semiformula.eval_nrel]
  · intro n φ ψ hφ hψ ihφ ihψ v
    simp [quote_and_sentence, ihφ v, ihψ v]
  · intro n φ ψ hφ hψ ihφ ihψ v
    simp [quote_or_sentence, isBounded_quote_iff, isUFormula_quote, hφ, hψ, ihφ v, ihψ v]
  · intro n t φ hφ ihφ v
    rw [quote_ball_sentence, BoundedSatisfaction.ball_iff (isUTerm_quote t)
      ((isBounded_quote_iff φ).mpr hφ) (isUFormula_quote φ), termVal_quote]
    simp only [Semiformula.eval_ball, Semiformula.Operator.lt_def, Semiformula.eval_rel]
    apply forall_congr'
    intro x
    rw [show (x ∷ matrixToVec v : V) = matrixToVec (x :> v) by simp, ihφ (x :> v)]
    simp [Function.comp_def]
  · intro n t φ hφ ihφ v
    rw [quote_bex_sentence, BoundedSatisfaction.bex_iff (isUTerm_quote t), termVal_quote]
    simp only [Semiformula.eval_bexs, Semiformula.Operator.lt_def, Semiformula.eval_rel]
    apply exists_congr
    intro x
    rw [show (x ∷ matrixToVec v : V) = matrixToVec (x :> v) by simp, ihφ (x :> v)]
    simp [Function.comp_def]

/-- The satisfaction predicate selected by a polarity: `SigmaSatisfaction` for `Σ`, `PiSatisfaction`
for `Π`. -/
def HierarchySatisfaction : Polarity → ℕ → V → V → Prop
  | .sigma, n, z, e => SigmaSatisfaction n z e
  | .pi, n, z, e => PiSatisfaction n z e

lemma hierarchySatisfaction_quote_iff {Γ : Polarity} {s k : ℕ} {φ : ArithmeticSemisentence k}
    (h : StrictHierarchy Γ s φ) :
    ∀ v : Fin k → V, HierarchySatisfaction Γ s (⌜φ⌝ : V) (matrixToVec v) ↔ V ⊧/v φ := by
  induction h with
  | @zero Γ₀ n₀ φ₀ hφ₀ =>
    intro v
    rcases Γ₀ with _ | _
    · show SigmaSatisfaction 0 _ _ ↔ _
      rw [SigmaSatisfaction.zero]; exact boundedSatisfaction_quote_iff hφ₀ v
    · show PiSatisfaction 0 _ _ ↔ _
      rw [PiSatisfaction.zero]; exact boundedSatisfaction_quote_iff hφ₀ v
  | @ofAlt Γ₀ s₀ n₀ φ₀ hφ₀ ih =>
    intro v
    rcases Γ₀ with _ | _
    · show SigmaSatisfaction (s₀ + 1) _ _ ↔ _
      rw [SigmaSatisfaction.of_pi ((isStrictPi_quote_iff φ₀).mpr hφ₀) (isUFormula_quote φ₀)]
      exact ih v
    · show PiSatisfaction (s₀ + 1) _ _ ↔ _
      rw [PiSatisfaction.of_sigma ((isStrictSigma_quote_iff φ₀).mpr hφ₀) (isUFormula_quote φ₀)]
      exact ih v
  | @exs s₀ n₀ φ₀ hφ₀ ih =>
    intro v
    show SigmaSatisfaction (s₀ + 1) _ _ ↔ _
    rw [quote_ex_sentence, SigmaSatisfaction.exs_iff]
    simp only [Semiformula.eval_ex]
    apply exists_congr
    intro x
    rw [show (x ∷ matrixToVec v : V) = matrixToVec (x :> v) by simp]
    exact ih (x :> v)
  | @all s₀ n₀ φ₀ hφ₀ ih =>
    intro v
    show PiSatisfaction (s₀ + 1) _ _ ↔ _
    rw [quote_all_sentence, PiSatisfaction.all_iff]
    simp only [Semiformula.eval_all]
    apply forall_congr'
    intro x
    rw [show (x ∷ matrixToVec v : V) = matrixToVec (x :> v) by simp]
    exact ih (x :> v)

section
variable {n k : ℕ} {φ : ArithmeticSemisentence k}

theorem sigmaSatisfaction_quote_iff (hφ : StrictHierarchy 𝚺 n φ) (v : Fin k → V) :
    SigmaSatisfaction n ⌜φ⌝ (matrixToVec v) ↔ V ⊧/v φ := hierarchySatisfaction_quote_iff hφ v

theorem piSatisfaction_quote_iff (hφ : StrictHierarchy 𝚷 n φ) (v : Fin k → V) :
    PiSatisfaction n ⌜φ⌝ (matrixToVec v) ↔ V ⊧/v φ := hierarchySatisfaction_quote_iff hφ v

end

/-- The sentence asserting agreement of `φ` with its level-$\Sigma_{n + 1}$ partial truth
definition. -/
noncomputable def snowing (n : ℕ) {k : ℕ}
    (φ : ArithmeticSemisentence k) : ArithmeticSentence :=
  ∀¹* (φ 🡘 (sigmaSatisfactionVec n k).val ⇜ ((⌜φ⌝ : ArithmeticSemiterm Empty k) :> fun i ↦ #i))

theorem models_snowing_iff {n k : ℕ} (φ : ArithmeticSemisentence k) :
    V↓[ℒₒᵣ] ⊧ snowing n φ ↔ ∀ v : Fin k → V, V ⊧/v φ ↔ SigmaSatisfaction (n + 1) ⌜φ⌝ (matrixToVec v) := by
  simp [snowing, models_iff, (sigmaSatisfactionVec.defined n k).df, Function.comp_def]

theorem ISigma1.provable_snowing {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) : 𝗜𝚺₁ ⊢ snowing n φ := by
  apply Arithmetic.complete.{0}
  intro M _ _
  exact (models_snowing_iff φ).mpr fun v ↦ (sigmaSatisfaction_quote_iff hφ v).symm

/-! ## The snowing lemma over `𝗣𝗔⁻` -/

section peanoMinus

open Tarski Reading PeanoMinus

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {n : ℕ}
  (hM : ∀ σ : ArithmeticSentence, tarski n σ → M↓[ℒₒᵣ] ⊧ σ)

/-! ### Codes of finite sequences -/

namespace Reading

/-- `Codes v ev` says that `ev` is a code for the finite sequence `v`: it has length `m` and its
`i`-th entry is `v i`. -/
def Codes {m : ℕ} (v : Fin m → M) (ev : M) : Prop := Len (m : M) ev ∧ ∀ i : Fin m, Nth (v i) ev (i.val : M)

end Reading

include hM in
lemma codes_nil (v : Fin 0 → M) : Codes v 0 := ⟨by simpa using (read_lenNil hM 0).mpr rfl, fun i ↦ i.elim0⟩

include hM in
lemma codes_cons {m : ℕ} {v : Fin m → M} {ev ev' x : M} (h : Codes v ev)
    (hadj : Adjoin ev' x ev) : Codes (x :> v) ev' := by
  refine ⟨?_, fun i ↦ ?_⟩
  · have := (read_lenAdjoin hM x ev ev' (m : M) hadj).mpr h.1
    simpa using this
  · refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa using (read_nthAdjoinZero hM x ev ev' x hadj).mpr rfl
    · have := (read_nthAdjoinSucc hM x ev ev' (j.val : M) (v j) hadj).mpr (h.2 j)
      simpa using this

include hM in
lemma exists_codes : ∀ {m : ℕ} (v : Fin m → M), ∃ ev, Codes v ev := by
  intro m
  induction m with
  | zero => exact fun v ↦ ⟨0, codes_nil hM v⟩
  | succ m ih =>
    intro v
    obtain ⟨ev, hev⟩ := ih (fun i ↦ v i.succ)
    obtain ⟨ev', hadj⟩ := read_adjoinTotal hM (v 0) ev
    have hcons : (v 0 :> fun i ↦ v i.succ) = v := by
      funext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
    exact ⟨ev', hcons ▸ codes_cons hM hev hadj⟩

/-! ### Coding facts about standard codes

- [HP98, 1.66]
- [HP98, Lemma I.1.68]
- [HP98, Lemma I.1.69] -/

private lemma uTerm_quote_cast {k : ℕ} (t : ClosedSemiterm ℒₒᵣ k) :
    UTerm ((⌜t⌝ : ℕ) : M) :=
  Delta1_cast₁ (isUTerm ℒₒᵣ) (by simpa using isUTerm_quote (V := ℕ) t)

private lemma uFormula_quote_cast {k : ℕ} (φ : ArithmeticSemisentence k) :
    UFormula ((⌜φ⌝ : ℕ) : M) :=
  Delta1_cast₁ (isUFormula ℒₒᵣ) (by simpa using isUFormula_quote (V := ℕ) φ)

private lemma bounded_quote_cast {k : ℕ} {φ : ArithmeticSemisentence k} (h : φ.Bounded) :
    Reading.Bounded ((⌜φ⌝ : ℕ) : M) :=
  Delta1_cast₁ isBounded (by simpa using (isBounded_quote_iff (V := ℕ) φ).mpr h)

private lemma strict_quote_cast {Γ : Polarity} {s k : ℕ} {φ : ArithmeticSemisentence k}
    (h : StrictHierarchy Γ s φ) : Strict Γ s ((⌜φ⌝ : ℕ) : M) := by
  rcases Γ with _ | _
  · exact Delta1_cast₁ (isStrictSigma s) (by simpa using (isStrictSigma_quote_iff (V := ℕ) φ).mpr h)
  · exact Delta1_cast₁ (isStrictPi s) (by simpa using (isStrictPi_quote_iff (V := ℕ) φ).mpr h)

/-! ### Evaluation of coded closed terms

- [HP98, 1.66] -/

include hM in
private lemma termVal_quote_cast {k : ℕ} {v : Fin k → M} {ev : M} (hev : Codes v ev) :
    ∀ t : ClosedSemiterm ℒₒᵣ k, TermVal (t.valb v) ev ((⌜t⌝ : ℕ) : M) := by
  intro t
  induction t with
  | bvar i =>
    have hb : M ⊧/![((⌜(#i : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M), ((i.val : ℕ) : M)] qqBvarDef.val :=
      Sigma0_cast₂ qqBvarDef (by simpa using quote_bvar_sentence (V := ℕ) i)
    have := (read_termValBvar hM ev ((i.val : ℕ) : M) ((⌜(#i : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M)
      (v i) hb).mpr (hev.2 i)
    simpa using this
  | fvar x => exact x.elim
  | @func k' f w ih =>
    match k', f, w, ih with
    | 0, .zero, w, _ =>
      have hval : (Semiterm.func Language.ORing.Func.zero w : ClosedSemiterm ℒₒᵣ k).valb v
          = 0 := rfl
      have hq : ((⌜(Semiterm.func Language.ORing.Func.zero w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M)
          = ((𝟎 : ℕ) : M) := by
        rw [show (⌜(Semiterm.func Language.ORing.Func.zero w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) = 𝟎 by
          simpa using quote_zeroTerm_sentence (V := ℕ) w]
      rw [hval, hq]
      exact (read_termValZero hM ev 0).mpr rfl
    | 0, .one, w, _ =>
      have hval : (Semiterm.func Language.ORing.Func.one w : ClosedSemiterm ℒₒᵣ k).valb v
          = 1 := rfl
      have hq : ((⌜(Semiterm.func Language.ORing.Func.one w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M)
          = ((𝟏 : ℕ) : M) := by
        rw [show (⌜(Semiterm.func Language.ORing.Func.one w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) = 𝟏 by
          simpa using quote_oneTerm_sentence (V := ℕ) w]
      rw [hval, hq]
      exact (read_termValOne hM ev 1).mpr rfl
    | 2, .add, w, ih =>
      have hval : (Semiterm.func Language.ORing.Func.add w : ClosedSemiterm ℒₒᵣ k).valb v
          = (w 0).valb v + (w 1).valb v := rfl
      have hq : M ⊧/![((⌜(Semiterm.func Language.ORing.Func.add w :
          ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M),
          ((⌜w 0⌝ : ℕ) : M), ((⌜w 1⌝ : ℕ) : M)] Arithmetic.qqAddGraph.val :=
        Sigma1_cast₃ Arithmetic.qqAddGraph (by simpa using quote_addTerm_sentence (V := ℕ) w)
      rw [hval]
      exact (read_termValAdd hM ev ((⌜w 0⌝ : ℕ) : M) ((⌜w 1⌝ : ℕ) : M)
        ((⌜(Semiterm.func Language.ORing.Func.add w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M)
        ((w 0).valb v) ((w 1).valb v) ((w 0).valb v + (w 1).valb v)
        (uTerm_quote_cast (w 0)) (uTerm_quote_cast (w 1)) hq (ih 0) (ih 1)).mpr rfl
    | 2, .mul, w, ih =>
      have hval : (Semiterm.func Language.ORing.Func.mul w : ClosedSemiterm ℒₒᵣ k).valb v
          = (w 0).valb v * (w 1).valb v := rfl
      have hq : M ⊧/![((⌜(Semiterm.func Language.ORing.Func.mul w :
          ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M),
          ((⌜w 0⌝ : ℕ) : M), ((⌜w 1⌝ : ℕ) : M)] Arithmetic.qqMulGraph.val :=
        Sigma1_cast₃ Arithmetic.qqMulGraph (by simpa using quote_mulTerm_sentence (V := ℕ) w)
      rw [hval]
      exact (read_termValMul hM ev ((⌜w 0⌝ : ℕ) : M) ((⌜w 1⌝ : ℕ) : M)
        ((⌜(Semiterm.func Language.ORing.Func.mul w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M)
        ((w 0).valb v) ((w 1).valb v) ((w 0).valb v * (w 1).valb v)
        (uTerm_quote_cast (w 0)) (uTerm_quote_cast (w 1)) hq (ih 0) (ih 1)).mpr rfl

/-! ### The $\Delta_0$ base case

- [HP98, Theorem I.1.70]
- [HP98, Corollary I.1.76] -/

include hM in
/-- Over `𝗣𝗔⁻` and the sentences of `tarski n`, the reading of `boundedSatisfaction` at the code of
a bounded
formula agrees with truth. -/
private lemma boundedSatisfaction_quote_reading {k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : φ.Bounded) :
    ∀ (v : Fin k → M) (ev : M), Codes v ev → (BoundedSatisfaction ((⌜φ⌝ : ℕ) : M) ev ↔ M ⊧/v φ) := by
  refine bounded_induction (ξ := Empty)
    (P := fun k φ ↦ ∀ (v : Fin k → M) (ev : M), Codes v ev → (BoundedSatisfaction ((⌜φ⌝ : ℕ) : M) ev ↔ M ⊧/v φ))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ k φ hφ
  · intro m v ev _
    have hq : M ⊧/![((⌜(⊤ : ArithmeticSemisentence m)⌝ : ℕ) : M)] qqVerumDef.val :=
      Sigma0_cast₁ qqVerumDef (by simp [Sentence.quote_def])
    simpa using read_boundedSatisfactionVerum hM _ ev hq
  · intro m v ev _
    have hq : M ⊧/![((⌜(⊥ : ArithmeticSemisentence m)⌝ : ℕ) : M)] qqFalsumDef.val :=
      Sigma0_cast₁ qqFalsumDef (by simp [Sentence.quote_def])
    simpa using read_boundedSatisfactionFalsum hM _ ev hq
  · intro m t u v ev hev
    have hq : M ⊧/![((⌜(.rel Language.Eq.eq ![t, u] : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((⌜t⌝ : ℕ) : M), ((⌜u⌝ : ℕ) : M)] qqEQDef.val :=
      Sigma1_cast₃ qqEQDef (by simpa using quote_eq_sentence (V := ℕ) t u)
    rw [read_boundedSatisfactionEq hM ((⌜t⌝ : ℕ) : M) ((⌜u⌝ : ℕ) : M) _ ev (t.valb v) (u.valb v)
      (uTerm_quote_cast t) (uTerm_quote_cast u) hq
      (termVal_quote_cast hM hev t) (termVal_quote_cast hM hev u)]
    simp [Semiformula.eval_rel]
  · intro m t u v ev hev
    have hq : M ⊧/![((⌜(.nrel Language.Eq.eq ![t, u] : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((⌜t⌝ : ℕ) : M), ((⌜u⌝ : ℕ) : M)] qqNEQDef.val :=
      Sigma1_cast₃ qqNEQDef (by simpa using quote_neq_sentence (V := ℕ) t u)
    rw [read_boundedSatisfactionNeq hM ((⌜t⌝ : ℕ) : M) ((⌜u⌝ : ℕ) : M) _ ev (t.valb v) (u.valb v)
      (uTerm_quote_cast t) (uTerm_quote_cast u) hq
      (termVal_quote_cast hM hev t) (termVal_quote_cast hM hev u)]
    simp [Semiformula.eval_nrel]
  · intro m t u v ev hev
    have hq : M ⊧/![((⌜(.rel Language.LT.lt ![t, u] : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((⌜t⌝ : ℕ) : M), ((⌜u⌝ : ℕ) : M)] qqLTDef.val :=
      Sigma1_cast₃ qqLTDef (by simpa using quote_lt_sentence (V := ℕ) t u)
    rw [read_boundedSatisfactionLt hM ((⌜t⌝ : ℕ) : M) ((⌜u⌝ : ℕ) : M) _ ev (t.valb v) (u.valb v)
      (uTerm_quote_cast t) (uTerm_quote_cast u) hq
      (termVal_quote_cast hM hev t) (termVal_quote_cast hM hev u)]
    simp [Semiformula.eval_rel]
  · intro m t u v ev hev
    have hq : M ⊧/![((⌜(.nrel Language.LT.lt ![t, u] : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((⌜t⌝ : ℕ) : M), ((⌜u⌝ : ℕ) : M)] qqNLTDef.val :=
      Sigma1_cast₃ qqNLTDef (by simpa using quote_nlt_sentence (V := ℕ) t u)
    rw [read_boundedSatisfactionNlt hM ((⌜t⌝ : ℕ) : M) ((⌜u⌝ : ℕ) : M) _ ev (t.valb v) (u.valb v)
      (uTerm_quote_cast t) (uTerm_quote_cast u) hq
      (termVal_quote_cast hM hev t) (termVal_quote_cast hM hev u)]
    simp [Semiformula.eval_nrel]
  · intro m φ ψ _ _ ihφ ihψ v ev hev
    have hq : M ⊧/![((⌜φ ⋏ ψ⌝ : ℕ) : M), ((⌜φ⌝ : ℕ) : M), ((⌜ψ⌝ : ℕ) : M)] qqAndDef.val :=
      Sigma0_cast₃ qqAndDef (by simpa using quote_and_sentence (V := ℕ) φ ψ)
    rw [read_boundedSatisfactionAnd hM ((⌜φ⌝ : ℕ) : M) ((⌜ψ⌝ : ℕ) : M) _ ev hq, ihφ v ev hev, ihψ v ev hev]
    simp
  · intro m φ ψ hφ hψ ihφ ihψ v ev hev
    have hq : M ⊧/![((⌜φ ⋎ ψ⌝ : ℕ) : M), ((⌜φ⌝ : ℕ) : M), ((⌜ψ⌝ : ℕ) : M)] qqOrDef.val :=
      Sigma0_cast₃ qqOrDef (by simpa using quote_or_sentence (V := ℕ) φ ψ)
    rw [read_boundedSatisfactionOr hM ((⌜φ⌝ : ℕ) : M) ((⌜ψ⌝ : ℕ) : M) _ ev
      (bounded_quote_cast hφ) (uFormula_quote_cast φ) (bounded_quote_cast hψ)
      (uFormula_quote_cast ψ) hq, ihφ v ev hev, ihψ v ev hev]
    simp
  · intro m t φ hφ ihφ v ev hev
    have hu : M ⊧/![((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M), ((⌜t⌝ : ℕ) : M)]
        (termBShiftGraph ℒₒᵣ).val := Sigma1_cast₂ (termBShiftGraph ℒₒᵣ) (by simp)
    have hq : M ⊧/![((⌜(∀¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M), ((⌜φ⌝ : ℕ) : M)] qqBallDef.val :=
      Sigma1_cast₃ qqBallDef (by simpa using quote_ball_sentence (V := ℕ) t φ)
    rw [read_boundedSatisfactionBall hM ((⌜t⌝ : ℕ) : M) ((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M)
      ((⌜φ⌝ : ℕ) : M) _ ev (t.valb v) (uTerm_quote_cast t) (bounded_quote_cast hφ)
      (uFormula_quote_cast φ) hu hq (termVal_quote_cast hM hev t)]
    simp only [Semiformula.eval_ball, Semiformula.Operator.lt_def, Semiformula.eval_rel]
    constructor
    · intro h x hx
      obtain ⟨e', hadj⟩ := read_adjoinTotal hM x ev
      exact (ihφ (x :> v) e' (codes_cons hM hev hadj)).mp
        (h x (by simpa [Function.comp_def] using hx) e' hadj)
    · intro h x hx e' hadj
      exact (ihφ (x :> v) e' (codes_cons hM hev hadj)).mpr
        (by simpa [Function.comp_def] using h x (by simpa [Function.comp_def] using hx))
  · intro m t φ hφ ihφ v ev hev
    have hu : M ⊧/![((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M), ((⌜t⌝ : ℕ) : M)]
        (termBShiftGraph ℒₒᵣ).val := Sigma1_cast₂ (termBShiftGraph ℒₒᵣ) (by simp)
    have hq : M ⊧/![((⌜(∃¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M), ((⌜φ⌝ : ℕ) : M)] qqBexDef.val :=
      Sigma1_cast₃ qqBexDef (by simpa using quote_bex_sentence (V := ℕ) t φ)
    rw [read_boundedSatisfactionBex hM ((⌜t⌝ : ℕ) : M) ((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M)
      ((⌜φ⌝ : ℕ) : M) _ ev (t.valb v) (uTerm_quote_cast t) hu hq
      (termVal_quote_cast hM hev t)]
    simp only [Semiformula.eval_bexs, Semiformula.Operator.lt_def, Semiformula.eval_rel]
    constructor
    · rintro ⟨x, hx, e', hadj, hsat⟩
      exact ⟨x, by simpa [Function.comp_def] using hx, (ihφ (x :> v) e' (codes_cons hM hev hadj)).mp hsat⟩
    · rintro ⟨x, hx, hsat⟩
      obtain ⟨e', hadj⟩ := read_adjoinTotal hM x ev
      exact ⟨x, by simpa [Function.comp_def] using hx, e', hadj,
        (ihφ (x :> v) e' (codes_cons hM hev hadj)).mpr (by simpa [Function.comp_def] using hsat)⟩

/-! ### The strict prenex induction

- [HP98, Corollary I.1.76]
- [HP98, Remark I.1.77] -/

include hM in
private lemma hierarchySatisfaction_quote_reading {Γ : Polarity} {s k : ℕ}
    {φ : ArithmeticSemisentence k}
    (h : StrictHierarchy Γ s φ) (hs : s ≤ n + 1) :
    ∀ (v : Fin k → M) (ev : M), Codes v ev → (Reading.HierarchySatisfaction Γ s ((⌜φ⌝ : ℕ) : M) ev ↔ M ⊧/v φ) := by
  revert hs
  induction h with
  | @zero Γ₀ m₀ φ₀ hφ₀ =>
    intro _ v ev hev
    exact boundedSatisfaction_quote_reading hM hφ₀ v ev hev
  | @ofAlt Γ₀ s₀ m₀ φ₀ hφ₀ ih =>
    intro hs v ev hev
    rw [read_ofAlt hM (show s₀ ≤ n by omega) Γ₀ ((⌜φ₀⌝ : ℕ) : M) ev
      (strict_quote_cast hφ₀) (uFormula_quote_cast φ₀)]
    exact ih (by omega) v ev hev
  | @exs s₀ m₀ φ₀ _ ih =>
    intro hs v ev hev
    have hq : M ⊧/![((⌜(∃¹ φ₀ : ArithmeticSemisentence m₀)⌝ : ℕ) : M), ((⌜φ₀⌝ : ℕ) : M)]
        qqExsDef.val := Sigma0_cast₂ qqExsDef (by simpa using quote_ex_sentence (V := ℕ) φ₀)
    show Reading.SigmaSatisfaction s₀ _ _ ↔ _
    rw [read_sigmaSatisfactionExs hM (show s₀ ≤ n by omega) ((⌜φ₀⌝ : ℕ) : M) _ ev hq]
    simp only [Semiformula.eval_ex]
    constructor
    · rintro ⟨x, e', hadj, hsat⟩
      exact ⟨x, (ih (by omega) (x :> v) e' (codes_cons hM hev hadj)).mp hsat⟩
    · rintro ⟨x, hsat⟩
      obtain ⟨e', hadj⟩ := read_adjoinTotal hM x ev
      exact ⟨x, e', hadj, (ih (by omega) (x :> v) e' (codes_cons hM hev hadj)).mpr hsat⟩
  | @all s₀ m₀ φ₀ _ ih =>
    intro hs v ev hev
    have hq : M ⊧/![((⌜(∀¹ φ₀ : ArithmeticSemisentence m₀)⌝ : ℕ) : M), ((⌜φ₀⌝ : ℕ) : M)]
        qqAllDef.val := Sigma0_cast₂ qqAllDef (by simpa using quote_all_sentence (V := ℕ) φ₀)
    show Reading.PiSatisfaction s₀ _ _ ↔ _
    rw [read_piSatisfactionAll hM (show s₀ ≤ n by omega) ((⌜φ₀⌝ : ℕ) : M) _ ev hq]
    simp only [Semiformula.eval_all]
    constructor
    · intro hsat x
      obtain ⟨e', hadj⟩ := read_adjoinTotal hM x ev
      exact (ih (by omega) (x :> v) e' (codes_cons hM hev hadj)).mp (hsat x e' hadj)
    · intro hsat x e' hadj
      exact (ih (by omega) (x :> v) e' (codes_cons hM hev hadj)).mpr (hsat x)

include hM in
/-- Over `𝗣𝗔⁻` and the sentences of `tarski n`, the reading of `sigmaSatisfaction n` at the code of
a
strict prenex $\Sigma_{n + 1}$ formula agrees with truth. -/
theorem sigmaSatisfaction_quote_reading {k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) {v : Fin k → M} {ev : M} (hev : Codes v ev) :
    Reading.SigmaSatisfaction n ((⌜φ⌝ : ℕ) : M) ev ↔ M ⊧/v φ :=
  hierarchySatisfaction_quote_reading hM hφ le_rfl v ev hev

/-! ### Assembling the snowing lemma over `𝗣𝗔⁻`

- [HP98, Corollary I.1.76]
- [HP98, Remark I.1.77] -/

private lemma eval_sigmaSatisfactionVec (p : M) (w : Fin k → M) :
    M ⊧/(p :> w) (sigmaSatisfactionVec n k).val ↔ ∃ ev, Codes w ev ∧ Reading.SigmaSatisfaction n p ev := by
  simp only [sigmaSatisfactionVec, Nat.succ_eq_add_one, Nat.reduceAdd, HierarchySymbol.Semiformula.val_mkSigma,
    Semiformula.eval_ex, LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp₂,
    Semiterm.val_operator, Matrix.comp₀, Structure.numeral_eq_numeral, numeral_eq_natCast_app,
    Semiterm.val_bvar, Matrix.cons_val_zero, Fin.isValue, Fin.Fin1.eq_one, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.conj_hom_prop, Matrix.comp₃, Semiformula.eval_operator,
    Matrix.cons_val_succ, Structure.eq_iff_eq, LogicalConnective.Prop.and_eq, exists_eq_right,
    Reading.Codes, Reading.Len, Reading.Nth, Reading.SigmaSatisfaction, and_assoc]

private lemma eval_snowing_rhs {k : ℕ} (φ : ArithmeticSemisentence k) (e : Fin k → M) :
    M ⊧/e ((sigmaSatisfactionVec n k).val ⇜ ((⌜φ⌝ : ArithmeticSemiterm Empty k) :> fun i ↦ #i))
      ↔ M ⊧/(((⌜φ⌝ : ℕ) : M) :> e) (sigmaSatisfactionVec n k).val := by
  simp only [Semiformula.eval_substs, Matrix.comp_vecCons'', Arithmetic.gödelNumber'_def,
    Semiterm.Operator.encode, Semiterm.Operator.const, Semiterm.val_operator,
    Structure.numeral_eq_numeral, numeral_eq_natCast_app, Sentence.quote_eq_encode_nat,
    Matrix.empty_eq]
  simp only [Function.comp_def, Semiterm.val_bvar]

end peanoMinus

theorem provable_snowing_of_tarski {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) : 𝗣𝗔⁻ ∪ tarski n ⊢ snowing n φ := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ (𝗣𝗔⁻ ∪ tarski n) := Entailment.WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance
      (Entailment.Axiomatized.le_of_subset Set.subset_union_left)
  unfold snowing
  apply Arithmetic.provable_iff_of_models_iff (T := 𝗣𝗔⁻ ∪ tarski n)
  intro M _ hMT e
  have hPA : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := Semantics.ModelsSet.of_subset hMT Set.subset_union_left
  have hM : ∀ σ : ArithmeticSentence, tarski n σ → M↓[ℒₒᵣ] ⊧ σ := fun σ hσ ↦
    Semantics.ModelsSet.models _ (Set.mem_union_right 𝗣𝗔⁻ hσ)
  have := hPA
  rw [eval_snowing_rhs, eval_sigmaSatisfactionVec]
  constructor
  · intro h
    obtain ⟨ev, hev⟩ := exists_codes hM e
    exact ⟨ev, hev, (hierarchySatisfaction_quote_reading hM hφ le_rfl e ev hev).mpr h⟩
  · rintro ⟨ev, hev, hsat⟩
    exact (hierarchySatisfaction_quote_reading hM hφ le_rfl e ev hev).mp hsat

end FFL.FirstOrder.Arithmetic
