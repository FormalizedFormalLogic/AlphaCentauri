module

public import AlphaCentauri.Bootstrapping.PartialTruth.Tarski

/-!
# Partial truth definitions agree with truth

This module proves the “it's snowing” agreement between partial satisfaction and semantics,
both in every model of `𝗜𝚺₁` and, uniformly, over `𝗣𝗔⁻` together with the finite Tarski theory.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

open Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Codes of quoted semisentences

Foundation's `quote_*` lemmas compute the code of a `Semiproposition`. A `Semisentence` is
quoted through its embedding (`Sentence.quote_def`), so each of them has a counterpart here,
proved by unfolding that embedding. -/

/-- A coded closed term is a well-formed internal term.
- [HP98, 1.66] -/
private lemma isUTerm_quote {k : ℕ} (t : ClosedSemiterm ℒₒᵣ k) : IsUTerm ℒₒᵣ (⌜t⌝ : V) := by
  simp [Semiterm.empty_quote_eq]

/-- A coded semisentence is a well-formed internal formula.
- [HP98, 1.66] -/
private lemma isUFormula_quote {k : ℕ} (φ : ArithmeticSemisentence k) :
    IsUFormula ℒₒᵣ (⌜φ⌝ : V) := (Sentence.quote_isSemiformula φ).isUFormula

/-- The code of an equation between closed terms.
- [HP98, 1.66] -/
private lemma quote_eq_sentence {k : ℕ} (t u : ClosedSemiterm ℒₒᵣ k) :
    (⌜(.rel Language.Eq.eq ![t, u] : ArithmeticSemisentence k)⌝ : V)
      = Arithmetic.qqEQ (⌜t⌝ : V) (⌜u⌝ : V) := by
  simpa [Sentence.quote_def, Semiformula.quote_rel, Arithmetic.qqEQ, Semiterm.empty_quote_eq,
    Semiterm.empty_typed_quote_def, Matrix.vecHead, Matrix.vecTail] using coe_quote_eq (V := V)

/-- The code of a negated equation between closed terms.
- [HP98, 1.66] -/
private lemma quote_neq_sentence {k : ℕ} (t u : ClosedSemiterm ℒₒᵣ k) :
    (⌜(.nrel Language.Eq.eq ![t, u] : ArithmeticSemisentence k)⌝ : V)
      = Arithmetic.qqNEQ (⌜t⌝ : V) (⌜u⌝ : V) := by
  simpa [Sentence.quote_def, Semiformula.quote_nrel, Arithmetic.qqNEQ, Semiterm.empty_quote_eq,
    Semiterm.empty_typed_quote_def, Matrix.vecHead, Matrix.vecTail] using coe_quote_eq (V := V)

/-- The code of a comparison between closed terms.
- [HP98, 1.66] -/
private lemma quote_lt_sentence {k : ℕ} (t u : ClosedSemiterm ℒₒᵣ k) :
    (⌜(.rel Language.LT.lt ![t, u] : ArithmeticSemisentence k)⌝ : V)
      = Arithmetic.qqLT (⌜t⌝ : V) (⌜u⌝ : V) := by
  simpa [Sentence.quote_def, Semiformula.quote_rel, Arithmetic.qqLT, Semiterm.empty_quote_eq,
    Semiterm.empty_typed_quote_def, Matrix.vecHead, Matrix.vecTail] using coe_quote_lt (V := V)

/-- The code of a negated comparison between closed terms.
- [HP98, 1.66] -/
private lemma quote_nlt_sentence {k : ℕ} (t u : ClosedSemiterm ℒₒᵣ k) :
    (⌜(.nrel Language.LT.lt ![t, u] : ArithmeticSemisentence k)⌝ : V)
      = Arithmetic.qqNLT (⌜t⌝ : V) (⌜u⌝ : V) := by
  simpa [Sentence.quote_def, Semiformula.quote_nrel, Arithmetic.qqNLT, Semiterm.empty_quote_eq,
    Semiterm.empty_typed_quote_def, Matrix.vecHead, Matrix.vecTail] using coe_quote_lt (V := V)

/-- The code of a conjunction of semisentences.
- [HP98, 1.66] -/
private lemma quote_and_sentence {k : ℕ} (φ ψ : ArithmeticSemisentence k) :
    (⌜φ ⋏ ψ⌝ : V) = (⌜φ⌝ : V) ^⋏ (⌜ψ⌝ : V) := by simp [Sentence.quote_def]

/-- The code of a disjunction of semisentences.
- [HP98, 1.66] -/
private lemma quote_or_sentence {k : ℕ} (φ ψ : ArithmeticSemisentence k) :
    (⌜φ ⋎ ψ⌝ : V) = (⌜φ⌝ : V) ^⋎ (⌜ψ⌝ : V) := by simp [Sentence.quote_def]

/-- The code of a universally quantified semisentence.
- [HP98, 1.66] -/
private lemma quote_all_sentence {k : ℕ} (φ : ArithmeticSemisentence (k + 1)) :
    (⌜(∀¹ φ : ArithmeticSemisentence k)⌝ : V) = ^∀ (⌜φ⌝ : V) := by simp [Sentence.quote_def]

/-- The code of an existentially quantified semisentence.
- [HP98, 1.66] -/
private lemma quote_ex_sentence {k : ℕ} (φ : ArithmeticSemisentence (k + 1)) :
    (⌜(∃¹ φ : ArithmeticSemisentence k)⌝ : V) = ^∃ (⌜φ⌝ : V) := by simp [Sentence.quote_def]

/-- The code of a bounded universal quantification; the semisentence form of Foundation's
`quote_ball`.
- [HP98, 0.30] -/
private lemma quote_ball_sentence {k : ℕ} (t : ClosedSemiterm ℒₒᵣ k)
    (φ : ArithmeticSemisentence (k + 1)) :
    (⌜(∀¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemisentence k)⌝ : V)
      = qqBall (termBShift ℒₒᵣ (⌜t⌝ : V)) (⌜φ⌝ : V) := by
  rw [Semiformula.ball_eq, Semiformula.imp_eq]
  simpa [Sentence.quote_def, Semiformula.Operator.lt_def, Semiformula.neg_rel, qqBall,
    Semiformula.quote_nrel, Arithmetic.qqNLT, Semiterm.empty_quote_eq, Matrix.vecHead,
    Matrix.vecTail, ← Rew.emb_bShift_term,
    ← Semiterm.empty_typed_quote_def] using coe_quote_lt (V := V)

/-- The code of a bounded existential quantification; the semisentence form of `quote_bex`.
- [HP98, 0.30] -/
private lemma quote_bex_sentence {k : ℕ} (t : ClosedSemiterm ℒₒᵣ k)
    (φ : ArithmeticSemisentence (k + 1)) :
    (⌜(∃¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemisentence k)⌝ : V)
      = qqBex (termBShift ℒₒᵣ (⌜t⌝ : V)) (⌜φ⌝ : V) := by
  rw [Semiformula.bexs_eq]
  simpa [Sentence.quote_def, Semiformula.Operator.lt_def, qqBex, Semiformula.quote_rel,
    Arithmetic.qqLT, Semiterm.empty_quote_eq, Matrix.vecHead, Matrix.vecTail,
    ← Rew.emb_bShift_term, ← Semiterm.empty_typed_quote_def] using coe_quote_lt (V := V)

/-! ## Agreement of satisfaction with truth -/

/-- For a bounded formula, internal `Δ₀` satisfaction of its code agrees with truth. This is the
base case of the snowing lemma, by recursion on the bounded formula: each clause is the matching
Tarski condition of `SatZero`, and the atoms are `termVal_quote`.
- [HP98, Theorem I.1.70]
- [HP98, Corollary I.1.76] -/
theorem satZero_quote_iff {k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : Hierarchy 𝚺 0 φ) (v : Fin k → V) :
    SatZero (⌜φ⌝ : V) (matrixToVec v) ↔ V ⊧/v φ := by
  revert v
  refine delta₀_induction (ξ := Empty)
    (P := fun k φ ↦ ∀ v : Fin k → V, SatZero (⌜φ⌝ : V) (matrixToVec v) ↔ V ⊧/v φ)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ k φ hφ
  · intro n v; simp [Sentence.quote_def]
  · intro n v; simp [Sentence.quote_def]
  · intro n t u v
    rw [quote_eq_sentence, SatZero.eq_iff (isUTerm_quote t) (isUTerm_quote u),
      termVal_quote, termVal_quote]
    simp [Semiformula.eval_rel]
  · intro n t u v
    rw [quote_neq_sentence, SatZero.neq_iff (isUTerm_quote t) (isUTerm_quote u),
      termVal_quote, termVal_quote]
    simp [Semiformula.eval_nrel]
  · intro n t u v
    rw [quote_lt_sentence, SatZero.lt_iff (isUTerm_quote t) (isUTerm_quote u),
      termVal_quote, termVal_quote]
    simp [Semiformula.eval_rel]
  · intro n t u v
    rw [quote_nlt_sentence, SatZero.nlt_iff (isUTerm_quote t) (isUTerm_quote u),
      termVal_quote, termVal_quote]
    simp [Semiformula.eval_nrel]
  · intro n φ ψ hφ hψ ihφ ihψ v
    rw [quote_and_sentence, SatZero.and_iff, ihφ v, ihψ v]
    simp
  · intro n φ ψ hφ hψ ihφ ihψ v
    rw [quote_or_sentence, SatZero.or_iff ((isDelta0_quote_iff φ).mpr hφ) (isUFormula_quote φ)
      ((isDelta0_quote_iff ψ).mpr hψ) (isUFormula_quote ψ), ihφ v, ihψ v]
    simp
  · intro n t φ hφ ihφ v
    rw [quote_ball_sentence, SatZero.ball_iff (isUTerm_quote t)
      ((isDelta0_quote_iff φ).mpr hφ) (isUFormula_quote φ), termVal_quote]
    simp only [Semiformula.eval_ball, Semiformula.Operator.lt_def, Semiformula.eval_rel]
    refine forall_congr' fun x ↦ ?_
    rw [show (x ∷ matrixToVec v : V) = matrixToVec (x :> v) by simp, ihφ (x :> v)]
    simp [Function.comp_def]
  · intro n t φ hφ ihφ v
    rw [quote_bex_sentence, SatZero.bex_iff (isUTerm_quote t), termVal_quote]
    simp only [Semiformula.eval_bexs, Semiformula.Operator.lt_def, Semiformula.eval_rel]
    refine exists_congr fun x ↦ ?_
    rw [show (x ∷ matrixToVec v : V) = matrixToVec (x :> v) by simp, ihφ (x :> v)]
    simp [Function.comp_def]

/-- The satisfaction predicate selected by a polarity. It lets one induction on a
`StrictHierarchy` derivation, whose polarity the `zero` and `ofAlt` constructors leave open,
produce the `Σ` and the `Π` statement at once.
- [HP98, Definition I.1.74] -/
def SatClass : Polarity → ℕ → V → V → Prop
  | .sigma, n, z, e => SatSigma n z e
  | .pi, n, z, e => SatPi n z e

/-- Internal satisfaction of the code of a strict prenex formula agrees with truth, by induction
on the derivation of its strict class.
- [HP98, Corollary I.1.76]
- [HP98, Remark I.1.80] -/
lemma satClass_quote_iff {Γ : Polarity} {s k : ℕ} {φ : ArithmeticSemisentence k}
    (h : StrictHierarchy Γ s φ) :
    ∀ v : Fin k → V, SatClass Γ s (⌜φ⌝ : V) (matrixToVec v) ↔ V ⊧/v φ := by
  induction h with
  | @zero Γ₀ n₀ φ₀ hφ₀ =>
    intro v
    rcases Γ₀ with _ | _
    · show SatSigma 0 _ _ ↔ _
      rw [SatSigma.zero]; exact satZero_quote_iff hφ₀ v
    · show SatPi 0 _ _ ↔ _
      rw [SatPi.zero]; exact satZero_quote_iff hφ₀ v
  | @ofAlt Γ₀ s₀ n₀ φ₀ hφ₀ ih =>
    intro v
    rcases Γ₀ with _ | _
    · show SatSigma (s₀ + 1) _ _ ↔ _
      rw [SatSigma.of_pi ((isStrictPi_quote_iff φ₀).mpr hφ₀) (isUFormula_quote φ₀)]
      exact ih v
    · show SatPi (s₀ + 1) _ _ ↔ _
      rw [SatPi.of_sigma ((isStrictSigma_quote_iff φ₀).mpr hφ₀) (isUFormula_quote φ₀)]
      exact ih v
  | @exs s₀ n₀ φ₀ hφ₀ ih =>
    intro v
    show SatSigma (s₀ + 1) _ _ ↔ _
    rw [quote_ex_sentence, SatSigma.exs_iff]
    simp only [Semiformula.eval_ex]
    refine exists_congr fun x ↦ ?_
    rw [show (x ∷ matrixToVec v : V) = matrixToVec (x :> v) by simp]
    exact ih (x :> v)
  | @all s₀ n₀ φ₀ hφ₀ ih =>
    intro v
    show SatPi (s₀ + 1) _ _ ↔ _
    rw [quote_all_sentence, SatPi.all_iff]
    simp only [Semiformula.eval_all]
    refine forall_congr' fun x ↦ ?_
    rw [show (x ∷ matrixToVec v : V) = matrixToVec (x :> v) by simp]
    exact ih (x :> v)

/-- For a strict prenex `Σₙ` formula, internal satisfaction of its code agrees with truth.
- [HP98, Corollary I.1.76]
- [HP98, Remark I.1.80] -/
theorem satSigma_quote_iff {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚺 n φ) (v : Fin k → V) :
    SatSigma n ⌜φ⌝ (matrixToVec v) ↔ V ⊧/v φ := satClass_quote_iff hφ v

/-- For a strict prenex `Πₙ` formula, internal satisfaction of its code agrees with truth.
- [HP98, Corollary I.1.76]
- [HP98, Remark I.1.80] -/
theorem satPi_quote_iff {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚷 n φ) (v : Fin k → V) :
    SatPi n ⌜φ⌝ (matrixToVec v) ↔ V ⊧/v φ := satClass_quote_iff hφ v

/-- The sentence asserting agreement of `φ` with its level-`Σₙ₊₁` partial truth definition.
- [HP98, Corollary I.1.76] -/
noncomputable def snowing (n : ℕ) {k : ℕ}
    (φ : ArithmeticSemisentence k) : ArithmeticSentence :=
  ∀¹* (φ 🡘 (satSigmaVec n k).val ⇜ ((⌜φ⌝ : ArithmeticSemiterm Empty k) :> fun i ↦ #i))

/-- Semantic interpretation of the sentence `snowing n φ`: the substituted right-hand side is
the defining formula of `satSigmaVec`, read under the assignment given by the free variables.
- [HP98, Corollary I.1.76] -/
theorem models_snowing_iff {n k : ℕ} (φ : ArithmeticSemisentence k) :
    V↓[ℒₒᵣ] ⊧ snowing n φ ↔
      ∀ v : Fin k → V, V ⊧/v φ ↔ SatSigma (n + 1) ⌜φ⌝ (matrixToVec v) := by
  simp [snowing, models_iff, (satSigmaVec.defined n k).df, Function.comp_def]

/-- The theory form of the snowing lemma follows from `𝗣𝗔⁻` and the finite Tarski theory.
- [HP98, Corollary I.1.76]
- [HP98, Remark I.1.77] -/
axiom provable_snowing_of_tarski {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) : 𝗣𝗔⁻ ∪ tarski n ⊢ snowing n φ

/-- `𝗜𝚺₁` proves the snowing sentence for every strict prenex `Σₙ₊₁` formula: the two sides
agree in every model of `𝗜𝚺₁` by `satSigma_quote_iff`, so completeness delivers a proof.
- [HP98, Corollary I.1.76] -/
theorem ISigma1.provable_snowing {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) : 𝗜𝚺₁ ⊢ snowing n φ := by
  apply Arithmetic.complete.{0}
  intro M _ _
  exact (models_snowing_iff φ).mpr fun v ↦ (satSigma_quote_iff hφ v).symm

end LO.FirstOrder.Arithmetic
