module

public import AlphaCentauri.Bootstrapping.PartialTruth.SatSigma

/-!
# The Tarski conditions as an explicit finite theory

This module packages the Tarski conditions for the partial truth definitions as explicit
arithmetic sentences, collects them into the finite theory `tarski n`, and proves that `𝗜𝚺₁`
proves every one of them.

- [HP98, Theorem I.1.70]
- [HP98, Theorem I.1.75(2)]
- [HP98, Remark I.1.77]
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

open Bootstrapping

/-! ## The sentences -/

namespace Tarski

/-- Satisfaction is restricted to internally coded `Δ₀` formulas.
- [HP98, Theorem I.1.70(i)] -/
noncomputable def satZeroDom : ArithmeticSentence :=
  “∀ z e, !satZero.val z e → !isDelta0.val z ∧ !(isUFormula ℒₒᵣ).val z”

/-- The Tarski sentence for truth.
- [HP98, Theorem I.1.70(ii)] -/
noncomputable def satZeroVerum : ArithmeticSentence :=
  “∀ z e, !qqVerumDef.val z → !satZero.val z e”

/-- The Tarski sentence for falsehood.
- [HP98, Theorem I.1.70(ii)] -/
noncomputable def satZeroFalsum : ArithmeticSentence :=
  “∀ z e, !qqFalsumDef.val z → ¬!satZero.val z e”

/-- The Tarski sentence for equality.
- [HP98, Theorem I.1.70(ii)] -/
noncomputable def satZeroEq : ArithmeticSentence :=
  “∀ t u z e vt vu, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !qqEQDef.val z t u → !termValGraph.val vt e t → !termValGraph.val vu e u →
    (!satZero.val z e ↔ vt = vu)”

/-- The Tarski sentence for inequality.
- [HP98, Theorem I.1.70(ii)] -/
noncomputable def satZeroNeq : ArithmeticSentence :=
  “∀ t u z e vt vu, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !qqNEQDef.val z t u → !termValGraph.val vt e t → !termValGraph.val vu e u →
    (!satZero.val z e ↔ vt ≠ vu)”

/-- The Tarski sentence for less-than.
- [HP98, Theorem I.1.70(ii)] -/
noncomputable def satZeroLt : ArithmeticSentence :=
  “∀ t u z e vt vu, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !qqLTDef.val z t u → !termValGraph.val vt e t → !termValGraph.val vu e u →
    (!satZero.val z e ↔ vt < vu)”

/-- The Tarski sentence for negated less-than.
- [HP98, Theorem I.1.70(ii)] -/
noncomputable def satZeroNlt : ArithmeticSentence :=
  “∀ t u z e vt vu, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !qqNLTDef.val z t u → !termValGraph.val vt e t → !termValGraph.val vu e u →
    (!satZero.val z e ↔ ¬(vt < vu))”

/-- The Tarski sentence for conjunction.
- [HP98, Theorem I.1.70(ii)] -/
noncomputable def satZeroAnd : ArithmeticSentence :=
  “∀ p q z e, !qqAndDef.val z p q →
    (!satZero.val z e ↔ !satZero.val p e ∧ !satZero.val q e)”

/-- The Tarski sentence for disjunction. Unlike conjunction, both disjuncts have to be assumed
well-formed: one satisfied disjunct says nothing about the shape of the other, while satisfaction
of the disjunction carries the well-formedness of both.
- [HP98, Theorem I.1.70(ii)] -/
noncomputable def satZeroOr : ArithmeticSentence :=
  “∀ p q z e, !isDelta0.val p → !(isUFormula ℒₒᵣ).val p → !isDelta0.val q →
    !(isUFormula ℒₒᵣ).val q → !qqOrDef.val z p q →
    (!satZero.val z e ↔ !satZero.val p e ∨ !satZero.val q e)”

/-- The Tarski sentence for negation.
- [HP98, Theorem I.1.70(iii)] -/
noncomputable def satZeroNeg : ArithmeticSentence :=
  “∀ p np e, !isDelta0.val p → !(isUFormula ℒₒᵣ).val p →
    !(negGraph ℒₒᵣ).val np p → (!satZero.val np e ↔ ¬!satZero.val p e)”

/-- The Tarski sentence for bounded universal quantification.
- [HP98, Theorem I.1.70(iv)] -/
noncomputable def satZeroBall : ArithmeticSentence :=
  “∀ t u q z e v, !(isUTerm ℒₒᵣ).val t → !isDelta0.val q →
    !(isUFormula ℒₒᵣ).val q → !(termBShiftGraph ℒₒᵣ).val u t →
    !qqBallDef.val z u q → !termValGraph.val v e t →
    (!satZero.val z e ↔ ∀ x < v, ∀ e', !adjoinDef.val e' x e → !satZero.val q e')”

/-- The Tarski sentence for bounded existential quantification.
- [HP98, Theorem I.1.70(iv)] -/
noncomputable def satZeroBex : ArithmeticSentence :=
  “∀ t u q z e v, !(isUTerm ℒₒᵣ).val t → !(termBShiftGraph ℒₒᵣ).val u t →
    !qqBexDef.val z u q → !termValGraph.val v e t →
    (!satZero.val z e ↔ ∃ x < v, ∃ e', !adjoinDef.val e' x e ∧ !satZero.val q e')”

/-- The defining sentence for evaluation of coded bound variables.
- [HP98, 1.64(5)] -/
noncomputable def termValBvar : ArithmeticSentence :=
  “∀ e z t v, !qqBvarDef.val t z → (!termValGraph.val v e t ↔ !nthDef.val v e z)”

/-- The defining sentence for evaluation of zero.
- [HP98, 1.64(5)] -/
noncomputable def termValZero : ArithmeticSentence :=
  “∀ e v, !termValGraph.val v e ↑Bootstrapping.Arithmetic.zero ↔ v = 0”

/-- The defining sentence for evaluation of one.
- [HP98, 1.64(5)] -/
noncomputable def termValOne : ArithmeticSentence :=
  “∀ e v, !termValGraph.val v e ↑Bootstrapping.Arithmetic.one ↔ v = 1”

/-- The defining sentence for evaluation of addition.
- [HP98, 1.64(5)] -/
noncomputable def termValAdd : ArithmeticSentence :=
  “∀ e t u s vt vu v, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !Bootstrapping.Arithmetic.qqAddGraph.val s t u → !termValGraph.val vt e t →
    !termValGraph.val vu e u →
    (!termValGraph.val v e s ↔ v = vt + vu)”

/-- The defining sentence for evaluation of multiplication.
- [HP98, 1.64(5)] -/
noncomputable def termValMul : ArithmeticSentence :=
  “∀ e t u s vt vu v, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !Bootstrapping.Arithmetic.qqMulGraph.val s t u → !termValGraph.val vt e t →
    !termValGraph.val vu e u →
    (!termValGraph.val v e s ↔ v = vt * vu)”

/-- Coded vector adjunction is total.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
noncomputable def adjoinTotal : ArithmeticSentence :=
  “∀ x v, ∃ e, !adjoinDef.val e x v”

/-- Coded vector adjunction is functional.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
noncomputable def adjoinUnique : ArithmeticSentence :=
  “∀ x v e e', !adjoinDef.val e x v → !adjoinDef.val e' x v → e = e'”

/-- The head of an adjoined coded vector is its new entry.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
noncomputable def nthAdjoinZero : ArithmeticSentence :=
  “∀ x v e y, !adjoinDef.val e x v → (!nthDef.val y e 0 ↔ y = x)”

/-- Successor indices into an adjoined coded vector read from its tail.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
noncomputable def nthAdjoinSucc : ArithmeticSentence :=
  “∀ x v e i y, !adjoinDef.val e x v →
    (!nthDef.val y e (i + 1) ↔ !nthDef.val y v i)”

/-- The empty coded vector has length zero.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
noncomputable def lenNil : ArithmeticSentence := “∀ l, !lenDef.val l 0 ↔ l = 0”

/-- Adjunction increases the length of a coded vector by one.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
noncomputable def lenAdjoin : ArithmeticSentence :=
  “∀ x v e l, !adjoinDef.val e x v → (!lenDef.val (l + 1) e ↔ !lenDef.val l v)”

/-- The empty-block Tarski condition for reading `Πₙ` satisfaction as `Σₙ₊₁` satisfaction.
- [HP98, Theorem I.1.75(2)(v)] -/
noncomputable def satSigmaOfPi : ℕ → ArithmeticSentence
  | 0 =>
      “∀ z e, !isDelta0.val z → !(isUFormula ℒₒᵣ).val z →
        (!(satSigma 0).val z e ↔ !satZero.val z e)”
  | n + 1 =>
      “∀ z e, !(isStrictPi (n + 1)).val z → !(isUFormula ℒₒᵣ).val z →
        (!(satSigma (n + 1)).val z e ↔ !(satPi n).val z e)”

/-- The empty-block Tarski condition for reading `Σₙ` satisfaction as `Πₙ₊₁` satisfaction.
- [HP98, Theorem I.1.75(2)(v′)] -/
noncomputable def satPiOfSigma : ℕ → ArithmeticSentence
  | 0 =>
      “∀ z e, !isDelta0.val z → !(isUFormula ℒₒᵣ).val z →
        (!(satPi 0).val z e ↔ !satZero.val z e)”
  | n + 1 =>
      “∀ z e, !(isStrictSigma (n + 1)).val z → !(isUFormula ℒₒᵣ).val z →
        (!(satPi (n + 1)).val z e ↔ !(satSigma n).val z e)”

/-- The domain Tarski condition for `Σₙ₊₁` satisfaction.
- [HP98, Theorem I.1.75(2)] -/
noncomputable def satSigmaDom (n : ℕ) : ArithmeticSentence :=
  “∀ z e, !(satSigma n).val z e →
    !(isStrictSigma (n + 1)).val z ∧ !(isUFormula ℒₒᵣ).val z”

/-- The domain Tarski condition for `Πₙ₊₁` satisfaction.
- [HP98, Theorem I.1.75(2)] -/
noncomputable def satPiDom (n : ℕ) : ArithmeticSentence :=
  “∀ z e, !(satPi n).val z e →
    !(isStrictPi (n + 1)).val z ∧ !(isUFormula ℒₒᵣ).val z”

/-- The Tarski condition for existential quantification at level `Σₙ₊₁`.
- [HP98, Theorem I.1.75(2)(v)] -/
noncomputable def satSigmaExs (n : ℕ) : ArithmeticSentence :=
  “∀ p z e, !qqExsDef.val z p →
    (!(satSigma n).val z e ↔
      ∃ x e', !adjoinDef.val e' x e ∧ !(satSigma n).val p e')”

/-- The Tarski condition for universal quantification at level `Πₙ₊₁`.
- [HP98, Theorem I.1.75(2)(v′)] -/
noncomputable def satPiAll (n : ℕ) : ArithmeticSentence :=
  “∀ p z e, !qqAllDef.val z p →
    (!(satPi n).val z e ↔
      ∀ x e', !adjoinDef.val e' x e → !(satPi n).val p e')”

/-- The negation-duality Tarski condition from `Σₙ₊₁` to `Πₙ₊₁`.
- [HP98, Theorem I.1.75(2)] -/
noncomputable def satPiNeg (n : ℕ) : ArithmeticSentence :=
  “∀ z nz e, !(isStrictSigma (n + 1)).val z → !(isUFormula ℒₒᵣ).val z →
    !(negGraph ℒₒᵣ).val nz z →
    (!(satPi n).val nz e ↔ ¬!(satSigma n).val z e)”

/-- The negation-duality Tarski condition from `Πₙ₊₁` to `Σₙ₊₁`.
- [HP98, Theorem I.1.75(2)] -/
noncomputable def satSigmaNeg (n : ℕ) : ArithmeticSentence :=
  “∀ z nz e, !(isStrictPi (n + 1)).val z → !(isUFormula ℒₒᵣ).val z →
    !(negGraph ℒₒᵣ).val nz z →
    (!(satSigma n).val nz e ↔ ¬!(satPi n).val z e)”

/-- The finite collection of `Δ₀` Tarski and term-evaluation sentences.
- [HP98, Theorem I.1.70]
- [HP98, Remark I.1.77] -/
noncomputable def satZeroAxioms : ArithmeticTheory :=
  {satZeroDom, satZeroVerum, satZeroFalsum, satZeroEq, satZeroNeq, satZeroLt,
    satZeroNlt, satZeroAnd, satZeroOr, satZeroNeg, satZeroBall, satZeroBex,
    termValBvar, termValZero, termValOne, termValAdd, termValMul, adjoinTotal,
    adjoinUnique, nthAdjoinZero, nthAdjoinSucc, lenNil, lenAdjoin}

/-- The finite collection of level-`n + 1` Tarski sentences.
- [HP98, Theorem I.1.75(2)]
- [HP98, Remark I.1.77] -/
noncomputable def satSigmaAxioms (n : ℕ) : ArithmeticTheory :=
  {satSigmaOfPi n, satPiOfSigma n, satSigmaDom n, satPiDom n, satSigmaExs n,
    satPiAll n, satPiNeg n, satSigmaNeg n}

end Tarski

/-- `tarski n` contains the finitely many Tarski conditions through level `n + 1`, together
with the vector and term-evaluation facts used in the proof of the snowing lemma. Its exact
membership may grow during the proof stage; downstream arguments use only finiteness and
`𝗜𝚺₁`-provability.

- [HP98, Remark I.1.77] -/
inductive tarski : ℕ → ArithmeticTheory
  | zero : ∀ n, ∀ φ ∈ Tarski.satZeroAxioms, tarski n φ
  | prev : ∀ n φ, tarski n φ → tarski (n + 1) φ
  | new  : ∀ n, ∀ φ ∈ Tarski.satSigmaAxioms n, tarski n φ

/-- At the bottom level the theory is the `Δ₀` block together with the level-`Σ₁` block.
- [HP98, Remark I.1.77] -/
lemma tarski_zero : tarski 0 = Tarski.satZeroAxioms ∪ Tarski.satSigmaAxioms 0 := by
  ext φ
  constructor
  · rintro (⟨⟩ | ⟨⟩)
    · exact Or.inl ‹φ ∈ Tarski.satZeroAxioms›
    · exact Or.inr ‹φ ∈ Tarski.satSigmaAxioms 0›
  · rintro (h | h)
    · exact tarski.zero 0 φ h
    · exact tarski.new 0 φ h

/-- Each level adds the Tarski conditions of the next satisfaction predicate.
- [HP98, Remark I.1.77] -/
lemma tarski_succ (n : ℕ) :
    tarski (n + 1) = tarski n ∪ Tarski.satSigmaAxioms (n + 1) := by
  ext φ
  constructor
  · rintro (⟨⟩ | ⟨⟩ | ⟨⟩)
    · exact Or.inl (tarski.zero n φ ‹φ ∈ Tarski.satZeroAxioms›)
    · exact Or.inl ‹tarski n φ›
    · exact Or.inr ‹φ ∈ Tarski.satSigmaAxioms (n + 1)›
  · rintro (h | h)
    · exact tarski.prev n φ h
    · exact tarski.new (n + 1) φ h

/-- The explicit Tarski theory at each level is finite.
- [HP98, Remark I.1.77] -/
lemma tarski_finite (n : ℕ) : (tarski n).Finite := by
  have hSigmaAx : ∀ m : ℕ, (Tarski.satSigmaAxioms m).Finite := by
    intro m; simp only [Tarski.satSigmaAxioms]; exact Set.toFinite _
  induction n with
  | zero =>
    rw [tarski_zero]
    exact Set.Finite.union (by simp only [Tarski.satZeroAxioms]; exact Set.toFinite _) (hSigmaAx 0)
  | succ n ih => rw [tarski_succ]; exact ih.union (hSigmaAx (n + 1))



/-! ## `𝗜𝚺₁` proves the Tarski conditions

Each sentence is read through the `via` instances of the formulas it mentions, which turns it
into the matching Tarski condition of `SatZero`, `SatSigma` and `SatPi`, or into a term-evaluation
or vector-coding fact. -/

namespace Tarski

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The domain condition holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.70(i)] -/
lemma models_satZeroDom : V↓[ℒₒᵣ] ⊧ satZeroDom := by
  suffices ∀ z e : V, SatZero z e → IsDelta0 z ∧ IsUFormula ℒₒᵣ z by
    simpa [models_iff, satZeroDom] using this
  exact fun _ _ h ↦ SatZero.dom h

/-- The Tarski condition for truth holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.70(ii)] -/
lemma models_satZeroVerum : V↓[ℒₒᵣ] ⊧ satZeroVerum := by
  suffices ∀ z e : V, z = ^⊤ → SatZero z e by simpa [models_iff, satZeroVerum] using this
  rintro _ e rfl
  exact SatZero.verum e

/-- The Tarski condition for falsehood holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.70(ii)] -/
lemma models_satZeroFalsum : V↓[ℒₒᵣ] ⊧ satZeroFalsum := by
  suffices ∀ z e : V, z = ^⊥ → ¬SatZero z e by simpa [models_iff, satZeroFalsum] using this
  rintro _ e rfl
  exact SatZero.falsum e

/-- The Tarski condition for equality holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.70(ii)] -/
lemma models_satZeroEq : V↓[ℒₒᵣ] ⊧ satZeroEq := by
  suffices ∀ t u z e vt vu : V, IsUTerm ℒₒᵣ t → IsUTerm ℒₒᵣ u → z = t ^= u →
      vt = termVal e t → vu = termVal e u → (SatZero z e ↔ vt = vu) by
    simpa [models_iff, satZeroEq] using this
  rintro t u _ e _ _ ht hu rfl rfl rfl
  exact SatZero.eq_iff ht hu

/-- The Tarski condition for inequality holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.70(ii)] -/
lemma models_satZeroNeq : V↓[ℒₒᵣ] ⊧ satZeroNeq := by
  suffices ∀ t u z e vt vu : V, IsUTerm ℒₒᵣ t → IsUTerm ℒₒᵣ u → z = t ^≠ u →
      vt = termVal e t → vu = termVal e u → (SatZero z e ↔ vt ≠ vu) by
    simpa [models_iff, satZeroNeq] using this
  rintro t u _ e _ _ ht hu rfl rfl rfl
  exact SatZero.neq_iff ht hu

/-- The Tarski condition for less-than holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.70(ii)] -/
lemma models_satZeroLt : V↓[ℒₒᵣ] ⊧ satZeroLt := by
  suffices ∀ t u z e vt vu : V, IsUTerm ℒₒᵣ t → IsUTerm ℒₒᵣ u → z = t ^< u →
      vt = termVal e t → vu = termVal e u → (SatZero z e ↔ vt < vu) by
    simpa [models_iff, satZeroLt] using this
  rintro t u _ e _ _ ht hu rfl rfl rfl
  exact SatZero.lt_iff ht hu

/-- The Tarski condition for negated less-than holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.70(ii)] -/
lemma models_satZeroNlt : V↓[ℒₒᵣ] ⊧ satZeroNlt := by
  suffices ∀ t u z e vt vu : V, IsUTerm ℒₒᵣ t → IsUTerm ℒₒᵣ u → z = t ^≮ u →
      vt = termVal e t → vu = termVal e u → (SatZero z e ↔ ¬(vt < vu)) by
    simpa [models_iff, satZeroNlt] using this
  rintro t u _ e _ _ ht hu rfl rfl rfl
  exact SatZero.nlt_iff ht hu

/-- The Tarski condition for conjunction holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.70(ii)] -/
lemma models_satZeroAnd : V↓[ℒₒᵣ] ⊧ satZeroAnd := by
  suffices ∀ p q z e : V, z = p ^⋏ q → (SatZero z e ↔ SatZero p e ∧ SatZero q e) by
    simpa [models_iff, satZeroAnd] using this
  rintro p q _ e rfl
  exact SatZero.and_iff

/-- The Tarski condition for disjunction holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.70(ii)] -/
lemma models_satZeroOr : V↓[ℒₒᵣ] ⊧ satZeroOr := by
  suffices ∀ p q z e : V, IsDelta0 p → IsUFormula ℒₒᵣ p → IsDelta0 q → IsUFormula ℒₒᵣ q →
      z = p ^⋎ q → (SatZero z e ↔ SatZero p e ∨ SatZero q e) by
    simpa [models_iff, satZeroOr] using this
  rintro p q _ e hdp hfp hdq hfq rfl
  exact SatZero.or_iff hdp hfp hdq hfq

/-- The Tarski condition for negation holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.70(iii)] -/
lemma models_satZeroNeg : V↓[ℒₒᵣ] ⊧ satZeroNeg := by
  suffices ∀ p np e : V, IsDelta0 p → IsUFormula ℒₒᵣ p → np = neg ℒₒᵣ p →
      (SatZero np e ↔ ¬SatZero p e) by
    simpa [models_iff, satZeroNeg] using this
  rintro p _ e hd hf rfl
  exact SatZero.neg_iff hd hf

/-- The Tarski condition for bounded universal quantification holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.70(iv)] -/
lemma models_satZeroBall : V↓[ℒₒᵣ] ⊧ satZeroBall := by
  suffices ∀ t u q z e v : V, IsUTerm ℒₒᵣ t → IsDelta0 q → IsUFormula ℒₒᵣ q →
      u = termBShift ℒₒᵣ t → z = qqBall u q → v = termVal e t →
      (SatZero z e ↔ ∀ x < v, SatZero q (x ∷ e)) by
    simpa [models_iff, satZeroBall] using this
  rintro t _ q _ e _ ht hdq hfq rfl rfl rfl
  exact SatZero.ball_iff ht hdq hfq

/-- The Tarski condition for bounded existential quantification holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.70(iv)] -/
lemma models_satZeroBex : V↓[ℒₒᵣ] ⊧ satZeroBex := by
  suffices ∀ t u q z e v : V, IsUTerm ℒₒᵣ t → u = termBShift ℒₒᵣ t → z = qqBex u q →
      v = termVal e t → (SatZero z e ↔ ∃ x < v, SatZero q (x ∷ e)) by
    simpa [models_iff, satZeroBex] using this
  rintro t _ q _ e _ ht rfl rfl rfl
  exact SatZero.bex_iff ht

/-- Evaluation of a coded bound variable holds in every model of `𝗜𝚺₁`.
- [HP98, 1.64(5)] -/
lemma models_termValBvar : V↓[ℒₒᵣ] ⊧ termValBvar := by
  suffices ∀ e z t v : V, t = ^#z → (v = termVal e t ↔ v = e.[z]) by
    simpa [models_iff, termValBvar] using this
  rintro e z _ v rfl
  simp

/-- Evaluation of the coded zero term holds in every model of `𝗜𝚺₁`.
- [HP98, 1.64(5)] -/
lemma models_termValZero : V↓[ℒₒᵣ] ⊧ termValZero := by
  simp [models_iff, termValZero, numeral_eq_natCast]

/-- Evaluation of the coded one term holds in every model of `𝗜𝚺₁`.
- [HP98, 1.64(5)] -/
lemma models_termValOne : V↓[ℒₒᵣ] ⊧ termValOne := by
  simp [models_iff, termValOne, numeral_eq_natCast]

/-- Evaluation of a coded sum holds in every model of `𝗜𝚺₁`.
- [HP98, 1.64(5)] -/
lemma models_termValAdd : V↓[ℒₒᵣ] ⊧ termValAdd := by
  suffices ∀ e t u s vt vu v : V, IsUTerm ℒₒᵣ t → IsUTerm ℒₒᵣ u → s = t ^+ u →
      vt = termVal e t → vu = termVal e u → (v = termVal e s ↔ v = vt + vu) by
    simpa [models_iff, termValAdd] using this
  rintro e t u _ _ _ v ht hu rfl rfl rfl
  simp [termVal_add ht hu]

/-- Evaluation of a coded product holds in every model of `𝗜𝚺₁`.
- [HP98, 1.64(5)] -/
lemma models_termValMul : V↓[ℒₒᵣ] ⊧ termValMul := by
  suffices ∀ e t u s vt vu v : V, IsUTerm ℒₒᵣ t → IsUTerm ℒₒᵣ u → s = t ^* u →
      vt = termVal e t → vu = termVal e u → (v = termVal e s ↔ v = vt * vu) by
    simpa [models_iff, termValMul] using this
  rintro e t u _ _ _ v ht hu rfl rfl rfl
  simp [termVal_mul ht hu]

/-- Totality of coded adjunction holds in every model of `𝗜𝚺₁`.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
lemma models_adjoinTotal : V↓[ℒₒᵣ] ⊧ adjoinTotal := by
  simp [models_iff, adjoinTotal]

/-- Functionality of coded adjunction holds in every model of `𝗜𝚺₁`.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
lemma models_adjoinUnique : V↓[ℒₒᵣ] ⊧ adjoinUnique := by
  simp [models_iff, adjoinUnique]

/-- The head equation of coded adjunction holds in every model of `𝗜𝚺₁`.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
lemma models_nthAdjoinZero : V↓[ℒₒᵣ] ⊧ nthAdjoinZero := by
  suffices ∀ x v e y : V, e = x ∷ v → (y = e.[0] ↔ y = x) by
    simpa [models_iff, nthAdjoinZero] using this
  rintro x v _ y rfl
  simp

/-- The tail equation of coded adjunction holds in every model of `𝗜𝚺₁`.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
lemma models_nthAdjoinSucc : V↓[ℒₒᵣ] ⊧ nthAdjoinSucc := by
  suffices ∀ x v e i y : V, e = x ∷ v → (y = e.[i + 1] ↔ y = v.[i]) by
    simpa [models_iff, nthAdjoinSucc] using this
  rintro x v _ i y rfl
  simp

/-- The length of the empty coded vector holds in every model of `𝗜𝚺₁`.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
lemma models_lenNil : V↓[ℒₒᵣ] ⊧ lenNil := by
  simp [models_iff, lenNil]

/-- The length equation of coded adjunction holds in every model of `𝗜𝚺₁`.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
lemma models_lenAdjoin : V↓[ℒₒᵣ] ⊧ lenAdjoin := by
  suffices ∀ x v e l : V, e = x ∷ v → (l + 1 = len e ↔ l = len v) by
    simpa [models_iff, lenAdjoin] using this
  rintro x v _ l rfl
  simp

/-- The empty-block condition from `Π` to `Σ` holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.75(2)(v)] -/
lemma models_satSigmaOfPi (n : ℕ) : V↓[ℒₒᵣ] ⊧ satSigmaOfPi n := by
  cases n with
  | zero =>
    suffices ∀ z e : V, IsDelta0 z → IsUFormula ℒₒᵣ z → (SatSigma 1 z e ↔ SatZero z e) by
      simpa [models_iff, satSigmaOfPi] using this
    intro z e hd hf
    rw [SatSigma.of_pi (IsStrictPi.of_delta0 hd) hf, SatPi.zero]
  | succ n =>
    suffices ∀ z e : V, IsStrictPi (n + 1) z → IsUFormula ℒₒᵣ z →
        (SatSigma (n + 2) z e ↔ SatPi (n + 1) z e) by
      simpa [models_iff, satSigmaOfPi] using this
    intro z e hs hf
    exact SatSigma.of_pi hs hf

/-- The empty-block condition from `Σ` to `Π` holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.75(2)(v′)] -/
lemma models_satPiOfSigma (n : ℕ) : V↓[ℒₒᵣ] ⊧ satPiOfSigma n := by
  cases n with
  | zero =>
    suffices ∀ z e : V, IsDelta0 z → IsUFormula ℒₒᵣ z → (SatPi 1 z e ↔ SatZero z e) by
      simpa [models_iff, satPiOfSigma] using this
    intro z e hd hf
    rw [SatPi.of_sigma (IsStrictSigma.of_delta0 hd) hf, SatSigma.zero]
  | succ n =>
    suffices ∀ z e : V, IsStrictSigma (n + 1) z → IsUFormula ℒₒᵣ z →
        (SatPi (n + 2) z e ↔ SatSigma (n + 1) z e) by
      simpa [models_iff, satPiOfSigma] using this
    intro z e hs hf
    exact SatPi.of_sigma hs hf

/-- The `Σ` domain condition holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.75(2)] -/
lemma models_satSigmaDom (n : ℕ) : V↓[ℒₒᵣ] ⊧ satSigmaDom n := by
  suffices ∀ z e : V, SatSigma (n + 1) z e → IsStrictSigma (n + 1) z ∧ IsUFormula ℒₒᵣ z by
    simpa [models_iff, satSigmaDom] using this
  exact fun _ _ h ↦ SatSigma.dom h

/-- The `Π` domain condition holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.75(2)] -/
lemma models_satPiDom (n : ℕ) : V↓[ℒₒᵣ] ⊧ satPiDom n := by
  suffices ∀ z e : V, SatPi (n + 1) z e → IsStrictPi (n + 1) z ∧ IsUFormula ℒₒᵣ z by
    simpa [models_iff, satPiDom] using this
  exact fun _ _ h ↦ SatPi.dom h

/-- The Tarski condition for existential quantification holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.75(2)(v)] -/
lemma models_satSigmaExs (n : ℕ) : V↓[ℒₒᵣ] ⊧ satSigmaExs n := by
  suffices ∀ p z e : V, z = ^∃ p → (SatSigma (n + 1) z e ↔ ∃ x, SatSigma (n + 1) p (x ∷ e)) by
    simpa [models_iff, satSigmaExs] using this
  rintro p _ e rfl
  exact SatSigma.exs_iff

/-- The Tarski condition for universal quantification holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.75(2)(v′)] -/
lemma models_satPiAll (n : ℕ) : V↓[ℒₒᵣ] ⊧ satPiAll n := by
  suffices ∀ p z e : V, z = ^∀ p → (SatPi (n + 1) z e ↔ ∀ x, SatPi (n + 1) p (x ∷ e)) by
    simpa [models_iff, satPiAll] using this
  rintro p _ e rfl
  exact SatPi.all_iff

/-- The negation-duality condition from `Σ` to `Π` holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.75(2)] -/
lemma models_satPiNeg (n : ℕ) : V↓[ℒₒᵣ] ⊧ satPiNeg n := by
  suffices ∀ z nz e : V, IsStrictSigma (n + 1) z → IsUFormula ℒₒᵣ z → nz = neg ℒₒᵣ z →
      (SatPi (n + 1) nz e ↔ ¬SatSigma (n + 1) z e) by
    simpa [models_iff, satPiNeg] using this
  rintro z _ e hs hf rfl
  exact SatPi.neg_iff hs hf

/-- The negation-duality condition from `Π` to `Σ` holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.75(2)] -/
lemma models_satSigmaNeg (n : ℕ) : V↓[ℒₒᵣ] ⊧ satSigmaNeg n := by
  suffices ∀ z nz e : V, IsStrictPi (n + 1) z → IsUFormula ℒₒᵣ z → nz = neg ℒₒᵣ z →
      (SatSigma (n + 1) nz e ↔ ¬SatPi (n + 1) z e) by
    simpa [models_iff, satSigmaNeg] using this
  rintro z _ e hs hf rfl
  exact SatSigma.neg_iff hs hf

/-- Every sentence of the `Δ₀` block holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.70] -/
lemma models_satZeroAxioms {φ : ArithmeticSentence} (h : φ ∈ satZeroAxioms) :
    V↓[ℒₒᵣ] ⊧ φ := by
  simp only [satZeroAxioms, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [models_satZeroDom, models_satZeroVerum, models_satZeroFalsum, models_satZeroEq,
    models_satZeroNeq, models_satZeroLt, models_satZeroNlt, models_satZeroAnd, models_satZeroOr,
    models_satZeroNeg, models_satZeroBall, models_satZeroBex, models_termValBvar,
    models_termValZero, models_termValOne, models_termValAdd, models_termValMul,
    models_adjoinTotal, models_adjoinUnique, models_nthAdjoinZero, models_nthAdjoinSucc,
    models_lenNil, models_lenAdjoin]

/-- Every sentence of the level-`n + 1` block holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.75(2)] -/
lemma models_satSigmaAxioms {n : ℕ} {φ : ArithmeticSentence} (h : φ ∈ satSigmaAxioms n) :
    V↓[ℒₒᵣ] ⊧ φ := by
  simp only [satSigmaAxioms, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [models_satSigmaOfPi n, models_satPiOfSigma n, models_satSigmaDom n, models_satPiDom n,
    models_satSigmaExs n, models_satPiAll n, models_satPiNeg n, models_satSigmaNeg n]

end Tarski

/-- Every sentence of the finite Tarski theory holds in every model of `𝗜𝚺₁`.
- [HP98, Theorem I.1.70]
- [HP98, Theorem I.1.75(2)] -/
lemma models_tarski {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {n : ℕ}
    {φ : ArithmeticSentence} (h : tarski n φ) : V↓[ℒₒᵣ] ⊧ φ := by
  induction h with
  | zero _ _ h => exact Tarski.models_satZeroAxioms h
  | prev _ _ _ ih => exact ih
  | new _ _ h => exact Tarski.models_satSigmaAxioms h

/-- `𝗜𝚺₁` proves every sentence in the finite Tarski theory.
- [HP98, Theorem I.1.70]
- [HP98, Theorem I.1.75(2)]
- [HP98, Remark I.1.77] -/
theorem ISigma1.provable_tarski (n : ℕ) : 𝗜𝚺₁ ⊢* tarski n := fun {_} hφ ↦
  Arithmetic.complete.{0} _ _ fun _ _ _ ↦ models_tarski hφ


/-! ## Reading the sentences in a model of `𝗣𝗔⁻`

A model of `𝗣𝗔⁻` carries none of the coding machinery as functions and predicates: `SatZero`,
`IsDelta0`, `termVal` and the coded vector operations are all defined only under `𝗜𝚺₁`. What such
a model does carry is the formulas themselves, so the sentences of `tarski n` are read here as
statements about their evaluation. Each definition below names one such reading. -/

namespace Reading

variable {V : Type*} [ORingStructure V]

/-- The reading of `satZero`. -/
def Sat0 (z e : V) : Prop := V ⊧/![z, e] satZero.val

/-- The reading of `satSigma m`, which speaks about level `Σₘ₊₁`. -/
def SatSig (m : ℕ) (z e : V) : Prop := V ⊧/![z, e] (satSigma m).val

/-- The reading of `satPi m`, which speaks about level `Πₘ₊₁`. -/
def SatPii (m : ℕ) (z e : V) : Prop := V ⊧/![z, e] (satPi m).val

/-- The reading of the satisfaction formula of level `s` selected by a polarity; the counterpart
of `SatClass` over a model that need not satisfy `𝗜𝚺₁`. -/
def Sat : Polarity → ℕ → V → V → Prop
  | _,       0     => Sat0
  | .sigma, m + 1 => SatSig m
  | .pi,    m + 1 => SatPii m

/-- The reading of `isDelta0`. -/
def Delta0 (z : V) : Prop := V ⊧/![z] isDelta0.val

/-- The reading of `isUFormula`. -/
def UFormula (z : V) : Prop := V ⊧/![z] (isUFormula ℒₒᵣ).val

/-- The reading of `isUTerm`. -/
def UTerm (t : V) : Prop := V ⊧/![t] (isUTerm ℒₒᵣ).val

/-- The reading of `isStrictSigma m`. -/
def StrictSig (m : ℕ) (z : V) : Prop := V ⊧/![z] (isStrictSigma m).val

/-- The reading of `isStrictPi m`. -/
def StrictPii (m : ℕ) (z : V) : Prop := V ⊧/![z] (isStrictPi m).val

/-- The reading of the strict-class recognizer of level `s` selected by a polarity. -/
def Strict : Polarity → ℕ → V → Prop
  | .sigma => StrictSig
  | .pi => StrictPii

/-- The reading of `adjoinDef`: `e'` codes the vector `e` with `x` put in front. -/
def Adjoin (e' x e : V) : Prop := V ⊧/![e', x, e] adjoinDef.val

/-- The reading of `nthDef`. -/
def Nth (y e i : V) : Prop := V ⊧/![y, e, i] nthDef.val

/-- The reading of `lenDef`. -/
def Len (l e : V) : Prop := V ⊧/![l, e] lenDef.val

/-- The reading of `termValGraph`. -/
def TermVal (y e t : V) : Prop := V ⊧/![y, e, t] termValGraph.val

end Reading

namespace Reading

open PeanoMinus

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- `Codes v ev` says that `ev` is a code for the finite sequence `v`: it has length `m` and its
`i`-th entry is `v i`. Over `𝗜𝚺₁` this pins `ev` down to `matrixToVec v`, but no uniqueness is
needed below: every step of the snowing argument only ever moves between a code of `v` and a code
of `x :> v`. -/
def Codes {m : ℕ} (v : Fin m → V) (ev : V) : Prop :=
  Len (m : V) ev ∧ ∀ i : Fin m, Nth (v i) ev (i.val : V)

end Reading

section reading

open Reading

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

open PeanoMinus

/-- A `𝚺₁` fact about standard numbers is inherited by every model of `𝗣𝗔⁻`, by `𝚺₁`-completeness.
This is how every purely syntactic coding fact about the code of a fixed formula is imported into
a model that satisfies no induction.
- [HP98, Theorem I.1.6] -/
lemma sigma_one_cast {m : ℕ} (σ : 𝚺₁.Semisentence m) {u : Fin m → ℕ}
    (h : ℕ ⊧/u σ.val) : V ⊧/(fun i ↦ (u i : V)) σ.val := by
  simpa [Function.comp_def] using sigmaOne_upward_absolute V σ u h

/-- The `𝚫₁` form of `sigma_one_cast`, reading the `𝚺₁` half of the definition.
- [HP98, Theorem I.1.6] -/
lemma delta_one_cast {m : ℕ} (σ : 𝚫₁.Semisentence m) {u : Fin m → ℕ}
    (h : ℕ ⊧/u σ.val) : V ⊧/(fun i ↦ (u i : V)) σ.val := by
  have h' : ℕ ⊧/u σ.sigma.val := by rwa [HierarchySymbol.Semiformula.val_sigma]
  have := sigma_one_cast (V := V) σ.sigma h'
  rwa [HierarchySymbol.Semiformula.val_sigma] at this

/-- `sigma_one_cast` at one argument.
- [HP98, Theorem I.1.6] -/
lemma cast_sigma₁ (σ : 𝚺₁.Semisentence 1) {a : ℕ} (h : ℕ ⊧/![a] σ.val) :
    V ⊧/![(a : V)] σ.val := by
  simpa [Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton] using sigma_one_cast (V := V) σ h

/-- `sigma_one_cast` at two arguments.
- [HP98, Theorem I.1.6] -/
lemma cast_sigma₂ (σ : 𝚺₁.Semisentence 2) {a b : ℕ} (h : ℕ ⊧/![a, b] σ.val) :
    V ⊧/![(a : V), (b : V)] σ.val := by
  simpa [Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton] using sigma_one_cast (V := V) σ h

/-- `sigma_one_cast` at three arguments.
- [HP98, Theorem I.1.6] -/
lemma cast_sigma₃ (σ : 𝚺₁.Semisentence 3) {a b c : ℕ} (h : ℕ ⊧/![a, b, c] σ.val) :
    V ⊧/![(a : V), (b : V), (c : V)] σ.val := by
  simpa [Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton] using sigma_one_cast (V := V) σ h

/-- `delta_one_cast` at one argument.
- [HP98, Theorem I.1.6] -/
lemma cast_delta₁ (σ : 𝚫₁.Semisentence 1) {a : ℕ} (h : ℕ ⊧/![a] σ.val) :
    V ⊧/![(a : V)] σ.val := by
  simpa [Matrix.comp_vecCons', Matrix.empty_eq, Matrix.constant_eq_singleton] using delta_one_cast (V := V) σ h

end reading


/-! ## The theory is monotone in its level -/

/-- A sentence of a lower level of the Tarski theory belongs to every higher level.
- [HP98, Remark I.1.77] -/
lemma tarski_mono {m n : ℕ} (hmn : m ≤ n) {σ : ArithmeticSentence} (h : tarski m σ) :
    tarski n σ := by
  induction n with
  | zero => rwa [Nat.le_zero.mp hmn] at h
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
    · exact h
    · exact tarski.prev n σ (ih (by omega))

/-! ## Reading the sentences in a model of `𝗣𝗔⁻`

Every reading lemma below takes the hypothesis that the sentences of `tarski n` hold in `V`, and
nothing else beyond `𝗣𝗔⁻`; together they are the whole of what the snowing argument may use. -/

section reading

open Reading PeanoMinus

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {n : ℕ}
  (hV : ∀ σ : ArithmeticSentence, tarski n σ → V↓[ℒₒᵣ] ⊧ σ)

include hV

section satZero

/-- The reading of the Tarski sentence for truth.
- [HP98, Theorem I.1.70(ii)] -/
lemma read_satZeroVerum : ∀ z e : V, V ⊧/![z] qqVerumDef.val → Sat0 z e := by
  simpa [models_iff, Tarski.satZeroVerum, Reading.Sat0]
    using hV _ (tarski.zero n Tarski.satZeroVerum (by simp [Tarski.satZeroAxioms]))

/-- The reading of the Tarski sentence for falsehood.
- [HP98, Theorem I.1.70(ii)] -/
lemma read_satZeroFalsum : ∀ z e : V, V ⊧/![z] qqFalsumDef.val → ¬Sat0 z e := by
  simpa [models_iff, Tarski.satZeroFalsum, Reading.Sat0]
    using hV _ (tarski.zero n Tarski.satZeroFalsum (by simp [Tarski.satZeroAxioms]))

/-- The reading of the Tarski sentence for equality.
- [HP98, Theorem I.1.70(ii)] -/
lemma read_satZeroEq : ∀ t u z e vt vu : V, UTerm t → UTerm u →
    V ⊧/![z, t, u] qqEQDef.val → TermVal vt e t → TermVal vu e u → (Sat0 z e ↔ vt = vu) := by
  simpa [models_iff, Tarski.satZeroEq, Reading.Sat0, Reading.UTerm, Reading.TermVal]
    using hV _ (tarski.zero n Tarski.satZeroEq (by simp [Tarski.satZeroAxioms]))

/-- The reading of the Tarski sentence for inequality.
- [HP98, Theorem I.1.70(ii)] -/
lemma read_satZeroNeq : ∀ t u z e vt vu : V, UTerm t → UTerm u →
    V ⊧/![z, t, u] qqNEQDef.val → TermVal vt e t → TermVal vu e u → (Sat0 z e ↔ vt ≠ vu) := by
  simpa [models_iff, Tarski.satZeroNeq, Reading.Sat0, Reading.UTerm, Reading.TermVal]
    using hV _ (tarski.zero n Tarski.satZeroNeq (by simp [Tarski.satZeroAxioms]))

/-- The reading of the Tarski sentence for less-than.
- [HP98, Theorem I.1.70(ii)] -/
lemma read_satZeroLt : ∀ t u z e vt vu : V, UTerm t → UTerm u →
    V ⊧/![z, t, u] qqLTDef.val → TermVal vt e t → TermVal vu e u → (Sat0 z e ↔ vt < vu) := by
  simpa [models_iff, Tarski.satZeroLt, Reading.Sat0, Reading.UTerm, Reading.TermVal]
    using hV _ (tarski.zero n Tarski.satZeroLt (by simp [Tarski.satZeroAxioms]))

/-- The reading of the Tarski sentence for negated less-than.
- [HP98, Theorem I.1.70(ii)] -/
lemma read_satZeroNlt : ∀ t u z e vt vu : V, UTerm t → UTerm u →
    V ⊧/![z, t, u] qqNLTDef.val → TermVal vt e t → TermVal vu e u →
    (Sat0 z e ↔ ¬(vt < vu)) := by
  simpa [models_iff, Tarski.satZeroNlt, Reading.Sat0, Reading.UTerm, Reading.TermVal]
    using hV _ (tarski.zero n Tarski.satZeroNlt (by simp [Tarski.satZeroAxioms]))

/-- The reading of the Tarski sentence for conjunction.
- [HP98, Theorem I.1.70(ii)] -/
lemma read_satZeroAnd : ∀ p q z e : V, V ⊧/![z, p, q] qqAndDef.val →
    (Sat0 z e ↔ Sat0 p e ∧ Sat0 q e) := by
  simpa [models_iff, Tarski.satZeroAnd, Reading.Sat0]
    using hV _ (tarski.zero n Tarski.satZeroAnd (by simp [Tarski.satZeroAxioms]))

/-- The reading of the Tarski sentence for disjunction.
- [HP98, Theorem I.1.70(ii)] -/
lemma read_satZeroOr : ∀ p q z e : V, Delta0 p → UFormula p → Delta0 q → UFormula q →
    V ⊧/![z, p, q] qqOrDef.val → (Sat0 z e ↔ Sat0 p e ∨ Sat0 q e) := by
  simpa [models_iff, Tarski.satZeroOr, Reading.Sat0, Reading.Delta0, Reading.UFormula]
    using hV _ (tarski.zero n Tarski.satZeroOr (by simp [Tarski.satZeroAxioms]))

/-- The reading of the Tarski sentence for bounded universal quantification.
- [HP98, Theorem I.1.70(iv)] -/
lemma read_satZeroBall : ∀ t u q z e v : V, UTerm t → Delta0 q → UFormula q →
    V ⊧/![u, t] (termBShiftGraph ℒₒᵣ).val → V ⊧/![z, u, q] qqBallDef.val → TermVal v e t →
    (Sat0 z e ↔ ∀ x < v, ∀ e', Adjoin e' x e → Sat0 q e') := by
  simpa [models_iff, Tarski.satZeroBall, Reading.Sat0, Reading.UTerm, Reading.Delta0, Reading.UFormula, Reading.TermVal, Reading.Adjoin]
    using hV _ (tarski.zero n Tarski.satZeroBall (by simp [Tarski.satZeroAxioms]))

/-- The reading of the Tarski sentence for bounded existential quantification.
- [HP98, Theorem I.1.70(iv)] -/
lemma read_satZeroBex : ∀ t u q z e v : V, UTerm t →
    V ⊧/![u, t] (termBShiftGraph ℒₒᵣ).val → V ⊧/![z, u, q] qqBexDef.val → TermVal v e t →
    (Sat0 z e ↔ ∃ x < v, ∃ e', Adjoin e' x e ∧ Sat0 q e') := by
  simpa [models_iff, Tarski.satZeroBex, Reading.Sat0, Reading.UTerm, Reading.TermVal, Reading.Adjoin]
    using hV _ (tarski.zero n Tarski.satZeroBex (by simp [Tarski.satZeroAxioms]))

/-- The reading of the defining sentence for coded bound variables.
- [HP98, 1.64(5)] -/
lemma read_termValBvar : ∀ e z t v : V, V ⊧/![t, z] qqBvarDef.val →
    (TermVal v e t ↔ Nth v e z) := by
  simpa [models_iff, Tarski.termValBvar, Reading.TermVal, Reading.Nth]
    using hV _ (tarski.zero n Tarski.termValBvar (by simp [Tarski.satZeroAxioms]))

/-- The reading of the defining sentence for the coded zero term.
- [HP98, 1.64(5)] -/
lemma read_termValZero : ∀ e v : V, TermVal v e ((𝟎 : ℕ) : V) ↔ v = 0 := by
  simpa [models_iff, Tarski.termValZero, Reading.TermVal, numeral_eq_natCast]
    using hV _ (tarski.zero n Tarski.termValZero (by simp [Tarski.satZeroAxioms]))

/-- The reading of the defining sentence for the coded one term.
- [HP98, 1.64(5)] -/
lemma read_termValOne : ∀ e v : V, TermVal v e ((𝟏 : ℕ) : V) ↔ v = 1 := by
  simpa [models_iff, Tarski.termValOne, Reading.TermVal, numeral_eq_natCast]
    using hV _ (tarski.zero n Tarski.termValOne (by simp [Tarski.satZeroAxioms]))

/-- The reading of the defining sentence for coded addition.
- [HP98, 1.64(5)] -/
lemma read_termValAdd : ∀ e t u s vt vu v : V, UTerm t → UTerm u →
    V ⊧/![s, t, u] Arithmetic.qqAddGraph.val → TermVal vt e t → TermVal vu e u →
    (TermVal v e s ↔ v = vt + vu) := by
  simpa [models_iff, Tarski.termValAdd, Reading.TermVal, Reading.UTerm]
    using hV _ (tarski.zero n Tarski.termValAdd (by simp [Tarski.satZeroAxioms]))

/-- The reading of the defining sentence for coded multiplication.
- [HP98, 1.64(5)] -/
lemma read_termValMul : ∀ e t u s vt vu v : V, UTerm t → UTerm u →
    V ⊧/![s, t, u] Arithmetic.qqMulGraph.val → TermVal vt e t → TermVal vu e u →
    (TermVal v e s ↔ v = vt * vu) := by
  simpa [models_iff, Tarski.termValMul, Reading.TermVal, Reading.UTerm]
    using hV _ (tarski.zero n Tarski.termValMul (by simp [Tarski.satZeroAxioms]))

/-- The reading of totality of coded adjunction.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
lemma read_adjoinTotal : ∀ x v : V, ∃ e, Adjoin e x v := by
  simpa [models_iff, Tarski.adjoinTotal, Reading.Adjoin]
    using hV _ (tarski.zero n Tarski.adjoinTotal (by simp [Tarski.satZeroAxioms]))

/-- The reading of the head equation of coded adjunction.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
lemma read_nthAdjoinZero : ∀ x v e y : V, Adjoin e x v → (Nth y e 0 ↔ y = x) := by
  simpa [models_iff, Tarski.nthAdjoinZero, Reading.Adjoin, Reading.Nth]
    using hV _ (tarski.zero n Tarski.nthAdjoinZero (by simp [Tarski.satZeroAxioms]))

/-- The reading of the tail equation of coded adjunction.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
lemma read_nthAdjoinSucc : ∀ x v e i y : V, Adjoin e x v → (Nth y e (i + 1) ↔ Nth y v i) := by
  simpa [models_iff, Tarski.nthAdjoinSucc, Reading.Adjoin, Reading.Nth]
    using hV _ (tarski.zero n Tarski.nthAdjoinSucc (by simp [Tarski.satZeroAxioms]))

/-- The reading of the length of the empty coded vector.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
lemma read_lenNil : ∀ l : V, Len l 0 ↔ l = 0 := by
  simpa [models_iff, Tarski.lenNil, Reading.Len]
    using hV _ (tarski.zero n Tarski.lenNil (by simp [Tarski.satZeroAxioms]))

/-- The reading of the length equation of coded adjunction.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
lemma read_lenAdjoin : ∀ x v e l : V, Adjoin e x v → (Len (l + 1) e ↔ Len l v) := by
  simpa [models_iff, Tarski.lenAdjoin, Reading.Adjoin, Reading.Len]
    using hV _ (tarski.zero n Tarski.lenAdjoin (by simp [Tarski.satZeroAxioms]))

end satZero

section satSigma

variable {m : ℕ} (hm : m ≤ n)

include hm

/-- The reading of the empty-block condition from `Π` to `Σ`.
- [HP98, Theorem I.1.75(2)(v)] -/
lemma read_satSigmaOfPi : ∀ z e : V, Strict 𝚷 m z → Reading.UFormula z →
    (Reading.SatSig m z e ↔ Sat 𝚷 m z e) := by
  have h := hV _ (tarski_mono hm (tarski.new m (Tarski.satSigmaOfPi m)
    (by simp [Tarski.satSigmaAxioms])))
  cases m with
  | zero =>
    simpa [models_iff, Tarski.satSigmaOfPi, Reading.Sat, Reading.Strict, Reading.SatSig,
      Reading.StrictPii, Reading.Sat0, Reading.UFormula, isStrictPi] using h
  | succ m =>
    simpa [models_iff, Tarski.satSigmaOfPi, Reading.Sat, Reading.Strict, Reading.SatSig,
      Reading.StrictPii, Reading.SatPii, Reading.UFormula] using h

/-- The reading of the empty-block condition from `Σ` to `Π`.
- [HP98, Theorem I.1.75(2)(v′)] -/
lemma read_satPiOfSigma : ∀ z e : V, Strict 𝚺 m z → Reading.UFormula z →
    (Reading.SatPii m z e ↔ Sat 𝚺 m z e) := by
  have h := hV _ (tarski_mono hm (tarski.new m (Tarski.satPiOfSigma m)
    (by simp [Tarski.satSigmaAxioms])))
  cases m with
  | zero =>
    simpa [models_iff, Tarski.satPiOfSigma, Reading.Sat, Reading.Strict, Reading.SatPii,
      Reading.StrictSig, Reading.Sat0, Reading.UFormula, isStrictSigma] using h
  | succ m =>
    simpa [models_iff, Tarski.satPiOfSigma, Reading.Sat, Reading.Strict, Reading.SatPii,
      Reading.StrictSig, Reading.SatSig, Reading.UFormula] using h

/-- The reading of the empty-block condition, in the polarity-indexed form used by the induction
on a strict prenex derivation.
- [HP98, Theorem I.1.75(2)(v)]
- [HP98, Theorem I.1.75(2)(v′)] -/
lemma read_ofAlt (Γ : Polarity) : ∀ z e : V, Strict Γ.alt m z → Reading.UFormula z →
    (Sat Γ (m + 1) z e ↔ Sat Γ.alt m z e) := by
  rcases Γ with _ | _
  · exact read_satSigmaOfPi hV hm
  · exact read_satPiOfSigma hV hm

/-- The reading of the Tarski condition for existential quantification.
- [HP98, Theorem I.1.75(2)(v)] -/
lemma read_satSigmaExs : ∀ p z e : V, V ⊧/![z, p] qqExsDef.val →
    (SatSig m z e ↔ ∃ x e', Adjoin e' x e ∧ SatSig m p e') := by
  simpa [models_iff, Tarski.satSigmaExs, Reading.SatSig, Reading.Adjoin]
    using hV _ (tarski_mono hm (tarski.new m (Tarski.satSigmaExs m) (by simp [Tarski.satSigmaAxioms])))

/-- The reading of the Tarski condition for universal quantification.
- [HP98, Theorem I.1.75(2)(v′)] -/
lemma read_satPiAll : ∀ p z e : V, V ⊧/![z, p] qqAllDef.val →
    (SatPii m z e ↔ ∀ x e', Adjoin e' x e → SatPii m p e') := by
  simpa [models_iff, Tarski.satPiAll, Reading.SatPii, Reading.Adjoin]
    using hV _ (tarski_mono hm (tarski.new m (Tarski.satPiAll m) (by simp [Tarski.satSigmaAxioms])))

end satSigma

end reading


/-! ## Codes of finite sequences

The vector sentences of `tarski n` say just enough about `adjoinDef`, `lenDef` and `nthDef` to
build a code for any finite sequence of the model and to extend one by a new first entry. -/

section codes

open Reading PeanoMinus

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {n : ℕ}
  (hV : ∀ σ : ArithmeticSentence, tarski n σ → V↓[ℒₒᵣ] ⊧ σ)

include hV

/-- The empty sequence is coded by `0`.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
lemma codes_nil (v : Fin 0 → V) : Codes v 0 :=
  ⟨by simpa using (read_lenNil hV 0).mpr rfl, fun i ↦ i.elim0⟩

/-- Adjoining a new first entry to a code of `v` gives a code of `x :> v`.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
lemma codes_cons {m : ℕ} {v : Fin m → V} {ev ev' x : V} (h : Codes v ev)
    (hadj : Adjoin ev' x ev) : Codes (x :> v) ev' := by
  refine ⟨?_, fun i ↦ ?_⟩
  · have := (read_lenAdjoin hV x ev ev' (m : V) hadj).mpr h.1
    simpa using this
  · refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa using (read_nthAdjoinZero hV x ev ev' x hadj).mpr rfl
    · have := (read_nthAdjoinSucc hV x ev ev' (j.val : V) (v j) hadj).mpr (h.2 j)
      simpa using this

/-- Every finite sequence of the model has a code.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
lemma exists_codes : ∀ {m : ℕ} (v : Fin m → V), ∃ ev, Codes v ev := by
  intro m
  induction m with
  | zero => exact fun v ↦ ⟨0, codes_nil hV v⟩
  | succ m ih =>
    intro v
    obtain ⟨ev, hev⟩ := ih (fun i ↦ v i.succ)
    obtain ⟨ev', hadj⟩ := read_adjoinTotal hV (v 0) ev
    have hcons : (v 0 :> fun i ↦ v i.succ) = v := by
      funext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
    exact ⟨ev', hcons ▸ codes_cons hV hev hadj⟩

end codes

end LO.FirstOrder.Arithmetic
