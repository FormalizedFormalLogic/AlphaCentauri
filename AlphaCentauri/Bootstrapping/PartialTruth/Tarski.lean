module

public import AlphaCentauri.Bootstrapping.PartialTruth.SatSigma
public import AlphaCentauri.Vorspiel.Hierarchy

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
  “∀ e v, !termValGraph.val v e ↑Arithmetic.zero ↔ v = 0”

/-- The defining sentence for evaluation of one.
- [HP98, 1.64(5)] -/
noncomputable def termValOne : ArithmeticSentence :=
  “∀ e v, !termValGraph.val v e ↑Arithmetic.one ↔ v = 1”

/-- The defining sentence for evaluation of addition.
- [HP98, 1.64(5)] -/
noncomputable def termValAdd : ArithmeticSentence :=
  “∀ e t u s vt vu v, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !Arithmetic.qqAddGraph.val s t u → !termValGraph.val vt e t →
    !termValGraph.val vu e u →
    (!termValGraph.val v e s ↔ v = vt + vu)”

/-- The defining sentence for evaluation of multiplication.
- [HP98, 1.64(5)] -/
noncomputable def termValMul : ArithmeticSentence :=
  “∀ e t u s vt vu v, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !Arithmetic.qqMulGraph.val s t u → !termValGraph.val vt e t →
    !termValGraph.val vu e u →
    (!termValGraph.val v e s ↔ v = vt * vu)”

noncomputable def adjoinTotal : ArithmeticSentence :=
  “∀ x v, ∃ e, !adjoinDef.val e x v”

noncomputable def adjoinUnique : ArithmeticSentence :=
  “∀ x v e e', !adjoinDef.val e x v → !adjoinDef.val e' x v → e = e'”

noncomputable def nthAdjoinZero : ArithmeticSentence :=
  “∀ x v e y, !adjoinDef.val e x v → (!nthDef.val y e 0 ↔ y = x)”

noncomputable def nthAdjoinSucc : ArithmeticSentence :=
  “∀ x v e i y, !adjoinDef.val e x v →
    (!nthDef.val y e (i + 1) ↔ !nthDef.val y v i)”

noncomputable def lenNil : ArithmeticSentence := “∀ l, !lenDef.val l 0 ↔ l = 0”

noncomputable def lenAdjoin : ArithmeticSentence :=
  “∀ x v e l, !adjoinDef.val e x v → (!lenDef.val (l + 1) e ↔ !lenDef.val l v)”

/-- The empty-block Tarski condition for reading `𝚷-[n]` satisfaction as `𝚺-[n + 1]` satisfaction.
- [HP98, Theorem I.1.75(2)(v)] -/
noncomputable def satSigmaOfPi : ℕ → ArithmeticSentence
  | 0 =>
      “∀ z e, !isDelta0.val z → !(isUFormula ℒₒᵣ).val z →
        (!(satSigma 0).val z e ↔ !satZero.val z e)”
  | n + 1 =>
      “∀ z e, !(isStrictPi (n + 1)).val z → !(isUFormula ℒₒᵣ).val z →
        (!(satSigma (n + 1)).val z e ↔ !(satPi n).val z e)”

/-- The empty-block Tarski condition for reading `𝚺-[n]` satisfaction as `𝚷-[n + 1]` satisfaction.
- [HP98, Theorem I.1.75(2)(v′)] -/
noncomputable def satPiOfSigma : ℕ → ArithmeticSentence
  | 0 =>
      “∀ z e, !isDelta0.val z → !(isUFormula ℒₒᵣ).val z →
        (!(satPi 0).val z e ↔ !satZero.val z e)”
  | n + 1 =>
      “∀ z e, !(isStrictSigma (n + 1)).val z → !(isUFormula ℒₒᵣ).val z →
        (!(satPi (n + 1)).val z e ↔ !(satSigma n).val z e)”

/-- The domain Tarski condition for `𝚺-[n + 1]` satisfaction.
- [HP98, Theorem I.1.75(2)] -/
noncomputable def satSigmaDom (n : ℕ) : ArithmeticSentence :=
  “∀ z e, !(satSigma n).val z e →
    !(isStrictSigma (n + 1)).val z ∧ !(isUFormula ℒₒᵣ).val z”

/-- The domain Tarski condition for `𝚷-[n + 1]` satisfaction.
- [HP98, Theorem I.1.75(2)] -/
noncomputable def satPiDom (n : ℕ) : ArithmeticSentence :=
  “∀ z e, !(satPi n).val z e →
    !(isStrictPi (n + 1)).val z ∧ !(isUFormula ℒₒᵣ).val z”

/-- The Tarski condition for existential quantification at level `𝚺-[n + 1]`.
- [HP98, Theorem I.1.75(2)(v)] -/
noncomputable def satSigmaExs (n : ℕ) : ArithmeticSentence :=
  “∀ p z e, !qqExsDef.val z p →
    (!(satSigma n).val z e ↔
      ∃ x e', !adjoinDef.val e' x e ∧ !(satSigma n).val p e')”

/-- The Tarski condition for universal quantification at level `𝚷-[n + 1]`.
- [HP98, Theorem I.1.75(2)(v′)] -/
noncomputable def satPiAll (n : ℕ) : ArithmeticSentence :=
  “∀ p z e, !qqAllDef.val z p →
    (!(satPi n).val z e ↔
      ∀ x e', !adjoinDef.val e' x e → !(satPi n).val p e')”

/-- The negation-duality Tarski condition from `𝚺-[n + 1]` to `𝚷-[n + 1]`.
- [HP98, Theorem I.1.75(2)] -/
noncomputable def satPiNeg (n : ℕ) : ArithmeticSentence :=
  “∀ z nz e, !(isStrictSigma (n + 1)).val z → !(isUFormula ℒₒᵣ).val z →
    !(negGraph ℒₒᵣ).val nz z →
    (!(satPi n).val nz e ↔ ¬!(satSigma n).val z e)”

/-- The negation-duality Tarski condition from `𝚷-[n + 1]` to `𝚺-[n + 1]`.
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

/-- `tarski n` contains the Tarski, vector, and term-evaluation conditions through level `n + 1`.
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

/-! ## The level of the Tarski conditions in the arithmetical hierarchy -/

namespace Tarski

section Hierarchy

variable {s m : ℕ}

/-! Each Tarski sentence is a universal closure of a Boolean combination of formulas of level at
most `𝚺-[m + 1]`, so `Hierarchy.iff_iff` splits the biconditionals and `Hierarchy.dummy_sigma`,
`Hierarchy.dummy_pi` absorb the quantifier blocks that raise the level by one. -/
attribute [local simp] Hierarchy.iff_iff Hierarchy.dummy_sigma Hierarchy.dummy_pi

@[simp] lemma hierarchy_satZeroDom : Hierarchy 𝚷 (s + 3) satZeroDom := by simp [satZeroDom]

@[simp] lemma hierarchy_satZeroVerum : Hierarchy 𝚷 (s + 3) satZeroVerum := by simp [satZeroVerum]

@[simp] lemma hierarchy_satZeroFalsum : Hierarchy 𝚷 (s + 3) satZeroFalsum := by
  simp [satZeroFalsum]

@[simp] lemma hierarchy_satZeroEq : Hierarchy 𝚷 (s + 3) satZeroEq := by simp [satZeroEq]

@[simp] lemma hierarchy_satZeroNeq : Hierarchy 𝚷 (s + 3) satZeroNeq := by simp [satZeroNeq]

@[simp] lemma hierarchy_satZeroLt : Hierarchy 𝚷 (s + 3) satZeroLt := by simp [satZeroLt]

@[simp] lemma hierarchy_satZeroNlt : Hierarchy 𝚷 (s + 3) satZeroNlt := by simp [satZeroNlt]

@[simp] lemma hierarchy_satZeroAnd : Hierarchy 𝚷 (s + 3) satZeroAnd := by simp [satZeroAnd]

@[simp] lemma hierarchy_satZeroOr : Hierarchy 𝚷 (s + 3) satZeroOr := by simp [satZeroOr]

@[simp] lemma hierarchy_satZeroNeg : Hierarchy 𝚷 (s + 3) satZeroNeg := by simp [satZeroNeg]

@[simp] lemma hierarchy_satZeroBall : Hierarchy 𝚷 (s + 3) satZeroBall := by simp [satZeroBall]

@[simp] lemma hierarchy_satZeroBex : Hierarchy 𝚷 (s + 3) satZeroBex := by simp [satZeroBex]

@[simp] lemma hierarchy_termValBvar : Hierarchy 𝚷 (s + 3) termValBvar := by simp [termValBvar]

@[simp] lemma hierarchy_termValZero : Hierarchy 𝚷 (s + 3) termValZero := by simp [termValZero]

@[simp] lemma hierarchy_termValOne : Hierarchy 𝚷 (s + 3) termValOne := by simp [termValOne]

@[simp] lemma hierarchy_termValAdd : Hierarchy 𝚷 (s + 3) termValAdd := by simp [termValAdd]

@[simp] lemma hierarchy_termValMul : Hierarchy 𝚷 (s + 3) termValMul := by simp [termValMul]

@[simp] lemma hierarchy_adjoinTotal : Hierarchy 𝚷 (s + 3) adjoinTotal := by simp [adjoinTotal]

@[simp] lemma hierarchy_adjoinUnique : Hierarchy 𝚷 (s + 3) adjoinUnique := by simp [adjoinUnique]

@[simp] lemma hierarchy_nthAdjoinZero : Hierarchy 𝚷 (s + 3) nthAdjoinZero := by
  simp [nthAdjoinZero]

@[simp] lemma hierarchy_nthAdjoinSucc : Hierarchy 𝚷 (s + 3) nthAdjoinSucc := by
  simp [nthAdjoinSucc]

@[simp] lemma hierarchy_lenNil : Hierarchy 𝚷 (s + 3) lenNil := by simp [lenNil]

@[simp] lemma hierarchy_lenAdjoin : Hierarchy 𝚷 (s + 3) lenAdjoin := by simp [lenAdjoin]

@[simp] lemma hierarchy_satSigmaOfPi : Hierarchy 𝚷 (m + 2) (satSigmaOfPi m) := by
  cases m <;> simp [satSigmaOfPi]

@[simp] lemma hierarchy_satPiOfSigma : Hierarchy 𝚷 (m + 2) (satPiOfSigma m) := by
  cases m <;> simp [satPiOfSigma]

@[simp] lemma hierarchy_satSigmaDom : Hierarchy 𝚷 (m + 2) (satSigmaDom m) := by simp [satSigmaDom]

@[simp] lemma hierarchy_satPiDom : Hierarchy 𝚷 (m + 2) (satPiDom m) := by simp [satPiDom]

@[simp] lemma hierarchy_satSigmaExs : Hierarchy 𝚷 (m + 2) (satSigmaExs m) := by simp [satSigmaExs]

@[simp] lemma hierarchy_satPiAll : Hierarchy 𝚷 (m + 2) (satPiAll m) := by simp [satPiAll]

@[simp] lemma hierarchy_satPiNeg : Hierarchy 𝚷 (m + 2) (satPiNeg m) := by simp [satPiNeg]

@[simp] lemma hierarchy_satSigmaNeg : Hierarchy 𝚷 (m + 2) (satSigmaNeg m) := by simp [satSigmaNeg]

lemma hierarchy_of_mem_satZeroAxioms {σ : ArithmeticSentence} (hσ : σ ∈ satZeroAxioms) :
    Hierarchy 𝚷 (s + 3) σ := by
  simp only [satZeroAxioms, Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma hierarchy_of_mem_satSigmaAxioms {σ : ArithmeticSentence} (hσ : σ ∈ satSigmaAxioms m) :
    Hierarchy 𝚷 (m + 2) σ := by
  simp only [satSigmaAxioms, Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end Hierarchy

end Tarski

/-- Every sentence of the finite Tarski theory at level `n` is `𝚷-[n + 3]`.
- [HP98, Remark I.1.77] -/
lemma hierarchy_of_tarski {n : ℕ} {σ : ArithmeticSentence} (hσ : tarski n σ) :
    Hierarchy 𝚷 (n + 3) σ := by
  induction hσ with
  | zero n φ hφ => exact Tarski.hierarchy_of_mem_satZeroAxioms hφ
  | prev n φ _ ih => exact ih.mono (by omega)
  | new n φ hφ => exact (Tarski.hierarchy_of_mem_satSigmaAxioms hφ).mono (by omega)

/-! ## `𝗜𝚺₁` proves the Tarski conditions -/

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

lemma models_adjoinTotal : V↓[ℒₒᵣ] ⊧ adjoinTotal := by
  simp [models_iff, adjoinTotal]

lemma models_adjoinUnique : V↓[ℒₒᵣ] ⊧ adjoinUnique := by
  simp [models_iff, adjoinUnique]

lemma models_nthAdjoinZero : V↓[ℒₒᵣ] ⊧ nthAdjoinZero := by
  suffices ∀ x v e y : V, e = x ∷ v → (y = e.[0] ↔ y = x) by
    simpa [models_iff, nthAdjoinZero] using this
  rintro x v _ y rfl
  simp

lemma models_nthAdjoinSucc : V↓[ℒₒᵣ] ⊧ nthAdjoinSucc := by
  suffices ∀ x v e i y : V, e = x ∷ v → (y = e.[i + 1] ↔ y = v.[i]) by
    simpa [models_iff, nthAdjoinSucc] using this
  rintro x v _ i y rfl
  simp

lemma models_lenNil : V↓[ℒₒᵣ] ⊧ lenNil := by
  simp [models_iff, lenNil]

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

/-! ## Reading the sentences in a model of `𝗣𝗔⁻` -/

namespace Reading

variable {V : Type*} [ORingStructure V]

/-- The reading of `satZero`. -/
def Sat0 (z e : V) : Prop := V ⊧/![z, e] satZero.val

/-- The reading of `satSigma m`, which speaks about level `𝚺-[m + 1]`. -/
def SatSigma (m : ℕ) (z e : V) : Prop := V ⊧/![z, e] (satSigma m).val

/-- The reading of `satPi m`, which speaks about level `𝚷-[m + 1]`. -/
def SatPi (m : ℕ) (z e : V) : Prop := V ⊧/![z, e] (satPi m).val

/-- The reading of the satisfaction formula of level `s` selected by a polarity. -/
def Sat : Polarity → ℕ → V → V → Prop
  | _,       0     => Sat0
  | .sigma, m + 1 => Reading.SatSigma m
  | .pi,    m + 1 => Reading.SatPi m

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

/-! ## Reading the sentences in a model of `𝗣𝗔⁻` -/

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

lemma read_adjoinTotal : ∀ x v : V, ∃ e, Adjoin e x v := by
  simpa [models_iff, Tarski.adjoinTotal, Reading.Adjoin]
    using hV _ (tarski.zero n Tarski.adjoinTotal (by simp [Tarski.satZeroAxioms]))

lemma read_nthAdjoinZero : ∀ x v e y : V, Adjoin e x v → (Nth y e 0 ↔ y = x) := by
  simpa [models_iff, Tarski.nthAdjoinZero, Reading.Adjoin, Reading.Nth]
    using hV _ (tarski.zero n Tarski.nthAdjoinZero (by simp [Tarski.satZeroAxioms]))

lemma read_nthAdjoinSucc : ∀ x v e i y : V, Adjoin e x v → (Nth y e (i + 1) ↔ Nth y v i) := by
  simpa [models_iff, Tarski.nthAdjoinSucc, Reading.Adjoin, Reading.Nth]
    using hV _ (tarski.zero n Tarski.nthAdjoinSucc (by simp [Tarski.satZeroAxioms]))

lemma read_lenNil : ∀ l : V, Len l 0 ↔ l = 0 := by
  simpa [models_iff, Tarski.lenNil, Reading.Len]
    using hV _ (tarski.zero n Tarski.lenNil (by simp [Tarski.satZeroAxioms]))

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
    (Reading.SatSigma m z e ↔ Sat 𝚷 m z e) := by
  have h := hV _ (tarski_mono hm (tarski.new m (Tarski.satSigmaOfPi m)
    (by simp [Tarski.satSigmaAxioms])))
  cases m with
  | zero =>
    simpa [models_iff, Tarski.satSigmaOfPi, Reading.Sat, Reading.Strict, Reading.SatSigma,
      Reading.StrictPii, Reading.Sat0, Reading.UFormula, isStrictPi] using h
  | succ m =>
    simpa [models_iff, Tarski.satSigmaOfPi, Reading.Sat, Reading.Strict, Reading.SatSigma,
      Reading.StrictPii, Reading.SatPi, Reading.UFormula] using h

/-- The reading of the empty-block condition from `Σ` to `Π`.
- [HP98, Theorem I.1.75(2)(v′)] -/
lemma read_satPiOfSigma : ∀ z e : V, Strict 𝚺 m z → Reading.UFormula z →
    (Reading.SatPi m z e ↔ Sat 𝚺 m z e) := by
  have h := hV _ (tarski_mono hm (tarski.new m (Tarski.satPiOfSigma m)
    (by simp [Tarski.satSigmaAxioms])))
  cases m with
  | zero =>
    simpa [models_iff, Tarski.satPiOfSigma, Reading.Sat, Reading.Strict, Reading.SatPi,
      Reading.StrictSig, Reading.Sat0, Reading.UFormula, isStrictSigma] using h
  | succ m =>
    simpa [models_iff, Tarski.satPiOfSigma, Reading.Sat, Reading.Strict, Reading.SatPi,
      Reading.StrictSig, Reading.SatSigma, Reading.UFormula] using h

/-- The reading of the empty-block condition, in the polarity-indexed form.
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
    (Reading.SatSigma m z e ↔ ∃ x e', Adjoin e' x e ∧ Reading.SatSigma m p e') := by
  simpa [models_iff, Tarski.satSigmaExs, Reading.SatSigma, Reading.Adjoin]
    using hV _ (tarski_mono hm (tarski.new m (Tarski.satSigmaExs m) (by simp [Tarski.satSigmaAxioms])))

/-- The reading of the Tarski condition for universal quantification.
- [HP98, Theorem I.1.75(2)(v′)] -/
lemma read_satPiAll : ∀ p z e : V, V ⊧/![z, p] qqAllDef.val →
    (Reading.SatPi m z e ↔ ∀ x e', Adjoin e' x e → Reading.SatPi m p e') := by
  simpa [models_iff, Tarski.satPiAll, Reading.SatPi, Reading.Adjoin]
    using hV _ (tarski_mono hm (tarski.new m (Tarski.satPiAll m) (by simp [Tarski.satSigmaAxioms])))

end satSigma

end reading

end LO.FirstOrder.Arithmetic
