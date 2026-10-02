module

public import AlphaCentauri.Bootstrapping.Proof.ReadableSoundness
public import Foundation.FirstOrder.Incompleteness.Definability

/-!
# The axioms of $\mathsf{PA}^-$ as false blocks

In a model of $\mathsf{I}\Sigma_1$, the negation of the code of each axiom of $\mathsf{PA}^-$ is a
block of existential quantifiers over a $\Delta_0$ matrix all of whose instances are false.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section membership

lemma satisfies_ofList_ch (l : List ArithmeticSentence) (p : V) :
    V ⊧/![p] (Theory.Δ₁.ofList l).ch.val ↔ ∃ σ ∈ l, p = (⌜σ⌝ : V) := by
  induction l with
  | nil =>
    change V ⊧/![p] (⊥ : 𝚫ᴬ₁.Semisentence 1).val ↔ _
    simp
  | cons φ l ih =>
    change V ⊧/![p] (Theory.Δ₁.ch ({φ} : Theory ℒₒᵣ) ⋎ (Theory.Δ₁.ofList l).ch).val ↔ _
    simp only [Bounding.HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or,
      Theory.Δ₁.singleton_toTDef_ch_val, ih]
    simp [Sentence.quote_eq_encode, numeral_eq_natCast]

lemma mem_peanoMinus_Δ₁Class_iff (p : V) :
    p ∈ (𝗣𝗔⁻ : ArithmeticTheory).Δ₁Class ↔ ∃ σ ∈ 𝗣𝗔⁻, p = (⌜σ⌝ : V) := by
  change V ⊧/![p] (Theory.Δ₁.ofList PeanoMinus.finite.toFinset.toList).ch.val ↔ _
  rw [satisfies_ofList_ch]
  simp

end membership

section quote

lemma quote_neg_sentence {n : ℕ} (σ : ArithmeticSemisentence n) :
    (⌜∼σ⌝ : V) = neg ℒₒᵣ (⌜σ⌝ : V) := by
  simp [Sentence.quote_eq, Sentence.typed_quote_def]

lemma quote_allClosure_sentence {m : ℕ} (θ : ArithmeticSemisentence m) :
    (⌜∀¹* θ⌝ : V) = qqAlls (⌜θ⌝ : V) (m : V) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show (∀¹* θ : ArithmeticSentence) = ∀¹* (∀¹ θ) from rfl]
    simpa [Sentence.quote_all, qqAlls_all] using ih (∀¹ θ)

lemma quote_neg_ne_exs {m : ℕ} {θ : ArithmeticSemisentence m} (h : ∀ ψ, θ ≠ ∀¹ ψ) (p : V) :
    (⌜∼θ⌝ : V) ≠ ^∃ p := by
  induction θ using Semiformula.rec' <;> first
    | exact absurd rfl (h _)
    | simp [Sentence.quote_def, qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

end quote

section falseBlock

/-- The negation of the code of a universal closure of a $\Delta_0$ formula that is true in `V`
is a block of existential quantifiers whose instances are all false. -/
lemma isFalseBlock_neg_quote_allClosure {k D m : ℕ} {θ : ArithmeticSemisentence m}
    (hθ : ℬ[<, ℒₒᵣ].Closure θ) (hn : ∀ ψ, θ ≠ ∀¹ ψ)
    (hσ : V↓[ℒₒᵣ] ⊧ (∀¹* θ : ArithmeticSentence)) :
    IsFalseBlock k D (neg ℒₒᵣ (⌜∀¹* θ⌝ : V)) := by
  have hb : IsBounded (⌜∼θ⌝ : V) := (isBounded_quote_iff _).mpr hθ.neg
  refine ⟨m, ⌜∼θ⌝, ?_, ?_, ?_, quote_neg_ne_exs hn, ?_, ?_⟩
  · rw [quote_allClosure_sentence, neg_qqAlls (Sentence.quote_isUFormula θ), quote_neg_sentence]
  · exact Sentence.quote_isSemiformula _
  · exact shift_quote _
  · exact .of_isPrenexAtom (IsPrenexAtMost.of_isBounded hb).isPrenexAtom
  · intro w hw
    have := ReadableTruth.subst_quote_iff (V := V) (k := k) (D := D) (Γ := 𝚺) (s := 0)
      (.of_le (Nat.zero_le k)) ⟨⟨∼θ, hθ.neg⟩⟩ hw
    have e : ((⟨⟨∼θ, hθ.neg⟩⟩ : ℬ[<, ℒₒᵣ].Prenex 𝚺 0 Empty m) : ArithmeticSemisentence m) = ∼θ :=
      rfl
    rw [e] at this
    rw [this]
    simp only [models_iff, Semiformula.eval_allClosure] at hσ
    simpa using hσ _

end falseBlock

section classification

lemma exists_allClosure_closure_of_peanoMinus {σ : ArithmeticSentence} (h : σ ∈ 𝗣𝗔⁻) :
    ∃ m, ∃ θ : ArithmeticSemisentence m, σ = ∀¹* θ ∧ ℬ[<, ℒₒᵣ].Closure θ ∧ ∀ ψ, θ ≠ ∀¹ ψ := by
  rcases h with ⟨φ, hφ⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  · rcases hφ with _ | _ | _ | @⟨k, f⟩ | @⟨k, r⟩
    all_goals
      first
      | refine ⟨k + k, _, rfl, ?_, ?_⟩
      | refine ⟨3, _, rfl, ?_, ?_⟩
      | refine ⟨2, _, rfl, ?_, ?_⟩
      | refine ⟨1, _, rfl, ?_, ?_⟩
    all_goals first
      | (rw [← Bounding.Hierarchy.zero_iff_bounded (Γ := 𝚺)]
         simp [Semiformula.Operator.operator, Semiformula.Operator.Eq.eq])
      | (intro ψ h; cases h)
  all_goals
    first
    | refine ⟨3, _, rfl, ?_, ?_⟩
    | refine ⟨2, _, rfl, ?_, ?_⟩
    | refine ⟨1, _, rfl, ?_, ?_⟩
    | refine ⟨0, _, rfl, ?_, ?_⟩
  all_goals first
    | (rw [← Bounding.Hierarchy.zero_iff_bounded (Γ := 𝚺)]
       simp [Semiformula.Operator.operator, Semiformula.Operator.Eq.eq,
         Semiformula.Operator.LT.lt, Semiformula.Operator.LE.sentence_eq])
    | (intro ψ h; cases h)

end classification

section peanoMinus

lemma isFalseBlock_neg_quote_of_mem_peanoMinus {σ : ArithmeticSentence} (h : σ ∈ 𝗣𝗔⁻) (k D : ℕ) :
    IsFalseBlock k D (neg ℒₒᵣ (⌜σ⌝ : V)) := by
  obtain ⟨m, θ, rfl, hθ, hn⟩ := exists_allClosure_closure_of_peanoMinus h
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (s := 1)
  exact isFalseBlock_neg_quote_allClosure hθ hn (Semantics.ModelsSet.models _ h)

lemma isFalseBlock_neg_of_mem_peanoMinus_Δ₁Class {p : V}
    (hp : p ∈ (𝗣𝗔⁻ : ArithmeticTheory).Δ₁Class) (k D : ℕ) : IsFalseBlock k D (neg ℒₒᵣ p) := by
  obtain ⟨σ, hσ, rfl⟩ := (mem_peanoMinus_Δ₁Class_iff p).mp hp
  exact isFalseBlock_neg_quote_of_mem_peanoMinus hσ k D

lemma derivable_of_mem_peanoMinus_Δ₁Class {p : V} (hp : p ∈ (𝗣𝗔⁻ : ArithmeticTheory).Δ₁Class) :
    Derivable (∅ : Theory ℒₒᵣ) (insert (neg ℒₒᵣ p) ({p} : V)) := by
  obtain ⟨σ, -, rfl⟩ := (mem_peanoMinus_Δ₁Class_iff p).mp hp
  have hf : IsFormula ℒₒᵣ (⌜σ⌝ : V) := Sentence.quote_isSemiformula₀ σ
  exact Derivable.em (by simp [hf]) (⌜σ⌝ : V) (by simp) (by simp)

end peanoMinus

end FFL.FirstOrder.Arithmetic.Bootstrapping
