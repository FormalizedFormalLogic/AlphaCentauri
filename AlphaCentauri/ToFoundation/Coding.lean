module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

/-!
# Codes of sentences and of closed arithmetic terms
-/

@[expose] public section

namespace FFL.FirstOrder.Semisentence

open Arithmetic Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] lemma shift_quote {n : ℕ} (σ : ArithmeticSemisentence n) :
    shift ℒₒᵣ (⌜σ⌝ : V) = ⌜σ⌝ := by
  have h : Rewriting.shift (Rewriting.emb σ : ArithmeticSemiproposition n) = Rewriting.emb σ := by
    simpa [Rewriting.shifts] using
      Rewriting.shifts_emb ({σ} : Multiset (ArithmeticSemisentence n))
  rw [Sentence.quote_def, ← Semiformula.quote_shift, h]

end FFL.FirstOrder.Semisentence

namespace FFL.FirstOrder.Semiterm

open Arithmetic Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {n : ℕ}

section

variable (w : Fin 0 → ClosedSemiterm ℒₒᵣ n)

@[simp] lemma empty_quote_func_zero :
    (⌜(func Language.ORing.Func.zero w : ClosedSemiterm ℒₒᵣ n)⌝ : V) = 𝟎 :=
  Arithmetic.coe_zero_eq.symm

@[simp] lemma empty_quote_func_one :
    (⌜(func Language.ORing.Func.one w : ClosedSemiterm ℒₒᵣ n)⌝ : V) = 𝟏 :=
  Arithmetic.coe_one_eq.symm

end

section

variable (w : Fin 2 → ClosedSemiterm ℒₒᵣ n)

@[simp] lemma empty_quote_func_add :
    (⌜(func Language.ORing.Func.add w : ClosedSemiterm ℒₒᵣ n)⌝ : V) = ⌜w 0⌝ ^+ ⌜w 1⌝ :=
  rfl

@[simp] lemma empty_quote_func_mul :
    (⌜(func Language.ORing.Func.mul w : ClosedSemiterm ℒₒᵣ n)⌝ : V) = ⌜w 0⌝ ^* ⌜w 1⌝ :=
  rfl

end

end FFL.FirstOrder.Semiterm

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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

end FFL.FirstOrder.Arithmetic.Bootstrapping
