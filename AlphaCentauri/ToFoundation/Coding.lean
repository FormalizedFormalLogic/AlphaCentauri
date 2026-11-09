module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

/-!
# Codes of sentences and of closed arithmetic terms

The code of a semisentence is fixed by the shift of free variables, the code of its negation is the
negation of its code, and the code of its universal closure is a block of universal quantifiers
over its code. The code of the negation of a semisentence that is not universal is not existential.
A number codes a sentence of a finite list exactly when the defining formula of the list holds of
it. The symbols of a language are standard in a model when every relation and function symbol
of the model is the code of a symbol of the language. A vector is `matrixToVec u` exactly when it
has the length of `u` and the entries of `u`. The code of a negation, an implication, a block of
universal quantifiers, a finite conjunction or a substitution instance of a formula is obtained
from the code of the formula by the corresponding function on codes.
-/

@[expose] public section

namespace FFL.FirstOrder.Language

open Arithmetic Bootstrapping

/-- Every relation and function symbol of `L` in `V` is a standard one. -/
def SymbolsStandard (L : Language) [L.Encodable] [L.LORDefinable] (V : Type*) [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : Prop :=
  (∀ k r : V, L.IsRel k r → ∃ (k' : ℕ) (R : L.Rel k'), k = k' ∧ r = (⌜R⌝ : V)) ∧
  (∀ k f : V, L.IsFunc k f → ∃ (k' : ℕ) (F : L.Func k'), k = k' ∧ f = (⌜F⌝ : V))

end FFL.FirstOrder.Language

namespace FFL.FirstOrder.Semisentence

open Arithmetic Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {L : Language} [L.Encodable]
  [L.LORDefinable]

@[simp] lemma shift_quote {n : ℕ} (σ : Semisentence L n) : shift L (⌜σ⌝ : V) = ⌜σ⌝ := by
  have h : Rewriting.shift (Rewriting.emb σ : Semiproposition L n) = Rewriting.emb σ := by
    simpa [Rewriting.shifts] using Rewriting.shifts_emb ({σ} : Multiset (Semisentence L n))
  rw [Sentence.quote_def, ← Semiformula.quote_shift, h]

lemma shift_typed_quote {n : ℕ} (σ : Semisentence L n) :
    (⌜σ⌝ : Bootstrapping.Semiformula V L n).shift = ⌜σ⌝ := by
  have h : Rewriting.shift (Rewriting.emb σ : Semiproposition L n) = Rewriting.emb σ := by
    simpa [Rewriting.shifts] using Rewriting.shifts_emb ({σ} : Multiset (Semisentence L n))
  rw [Sentence.typed_quote_def, ← Semiformula.typed_quote_shift, h]

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

namespace FFL.FirstOrder

open Arithmetic Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma Arithmetic.Bootstrapping.eq_matrixToVec_iff {k : ℕ} {w : V} {u : Fin k → V} :
    w = matrixToVec u ↔ (k : V) = len w ∧ ∀ i : Fin k, w.[((i : ℕ) : V)] = u i := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h₁, h₂⟩
    apply nth_ext' (k : V) h₁.symm (by simp)
    intro i hi
    obtain ⟨i, rfl⟩ := eq_fin_of_lt_nat hi
    simp [h₂]

namespace Semiformula

variable {L : Language} [L.Encodable] [L.LORDefinable]

@[simp] lemma quote_neg {n : ℕ} (φ : Semiproposition L n) :
    (⌜∼φ⌝ : V) = Bootstrapping.neg L ⌜φ⌝ := by
  simp [quote_def]

@[simp] lemma quote_imp {n : ℕ} (φ ψ : Semiproposition L n) :
    (⌜φ 🡒 ψ⌝ : V) = Bootstrapping.imp L ⌜φ⌝ ⌜ψ⌝ := by
  simp [quote_def, Bootstrapping.imp]

lemma quote_allItr {n k : ℕ} (φ : Semiproposition L (n + k)) :
    (⌜∀¹^[k] φ⌝ : V) = qqAlls (⌜φ⌝ : V) (k : V) := by
  induction k with
  | zero => simp
  | succ k ih => simpa [allItr_succ, qqAlls_all] using ih (∀¹ φ)

lemma quote_conj {n k : ℕ} (φ : Fin k → Semiproposition L n) :
    (⌜Matrix.conj φ⌝ : V) = ^⋀ matrixToVec fun i ↦ (⌜φ i⌝ : V) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simpa [Matrix.conj, Matrix.vecHead, Matrix.vecTail, Function.comp_def] using
      ih (Matrix.vecTail φ)

lemma quote_substs {n m : ℕ} (w : Fin n → SyntacticSemiterm L m) (φ : Semiproposition L n) :
    (⌜φ ⇜ w⌝ : V) = Bootstrapping.subst L (matrixToVec fun i ↦ (⌜w i⌝ : V)) ⌜φ⌝ := by
  simp [quote_def, Semiterm.quote_def]
  rfl

end Semiformula

end FFL.FirstOrder

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {L : Language} [L.Encodable]
  [L.LORDefinable]

lemma exists_termVec {k : ℕ} {v : V} (hv : IsSemitermVec L (k : V) 0 v) :
    ∃ u : Fin k → Term V L, SemitermVec.val u = v := by
  have hu : ∀ i : Fin k, IsSemiterm L 0 v.[((i : ℕ) : V)] := fun i ↦ hv.nth (by simp)
  exact ⟨fun i ↦ ⟨v.[((i : ℕ) : V)], hu i⟩, by
    change matrixToVec (fun i : Fin k ↦ v.[((i : ℕ) : V)]) = v
    symm
    rw [eq_matrixToVec_iff]
    exact ⟨hv.lh.symm, fun i ↦ rfl⟩⟩

end FFL.FirstOrder.Arithmetic.Bootstrapping
