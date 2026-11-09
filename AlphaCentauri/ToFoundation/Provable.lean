module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D3
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.FixedPoint
public import AlphaCentauri.ToFoundation.TypedProof

@[expose] public section
/-!
# Internal provability: universal instantiation and modus ponens

Generic facts about `Bootstrapping.Provable`: instantiating an internally-provable universal
sentence at a numeral, modus ponens for arbitrary (not necessarily quoted) codes, and the internal
provability of the numeral instances of a theorem of `𝗜𝚺₁` and of a true $\Sigma_1$ formula.
-/

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section modus_ponens

variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

/-- Modus ponens for internal provability of arbitrary codes, not necessarily quotes of standard
propositions. -/
theorem provable_of_provable_imp_of_provable {a b : V}
    (hab : Provable T (imp L a b)) (ha : Provable T a) : Provable T b := by
  have hab' : IsFormula L (imp L a b) := by simpa using hab.toDerivable.isFormulaSet
  have ha' : IsFormula L a := by simpa using ha.toDerivable.isFormulaSet
  have hb' : IsFormula L b := (IsSemiformula.imp.mp hab').2
  set φ : Formula V L := ⟨a, ha'⟩
  set ψ : Formula V L := ⟨b, hb'⟩
  have hφψ : T.internalize V ⊢ φ 🡒 ψ := tprovable_iff_provable.mpr (by simpa [φ, ψ] using hab)
  have hφ : T.internalize V ⊢ φ := tprovable_iff_provable.mpr (by simpa [φ] using ha)
  simpa [φ, ψ] using tprovable_iff_provable.mp (hφψ ⨀ hφ)

end modus_ponens

section specialize

open Bootstrapping.Arithmetic

variable {T : ArithmeticTheory} [T.Δ₁]

/-- Instantiating an internally-provable `∀¹ φ` at the numeral for `x`. -/
theorem provable_substNumeral_of_provable_quote_all (φ : ArithmeticSemisentence 1)
    (h : Provable T (⌜∀¹ φ⌝ : V)) (x : V) : Provable T (substNumeral (⌜φ⌝ : V) x) := by
  have h1 : T.internalize V ⊢ (⌜∀¹ φ⌝ : Formula V ℒₒᵣ) :=
    tprovable_tquote_iff_provable_quote_sentence.mpr h
  have h2 : T.internalize V ⊢ ∀¹ (⌜φ⌝ : Semiformula V ℒₒᵣ 1) := by simpa using h1
  have h3 := TProof.specialize! h2 (𝕹 x)
  simpa [substNumeral, Sentence.quote_eq] using tprovable_iff_provable.mp h3

variable [𝗜𝚺₁ ⪯ T]

/-- A theorem of `𝗜𝚺₁`, given by its truth in every model, is internally provable at numerals. -/
lemma tprovable_subst_numeral_of_models {k : ℕ} {φ : ArithmeticSemisentence k}
    (h : ∀ (W : Type) [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin k → W), W ⊧/e φ)
    (w : Fin k → V) :
    T.internalize V ⊢ (⌜φ⌝ : Semiformula V ℒₒᵣ k).subst (fun i ↦ 𝕹 (w i)) :=
  tprovable_subst_of_allClosure T _ <| internal_provable_of_outer_provable <|
    Entailment.WeakerThan.pbl <| complete 𝗜𝚺₁ _ fun W _ _ ↦ by simpa [models_iff] using h W

/-- A $\Sigma_1$ formula true at `w` is internally provable at the numerals of `w`. -/
lemma tprovable_subst_numeral_of_sigma1 {k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ) {w : Fin k → V} (h : V ⊧/w φ) :
    T.internalize V ⊢ (⌜φ⌝ : Semiformula V ℒₒᵣ k).subst (fun i ↦ 𝕹 (w i)) :=
  bold_sigma_one_complete T hφ h

end specialize

end FFL.FirstOrder.Arithmetic.Bootstrapping
