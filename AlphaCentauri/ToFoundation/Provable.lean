module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.FixedPoint

@[expose] public section
/-!
# Internal provability: universal instantiation and modus ponens

Two generic facts about `Bootstrapping.Provable` needed to internalize induction over a model:
instantiating an internally-provable universal sentence at a numeral, and modus ponens for
arbitrary (not necessarily quoted) codes.
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

end specialize

end FFL.FirstOrder.Arithmetic.Bootstrapping
