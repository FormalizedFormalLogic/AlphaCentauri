module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.FixedPoint
public import AlphaCentauri.ToFoundation.Syntax

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

@[simp] lemma substNumerals_quote_of_isEmpty (σ : ArithmeticSentence) (v : Fin 0 → V) :
    substNumerals (⌜σ⌝ : V) v = ⌜σ⌝ := by
  simpa [Matrix.empty_eq] using substNumerals_app_quote (V := V) σ ![]

/-- Instantiating an internally-provable instance by numerals of `∀¹ φ` at one more numeral. -/
theorem provable_substNumerals_of_provable_substNumerals_all {m : ℕ}
    (φ : ArithmeticSemisentence (m + 1)) {v : Fin m → V}
    (h : Provable T (substNumerals (⌜∀¹ φ⌝ : V) v)) (x : V) :
    Provable T (substNumerals (⌜φ⌝ : V) (x :> v)) := by
  let w : V := matrixToVec fun i ↦ numeral (v i)
  have hw : IsSemitermVec ℒₒᵣ (m : V) 0 w :=
    SemitermVec.isSemitermVec (V := V) (L := ℒₒᵣ) (k := m) (n := 0) fun i ↦ 𝕹 (v i)
  have hφ : IsSemiformula ℒₒᵣ (m + 1 : V) (⌜φ⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) φ
  let ψ : Semiformula V ℒₒᵣ 1 :=
    ⟨subst ℒₒᵣ (qVec ℒₒᵣ w) ⌜φ⌝, by simpa using hφ.subst hw.qVec⟩
  have h₁ : T.internalize V ⊢ ∀¹ ψ :=
    tprovable_iff_provable.mpr (by simpa [ψ, w, substNumerals] using h)
  have h₂ := tprovable_iff_provable.mp (TProof.specialize! h₁ (𝕹 x))
  have e := substs1_subst_qVec hw hφ (t := numeral x) (by simp)
  simp only [substs1] at e
  simp only [Semiformula.val_substs, ψ, SemitermVec.val_succ] at h₂
  simpa [e, w, substNumerals, Matrix.vecHead, Matrix.vecTail, Function.comp_def] using h₂

end specialize

end FFL.FirstOrder.Arithmetic.Bootstrapping
