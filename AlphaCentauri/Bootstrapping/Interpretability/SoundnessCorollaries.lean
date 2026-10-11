module

public import AlphaCentauri.Bootstrapping.Interpretability.Soundness
public import AlphaCentauri.Bootstrapping.Proof.CutFree
public import Foundation.FirstOrder.Incompleteness.Consistency

/-!
# Corollaries of the internal soundness of a translation

Consequences of the translated derivability of derivable sets: provability of formula codes is
transferred along a translation, and so is consistency.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1

section translation

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S]
  {π : DirectTranslation S L₂} {tbl : V}

/-- A formula code fixed by the shift of free variables and provable in `S'` has its translation
provable in `S`.
- [Lin97, Corollary 6.1]
- [HP98, Lemma III.2.42] -/
theorem provable_translate (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {S' : Theory L₂} [S'.Δ₁]
    (hax : ∀ p ∈ S'.Δ₁Class (V := V), Provable S (Bootstrapping.translate L₁ L₂ tbl p)) {φ : V}
    (hφ : Bootstrapping.shift L₂ φ = φ) (hpr : Provable S' φ) :
    Provable S (Bootstrapping.translate L₁ L₂ tbl φ) := by
  have hΓ : IsFormulaSet L₂ (insert φ ∅ : V) := hpr.toDerivable.isFormulaSet
  have hφF : IsFormula L₂ φ := (IsFormulaSet.insert_iff.mp hΓ).1
  have hfresh : ∀ j, 0 ≤ j → j < (insert φ ∅ : V) → ∀ q ∈ (insert φ ∅ : V),
      fvSubst L₂ (freshVec j) q = shift L₂ q := by
    intro j _ _ q hq
    obtain rfl : q = φ := by simpa using hq
    exact (fvSubst_eq_self_of_shift hφF hφ).trans hφ.symm
  have hd : Derivable S (translateSet L₁ L₂ tbl (insert φ ∅) ∪
      negDomSet L₁ tbl.[0] (insert φ ∅)) :=
    TranslatedDerivable.of_derivable hS h hL₂ hax hpr.toDerivable
  have h₀ := elim_translateSet hS h hL₂ hΓ zero_le hfresh hd
  rw [negDomSet_zero, translateSet_insert, translateSet_empty] at h₀
  exact internal_provable_iff_internal_derivable.mpr (Derivable.ofSetEq (fun x ↦ by simp) h₀)

/-- If `S` is consistent in `V`, then so is `S'`.
- [Lin97, Corollary 6.1]
- [HP98, Lemma III.2.42] -/
theorem consistent_of_translate (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {S' : Theory L₂} [S'.Δ₁]
    (hax : ∀ p ∈ S'.Δ₁Class (V := V), Provable S (Bootstrapping.translate L₁ L₂ tbl p))
    (hcon : S.Consistent V) : S'.Consistent V := by
  intro hp
  apply hcon
  have h₁ := provable_translate hS h hL₂ hax (φ := (⌜(⊥ : Sentence L₂)⌝ : V))
    (shift_falsum (L := L₂)) hp
  have h₂ : Bootstrapping.translate L₁ L₂ tbl (⌜(⊥ : Sentence L₂)⌝ : V) =
      (⌜(⊥ : Sentence L₁)⌝ : V) :=
    translate_falsum tbl
  rw [h₂] at h₁
  exact h₁

end translation

section finite

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S]

/-- For a finite theory `S'` interpreted in `S`, provability of a formula code from `S'` yields
provability of its translation in `S`, without assuming the hypothesis on the axioms.
- [Lin97, Corollary 6.1]
- [HP98, Lemma III.2.42] -/
theorem provable_translate_of_finite (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (l : List (Sentence L₂)) (π : S ⊳ {φ | φ ∈ l})
    {tbl : V} (h : IsTableOf π.trln tbl) (hL₂ : L₂.SymbolsStandard V) {φ : V}
    (hφ : Bootstrapping.shift L₂ φ = φ) :
    letI := Theory.Δ₁.ofList l
    Provable ({φ | φ ∈ l} : Theory L₂) φ → Provable S (Bootstrapping.translate L₁ L₂ tbl φ) := by
  let _ := Theory.Δ₁.ofList l
  intro hpr
  have hax : ∀ p ∈ Theory.Δ₁Class (V := V) ({φ | φ ∈ l} : Theory L₂),
      Provable S (Bootstrapping.translate L₁ L₂ tbl p) := by
    intro p hp
    obtain ⟨σ, hσ, rfl⟩ := (Derivation.mem_deltaClass_ofList_iff l p).mp hp
    rw [h.translate_quote_sentence σ]
    exact internalize_provability (π.interpret_theory σ hσ)
  exact provable_translate hS h hL₂ hax hφ hpr

end finite

end FFL.FirstOrder.Arithmetic.Bootstrapping
