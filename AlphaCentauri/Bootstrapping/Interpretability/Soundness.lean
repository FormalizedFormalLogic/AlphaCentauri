module

public import AlphaCentauri.Bootstrapping.Interpretability.SoundnessExs
public import AlphaCentauri.Bootstrapping.Interpretability.SoundnessRules

/-!
# Translated derivability of derivable sets

Every set of $L_2$-formulas derivable in a theory `S'` is translated derivable in `S`, provided
the $\Delta_1$ axioms of `S'` are provable in `S` after translation.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1

section rules

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S]
  {π : DirectTranslation S L₂} {tbl : V}

theorem TranslatedDerivable.of_derivable
    (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTableOf π tbl) (hL₂ : L₂.SymbolsStandard V) {S' : Theory L₂} [S'.Δ₁]
    (hax : ∀ p ∈ S'.Δ₁Class (V := V), Provable S (Bootstrapping.translate L₁ L₂ tbl p)) {s : V}
    (hs : Derivable S' s) : TranslatedDerivable S L₂ tbl s := by
  obtain ⟨d, hds, hd⟩ := hs
  subst hds
  apply Derivation.induction1 𝚺 (P := fun d ↦ TranslatedDerivable S L₂ tbl (fstIdx d)) ?_ hd
  · intro s hs p hp hn
    simp only [fstIdx_axL]
    exact translated_em h hL₂ hs hp hn
  · intro s hs hv
    simp only [fstIdx_verumIntro]
    exact translated_verum h hL₂ hs hv
  · intro s hs p q dp dq hpq hdp hdq ihp ihq
    simp only [hdp.1] at ihp
    simp only [hdq.1] at ihq
    simp only [fstIdx_andIntro]
    exact translated_and hS h hL₂ hs hpq ihp ihq
  · intro s hs p q d hpq hd ih
    simp only [hd.1] at ih
    simp only [fstIdx_orIntro]
    exact translated_or hS h hL₂ hs hpq ih
  · intro s hs p d hp hd ih
    simp only [hd.1] at ih
    simp only [fstIdx_allIntro]
    exact translated_all hS h hL₂ hs hp ih
  · intro s hs p t d hp ht hd ih
    simp only [hd.1] at ih
    simp only [fstIdx_exsIntro]
    exact translated_exs hS h hL₂ hs hp ht ih
  · intro s hs d hsub _ ih
    simp only [fstIdx_wkRule]
    exact translated_wk h hL₂ hs hsub ih
  · intro s hs d hds hd' ih
    simp only [fstIdx_shiftRule]
    subst hds
    exact translated_shift hS h hL₂ (Derivation.isFormulaSet hd') ih
  · intro s hs p d₁ d₂ h₁ h₂ ih₁ ih₂
    simp only [h₁.1] at ih₁
    simp only [h₂.1] at ih₂
    simp only [fstIdx_cutRule]
    have hp : IsFormula L₂ p := (IsFormulaSet.insert_iff.mp h₁.isFormulaSet).1
    exact translated_cut hS h hL₂ hs hp ih₁ ih₂
  · intro s hs p hps hpT
    simp only [fstIdx_axm]
    exact translated_axm h hL₂ hs hps (hax p hpT)
  · definability

end rules

end FFL.FirstOrder.Arithmetic.Bootstrapping
