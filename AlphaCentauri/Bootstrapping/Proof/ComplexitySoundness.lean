module

public import AlphaCentauri.Bootstrapping.PartialTruth.Combination
public import AlphaCentauri.Bootstrapping.PartialTruth.Complexity
public import AlphaCentauri.Bootstrapping.Proof.CutElimination
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.HFS.Basic

/-!
# Soundness of cut-free derivations for satisfaction by complexity

In every model of `𝗜𝚺⁺(N + 1)`, a sequent of formulas of complexity at most `N` derivable without
cuts in pure logic contains a formula satisfied under `ComplexitySatisfied N`. Consequently, a
sequent of codes of sentences of complexity at most `N` derivable in pure logic contains the code
of a true sentence.

## References

- [HP98, Theorem I.4.33]
- [Kay91, Exercise 10.8]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic
namespace Bootstrapping

section ComplexitySoundness

open PeanoMinus ISigma0 ISigma1
open Arithmetic (numeral numeral_semiterm)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Some formula of `s` is satisfied under `ComplexitySatisfied N` once its free variables are
assigned by `f`. -/
private def HasSatisfied (N : ℕ) (s f : V) : Prop :=
  ∃ p ∈ s, ComplexitySatisfied N 0 (fvAssign f p)

section complexitySoundness

variable {N : ℕ} {s p q f : V}

private lemma hasSatisfied_of_insert (h : HasSatisfied N (insert p s) f)
    (hp : ¬ComplexitySatisfied N 0 (fvAssign f p)) : HasSatisfied N s f := by
  obtain ⟨r, hr, hrT⟩ := h
  rcases mem_bitInsert_iff.mp hr with rfl | hr
  · exact absurd hrT hp
  · exact ⟨r, hr, hrT⟩

private lemma formulaComplexity_insert_le (hp : formulaComplexity ℒₒᵣ p ≤ N)
    (hs : ∀ r ∈ s, formulaComplexity ℒₒᵣ r ≤ N) :
    ∀ r ∈ insert p s, formulaComplexity ℒₒᵣ r ≤ N := by
  intro r hr
  rcases mem_bitInsert_iff.mp hr with rfl | hr <;> grind

private lemma formulaComplexity_fvAssign_le (hs : IsFormulaSet ℒₒᵣ s) (hp : p ∈ s)
    (hb : ∀ r ∈ s, formulaComplexity ℒₒᵣ r ≤ N) : formulaComplexity ℒₒᵣ (fvAssign f p) ≤ N := by
  rw [formulaComplexity_fvAssign (hs p hp).isUFormula]
  exact hb p hp

private lemma hasSatisfied_of_and (hs : IsFormulaSet ℒₒᵣ s) (hpq : p ^⋏ q ∈ s)
    (hb : ∀ r ∈ s, formulaComplexity ℒₒᵣ r ≤ N)
    (ihp : (∀ r ∈ insert p s, formulaComplexity ℒₒᵣ r ≤ N) → HasSatisfied N (insert p s) f)
    (ihq : (∀ r ∈ insert q s, formulaComplexity ℒₒᵣ r ≤ N) → HasSatisfied N (insert q s) f) :
    HasSatisfied N s f := by
  have hF : IsFormula ℒₒᵣ p ∧ IsFormula ℒₒᵣ q := by simpa using hs _ hpq
  have e : fvAssign f (p ^⋏ q) = fvAssign f p ^⋏ fvAssign f q :=
    fvAssign_and hF.1.isUFormula hF.2.isUFormula
  have hc := hb _ hpq
  have hc' : formulaComplexity ℒₒᵣ (fvAssign f p ^⋏ fvAssign f q) ≤ N := by
    rwa [← e, formulaComplexity_fvAssign (hs _ hpq).isUFormula]
  by_cases ht : ComplexitySatisfied N 0 (fvAssign f (p ^⋏ q))
  · exact ⟨_, hpq, ht⟩
  rw [e, ComplexitySatisfied.and_iff hF.1.isUFormula.fvAssign hF.2.isUFormula.fvAssign hc',
    not_and_or] at ht
  rw [formulaComplexity_and hF.1.isUFormula hF.2.isUFormula] at hc
  obtain ⟨hp, hq⟩ := max_le_iff.mp (le_self_add.trans hc)
  rcases ht with ht | ht
  · exact hasSatisfied_of_insert (ihp (formulaComplexity_insert_le hp hb)) ht
  · exact hasSatisfied_of_insert (ihq (formulaComplexity_insert_le hq hb)) ht

private lemma hasSatisfied_of_or (hs : IsFormulaSet ℒₒᵣ s) (hpq : p ^⋎ q ∈ s)
    (hb : ∀ r ∈ s, formulaComplexity ℒₒᵣ r ≤ N)
    (ih : (∀ r ∈ insert p (insert q s), formulaComplexity ℒₒᵣ r ≤ N) →
      HasSatisfied N (insert p (insert q s)) f) :
    HasSatisfied N s f := by
  have hF : IsFormula ℒₒᵣ p ∧ IsFormula ℒₒᵣ q := by simpa using hs _ hpq
  have e : fvAssign f (p ^⋎ q) = fvAssign f p ^⋎ fvAssign f q :=
    fvAssign_or hF.1.isUFormula hF.2.isUFormula
  have hc := hb _ hpq
  have hc' : formulaComplexity ℒₒᵣ (fvAssign f p ^⋎ fvAssign f q) ≤ N := by
    rwa [← e, formulaComplexity_fvAssign (hs _ hpq).isUFormula]
  by_cases ht : ComplexitySatisfied N 0 (fvAssign f (p ^⋎ q))
  · exact ⟨_, hpq, ht⟩
  rw [e, ComplexitySatisfied.or_iff hF.1.isUFormula.fvAssign hF.2.isUFormula.fvAssign hc',
    not_or] at ht
  rw [formulaComplexity_or hF.1.isUFormula hF.2.isUFormula] at hc
  obtain ⟨hp, hq⟩ := max_le_iff.mp (le_self_add.trans hc)
  exact hasSatisfied_of_insert (hasSatisfied_of_insert
    (ih (formulaComplexity_insert_le hp (formulaComplexity_insert_le hq hb))) ht.1) ht.2

private lemma hasSatisfied_of_all (hs : IsFormulaSet ℒₒᵣ s) (hp : ^∀ p ∈ s)
    (hb : ∀ r ∈ s, formulaComplexity ℒₒᵣ r ≤ N)
    (ih : ∀ g, (∀ r ∈ insert (free ℒₒᵣ p) (setShift ℒₒᵣ s), formulaComplexity ℒₒᵣ r ≤ N) →
      HasSatisfied N (insert (free ℒₒᵣ p) (setShift ℒₒᵣ s)) g) :
    HasSatisfied N s f := by
  have hpF : IsSemiformula ℒₒᵣ 1 p := by simpa using hs _ hp
  have hc := hb _ hp
  have hc' := formulaComplexity_fvAssign_le (f := f) hs hp hb
  by_cases ht : ComplexitySatisfied N 0 (fvAssign f (^∀ p))
  · use ^∀ p, hp
  rw [fvAssign_all hpF.isUFormula] at ht hc'
  rw [ComplexitySatisfied.all_iff hpF.fvAssign.isUFormula hc', not_forall] at ht
  obtain ⟨x, hx⟩ := ht
  have hsh : ∀ q ∈ s, fvAssign (x ∷ f) (shift ℒₒᵣ q) = fvAssign f q :=
    fun q hq ↦ fvAssign_shift (hs q hq).isUFormula
  have hfree : fvAssign (x ∷ f) (free ℒₒᵣ p) = substs1 ℒₒᵣ (numeral x) (fvAssign f p) :=
    fvAssign_free hpF
  have hb' : ∀ r ∈ insert (free ℒₒᵣ p) (setShift ℒₒᵣ s), formulaComplexity ℒₒᵣ r ≤ N := by
    apply formulaComplexity_insert_le
    · rw [fomulaComplexity_free hpF]
      rw [formulaComplexity_all hpF.isUFormula] at hc
      exact le_self_add.trans hc
    · intro r hr
      obtain ⟨q, hq, rfl⟩ := mem_setShift_iff.mp hr
      rw [formulaComplexity_shift (hs q hq).isUFormula]
      exact hb q hq
  obtain ⟨r, hr, hrT⟩ := hasSatisfied_of_insert (ih (x ∷ f) hb') (by
    rw [hfree, substs1, ComplexitySatisfied.subst (m := 0) (by simp) hpF.fvAssign]
    simpa using hx)
  obtain ⟨q, hq, rfl⟩ := mem_setShift_iff.mp hr
  rw [hsh q hq] at hrT
  exact ⟨q, hq, hrT⟩

private lemma hasSatisfied_of_exs {t : V} (hs : IsFormulaSet ℒₒᵣ s) (hp : ^∃ p ∈ s)
    (ht : IsTerm ℒₒᵣ t) (hb : ∀ r ∈ s, formulaComplexity ℒₒᵣ r ≤ N)
    (ih : (∀ r ∈ insert (substs1 ℒₒᵣ t p) s, formulaComplexity ℒₒᵣ r ≤ N) →
      HasSatisfied N (insert (substs1 ℒₒᵣ t p) s) f) :
    HasSatisfied N s f := by
  have hpF : IsSemiformula ℒₒᵣ 1 p := by simpa using hs _ hp
  have et : fvAssign f (substs1 ℒₒᵣ t p) = substs1 ℒₒᵣ (termFvAssign f t) (fvAssign f p) :=
    fvAssign_substs1 ht hpF
  have hc := hb _ hp
  have hb' : ∀ r ∈ insert (substs1 ℒₒᵣ t p) s, formulaComplexity ℒₒᵣ r ≤ N := by
    apply formulaComplexity_insert_le _ hb
    rw [fomulaComplexity_substs1 hpF ht]
    rw [formulaComplexity_ex hpF.isUFormula] at hc
    exact le_self_add.trans hc
  obtain ⟨r, hr, hrT⟩ := ih hb'
  rcases mem_bitInsert_iff.mp hr with rfl | hr
  · have hc' := formulaComplexity_fvAssign_le (f := f) hs hp hb
    rw [fvAssign_exs hpF.isUFormula] at hc'
    rw [et, substs1, ComplexitySatisfied.subst (m := 0) (by simp [ht.termFvAssign])
      hpF.fvAssign, termValVec_cons₁ ht.termFvAssign.isUTerm] at hrT
    use ^∃ p, hp
    rw [fvAssign_exs hpF.isUFormula]
    exact (ComplexitySatisfied.exs_iff hpF.fvAssign.isUFormula hc').mpr ⟨_, hrT⟩
  · exact ⟨r, hr, hrT⟩

private lemma hasSatisfied_of_shift {Γ : V} (hΓ : IsFormulaSet ℒₒᵣ Γ)
    (hb : ∀ r ∈ setShift ℒₒᵣ Γ, formulaComplexity ℒₒᵣ r ≤ N)
    (ih : ∀ g, (∀ r ∈ Γ, formulaComplexity ℒₒᵣ r ≤ N) → HasSatisfied N Γ g) :
    HasSatisfied N (setShift ℒₒᵣ Γ) f := by
  obtain ⟨b, g, hfg⟩ : ∃ b g : V, ∀ i, f.[i] = (b ∷ g).[i] := by
    rcases adjoin_cases f with rfl | ⟨b, g, rfl⟩
    · use 0, 0
      intro i
      rcases zero_or_succ i with rfl | ⟨i, rfl⟩ <;> simp
    · exact ⟨b, g, fun _ ↦ rfl⟩
  have hsh : ∀ q ∈ Γ, fvAssign f (shift ℒₒᵣ q) = fvAssign g q := by
    intro q hq
    rw [fvAssign_congr hfg, fvAssign_shift (hΓ q hq).isUFormula]
  obtain ⟨r, hr, hrT⟩ := ih g fun r hr ↦ by
    simpa [formulaComplexity_shift (hΓ r hr).isUFormula] using hb _ (shift_mem_setShift hr)
  exact ⟨_, shift_mem_setShift hr, by rwa [hsh r hr]⟩

private lemma hasSatisfied_of_axL (hs : IsFormulaSet ℒₒᵣ s) (hp : p ∈ s) (hnp : neg ℒₒᵣ p ∈ s)
    (hb : ∀ r ∈ s, formulaComplexity ℒₒᵣ r ≤ N) : HasSatisfied N s f := by
  have hpU : IsUFormula ℒₒᵣ p := (hs p hp).isUFormula
  by_cases ht : ComplexitySatisfied N 0 (fvAssign f p)
  · use p, hp
  · use neg ℒₒᵣ p, hnp
    rw [fvAssign_neg hpU, ComplexitySatisfied.neg_iff hpU.fvAssign
      (formulaComplexity_fvAssign_le hs hp hb)]
    exact ht

private lemma hasSatisfied_definable :
    𝚷ᴬ_[N + 1].DefinablePred fun d : V ↦ ∀ f, CutFreeDerivation (∅ : Theory ℒₒᵣ) d →
      (∀ r ∈ fstIdx d, formulaComplexity ℒₒᵣ r ≤ N) → HasSatisfied N (fstIdx d) f := by
  unfold HasSatisfied
  definability

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺(N + 1)]

private lemma hasSatisfied_aux :
    ∀ d f : V, CutFreeDerivation (∅ : Theory ℒₒᵣ) d →
      (∀ r ∈ fstIdx d, formulaComplexity ℒₒᵣ r ≤ N) → HasSatisfied N (fstIdx d) f := by
  intro d
  apply InductionOnHierarchy.order_induction_sigma 𝚷 (N + 1) hasSatisfied_definable
  intro d ih f hd hb
  have ih' : ∀ d₀ < d, ∀ s, CutFreeDerivationOf (∅ : Theory ℒₒᵣ) d₀ s → ∀ g,
      (∀ r ∈ s, formulaComplexity ℒₒᵣ r ≤ N) → HasSatisfied N s g := by
    rintro d₀ hd₀ s ⟨rfl, hd₀'⟩ g hg
    exact ih d₀ hd₀ g hd₀' hg
  have hs := hd.isFormulaSet
  rcases hd.case.2 with (⟨s, p, rfl, hp, hnp⟩ | ⟨s, rfl, hv⟩ |
    ⟨s, p, q, dp, dq, rfl, hpq, hdp, hdq⟩ | ⟨s, p, q, d₀, rfl, hpq, hd₀⟩ |
    ⟨s, p, d₀, rfl, hp, hd₀⟩ | ⟨s, p, t, d₀, rfl, hp, ht, hd₀⟩ |
    ⟨s, d₀, rfl, hsub, hd₀⟩ | ⟨s, d₀, rfl, rfl, hd₀⟩ | ⟨s, p, rfl, -, hT⟩)
  · rw [fstIdx_axL] at hs hb ⊢
    exact hasSatisfied_of_axL hs hp hnp hb
  · rw [fstIdx_verumIntro] at hb ⊢
    exact ⟨_, hv, by simp⟩
  · rw [fstIdx_andIntro] at hs hb ⊢
    exact hasSatisfied_of_and hs hpq hb (ih' dp (dp_lt_andIntro _ _ _ _ _) _ hdp f)
      (ih' dq (dq_lt_andIntro _ _ _ _ _) _ hdq f)
  · rw [fstIdx_orIntro] at hs hb ⊢
    exact hasSatisfied_of_or hs hpq hb (ih' d₀ (d_lt_orIntro _ _ _ _) _ hd₀ f)
  · rw [fstIdx_allIntro] at hs hb ⊢
    exact hasSatisfied_of_all hs hp hb (ih' d₀ (s_lt_allIntro _ _ _) _ hd₀)
  · rw [fstIdx_exsIntro] at hs hb ⊢
    exact hasSatisfied_of_exs hs hp ht hb (ih' d₀ (d_lt_exsIntro _ _ _ _) _ hd₀ f)
  · rw [fstIdx_wkRule] at hb ⊢
    obtain ⟨r, hr, hrT⟩ := ih d₀ (d_lt_wkRule _ _) f hd₀ fun r hr ↦ hb r (hsub hr)
    exact ⟨r, hsub hr, hrT⟩
  · rw [fstIdx_shiftRule] at hb ⊢
    exact hasSatisfied_of_shift hd₀.isFormulaSet hb (ih d₀ (d_lt_shiftRule _ _) · hd₀)
  · exact absurd hT (not_mem_empty_Δ₁Class p)

/-- A sequent of codes of sentences of complexity at most `N` derivable in pure logic contains the
code of a true sentence.
- [HP98, Corollary I.4.34] -/
theorem Derivable.exists_models (h : Derivable (∅ : Theory ℒₒᵣ) s)
    (hs : ∀ r ∈ s, ∃ σ : ArithmeticSentence, σ.complexity ≤ N ∧ r = ⌜σ⌝) :
    ∃ σ : ArithmeticSentence, (⌜σ⌝ : V) ∈ s ∧ V↓[ℒₒᵣ] ⊧ σ := by
  obtain ⟨d, rfl, hd⟩ := h.cutFree
  obtain ⟨r, hr, hrT⟩ := hasSatisfied_aux d 0 hd fun r hr ↦ by
    obtain ⟨σ, hσ, rfl⟩ := hs r hr
    simpa using hσ
  obtain ⟨σ, hσ, rfl⟩ := hs r hr
  use σ, hr
  rw [fvAssign_quote] at hrT
  exact (ComplexitySatisfied.quote_sentence_iff hσ).mp hrT

end complexitySoundness

end ComplexitySoundness

end Bootstrapping
end FFL.FirstOrder.Arithmetic
