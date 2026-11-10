module

public import AlphaCentauri.Bootstrapping.Proof.CutFree
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Basic
public import AlphaCentauri.Bootstrapping.Proof.Measures

/-!
# Internal derivations of bounded cut rank

`RankedDerivation T r d` says that `d` codes a derivation of Foundation's internal one-sided
calculus over `T` whose cut rank is at most `r`, i.e. all of whose cut formulas have complexity
below `r`. At rank `0` these are the cut-free derivations.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

section RankedDerivation

open PeanoMinus ISigma0 ISigma1 InternalMeasures

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

/-- A cut-free derivation cuts on nothing, so its cut rank is `0`.
- [Bus98, Ch. I §2.4] -/
lemma CutFreeDerivation.cutRank_eq_zero {d : V} (h : CutFreeDerivation T d) :
    cutRank L d = 0 := by
  apply CutFreeDerivation.induction1 𝚺 ?_ h
  · intro s _ p _ _; simp
  · intro s _ _; simp
  · intro s _ p q dp dq _ _ _ ihp ihq; simp [ihp, ihq]
  · intro s _ p q d _ _ ih; simp [ih]
  · intro s _ p d _ _ ih; simp [ih]
  · intro s _ p t d _ _ _ ih; simp [ih]
  · intro s _ d _ _ ih; simp [ih]
  · rintro _ _ d rfl _ ih; simp [ih]
  · intro s _ p _ _; simp
  · definability

variable (T) in
/-- `RankedDerivation T r d`: `d` codes a derivation of `T` whose cut formulas all have complexity
below `r`.
- [Bus98, Ch. I §2.4] -/
def RankedDerivation (r d : V) : Prop := Derivation T d ∧ cutRank L d ≤ r

variable (T) in
/-- `RankedDerivationOf T r d s`: `d` codes a derivation of `T` of cut rank at most `r` whose
end-sequent is `s`. -/
def RankedDerivationOf (r d s : V) : Prop := fstIdx d = s ∧ RankedDerivation T r d

variable (T) in
/-- `RankedDerivable T r s`: the sequent `s` has a derivation over `T` of cut rank at most `r`. -/
def RankedDerivable (r s : V) : Prop := ∃ d, RankedDerivationOf T r d s

section definability

variable {Γ : SigmaPiDelta} {m : ℕ}

instance RankedDerivation.definable : 𝚫ᴬ₁-Relation (RankedDerivation T : V → V → Prop) := by
  unfold RankedDerivation
  definability

instance RankedDerivation.definable' : Γᴬ_[m + 1]-Relation (RankedDerivation T : V → V → Prop) :=
  RankedDerivation.definable.of_deltaOne

instance RankedDerivationOf.definable :
    𝚫ᴬ₁-Relation₃ (RankedDerivationOf T : V → V → V → Prop) := by
  unfold RankedDerivationOf
  definability

instance RankedDerivationOf.definable' :
    Γᴬ_[m + 1]-Relation₃ (RankedDerivationOf T : V → V → V → Prop) :=
  RankedDerivationOf.definable.of_deltaOne

instance RankedDerivable.definable : 𝚺ᴬ₁-Relation (RankedDerivable T : V → V → Prop) := by
  unfold RankedDerivable
  definability

instance RankedDerivable.definable' : 𝚺ᴬ_[0 + 1]-Relation (RankedDerivable T : V → V → Prop) :=
  RankedDerivable.definable

end definability

variable {r r' d s : V}

namespace RankedDerivation

lemma isFormulaSet (h : RankedDerivation T r d) : IsFormulaSet L (fstIdx d) := h.1.isFormulaSet

lemma of_le (h : RankedDerivation T r d) (hr : r ≤ r') : RankedDerivation T r' d :=
  ⟨h.1, le_trans h.2 hr⟩

/-- `RankedDerivation T r d` unfolds one step: `d` is a rule application whose immediate
subderivations again have cut rank at most `r`, and a cut is on a formula of complexity below
`r`. -/
lemma case (h : RankedDerivation T r d) :
    IsFormulaSet L (fstIdx d) ∧
    ( (∃ s p, d = axL s p ∧ p ∈ s ∧ neg L p ∈ s) ∨
      (∃ s, d = verumIntro s ∧ ^⊤ ∈ s) ∨
      (∃ s p q dp dq, d = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧
        RankedDerivationOf T r dp (insert p s) ∧ RankedDerivationOf T r dq (insert q s)) ∨
      (∃ s p q dpq, d = orIntro s p q dpq ∧ p ^⋎ q ∈ s ∧
        RankedDerivationOf T r dpq (insert p (insert q s))) ∨
      (∃ s p dp, d = allIntro s p dp ∧ ^∀ p ∈ s ∧
        RankedDerivationOf T r dp (insert (free L p) (setShift L s))) ∨
      (∃ s p t dp, d = exsIntro s p t dp ∧ ^∃ p ∈ s ∧ IsTerm L t ∧
        RankedDerivationOf T r dp (insert (substs1 L t p) s)) ∨
      (∃ s d', d = wkRule s d' ∧ fstIdx d' ⊆ s ∧ RankedDerivation T r d') ∨
      (∃ s d', d = shiftRule s d' ∧ s = setShift L (fstIdx d') ∧ RankedDerivation T r d') ∨
      (∃ s p d₁ d₂, d = cutRule s p d₁ d₂ ∧ formulaComplexity L p < r ∧
        RankedDerivationOf T r d₁ (insert p s) ∧ RankedDerivationOf T r d₂ (insert (neg L p) s)) ∨
      (∃ s p, d = axm s p ∧ p ∈ s ∧ p ∈ T.Δ₁Class) ) := by
  obtain ⟨hd, hr⟩ := h
  refine ⟨hd.isFormulaSet, ?_⟩
  rcases hd.case.2 with (h | h | ⟨s, p, q, dp, dq, rfl, hpq, hdp, hdq⟩ |
    ⟨s, p, q, d₀, rfl, hpq, hd₀⟩ | ⟨s, p, d₀, rfl, hp, hd₀⟩ | ⟨s, p, t, d₀, rfl, hp, ht, hd₀⟩ |
    ⟨s, d₀, rfl, hsub, hd₀⟩ | ⟨s, d₀, rfl, hsh, hd₀⟩ | ⟨s, p, d₁, d₂, rfl, hd₁, hd₂⟩ | h)
  · disj 1; exact h
  · disj 2; exact h
  · simp only [cutRank_andIntro, max_le_iff] at hr
    disj 3
    exact ⟨s, p, q, dp, dq, rfl, hpq, ⟨hdp.1, hdp.2, hr.1⟩, ⟨hdq.1, hdq.2, hr.2⟩⟩
  · rw [cutRank_orIntro] at hr
    disj 4; exact ⟨s, p, q, d₀, rfl, hpq, ⟨hd₀.1, hd₀.2, hr⟩⟩
  · rw [cutRank_allIntro] at hr
    disj 5; exact ⟨s, p, d₀, rfl, hp, ⟨hd₀.1, hd₀.2, hr⟩⟩
  · rw [cutRank_exsIntro] at hr
    disj 6; exact ⟨s, p, t, d₀, rfl, hp, ht, ⟨hd₀.1, hd₀.2, hr⟩⟩
  · rw [cutRank_wkRule] at hr
    disj 7; exact ⟨s, d₀, rfl, hsub, hd₀, hr⟩
  · rw [cutRank_shiftRule] at hr
    disj 8; exact ⟨s, d₀, rfl, hsh, hd₀, hr⟩
  · simp only [cutRank_cutRule, max_le_iff] at hr
    disj 9
    exact ⟨s, p, d₁, d₂, rfl, succ_le_iff_lt.mp hr.2, ⟨hd₁.1, hd₁.2, hr.1.1⟩,
      ⟨hd₂.1, hd₂.2, hr.1.2⟩⟩
  · disj 10; exact h

lemma of_cutFreeDerivation (h : CutFreeDerivation T d) : RankedDerivation T 0 d :=
  ⟨h.toDerivation, by rw [h.cutRank_eq_zero]⟩

/-- A derivation of cut rank `0` is cut-free. -/
lemma toCutFreeDerivation (h : RankedDerivation T 0 d) : CutFreeDerivation T d := by
  obtain ⟨hd, hr⟩ := h
  revert hr
  apply Derivation.induction1 𝚺 (P := fun d ↦ cutRank L d ≤ 0 → CutFreeDerivation T d) ?_ hd
  · intro s hs p hp hn _
    exact CutFreeDerivation.axL hs hp hn
  · intro s hs hv _
    exact CutFreeDerivation.verumIntro hs hv
  · intro s _ p q dp dq hpq hdp hdq ihp ihq hr
    simp only [cutRank_andIntro, max_le_iff] at hr
    exact CutFreeDerivation.andIntro hpq ⟨hdp.1, ihp hr.1⟩ ⟨hdq.1, ihq hr.2⟩
  · intro s _ p q d hpq hd ih hr
    rw [cutRank_orIntro] at hr
    exact CutFreeDerivation.orIntro hpq ⟨hd.1, ih hr⟩
  · intro s _ p d hp hd ih hr
    rw [cutRank_allIntro] at hr
    exact CutFreeDerivation.allIntro hp ⟨hd.1, ih hr⟩
  · intro s _ p t d hp ht hd ih hr
    rw [cutRank_exsIntro] at hr
    exact CutFreeDerivation.exsIntro hp ht ⟨hd.1, ih hr⟩
  · intro s hs d hsd _ ih hr
    rw [cutRank_wkRule] at hr
    exact CutFreeDerivation.wkRule hs hsd ⟨rfl, ih hr⟩
  · rintro _ _ d rfl _ ih hr
    rw [cutRank_shiftRule] at hr
    exact CutFreeDerivation.shiftRule ⟨rfl, ih hr⟩
  · intro s _ p d₁ d₂ _ _ _ _ hr
    simp at hr
  · intro s hs p hp hT _
    exact CutFreeDerivation.axm hs hp hT
  · definability

end RankedDerivation

lemma RankedDerivationOf.isFormulaSet (h : RankedDerivationOf T r d s) : IsFormulaSet L s :=
  h.1 ▸ h.2.isFormulaSet

namespace RankedDerivable

lemma isFormulaSet (h : RankedDerivable T r s) : IsFormulaSet L s := by
  obtain ⟨d, hd⟩ := h
  exact hd.isFormulaSet

lemma of_le (h : RankedDerivable T r s) (hr : r ≤ r') : RankedDerivable T r' s := by
  obtain ⟨d, hd, hd'⟩ := h
  exact ⟨d, hd, hd'.of_le hr⟩

lemma toDerivable (h : RankedDerivable T r s) : Derivable T s := by
  obtain ⟨d, hd, hd'⟩ := h
  exact ⟨d, hd, hd'.1⟩

lemma em (hs : IsFormulaSet L s) (p : V) (h : p ∈ s) (hn : neg L p ∈ s) : RankedDerivable T r s :=
  ⟨_, by simp, Derivation.axL hs h hn, by simp⟩

lemma verum (hs : IsFormulaSet L s) (h : ^⊤ ∈ s) : RankedDerivable T r s :=
  ⟨_, by simp, Derivation.verumIntro hs h, by simp⟩

lemma and_m {p q : V} (h : p ^⋏ q ∈ s) (hp : RankedDerivable T r (insert p s))
    (hq : RankedDerivable T r (insert q s)) : RankedDerivable T r s := by
  obtain ⟨dp, hdp, hdp'⟩ := hp
  obtain ⟨dq, hdq, hdq'⟩ := hq
  exact ⟨_, by simp, Derivation.andIntro h ⟨hdp, hdp'.1⟩ ⟨hdq, hdq'.1⟩,
    by simp [hdp'.2, hdq'.2]⟩

lemma or_m {p q : V} (h : p ^⋎ q ∈ s) (hpq : RankedDerivable T r (insert p (insert q s))) :
    RankedDerivable T r s := by
  obtain ⟨d, hd, hd'⟩ := hpq
  exact ⟨_, by simp, Derivation.orIntro h ⟨hd, hd'.1⟩, by simp [hd'.2]⟩

lemma all_m {p : V} (h : ^∀ p ∈ s) (hp : RankedDerivable T r (insert (free L p) (setShift L s))) :
    RankedDerivable T r s := by
  obtain ⟨d, hd, hd'⟩ := hp
  exact ⟨_, by simp, Derivation.allIntro h ⟨hd, hd'.1⟩, by simp [hd'.2]⟩

lemma ex_m {p t : V} (h : ^∃ p ∈ s) (ht : IsTerm L t)
    (hp : RankedDerivable T r (insert (substs1 L t p) s)) : RankedDerivable T r s := by
  obtain ⟨d, hd, hd'⟩ := hp
  exact ⟨_, by simp, Derivation.exsIntro h ht ⟨hd, hd'.1⟩, by simp [hd'.2]⟩

lemma wk {s' : V} (hs : IsFormulaSet L s) (h : s' ⊆ s) (hd : RankedDerivable T r s') :
    RankedDerivable T r s := by
  obtain ⟨d, rfl, hd'⟩ := hd
  exact ⟨_, by simp, Derivation.wkRule hs h ⟨rfl, hd'.1⟩, by simp [hd'.2]⟩

lemma shift_m (hd : RankedDerivable T r s) : RankedDerivable T r (setShift L s) := by
  obtain ⟨d, rfl, hd'⟩ := hd
  exact ⟨_, by simp, Derivation.shiftRule ⟨rfl, hd'.1⟩, by simp [hd'.2]⟩

/-- A cut on a formula of complexity below `r` keeps the cut rank at most `r`. -/
lemma cut {p : V} (hp : formulaComplexity L p < r) (hd₁ : RankedDerivable T r (insert p s))
    (hd₂ : RankedDerivable T r (insert (neg L p) s)) : RankedDerivable T r s := by
  obtain ⟨d₁, hd₁, hd₁'⟩ := hd₁
  obtain ⟨d₂, hd₂, hd₂'⟩ := hd₂
  have hs : IsFormulaSet L s :=
    (IsFormulaSet.insert_iff.mp (hd₁ ▸ hd₁'.isFormulaSet)).2
  exact ⟨_, by simp, Derivation.cutRule ⟨hd₁, hd₁'.1⟩ ⟨hd₂, hd₂'.1⟩,
    by simp [hd₁'.2, hd₂'.2, succ_le_iff_lt.mpr hp]⟩

lemma iff_cutFreeDerivable : RankedDerivable T 0 s ↔ CutFreeDerivable T s :=
  ⟨fun ⟨d, hd, hd'⟩ ↦ ⟨d, hd, hd'.toCutFreeDerivation⟩,
    fun ⟨d, hd, hd'⟩ ↦ ⟨d, hd, .of_cutFreeDerivation hd'⟩⟩

end RankedDerivable

end RankedDerivation

end FFL.FirstOrder.Arithmetic.Bootstrapping
