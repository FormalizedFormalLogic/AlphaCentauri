module

public import AlphaCentauri.Bootstrapping.Proof.CutFreeRewrite

/-!
# Cut elimination for the internal calculus

This module proves that the cut rule is admissible in the cut-free fragment of Foundation's
internal one-sided calculus over the empty theory, and hence that every internal derivation over
the empty theory has a cut-free counterpart with the same end-sequent. Both hold in every model of
`𝗜𝚺⁺2`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- No formula code is its own negation. -/
private lemma neg_ne_self {p : V} (hp : IsUFormula L p) : neg L p ≠ p := by
  rcases hp.case with (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl |
    ⟨q, r, hq, hr, rfl⟩ | ⟨q, r, hq, hr, rfl⟩ | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
  · rw [neg_rel hR hv]; simp [qqRel, qqNRel]
  · rw [neg_nrel hR hv]; simp [qqRel, qqNRel]
  · rw [neg_verum]; simp [qqVerum, qqFalsum]
  · rw [neg_falsum]; simp [qqVerum, qqFalsum]
  · rw [neg_and hq hr]; simp [qqAnd, qqOr]
  · rw [neg_or hq hr]; simp [qqAnd, qqOr]
  · rw [neg_all hq]; simp [qqAll, qqExs]
  · rw [neg_ex hq]; simp [qqAll, qqExs]

/-- Adding two codes to a coded set does not depend on their order. -/
private lemma insert_comm (x y s : V) : insert x (insert y s) = insert y (insert x s) :=
  mem_ext fun z ↦ by
    simp only [mem_bitInsert_iff]
    tauto

/-- A member of `insert y s` other than `y` is a member of `s`. -/
private lemma mem_of_mem_insert_of_ne {x y s : V} (h : x ∈ insert y s) (hne : x ≠ y) : x ∈ s := by
  rcases mem_bitInsert_iff.mp h with rfl | h
  · exact absurd rfl hne
  · exact h

/-- Adding a code on both sides preserves a sequent being covered by a formula beside a set. -/
private lemma insert_subset_insert_insert {a p Γ s : V} (h : Γ ⊆ insert p s) :
    insert a Γ ⊆ insert p (insert a s) := by
  intro x hx
  rcases mem_bitInsert_iff.mp hx with rfl | hx
  · simp
  · rcases mem_bitInsert_iff.mp (h hx) with rfl | hx
    · simp
    · simp [hx]

/-- The external-variable shift of coded formula sets is monotone. -/
private lemma setShift_subset_setShift {s t : V} (h : s ⊆ t) : setShift L s ⊆ setShift L t := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_setShift_iff.mp hx
  exact shift_mem_setShift (h hy)

/-- A formula code has complexity zero or is existential exactly when its shift does. -/
private lemma complexity_eq_zero_or_exs_shift_iff {p : V} (hp : IsUFormula L p) :
    (formulaComplexity L (shift L p) = 0 ∨ ∃ a < shift L p, shift L p = ^∃ a) ↔
      (formulaComplexity L p = 0 ∨ ∃ a < p, p = ^∃ a) := by
  rw [formulaComplexity_shift hp]
  apply or_congr_right
  constructor
  · rintro ⟨a, -, ha⟩
    obtain ⟨a₀, -, rfl, -⟩ := exists_exs_of_shift_eq_exs hp ha
    exact ⟨a₀, by simp, rfl⟩
  · rintro ⟨a, -, rfl⟩
    have ha : IsUFormula L a := by simpa using hp
    exact ⟨shift L a, by simp [shift_exs ha], shift_exs ha⟩

namespace CutFreeDerivable

variable {T : Theory L} [T.Δ₁]

/-- Adding a formula beside the first one of a cut-free derivable sequent keeps it cut-free
derivable. -/
private lemma wk_insert {x a s : V} (ha : IsFormula L a) (hd : CutFreeDerivable T (insert x s)) :
    CutFreeDerivable T (insert x (insert a s)) := by
  have hs := IsFormulaSet.insert_iff.mp hd.isFormulaSet
  exact hd.wk (by simp [hs.1, hs.2, ha]) (insert_subset_insert_of_subset x (susbset_insert a s))

end CutFreeDerivable

/-- Cut on a conjunction, given cut on every formula of smaller complexity. -/
private lemma cut_and {c q r s : V}
    (ih : ∀ p s : V, formulaComplexity L p < c → CutFreeDerivable (∅ : Theory L) (insert p s) →
      CutFreeDerivable (∅ : Theory L) (insert (neg L p) s) → CutFreeDerivable (∅ : Theory L) s)
    (hc : formulaComplexity L (q ^⋏ r) ≤ c)
    (h₁ : CutFreeDerivable (∅ : Theory L) (insert (q ^⋏ r) s))
    (h₂ : CutFreeDerivable (∅ : Theory L) (insert (neg L (q ^⋏ r)) s)) :
    CutFreeDerivable (∅ : Theory L) s := by
  have hqr : IsFormula L q ∧ IsFormula L r := by
    simpa using (IsFormulaSet.insert_iff.mp h₁.isFormulaSet).1
  rw [neg_and hqr.1.isUFormula hqr.2.isUFormula] at h₂
  rw [formulaComplexity_and hqr.1.isUFormula hqr.2.isUFormula] at hc
  obtain ⟨d₁, hd₁⟩ := h₁
  obtain ⟨d₂, hd₂⟩ := h₂
  obtain ⟨eq, heq, -⟩ := CutFreeDerivation.inversion_and (Or.inl rfl) hd₁
  obtain ⟨er, her, -⟩ := CutFreeDerivation.inversion_and (Or.inr rfl) hd₁
  obtain ⟨e, he, -⟩ := CutFreeDerivation.inversion_or hd₂
  have h₃ : CutFreeDerivable (∅ : Theory L) (insert (neg L q) s) :=
    ih r _ (lt_of_lt_of_le (lt_max_succ_right _ _) hc)
      (CutFreeDerivable.wk_insert hqr.1.neg ⟨er, her⟩) (by rw [insert_comm]; exact ⟨e, he⟩)
  exact ih q s (lt_of_lt_of_le (lt_max_succ_left _ _) hc) ⟨eq, heq⟩ h₃

section

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺2]

/-- A cut on the shift of `p` beside a set `s` covering the shift of a sequent `Δ` containing `p`
reduces to cuts on `p` itself beside sets covering `Δ`. -/
private lemma cut_of_setShift_subset {Δ p s : V} (hΔ : IsFormulaSet L Δ) (hp : p ∈ Δ)
    (hsub : setShift L Δ ⊆ insert (shift L p) s)
    (he : CutFreeDerivable (∅ : Theory L) (insert (neg L (shift L p)) s))
    (ih : ∀ s' e' : V, Δ ⊆ insert p s' →
      CutFreeDerivationOf (∅ : Theory L) e' (insert (neg L p) s') →
      CutFreeDerivable (∅ : Theory L) s') :
    CutFreeDerivable (∅ : Theory L) s := by
  have hsF : IsFormulaSet L s := (IsFormulaSet.insert_iff.mp he.isFormulaSet).2
  have hpF : IsFormula L p := hΔ p hp
  obtain ⟨N, hsN, hΔN, hpN⟩ : ∃ N : V, s ≤ N ∧ Δ ≤ N ∧ neg L p ≤ N :=
    ⟨s + Δ + neg L p, by simp [add_assoc], by simp [add_comm s Δ, add_assoc], by simp⟩
  obtain ⟨w, hw, hvw, hwv⟩ := exists_inverse_freshVec (L := L) N
  have hback : ∀ q, IsFormula L q → q ≤ N → fvSubst L w (shift L q) = q := by
    intro q hq hqN
    rw [← fvSubst_eq_shift (by simp) (fun x hx ↦ nth_freshVec_of_lt hx) hq hqN]
    exact fvSubst_fvSubst_eq_self (isSemitermVec_freshVec N) hvw hq hqN
  have h₁ := CutFreeDerivable.rewrite hw he
  rw [fvSubstImage_insert, ← shift_neg hpF, hback _ hpF.neg hpN] at h₁
  have h₂ : Δ ⊆ insert p (fvSubstImage (L := L) w s) := by
    intro x hx
    have hxN : x ≤ N := le_trans (le_of_lt (lt_of_mem hx)) hΔN
    rcases mem_bitInsert_iff.mp (hsub (shift_mem_setShift hx)) with h | h
    · rw [shift_inj (hΔ x hx).isUFormula hpF.isUFormula h]
      simp
    · exact mem_bitInsert_iff.mpr <| Or.inr <|
        mem_fvSubstImage_iff.mpr ⟨_, h, (hback x (hΔ x hx) hxN).symm⟩
  obtain ⟨e, he⟩ := h₁
  have h₃ := CutFreeDerivable.rewrite (isSemitermVec_freshVec N) (ih _ e h₂ he)
  rwa [fvSubstImage_fvSubstImage_eq_self hw hwv hsF hsN] at h₃

/-- Cut on a formula of complexity zero or on an existential formula of complexity at most `c`,
whose side is covered by the end-sequent of a cut-free derivation code, given cut on every formula
of complexity below `c`. -/
private lemma cut_aux {c : V}
    (hcut : ∀ p s : V, formulaComplexity L p < c → CutFreeDerivable (∅ : Theory L) (insert p s) →
      CutFreeDerivable (∅ : Theory L) (insert (neg L p) s) → CutFreeDerivable (∅ : Theory L) s) :
    ∀ d p s e : V, formulaComplexity L p ≤ c →
      (formulaComplexity L p = 0 ∨ ∃ a < p, p = ^∃ a) →
      CutFreeDerivation (∅ : Theory L) d → fstIdx d ⊆ insert p s →
      CutFreeDerivationOf (∅ : Theory L) e (insert (neg L p) s) →
      CutFreeDerivable (∅ : Theory L) s := by
  have hP : 𝚷ᴬ-[2].DefinablePred fun d : V ↦ ∀ p s e : V, formulaComplexity L p ≤ c →
      (formulaComplexity L p = 0 ∨ ∃ a < p, p = ^∃ a) →
      CutFreeDerivation (∅ : Theory L) d → fstIdx d ⊆ insert p s →
      CutFreeDerivationOf (∅ : Theory L) e (insert (neg L p) s) →
      CutFreeDerivable (∅ : Theory L) s := by
    apply HierarchySymbol.Definable.all
    apply HierarchySymbol.Definable.all
    apply HierarchySymbol.Definable.all
    exact HierarchySymbol.Definable.of_lt (C := 𝚺ᴬ-[1]) (by definability) (by simp)
  intro d
  refine InductionOnHierarchy.order_induction_sigma 𝚷 2 hP ?_ d
  intro d ih p s e hpc hpg hd hsub he
  have ih' : ∀ d₀ < d, ∀ q s₀, formulaComplexity L q ≤ c →
      (formulaComplexity L q = 0 ∨ ∃ a < q, q = ^∃ a) →
      CutFreeDerivation (∅ : Theory L) d₀ → fstIdx d₀ ⊆ insert q s₀ →
      CutFreeDerivable (∅ : Theory L) (insert (neg L q) s₀) →
      CutFreeDerivable (∅ : Theory L) s₀ := by
    rintro d₀ hd₀ q s₀ hqc hqg hd₀' hsub₀ ⟨e₀, he₀⟩
    exact ih d₀ hd₀ q s₀ e₀ hqc hqg hd₀' hsub₀ he₀
  have hsF : IsFormulaSet L s := (IsFormulaSet.insert_iff.mp he.isFormulaSet).2
  have hpF : IsFormula L p := (IsFormulaSet.insert_iff.mp he.isFormulaSet).1.elim_neg
  have hmem : ∀ x ∈ insert p s, formulaComplexity L x ≠ 0 → (∀ a, x ≠ ^∃ a) → x ∈ s := by
    intro x hx h₀ h₁
    refine mem_of_mem_insert_of_ne hx ?_
    rintro rfl
    rcases hpg with h | ⟨a, -, rfl⟩
    · exact h₀ h
    · exact h₁ a rfl
  have hΓF := hd.isFormulaSet
  rcases hd.case.2 with (⟨Γ, r, rfl, hr, hnr⟩ | ⟨Γ, rfl, hv⟩ |
    ⟨Γ, a, b, da, db, rfl, hab, hda, hdb⟩ | ⟨Γ, a, b, d₀, rfl, hab, hd₀⟩ |
    ⟨Γ, a, d₀, rfl, ha, hd₀⟩ | ⟨Γ, a, t, d₀, rfl, ha, ht, hd₀⟩ |
    ⟨Γ, d₀, rfl, hΓ, hd₀⟩ | ⟨Γ, d₀, rfl, hΓ, hd₀⟩ | ⟨Γ, r, rfl, -, hT⟩)
  · rw [fstIdx_axL] at hsub hΓF
    by_cases hn : neg L p ∈ s
    · rw [insert_eq_self_of_mem hn] at he
      exact ⟨e, he⟩
    · have h₁ : r ≠ p := by
        rintro rfl
        exact hn (mem_of_mem_insert_of_ne (hsub hnr) (neg_ne_self hpF.isUFormula))
      have h₂ : neg L r ≠ p := by
        intro h
        have hrp : r = neg L p := by rw [← h, (hΓF r hr).isUFormula.neg_neg]
        exact hn (hrp ▸ mem_of_mem_insert_of_ne (hsub hr) (hrp ▸ neg_ne_self hpF.isUFormula))
      exact ⟨_, by simp, CutFreeDerivation.axL hsF (mem_of_mem_insert_of_ne (hsub hr) h₁)
        (mem_of_mem_insert_of_ne (hsub hnr) h₂)⟩
  · rw [fstIdx_verumIntro] at hsub
    by_cases hv' : (^⊤ : V) ∈ s
    · exact ⟨_, by simp, CutFreeDerivation.verumIntro hsF hv'⟩
    · obtain rfl : (^⊤ : V) = p := by
        rcases mem_bitInsert_iff.mp (hsub hv) with h | h
        · exact h
        · exact absurd h hv'
      rw [neg_verum] at he
      exact CutFreeDerivable.of_insert_falsum ⟨e, he⟩
  · rw [fstIdx_andIntro] at hsub hΓF
    have habF : IsFormula L a ∧ IsFormula L b := by simpa using hΓF _ hab
    have hab' : a ^⋏ b ∈ s := hmem _ (hsub hab)
      (by simp [habF.1.isUFormula, habF.2.isUFormula]) (by simp [qqAnd, qqExs])
    obtain ⟨ea, hea⟩ := ih' da (dp_lt_andIntro _ _ _ _ _) p _ hpc hpg hda.2
      (by rw [hda.1]; exact insert_subset_insert_insert hsub)
      (CutFreeDerivable.wk_insert habF.1 ⟨e, he⟩)
    obtain ⟨eb, heb⟩ := ih' db (dq_lt_andIntro _ _ _ _ _) p _ hpc hpg hdb.2
      (by rw [hdb.1]; exact insert_subset_insert_insert hsub)
      (CutFreeDerivable.wk_insert habF.2 ⟨e, he⟩)
    exact ⟨_, by simp, CutFreeDerivation.andIntro hab' hea heb⟩
  · rw [fstIdx_orIntro] at hsub hΓF
    have habF : IsFormula L a ∧ IsFormula L b := by simpa using hΓF _ hab
    have hab' : a ^⋎ b ∈ s := hmem _ (hsub hab)
      (by simp [habF.1.isUFormula, habF.2.isUFormula]) (by simp [qqOr, qqExs])
    obtain ⟨e₀, he₀⟩ := ih' d₀ (d_lt_orIntro _ _ _ _) p _ hpc hpg hd₀.2
      (by rw [hd₀.1]; exact insert_subset_insert_insert (insert_subset_insert_insert hsub))
      (CutFreeDerivable.wk_insert habF.1 (CutFreeDerivable.wk_insert habF.2 ⟨e, he⟩))
    exact ⟨_, by simp, CutFreeDerivation.orIntro hab' he₀⟩
  · rw [fstIdx_allIntro] at hsub hΓF
    have haF : IsSemiformula L 1 a := by simpa using hΓF _ ha
    have ha' : ^∀ a ∈ s := hmem _ (hsub ha) (by simp [haF.isUFormula]) (by simp [qqAll, qqExs])
    have hfree : IsFormula L (free L a) := (IsFormulaSet.insert_iff.mp hd₀.isFormulaSet).1
    have hsh : CutFreeDerivable (∅ : Theory L) (setShift L (insert (neg L p) s)) :=
      ⟨_, by simp, CutFreeDerivation.shiftRule he⟩
    rw [mem_setShift_insert, shift_neg hpF] at hsh
    obtain ⟨e₀, he₀⟩ := ih' d₀ (s_lt_allIntro _ _ _) (shift L p) _
      (by rwa [formulaComplexity_shift hpF.isUFormula])
      ((complexity_eq_zero_or_exs_shift_iff hpF.isUFormula).mpr hpg) hd₀.2
      (by
        rw [hd₀.1]
        apply insert_subset_insert_insert
        rw [← mem_setShift_insert]
        exact setShift_subset_setShift hsub)
      (CutFreeDerivable.wk_insert hfree hsh)
    exact ⟨_, by simp, CutFreeDerivation.allIntro ha' he₀⟩
  · rw [fstIdx_exsIntro] at hsub hΓF
    have haF : IsSemiformula L 1 a := by simpa using hΓF _ ha
    have h₁ := ih' d₀ (d_lt_exsIntro _ _ _ _) p _ hpc hpg hd₀.2
      (by rw [hd₀.1]; exact insert_subset_insert_insert hsub)
      (CutFreeDerivable.wk_insert (haF.substs1 ht) ⟨e, he⟩)
    by_cases hap : ^∃ a = p
    · subst hap
      rw [neg_ex haF.isUFormula] at he
      rw [formulaComplexity_ex haF.isUFormula] at hpc
      have h₂ := CutFreeDerivation.inversion_all ht he
      rw [show substs1 L t (neg L a) = neg L (substs1 L t a) from
        substs_neg haF (by simp [ht] : IsSemitermVec L 1 0 (?[t] : V))] at h₂
      exact hcut _ s (by rw [fomulaComplexity_substs1 haF ht]; exact lt_of_lt_of_le (by simp) hpc)
        h₁ h₂
    · obtain ⟨e₀, he₀⟩ := h₁
      exact ⟨_, by simp, CutFreeDerivation.exsIntro (mem_of_mem_insert_of_ne (hsub ha) hap) ht he₀⟩
  · rw [fstIdx_wkRule] at hsub
    exact ih' d₀ (d_lt_wkRule _ _) p s hpc hpg hd₀ (fun x hx ↦ hsub (hΓ hx)) ⟨e, he⟩
  · rw [fstIdx_shiftRule] at hsub
    subst hΓ
    by_cases hp' : p ∈ setShift L (fstIdx d₀)
    · obtain ⟨p₀, hp₀, rfl⟩ := mem_setShift_iff.mp hp'
      have hp₀F : IsUFormula L p₀ := (hd₀.isFormulaSet p₀ hp₀).isUFormula
      exact cut_of_setShift_subset hd₀.isFormulaSet hp₀ hsub ⟨e, he⟩ fun s' e' hs' he' ↦
        ih d₀ (d_lt_shiftRule _ _) p₀ s' e' (by rwa [formulaComplexity_shift hp₀F] at hpc)
          ((complexity_eq_zero_or_exs_shift_iff hp₀F).mp hpg) hd₀ hs' he'
    · refine ⟨_, by simp, CutFreeDerivation.wkRule hsF ?_ ⟨rfl, hd⟩⟩
      intro x hx
      rw [fstIdx_shiftRule] at hx
      exact mem_of_mem_insert_of_ne (hsub hx) (by rintro rfl; exact hp' hx)
  · exact absurd hT (not_mem_empty_Δ₁Class r)

/-- Cut on a formula of complexity `c`, for every `c`. -/
private lemma cut_complexity :
    ∀ c p s d₁ d₂ : V, formulaComplexity L p = c →
      CutFreeDerivationOf (∅ : Theory L) d₁ (insert p s) →
      CutFreeDerivationOf (∅ : Theory L) d₂ (insert (neg L p) s) →
      CutFreeDerivable (∅ : Theory L) s := by
  have hP : 𝚷ᴬ-[2].DefinablePred fun c : V ↦ ∀ p s d₁ d₂ : V, formulaComplexity L p = c →
      CutFreeDerivationOf (∅ : Theory L) d₁ (insert p s) →
      CutFreeDerivationOf (∅ : Theory L) d₂ (insert (neg L p) s) →
      CutFreeDerivable (∅ : Theory L) s := by
    apply HierarchySymbol.Definable.all
    apply HierarchySymbol.Definable.all
    apply HierarchySymbol.Definable.all
    apply HierarchySymbol.Definable.all
    exact HierarchySymbol.Definable.of_lt (C := 𝚺ᴬ-[1]) (by definability) (by simp)
  intro c
  refine InductionOnHierarchy.order_induction_sigma 𝚷 2 hP ?_ c
  intro c ih p s d₁ d₂ hpc hd₁ hd₂
  have hcut : ∀ q s : V, formulaComplexity L q < c →
      CutFreeDerivable (∅ : Theory L) (insert q s) →
      CutFreeDerivable (∅ : Theory L) (insert (neg L q) s) → CutFreeDerivable (∅ : Theory L) s := by
    rintro q s hq ⟨e₁, he₁⟩ ⟨e₂, he₂⟩
    exact ih _ hq q s e₁ e₂ rfl he₁ he₂
  have hsub₁ : fstIdx d₁ ⊆ insert p s := by rw [hd₁.1]
  have hpF : IsUFormula L p := (IsFormulaSet.insert_iff.mp hd₁.isFormulaSet).1.isUFormula
  rcases hpF.case with (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl |
    ⟨q, r, hq, hr, rfl⟩ | ⟨q, r, hq, hr, rfl⟩ | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
  · exact cut_aux hcut d₁ _ s d₂ hpc.le (Or.inl (by simp [hR, hv])) hd₁.2 hsub₁ hd₂
  · exact cut_aux hcut d₁ _ s d₂ hpc.le (Or.inl (by simp [hR, hv])) hd₁.2 hsub₁ hd₂
  · exact cut_aux hcut d₁ _ s d₂ hpc.le (Or.inl (by simp)) hd₁.2 hsub₁ hd₂
  · exact cut_aux hcut d₁ _ s d₂ hpc.le (Or.inl (by simp)) hd₁.2 hsub₁ hd₂
  · exact cut_and hcut hpc.le ⟨d₁, hd₁⟩ ⟨d₂, hd₂⟩
  · rw [neg_or hq hr] at hd₂
    have h₁ : CutFreeDerivable (∅ : Theory L) (insert (neg L (neg L q ^⋏ neg L r)) s) := by
      rw [neg_and hq.neg hr.neg, hq.neg_neg, hr.neg_neg]
      exact ⟨d₁, hd₁⟩
    exact cut_and hcut (by simpa [hq, hr, hq.neg, hr.neg] using hpc.le) ⟨d₂, hd₂⟩ h₁
  · rw [neg_all hq] at hd₂
    have hsub₂ : fstIdx d₂ ⊆ insert (^∃ neg L q) s := by rw [hd₂.1]
    have hd₁' : CutFreeDerivationOf (∅ : Theory L) d₁ (insert (neg L (^∃ neg L q)) s) := by
      rwa [neg_ex hq.neg, hq.neg_neg]
    exact cut_aux hcut d₂ _ s d₁ (by simpa [hq, hq.neg] using hpc.le)
      (Or.inr ⟨neg L q, by simp, rfl⟩) hd₂.2 hsub₂ hd₁'
  · exact cut_aux hcut d₁ _ s d₂ hpc.le (Or.inr ⟨q, by simp, rfl⟩) hd₁.2 hsub₁ hd₂

/-- The cut rule is admissible in the cut-free calculus over the empty theory.
- [Bus98, Lemma 2.4.2.1] -/
theorem CutFreeDerivable.cut {p s : V} (h₁ : CutFreeDerivable (∅ : Theory L) (insert p s))
    (h₂ : CutFreeDerivable (∅ : Theory L) (insert (neg L p) s)) :
    CutFreeDerivable (∅ : Theory L) s := by
  obtain ⟨d₁, hd₁⟩ := h₁
  obtain ⟨d₂, hd₂⟩ := h₂
  exact cut_complexity _ p s d₁ d₂ rfl hd₁ hd₂

/-- Cut elimination: every sequent derivable over the empty theory is cut-free derivable.
- [Bus98, Theorem 2.4.2]
- [AB05, Theorem 152] -/
theorem Derivable.cutFree {s : V} (h : Derivable (∅ : Theory L) s) :
    CutFreeDerivable (∅ : Theory L) s := by
  obtain ⟨d, rfl, hd⟩ := h
  apply Derivation.induction1 𝚺 (P := fun d ↦ CutFreeDerivable (∅ : Theory L) (fstIdx d)) ?_ hd
  · intro s hs p hp hn
    rw [fstIdx_axL]
    exact ⟨_, by simp, CutFreeDerivation.axL hs hp hn⟩
  · intro s hs hv
    rw [fstIdx_verumIntro]
    exact ⟨_, by simp, CutFreeDerivation.verumIntro hs hv⟩
  · intro s _ p q dp dq hpq hdp hdq ihp ihq
    rw [hdp.1] at ihp
    rw [hdq.1] at ihq
    obtain ⟨ep, hep⟩ := ihp
    obtain ⟨eq, heq⟩ := ihq
    rw [fstIdx_andIntro]
    exact ⟨_, by simp, CutFreeDerivation.andIntro hpq hep heq⟩
  · intro s _ p q d hpq hd ih
    rw [hd.1] at ih
    obtain ⟨e, he⟩ := ih
    rw [fstIdx_orIntro]
    exact ⟨_, by simp, CutFreeDerivation.orIntro hpq he⟩
  · intro s _ p d hp hd ih
    rw [hd.1] at ih
    obtain ⟨e, he⟩ := ih
    rw [fstIdx_allIntro]
    exact ⟨_, by simp, CutFreeDerivation.allIntro hp he⟩
  · intro s _ p t d hp ht hd ih
    rw [hd.1] at ih
    obtain ⟨e, he⟩ := ih
    rw [fstIdx_exsIntro]
    exact ⟨_, by simp, CutFreeDerivation.exsIntro hp ht he⟩
  · intro s hs d hsub _ ih
    rw [fstIdx_wkRule]
    exact ih.wk hs hsub
  · rintro s _ d rfl _ ih
    obtain ⟨e, he⟩ := ih
    rw [fstIdx_shiftRule]
    exact ⟨_, by simp, CutFreeDerivation.shiftRule he⟩
  · intro s _ p d₁ d₂ hd₁ hd₂ ih₁ ih₂
    rw [hd₁.1] at ih₁
    rw [hd₂.1] at ih₂
    rw [fstIdx_cutRule]
    exact CutFreeDerivable.cut ih₁ ih₂
  · intro s _ p _ hT
    exact absurd hT (not_mem_empty_Δ₁Class p)
  · definability

end

end FFL.FirstOrder.Arithmetic.Bootstrapping
