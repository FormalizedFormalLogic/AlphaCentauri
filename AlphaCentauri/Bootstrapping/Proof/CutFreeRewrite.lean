module

public import AlphaCentauri.Bootstrapping.Proof.Inversion
public import AlphaCentauri.Bootstrapping.Proof.Substitution

/-!
# Free-variable substitution and universal inversion for cut-free derivations

This module shows that cut-free derivability over the empty theory is closed under substituting
closed terms for free variables, that the universal rule is invertible with an arbitrary closed
term as the instance, and that `⊥` can be deleted from a cut-free derivable sequent.  The first two
hold in every model of `𝗜𝚺⁺2`, the last in every model of `𝗜𝚺₁`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- Adding two codes to a coded set does not depend on their order. -/
private lemma insert_comm (x y s : V) : insert x (insert y s) = insert y (insert x s) :=
  mem_ext fun z ↦ by
    simp only [mem_bitInsert_iff]
    tauto

/-- Adding the same code twice to a coded set is adding it once. -/
private lemma insert_insert_self (x s : V) : insert x (insert x s) = insert x s :=
  mem_ext fun z ↦ by
    simp only [mem_bitInsert_iff]
    tauto

/-- A member of `insert y s` other than `y` is a member of `s`. -/
private lemma mem_of_mem_insert_of_ne {x y s : V} (h : x ∈ insert y s) (hne : x ≠ y) : x ∈ s := by
  rcases mem_bitInsert_iff.mp h with rfl | h
  · exact absurd rfl hne
  · exact h

/-- The rest of an end-sequent split off by `insert` is bounded by the proof code. -/
private lemma le_of_fstIdx_eq_insert {d x s : V} (h : fstIdx d = insert x s) : s ≤ d :=
  le_trans (le_of_subset (by rw [h]; exact susbset_insert x s)) (fstIdx_le d)

/-- The body and the rest of an end-sequent containing a universal formula are bounded by the
proof code. -/
private lemma all_bounds {d p s : V} (h : fstIdx d = insert (^∀ p) s) : p ≤ d ∧ s ≤ d := by
  have hp : ^∀ p ∈ fstIdx d := by rw [h]; simp
  exact ⟨le_of_lt <| lt_of_lt_of_le (lt_trans (by simp) (lt_of_mem hp)) (fstIdx_le d),
    le_of_fstIdx_eq_insert h⟩

/-- The substitution of a member of a coded formula set is a member of its image. -/
private lemma fvSubst_mem_fvSubstImage {w q s : V} (h : q ∈ s) :
    fvSubst L w q ∈ fvSubstImage (L := L) w s :=
  mem_fvSubstImage_iff.mpr ⟨q, h, rfl⟩

namespace CutFreeDerivable

/-- The $\Sigma_1$ form of the deletion of `⊥` that the course-of-values induction proves. -/
private lemma of_insert_falsum_aux :
    ∀ d : V, ∀ s ≤ d, CutFreeDerivationOf (∅ : Theory L) d (insert ^⊥ s) →
      CutFreeDerivable (∅ : Theory L) s := by
  have hP : 𝚺ᴬ₁-Predicate fun d : V ↦ ∀ s ≤ d,
      CutFreeDerivationOf (∅ : Theory L) d (insert ^⊥ s) → CutFreeDerivable (∅ : Theory L) s := by
    definability
  intro d
  refine ISigma1.order_induction 𝚺 hP ?_ d
  intro d ih
  have ih' : ∀ d₀ < d, ∀ s₀, CutFreeDerivationOf (∅ : Theory L) d₀ (insert ^⊥ s₀) →
      CutFreeDerivable (∅ : Theory L) s₀ :=
    fun d₀ hd₀ s₀ h ↦ ih d₀ hd₀ s₀ (le_of_fstIdx_eq_insert h.1) h
  rintro s - ⟨hd1, hd2⟩
  have hfs : IsFormulaSet L (insert ^⊥ s) := hd1 ▸ hd2.isFormulaSet
  have hsF : IsFormulaSet L s := fun x hx ↦ hfs x (by simp [hx])
  have hvf : (^⊤ : V) ≠ ^⊥ := by simp [qqVerum, qqFalsum]
  rcases hd2.case.2 with (⟨s₀, r, rfl, hrs, hnrs⟩ | ⟨s₀, rfl, hv⟩ |
    ⟨s₀, a, b, dp, dq, rfl, hab, hdp, hdq⟩ | ⟨s₀, a, b, d₀, rfl, hab, hd₀⟩ |
    ⟨s₀, a, d₀, rfl, ha, hd₀⟩ | ⟨s₀, a, t, d₀, rfl, ha, ht, hd₀⟩ |
    ⟨s₀, d₀, rfl, hsub, hd₀⟩ | ⟨s₀, d₀, rfl, hsh, hd₀⟩ | ⟨s₀, r, rfl, -, hT⟩)
  · rw [fstIdx_axL] at hd1
    subst hd1
    by_cases hv : (^⊤ : V) ∈ s
    · exact ⟨_, by simp, CutFreeDerivation.verumIntro hsF hv⟩
    · have hr : r ≠ ^⊥ := by
        rintro rfl
        rw [neg_falsum] at hnrs
        exact hv (mem_of_mem_insert_of_ne hnrs hvf)
      have hnr : neg L r ≠ ^⊥ := by
        intro h
        have : r = ^⊤ := by rw [← (hfs r hrs).isUFormula.neg_neg, h, neg_falsum]
        exact hv (mem_of_mem_insert_of_ne (this ▸ hrs) hvf)
      exact ⟨_, by simp, CutFreeDerivation.axL hsF (mem_of_mem_insert_of_ne hrs hr)
        (mem_of_mem_insert_of_ne hnrs hnr)⟩
  · rw [fstIdx_verumIntro] at hd1
    subst hd1
    exact ⟨_, by simp, CutFreeDerivation.verumIntro hsF (mem_of_mem_insert_of_ne hv hvf)⟩
  · rw [fstIdx_andIntro] at hd1
    subst hd1
    rw [insert_comm] at hdp hdq
    obtain ⟨ep, hep⟩ := ih' dp (dp_lt_andIntro _ _ _ _ _) _ hdp
    obtain ⟨eq, heq⟩ := ih' dq (dq_lt_andIntro _ _ _ _ _) _ hdq
    exact ⟨_, by simp, CutFreeDerivation.andIntro
      (mem_of_mem_insert_of_ne hab (by simp [qqAnd, qqFalsum])) hep heq⟩
  · rw [fstIdx_orIntro] at hd1
    subst hd1
    rw [insert_comm b, insert_comm a] at hd₀
    obtain ⟨e, he⟩ := ih' d₀ (d_lt_orIntro _ _ _ _) _ hd₀
    exact ⟨_, by simp, CutFreeDerivation.orIntro
      (mem_of_mem_insert_of_ne hab (by simp [qqOr, qqFalsum])) he⟩
  · rw [fstIdx_allIntro] at hd1
    subst hd1
    rw [mem_setShift_insert, shift_falsum, insert_comm] at hd₀
    obtain ⟨e, he⟩ := ih' d₀ (s_lt_allIntro _ _ _) _ hd₀
    exact ⟨_, by simp, CutFreeDerivation.allIntro
      (mem_of_mem_insert_of_ne ha (by simp [qqAll, qqFalsum])) he⟩
  · rw [fstIdx_exsIntro] at hd1
    subst hd1
    rw [insert_comm] at hd₀
    obtain ⟨e, he⟩ := ih' d₀ (d_lt_exsIntro _ _ _ _) _ hd₀
    exact ⟨_, by simp, CutFreeDerivation.exsIntro
      (mem_of_mem_insert_of_ne ha (by simp [qqExs, qqFalsum])) ht he⟩
  · rw [fstIdx_wkRule] at hd1
    subst hd1
    by_cases hf : (^⊥ : V) ∈ fstIdx d₀
    · obtain ⟨e, he⟩ :=
        ih' d₀ (d_lt_wkRule _ _) (bitRemove ^⊥ (fstIdx d₀)) ⟨(insert_remove hf).symm, hd₀⟩
      refine ⟨_, by simp, CutFreeDerivation.wkRule hsF ?_ he⟩
      intro x hx
      have hx' := mem_bitRemove_iff.mp hx
      exact mem_of_mem_insert_of_ne (hsub hx'.2) hx'.1
    · refine ⟨_, by simp, CutFreeDerivation.wkRule hsF ?_ ⟨rfl, hd₀⟩⟩
      intro x hx
      exact mem_of_mem_insert_of_ne (hsub hx) (by rintro rfl; exact hf hx)
  · rw [fstIdx_shiftRule] at hd1
    subst hd1
    have hΔ := hd₀.isFormulaSet
    obtain ⟨r, hr, hre⟩ :=
      mem_setShift_iff.mp (show (^⊥ : V) ∈ setShift L (fstIdx d₀) by rw [← hsh]; simp)
    obtain rfl : r = ^⊥ := shift_inj (hΔ r hr).isUFormula (by simp) (by rw [← hre, shift_falsum])
    obtain ⟨e, he⟩ :=
      ih' d₀ (d_lt_shiftRule _ _) (bitRemove ^⊥ (fstIdx d₀)) ⟨(insert_remove hr).symm, hd₀⟩
    refine ⟨_, by simp, CutFreeDerivation.wkRule hsF ?_ ⟨rfl, CutFreeDerivation.shiftRule he⟩⟩
    rw [fstIdx_shiftRule, setShift_bitRemove hΔ (by simp), shift_falsum, ← hsh]
    intro x hx
    have hx' := mem_bitRemove_iff.mp hx
    exact mem_of_mem_insert_of_ne hx'.2 hx'.1
  · exact absurd hT (not_mem_empty_Δ₁Class r)

/-- Deleting `⊥` from a cut-free derivable sequent over the empty theory leaves it cut-free
derivable. -/
theorem of_insert_falsum {s : V} (h : CutFreeDerivable (∅ : Theory L) (insert ^⊥ s)) :
    CutFreeDerivable (∅ : Theory L) s := by
  obtain ⟨d, hd⟩ := h
  exact of_insert_falsum_aux d s (le_of_fstIdx_eq_insert hd.1) hd

section

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺2]

/-- The $\Pi_2$ form of the substitution for free variables that the course-of-values induction
proves. -/
private lemma rewrite_aux :
    ∀ d : V, ∀ w, IsSemitermVec L (len w) 0 w → CutFreeDerivation (∅ : Theory L) d →
      CutFreeDerivable (∅ : Theory L) (fvSubstImage (L := L) w (fstIdx d)) := by
  have hP : 𝚷ᴬ-[2].DefinablePred fun d : V ↦ ∀ w, IsSemitermVec L (len w) 0 w →
      CutFreeDerivation (∅ : Theory L) d →
      CutFreeDerivable (∅ : Theory L) (fvSubstImage (L := L) w (fstIdx d)) := by
    apply HierarchySymbol.Definable.all
    exact HierarchySymbol.Definable.of_lt (C := 𝚺ᴬ-[1]) (by definability) (by simp)
  intro d
  refine InductionOnHierarchy.order_induction_sigma 𝚷 2 hP ?_ d
  intro d ih w hw hd
  have hsF := hd.isFormulaSet
  rcases hd.case.2 with (⟨s, p, rfl, hp, hnp⟩ | ⟨s, rfl, hv⟩ |
    ⟨s, p, q, dp, dq, rfl, hpq, hdp, hdq⟩ | ⟨s, p, q, d₀, rfl, hpq, hd₀⟩ |
    ⟨s, p, d₀, rfl, hp, hd₀⟩ | ⟨s, p, t, d₀, rfl, hp, ht, hd₀⟩ |
    ⟨s, d₀, rfl, hsub, hd₀⟩ | ⟨s, d₀, rfl, rfl, hd₀⟩ | ⟨s, p, rfl, -, hT⟩)
  · rw [fstIdx_axL] at hsF ⊢
    refine ⟨_, by simp, CutFreeDerivation.axL (formulaSet_fvSubstImage hw hsF)
      (fvSubst_mem_fvSubstImage hp) ?_⟩
    rw [← fvSubst_neg hw (hsF p hp)]
    exact fvSubst_mem_fvSubstImage hnp
  · rw [fstIdx_verumIntro] at hsF ⊢
    exact ⟨_, by simp, CutFreeDerivation.verumIntro (formulaSet_fvSubstImage hw hsF)
      (by simpa using fvSubst_mem_fvSubstImage (L := L) (w := w) hv)⟩
  · rw [fstIdx_andIntro] at hsF ⊢
    have hpqF : IsFormula L p ∧ IsFormula L q := by simpa using hsF _ hpq
    obtain ⟨ep, hep⟩ := ih dp (dp_lt_andIntro _ _ _ _ _) w hw hdp.2
    obtain ⟨eq, heq⟩ := ih dq (dq_lt_andIntro _ _ _ _ _) w hw hdq.2
    rw [hdp.1, fvSubstImage_insert] at hep
    rw [hdq.1, fvSubstImage_insert] at heq
    have h := fvSubst_mem_fvSubstImage (L := L) (w := w) hpq
    rw [fvSubst_and hpqF.1.isUFormula hpqF.2.isUFormula] at h
    exact ⟨_, by simp, CutFreeDerivation.andIntro h hep heq⟩
  · rw [fstIdx_orIntro] at hsF ⊢
    have hpqF : IsFormula L p ∧ IsFormula L q := by simpa using hsF _ hpq
    obtain ⟨e, he⟩ := ih d₀ (d_lt_orIntro _ _ _ _) w hw hd₀.2
    rw [hd₀.1, fvSubstImage_insert, fvSubstImage_insert] at he
    have h := fvSubst_mem_fvSubstImage (L := L) (w := w) hpq
    rw [fvSubst_or hpqF.1.isUFormula hpqF.2.isUFormula] at h
    exact ⟨_, by simp, CutFreeDerivation.orIntro h he⟩
  · rw [fstIdx_allIntro] at hsF ⊢
    have hpF : IsSemiformula L 1 p := by simpa using hsF _ hp
    have hw' : IsSemitermVec L (len (^&0 ∷ termShiftVec L (len w) w)) 0
        (^&0 ∷ termShiftVec L (len w) w) := by
      simp [hw.isUTerm, hw.termShiftVec]
    obtain ⟨e, he⟩ := ih d₀ (s_lt_allIntro _ _ _) _ hw' hd₀.2
    rw [hd₀.1, fvSubstImage_insert, ← free_fvSubst hw hpF, ← setShift_fvSubstImage hw hsF] at he
    have h := fvSubst_mem_fvSubstImage (L := L) (w := w) hp
    rw [fvSubst_all hpF.isUFormula] at h
    exact ⟨_, by simp, CutFreeDerivation.allIntro h he⟩
  · rw [fstIdx_exsIntro] at hsF ⊢
    have hpF : IsSemiformula L 1 p := by simpa using hsF _ hp
    obtain ⟨e, he⟩ := ih d₀ (d_lt_exsIntro _ _ _ _) w hw hd₀.2
    rw [hd₀.1, fvSubstImage_insert, fvSubst_substs1 hw ht hpF] at he
    have h := fvSubst_mem_fvSubstImage (L := L) (w := w) hp
    rw [fvSubst_exs hpF.isUFormula] at h
    exact ⟨_, by simp, CutFreeDerivation.exsIntro h (ht.termFvSubst hw) he⟩
  · rw [fstIdx_wkRule] at hsF ⊢
    obtain ⟨e, he⟩ := ih d₀ (d_lt_wkRule _ _) w hw hd₀
    refine ⟨_, by simp, CutFreeDerivation.wkRule (formulaSet_fvSubstImage hw hsF) ?_ he⟩
    intro x hx
    obtain ⟨q, hq, rfl⟩ := mem_fvSubstImage_iff.mp hx
    exact fvSubst_mem_fvSubstImage (hsub hq)
  · rw [fstIdx_shiftRule]
    obtain ⟨v, hvl, hv⟩ := sigmaOne_skolem_vec
      (R := fun x y : V ↦ (x + 1 < len w → y = w.[x + 1]) ∧ (len w ≤ x + 1 → y = ^&(x + 1)))
      (by definability) (l := d₀)
      (fun x _ ↦ ⟨termFvSubst L w ^&(x + 1), fun h ↦ by simp [h], fun h ↦ by simp [not_lt.mpr h]⟩)
    replace hv : ∀ x < d₀, v.[x] = termFvSubst L w ^&(x + 1) := by
      intro x hx
      rw [termFvSubst_fvar]
      split_ifs with h
      · exact (hv x hx).1 h
      · exact (hv x hx).2 (not_lt.mp h)
    have hvc : IsSemitermVec L (len v) 0 v := IsSemitermVec.iff.mpr ⟨rfl, fun i hi ↦ by
      rw [hv i (by rwa [hvl] at hi)]
      exact IsSemiterm.termFvSubst hw (by simp)⟩
    obtain ⟨e, he⟩ := ih d₀ (d_lt_shiftRule _ _) v hvc hd₀
    rw [← fvSubstImage_setShift (fun x hx ↦ ⟨by rwa [hvl], hv x hx⟩) hd₀.isFormulaSet
      (fstIdx_le d₀)] at he
    exact ⟨e, he⟩
  · exact absurd hT (not_mem_empty_Δ₁Class p)

/-- Cut-free derivability over the empty theory is closed under substituting closed terms for
free variables.
- [Bus98, Ch. I §2.3.4] -/
theorem rewrite {w s : V} (hw : IsSemitermVec L (len w) 0 w)
    (h : CutFreeDerivable (∅ : Theory L) s) :
    CutFreeDerivable (∅ : Theory L) (fvSubstImage (L := L) w s) := by
  obtain ⟨d, rfl, hd⟩ := h
  exact rewrite_aux d w hw hd

/-- From the free instance of `p` beside the shifted sequent, the instance of `p` at a closed term
beside the sequent itself. -/
private lemma substs1_of_free {t p s : V} (ht : IsTerm L t) (hp : IsSemiformula L 1 p)
    (hs : IsFormulaSet L s)
    (h : CutFreeDerivable (∅ : Theory L) (insert (free L p) (setShift L s))) :
    CutFreeDerivable (∅ : Theory L) (insert (substs1 L t p) s) := by
  obtain ⟨ι, hιl, hι⟩ := sigmaOne_skolem_vec (R := fun x y : V ↦ y = ^&x) (by definability)
    (l := p + s) (fun x _ ↦ ⟨_, rfl⟩)
  have hιc : IsSemitermVec L (len ι) 0 ι := IsSemitermVec.iff.mpr ⟨rfl, fun i hi ↦ by
    rw [hι i (by rwa [hιl] at hi)]
    simp⟩
  have hu : IsSemitermVec L (len (t ∷ ι)) 0 (t ∷ ι) := by simp [hιc, ht]
  have h₀ : termFvSubst L (t ∷ ι) ^&0 = t := by simp
  have h₁ : ∀ x < p + s, x < len ι ∧ ι.[x] = termFvSubst L (t ∷ ι) ^&(x + 1) := by
    intro x hx
    have hx' : x < len ι := by rwa [hιl]
    exact ⟨hx', by simp [hx']⟩
  have h₂ : ∀ x < p + s, x < len ι ∧ ι.[x] = ^&x := fun x hx ↦ ⟨by rwa [hιl], hι x hx⟩
  have := rewrite hu h
  rwa [fvSubstImage_insert, free,
    fvSubst_substs1 hu (by simp : IsSemiterm L 0 (^&0 : V)) hp.shift, h₀,
    fvSubst_shift h₁ hp (by simp), fvSubst_eq_self h₂ hp (by simp),
    fvSubstImage_setShift h₁ hs (by simp), fvSubstImage_eq_self h₂ hs (by simp)] at this

/-- From the instance of `p` at a free variable `^&M` above the codes of `p` and of the sequent,
the instance of the shift of `p` at a closed term beside the shifted sequent. -/
private lemma shift_substs1_of_fvar {M t p s : V} (ht : IsTerm L t) (hp : IsSemiformula L 1 p)
    (hpM : p ≤ M) (hs : IsFormulaSet L s) (hsM : s ≤ M)
    (h : CutFreeDerivable (∅ : Theory L) (insert (substs1 L ^&M p) s)) :
    CutFreeDerivable (∅ : Theory L) (insert (substs1 L t (shift L p)) (setShift L s)) := by
  obtain ⟨w, hwl, hw⟩ := sigmaOne_skolem_vec
    (R := fun x y : V ↦ (x < M → y = ^&(x + 1)) ∧ (M ≤ x → y = t)) (by definability)
    (l := M + 1) (fun x _ ↦ by
      by_cases hx : x < M
      · exact ⟨^&(x + 1), fun _ ↦ rfl, fun h ↦ absurd hx (not_lt.mpr h)⟩
      · exact ⟨t, fun h ↦ absurd h hx, fun _ ↦ rfl⟩)
  have hM : M < len w := by simp [hwl]
  have hw₁ : ∀ x < M, w.[x] = ^&(x + 1) := fun x hx ↦ (hw x (lt_trans hx (by simp))).1 hx
  have hwc : IsSemitermVec L (len w) 0 w := IsSemitermVec.iff.mpr ⟨rfl, fun i hi ↦ by
    rcases lt_or_ge i M with hiM | hiM
    · rw [hw₁ i hiM]
      simp
    · rw [(hw i (by rwa [hwl] at hi)).2 hiM]
      exact ht⟩
  have := rewrite hwc h
  rwa [fvSubstImage_insert, fvSubst_substs1 hwc (by simp : IsSemiterm L 0 (^&M : V)) hp,
    termFvSubst_fvar, ite_eq_left hM, (hw M (by simp)).2 le_rfl, fvSubst_eq_shift hM hw₁ hp hpM,
    fvSubstImage_eq_setShift hM hw₁ hs hsM] at this

end

end CutFreeDerivable

namespace CutFreeDerivation

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺2]

/-- The $\Pi_2$ form of the universal inversion that the course-of-values induction proves. -/
private lemma inversion_all_aux :
    ∀ d : V, ∀ t, ∀ p ≤ d, ∀ s ≤ d, IsTerm L t →
      CutFreeDerivationOf (∅ : Theory L) d (insert (^∀ p) s) →
      CutFreeDerivable (∅ : Theory L) (insert (substs1 L t p) s) := by
  have hP : 𝚷ᴬ-[2].DefinablePred fun d : V ↦ ∀ t, ∀ p ≤ d, ∀ s ≤ d, IsTerm L t →
      CutFreeDerivationOf (∅ : Theory L) d (insert (^∀ p) s) →
      CutFreeDerivable (∅ : Theory L) (insert (substs1 L t p) s) := by
    apply HierarchySymbol.Definable.all
    exact HierarchySymbol.Definable.of_lt (C := 𝚺ᴬ-[1]) (by definability) (by simp)
  intro d
  refine InductionOnHierarchy.order_induction_sigma 𝚷 2 hP ?_ d
  intro d ih
  rintro t p - s - ht ⟨hd1, hd2⟩
  have ih' : ∀ d₀ < d, ∀ t₀ p₀ s₀, IsTerm L t₀ →
      CutFreeDerivationOf (∅ : Theory L) d₀ (insert (^∀ p₀) s₀) →
      CutFreeDerivable (∅ : Theory L) (insert (substs1 L t₀ p₀) s₀) :=
    fun d₀ hd₀ t₀ p₀ s₀ ht₀ h ↦ ih d₀ hd₀ t₀ p₀ (all_bounds h.1).1 s₀ (all_bounds h.1).2 ht₀ h
  have hfs : IsFormulaSet L (insert (^∀ p) s) := hd1 ▸ hd2.isFormulaSet
  have hpF : IsSemiformula L 1 p := by simpa using hfs (^∀ p) (by simp)
  have hsF : IsFormulaSet L s := fun x hx ↦ hfs x (by simp [hx])
  have hT : IsFormulaSet L (insert (substs1 L t p) s) := by simp [hsF, hpF.substs1 ht]
  rcases hd2.case.2 with (⟨Γ, r, rfl, hrs, hnrs⟩ | ⟨Γ, rfl, hv⟩ |
    ⟨Γ, a, b, dp, dq, rfl, hab, hdp, hdq⟩ | ⟨Γ, a, b, d₀, rfl, hab, hd₀⟩ |
    ⟨Γ, a, d₀, rfl, ha, hd₀⟩ | ⟨Γ, a, u, d₀, rfl, ha, hu, hd₀⟩ |
    ⟨Γ, d₀, rfl, hsub, hd₀⟩ | ⟨Γ, d₀, rfl, hsh, hd₀⟩ | ⟨Γ, r, rfl, -, hr⟩)
  · rw [fstIdx_axL] at hd1
    subst hd1
    by_cases hex : ^∃ (neg L p) ∈ s
    · have e : substs1 L t (neg L p) = neg L (substs1 L t p) :=
        substs_neg hpF (by simp [ht] : IsSemitermVec L 1 0 (?[t] : V))
      refine ⟨Bootstrapping.exsIntro (insert (substs1 L t p) s) (neg L p) t
          (Bootstrapping.axL (insert (substs1 L t (neg L p)) (insert (substs1 L t p) s))
            (substs1 L t p)),
        by simp, CutFreeDerivation.exsIntro (by simp [hex]) ht ⟨by simp, ?_⟩⟩
      exact CutFreeDerivation.axL (by simp [hT, hpF.neg.substs1 ht]) (by simp) (by rw [← e]; simp)
    · have hr : r ≠ ^∀ p := by
        rintro rfl
        rw [neg_all hpF.isUFormula] at hnrs
        exact hex (mem_of_mem_insert_of_ne hnrs (by simp [qqAll, qqExs]))
      have hnr : neg L r ≠ ^∀ p := by
        intro h
        have : r = ^∃ (neg L p) := by
          rw [← (hfs r hrs).isUFormula.neg_neg, h, neg_all hpF.isUFormula]
        exact hex (mem_of_mem_insert_of_ne (this ▸ hrs) (by simp [qqAll, qqExs]))
      exact ⟨Bootstrapping.axL _ r, by simp,
        CutFreeDerivation.axL hT (by simp [mem_of_mem_insert_of_ne hrs hr])
        (by simp [mem_of_mem_insert_of_ne hnrs hnr])⟩
  · rw [fstIdx_verumIntro] at hd1
    subst hd1
    exact ⟨_, by simp, CutFreeDerivation.verumIntro hT
      (by simp [mem_of_mem_insert_of_ne hv (by simp [qqVerum, qqAll])])⟩
  · rw [fstIdx_andIntro] at hd1
    subst hd1
    rw [insert_comm a] at hdp
    rw [insert_comm b] at hdq
    obtain ⟨ep, hep⟩ := ih' dp (dp_lt_andIntro _ _ _ _ _) t p _ ht hdp
    obtain ⟨eq, heq⟩ := ih' dq (dq_lt_andIntro _ _ _ _ _) t p _ ht hdq
    rw [insert_comm] at hep heq
    exact ⟨_, by simp, CutFreeDerivation.andIntro
      (by simp [mem_of_mem_insert_of_ne hab (by simp [qqAnd, qqAll])]) hep heq⟩
  · rw [fstIdx_orIntro] at hd1
    subst hd1
    rw [insert_comm b, insert_comm a] at hd₀
    obtain ⟨e, he⟩ := ih' d₀ (d_lt_orIntro _ _ _ _) t p _ ht hd₀
    rw [insert_comm _ a, insert_comm _ b] at he
    exact ⟨_, by simp, CutFreeDerivation.orIntro
      (by simp [mem_of_mem_insert_of_ne hab (by simp [qqOr, qqAll])]) he⟩
  · rw [fstIdx_allIntro] at hd1
    subst hd1
    rw [mem_setShift_insert, shift_all hpF.isUFormula, insert_comm] at hd₀
    by_cases hap : a = p
    · rw [hap] at hd₀
      obtain ⟨e, he⟩ := ih' d₀ (s_lt_allIntro _ _ _) ^&0 (shift L p) _ (by simp) hd₀
      rw [← free, insert_insert_self] at he
      exact CutFreeDerivable.substs1_of_free ht hpF hsF ⟨e, he⟩
    · have e₁ : substs1 L (termShift L t) (shift L p) = shift L (substs1 L t p) := by
        rw [substs1, substs1, shift_substs hpF (by simp [ht] : IsSemitermVec L 1 0 (?[t] : V))]
        simp [ht.isUTerm]
      obtain ⟨e, he⟩ := ih' d₀ (s_lt_allIntro _ _ _) (termShift L t) (shift L p) _ ht.termShift hd₀
      rw [e₁, insert_comm, ← mem_setShift_insert] at he
      exact ⟨_, by simp, CutFreeDerivation.allIntro
        (by simp [mem_of_mem_insert_of_ne ha (by simpa using hap)]) he⟩
  · rw [fstIdx_exsIntro] at hd1
    subst hd1
    rw [insert_comm] at hd₀
    obtain ⟨e, he⟩ := ih' d₀ (d_lt_exsIntro _ _ _ _) t p _ ht hd₀
    rw [insert_comm] at he
    exact ⟨_, by simp, CutFreeDerivation.exsIntro
      (by simp [mem_of_mem_insert_of_ne ha (by simp [qqAll, qqExs])]) hu he⟩
  · rw [fstIdx_wkRule] at hd1
    subst hd1
    by_cases hA : ^∀ p ∈ fstIdx d₀
    · obtain ⟨e, he⟩ := ih' d₀ (d_lt_wkRule _ _) t p (bitRemove (^∀ p) (fstIdx d₀)) ht
        ⟨(insert_remove hA).symm, hd₀⟩
      refine ⟨_, by simp, CutFreeDerivation.wkRule hT ?_ he⟩
      intro x hx
      rcases mem_bitInsert_iff.mp hx with rfl | hx
      · simp
      · have hx' := mem_bitRemove_iff.mp hx
        simp [mem_of_mem_insert_of_ne (hsub hx'.2) hx'.1]
    · refine ⟨_, by simp, CutFreeDerivation.wkRule hT ?_ ⟨rfl, hd₀⟩⟩
      intro x hx
      simp [mem_of_mem_insert_of_ne (hsub hx) (by rintro rfl; exact hA hx)]
  · rw [fstIdx_shiftRule] at hd1
    subst hd1
    have hΔ := hd₀.isFormulaSet
    obtain ⟨r, hr, hre⟩ :=
      mem_setShift_iff.mp (show ^∀ p ∈ setShift L (fstIdx d₀) by rw [← hsh]; simp)
    obtain ⟨p₀, -, rfl, rfl⟩ := exists_all_of_shift_eq_all (hΔ _ hr).isUFormula hre.symm
    have hp₀ : IsSemiformula L 1 p₀ := by simpa using hΔ _ hr
    obtain ⟨e, he⟩ := ih' d₀ (d_lt_shiftRule _ _) ^&d₀ p₀ (bitRemove (^∀ p₀) (fstIdx d₀))
      (by simp) ⟨(insert_remove hr).symm, hd₀⟩
    obtain ⟨e', he'⟩ := CutFreeDerivable.shift_substs1_of_fvar ht hp₀
      (le_of_lt <| lt_of_lt_of_le (lt_trans (by simp) (lt_of_mem hr)) (fstIdx_le d₀))
      (fun x hx ↦ hΔ x (mem_bitRemove_iff.mp hx).2)
      (le_trans (le_of_subset fun x hx ↦ (mem_bitRemove_iff.mp hx).2) (fstIdx_le d₀)) ⟨e, he⟩
    rw [setShift_bitRemove hΔ (hΔ _ hr).isUFormula, shift_all hp₀.isUFormula, ← hsh] at he'
    refine ⟨_, by simp, CutFreeDerivation.wkRule hT ?_ he'⟩
    intro x hx
    rcases mem_bitInsert_iff.mp hx with rfl | hx
    · simp
    · have hx' := mem_bitRemove_iff.mp hx
      simp [mem_of_mem_insert_of_ne hx'.2 hx'.1]
  · exact absurd hr (not_mem_empty_Δ₁Class r)

/-- Inversion for the universal rule: a cut-free derivation of a sequent containing `^∀ p` yields,
for every closed term `t`, a cut-free derivation of the sequent with the instance of `p` at `t` in
place of `^∀ p`.
- [Bus98, Ch. I §2.4] -/
theorem inversion_all {p s t d : V} (ht : IsTerm L t)
    (hd : CutFreeDerivationOf (∅ : Theory L) d (insert (^∀ p) s)) :
    CutFreeDerivable (∅ : Theory L) (insert (substs1 L t p) s) :=
  inversion_all_aux d t p (all_bounds hd.1).1 s (all_bounds hd.1).2 ht hd

end CutFreeDerivation

end FFL.FirstOrder.Arithmetic.Bootstrapping
