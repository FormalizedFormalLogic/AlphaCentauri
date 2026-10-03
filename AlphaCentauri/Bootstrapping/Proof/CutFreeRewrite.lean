module

public import AlphaCentauri.Bootstrapping.Proof.Inversion
public import AlphaCentauri.Bootstrapping.Proof.Substitution
public import AlphaCentauri.ToFoundation.Set

/-!
# Free-variable substitution and universal inversion for cut-free derivations

This module shows that cut-free derivability over the empty theory is closed under substituting
closed terms for free variables, that the universal rule is invertible with an arbitrary closed
term as the instance, and that `⊥` can be deleted from a cut-free derivable sequent. The first two
hold in every model of `𝗜𝚺⁺2`, the last in every model of `𝗜𝚺₁`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

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

variable (L) in
/-- `⊥` can be deleted from the end-sequent of every cut-free derivation coded below `d`. -/
private def DeletesFalsumBelow (d : V) : Prop :=
  ∀ d₀ < d, ∀ s₀ : V, CutFreeDerivationOf (∅ : Theory L) d₀ (insert ^⊥ s₀) →
    CutFreeDerivable (∅ : Theory L) s₀

section deleteFalsum

variable {s : V}

private lemma falsum_axL {r : V} (hfs : IsFormulaSet L (insert ^⊥ s)) (hrs : r ∈ insert ^⊥ s)
    (hnrs : neg L r ∈ insert ^⊥ s) : CutFreeDerivable (∅ : Theory L) s := by
  have hsF : IsFormulaSet L s := fun x hx ↦ hfs x (by simp [hx])
  have hvf : (^⊤ : V) ≠ ^⊥ := by simp [qqVerum, qqFalsum]
  by_cases hv : (^⊤ : V) ∈ s
  · exact .verum hsF hv
  · have hr : r ≠ ^⊥ := by
      rintro rfl
      rw [neg_falsum] at hnrs
      exact hv (mem_of_mem_insert_of_ne hnrs hvf)
    have hnr : neg L r ≠ ^⊥ := by
      intro h
      have : r = ^⊤ := by rw [← (hfs r hrs).isUFormula.neg_neg, h, neg_falsum]
      exact hv (mem_of_mem_insert_of_ne (this ▸ hrs) hvf)
    exact .em hsF r (mem_of_mem_insert_of_ne hrs hr) (mem_of_mem_insert_of_ne hnrs hnr)

private lemma falsum_and {a b dp dq : V}
    (ih : DeletesFalsumBelow L (andIntro (insert ^⊥ s) a b dp dq)) (hab : a ^⋏ b ∈ insert ^⊥ s)
    (hdp : CutFreeDerivationOf (∅ : Theory L) dp (insert a (insert ^⊥ s)))
    (hdq : CutFreeDerivationOf (∅ : Theory L) dq (insert b (insert ^⊥ s))) :
    CutFreeDerivable (∅ : Theory L) s := by
  rw [insert_comm] at hdp hdq
  exact .and_m (mem_of_mem_insert_of_ne hab (by simp [qqAnd, qqFalsum]))
    (ih dp (dp_lt_andIntro _ _ _ _ _) _ hdp) (ih dq (dq_lt_andIntro _ _ _ _ _) _ hdq)

private lemma falsum_or {a b d₀ : V} (ih : DeletesFalsumBelow L (orIntro (insert ^⊥ s) a b d₀))
    (hab : a ^⋎ b ∈ insert ^⊥ s)
    (hd₀ : CutFreeDerivationOf (∅ : Theory L) d₀ (insert a (insert b (insert ^⊥ s)))) :
    CutFreeDerivable (∅ : Theory L) s := by
  rw [insert_comm b, insert_comm a] at hd₀
  exact .or_m (mem_of_mem_insert_of_ne hab (by simp [qqOr, qqFalsum]))
    (ih d₀ (d_lt_orIntro _ _ _ _) _ hd₀)

private lemma falsum_all {a d₀ : V} (ih : DeletesFalsumBelow L (allIntro (insert ^⊥ s) a d₀))
    (ha : ^∀ a ∈ insert ^⊥ s)
    (hd₀ : CutFreeDerivationOf (∅ : Theory L) d₀ (insert (free L a) (setShift L (insert ^⊥ s)))) :
    CutFreeDerivable (∅ : Theory L) s := by
  rw [mem_setShift_insert, shift_falsum, insert_comm] at hd₀
  exact .all_m (mem_of_mem_insert_of_ne ha (by simp [qqAll, qqFalsum]))
    (ih d₀ (s_lt_allIntro _ _ _) _ hd₀)

private lemma falsum_exs {a t d₀ : V} (ih : DeletesFalsumBelow L (exsIntro (insert ^⊥ s) a t d₀))
    (ha : ^∃ a ∈ insert ^⊥ s) (ht : IsTerm L t)
    (hd₀ : CutFreeDerivationOf (∅ : Theory L) d₀ (insert (substs1 L t a) (insert ^⊥ s))) :
    CutFreeDerivable (∅ : Theory L) s := by
  rw [insert_comm] at hd₀
  exact .ex_m (mem_of_mem_insert_of_ne ha (by simp [qqExs, qqFalsum])) ht
    (ih d₀ (d_lt_exsIntro _ _ _ _) _ hd₀)

private lemma falsum_wk {d₀ : V} (ih : DeletesFalsumBelow L (wkRule (insert ^⊥ s) d₀))
    (hsF : IsFormulaSet L s) (hsub : fstIdx d₀ ⊆ insert ^⊥ s)
    (hd₀ : CutFreeDerivation (∅ : Theory L) d₀) : CutFreeDerivable (∅ : Theory L) s := by
  by_cases hf : (^⊥ : V) ∈ fstIdx d₀
  · refine .wk hsF ?_
      (ih d₀ (d_lt_wkRule _ _) (bitRemove ^⊥ (fstIdx d₀)) ⟨(insert_remove hf).symm, hd₀⟩)
    intro x hx
    have hx' := mem_bitRemove_iff.mp hx
    exact mem_of_mem_insert_of_ne (hsub hx'.2) hx'.1
  · refine .wk hsF ?_ ⟨d₀, rfl, hd₀⟩
    intro x hx
    exact mem_of_mem_insert_of_ne (hsub hx) (by rintro rfl; exact hf hx)

private lemma falsum_shift {d₀ : V} (ih : DeletesFalsumBelow L (shiftRule (insert ^⊥ s) d₀))
    (hsF : IsFormulaSet L s) (hsh : insert ^⊥ s = setShift L (fstIdx d₀))
    (hd₀ : CutFreeDerivation (∅ : Theory L) d₀) : CutFreeDerivable (∅ : Theory L) s := by
  have hΔ := hd₀.isFormulaSet
  obtain ⟨r, hr, hre⟩ :=
    mem_setShift_iff.mp (show (^⊥ : V) ∈ setShift L (fstIdx d₀) by rw [← hsh]; simp)
  obtain rfl : r = ^⊥ := shift_inj (hΔ r hr).isUFormula (by simp) (by rw [← hre, shift_falsum])
  refine .wk hsF ?_
    (ih d₀ (d_lt_shiftRule _ _) (bitRemove ^⊥ (fstIdx d₀)) ⟨(insert_remove hr).symm, hd₀⟩).shift_m
  rw [setShift_bitRemove hΔ (by simp), shift_falsum, ← hsh]
  intro x hx
  have hx' := mem_bitRemove_iff.mp hx
  exact mem_of_mem_insert_of_ne hx'.2 hx'.1

end deleteFalsum

/-- Deleting `⊥` from the end-sequent of a cut-free derivation code bounding the rest of it. -/
private lemma of_insert_falsum_aux :
    ∀ d : V, ∀ s ≤ d, CutFreeDerivationOf (∅ : Theory L) d (insert ^⊥ s) →
      CutFreeDerivable (∅ : Theory L) s := by
  have hP : 𝚺ᴬ₁-Predicate fun d : V ↦ ∀ s ≤ d,
      CutFreeDerivationOf (∅ : Theory L) d (insert ^⊥ s) → CutFreeDerivable (∅ : Theory L) s := by
    definability
  intro d
  refine ISigma1.order_induction 𝚺 hP ?_ d
  intro d ih
  have ih' : DeletesFalsumBelow L d :=
    fun d₀ hd₀ s₀ h ↦ ih d₀ hd₀ s₀ (le_of_fstIdx_eq_insert h.1) h
  rintro s - ⟨hd1, hd2⟩
  have hfs : IsFormulaSet L (insert ^⊥ s) := hd1 ▸ hd2.isFormulaSet
  have hsF : IsFormulaSet L s := fun x hx ↦ hfs x (by simp [hx])
  rcases hd2.case.2 with (⟨s₀, r, rfl, hrs, hnrs⟩ | ⟨s₀, rfl, hv⟩ |
    ⟨s₀, a, b, dp, dq, rfl, hab, hdp, hdq⟩ | ⟨s₀, a, b, d₀, rfl, hab, hd₀⟩ |
    ⟨s₀, a, d₀, rfl, ha, hd₀⟩ | ⟨s₀, a, t, d₀, rfl, ha, ht, hd₀⟩ |
    ⟨s₀, d₀, rfl, hsub, hd₀⟩ | ⟨s₀, d₀, rfl, hsh, hd₀⟩ | ⟨s₀, r, rfl, -, hT⟩)
  · rw [fstIdx_axL] at hd1
    subst hd1
    exact falsum_axL hfs hrs hnrs
  · rw [fstIdx_verumIntro] at hd1
    subst hd1
    exact .verum hsF (mem_of_mem_insert_of_ne hv (by simp [qqVerum, qqFalsum]))
  · rw [fstIdx_andIntro] at hd1
    subst hd1
    exact falsum_and ih' hab hdp hdq
  · rw [fstIdx_orIntro] at hd1
    subst hd1
    exact falsum_or ih' hab hd₀
  · rw [fstIdx_allIntro] at hd1
    subst hd1
    exact falsum_all ih' ha hd₀
  · rw [fstIdx_exsIntro] at hd1
    subst hd1
    exact falsum_exs ih' ha ht hd₀
  · rw [fstIdx_wkRule] at hd1
    subst hd1
    exact falsum_wk ih' hsF hsub hd₀
  · rw [fstIdx_shiftRule] at hd1
    subst hd1
    exact falsum_shift ih' hsF hsh hd₀
  · exact absurd hT (not_mem_empty_Δ₁Class r)

/-- Deleting `⊥` from a cut-free derivable sequent over the empty theory leaves it cut-free
derivable. -/
theorem of_insert_falsum {s : V} (h : CutFreeDerivable (∅ : Theory L) (insert ^⊥ s)) :
    CutFreeDerivable (∅ : Theory L) s := by
  obtain ⟨d, hd⟩ := h
  exact of_insert_falsum_aux d s (le_of_fstIdx_eq_insert hd.1) hd

variable (L) in
/-- Cut-free derivability of the image of the end-sequent under every substitution of closed terms
for free variables holds for every cut-free derivation coded below `d`. -/
private def RewritesBelow (d : V) : Prop :=
  ∀ d₀ < d, ∀ w, IsSemitermVec L (len w) 0 w → CutFreeDerivation (∅ : Theory L) d₀ →
    CutFreeDerivable (∅ : Theory L) (fvSubstImage (L := L) w (fstIdx d₀))

section rewrite

variable {w s : V}

private lemma rewrite_axL {p : V} (hw : IsSemitermVec L (len w) 0 w) (hsF : IsFormulaSet L s)
    (hp : p ∈ s) (hnp : neg L p ∈ s) :
    CutFreeDerivable (∅ : Theory L) (fvSubstImage (L := L) w s) :=
  .em (formulaSet_fvSubstImage hw hsF) _ (fvSubst_mem_fvSubstImage hp)
    (by rw [← fvSubst_neg hw (hsF p hp)]; exact fvSubst_mem_fvSubstImage hnp)

private lemma rewrite_and {p q dp dq : V} (ih : RewritesBelow L (andIntro s p q dp dq))
    (hw : IsSemitermVec L (len w) 0 w) (hsF : IsFormulaSet L s) (hpq : p ^⋏ q ∈ s)
    (hdp : CutFreeDerivationOf (∅ : Theory L) dp (insert p s))
    (hdq : CutFreeDerivationOf (∅ : Theory L) dq (insert q s)) :
    CutFreeDerivable (∅ : Theory L) (fvSubstImage (L := L) w s) := by
  have hpqF : IsFormula L p ∧ IsFormula L q := by simpa using hsF _ hpq
  have hep := ih dp (dp_lt_andIntro _ _ _ _ _) w hw hdp.2
  have heq := ih dq (dq_lt_andIntro _ _ _ _ _) w hw hdq.2
  rw [hdp.1, fvSubstImage_insert] at hep
  rw [hdq.1, fvSubstImage_insert] at heq
  have h := fvSubst_mem_fvSubstImage (L := L) (w := w) hpq
  rw [fvSubst_and hpqF.1.isUFormula hpqF.2.isUFormula] at h
  exact .and_m h hep heq

private lemma rewrite_or {p q d₀ : V} (ih : RewritesBelow L (orIntro s p q d₀))
    (hw : IsSemitermVec L (len w) 0 w) (hsF : IsFormulaSet L s) (hpq : p ^⋎ q ∈ s)
    (hd₀ : CutFreeDerivationOf (∅ : Theory L) d₀ (insert p (insert q s))) :
    CutFreeDerivable (∅ : Theory L) (fvSubstImage (L := L) w s) := by
  have hpqF : IsFormula L p ∧ IsFormula L q := by simpa using hsF _ hpq
  have he := ih d₀ (d_lt_orIntro _ _ _ _) w hw hd₀.2
  rw [hd₀.1, fvSubstImage_insert, fvSubstImage_insert] at he
  have h := fvSubst_mem_fvSubstImage (L := L) (w := w) hpq
  rw [fvSubst_or hpqF.1.isUFormula hpqF.2.isUFormula] at h
  exact .or_m h he

private lemma rewrite_all {p d₀ : V} (ih : RewritesBelow L (allIntro s p d₀))
    (hw : IsSemitermVec L (len w) 0 w) (hsF : IsFormulaSet L s) (hp : ^∀ p ∈ s)
    (hd₀ : CutFreeDerivationOf (∅ : Theory L) d₀ (insert (free L p) (setShift L s))) :
    CutFreeDerivable (∅ : Theory L) (fvSubstImage (L := L) w s) := by
  have hpF : IsSemiformula L 1 p := by simpa using hsF _ hp
  have he := ih d₀ (s_lt_allIntro _ _ _) _ hw.fvar_cons_termShiftVec hd₀.2
  rw [hd₀.1, fvSubstImage_insert, ← free_fvSubst hw hpF, ← setShift_fvSubstImage hw hsF] at he
  have h := fvSubst_mem_fvSubstImage (L := L) (w := w) hp
  rw [fvSubst_all hpF.isUFormula] at h
  exact .all_m h he

private lemma rewrite_exs {p t d₀ : V} (ih : RewritesBelow L (exsIntro s p t d₀))
    (hw : IsSemitermVec L (len w) 0 w) (hsF : IsFormulaSet L s) (hp : ^∃ p ∈ s) (ht : IsTerm L t)
    (hd₀ : CutFreeDerivationOf (∅ : Theory L) d₀ (insert (substs1 L t p) s)) :
    CutFreeDerivable (∅ : Theory L) (fvSubstImage (L := L) w s) := by
  have hpF : IsSemiformula L 1 p := by simpa using hsF _ hp
  have he := ih d₀ (d_lt_exsIntro _ _ _ _) w hw hd₀.2
  rw [hd₀.1, fvSubstImage_insert, fvSubst_substs1 hw ht hpF] at he
  have h := fvSubst_mem_fvSubstImage (L := L) (w := w) hp
  rw [fvSubst_exs hpF.isUFormula] at h
  exact .ex_m h (ht.termFvSubst hw) he

end rewrite

section

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺2]

private lemma rewrite_shift {d₀ w : V}
    (ih : RewritesBelow L (shiftRule (setShift L (fstIdx d₀)) d₀))
    (hw : IsSemitermVec L (len w) 0 w) (hd₀ : CutFreeDerivation (∅ : Theory L) d₀) :
    CutFreeDerivable (∅ : Theory L) (fvSubstImage (L := L) w (setShift L (fstIdx d₀))) := by
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
  have he := ih d₀ (d_lt_shiftRule _ _) v hvc hd₀
  rwa [← fvSubstImage_setShift (fun x hx ↦ ⟨by rwa [hvl], hv x hx⟩) hd₀.isFormulaSet
    (fstIdx_le d₀)] at he

/-- Substituting closed terms for free variables in the end-sequent of a cut-free derivation
code. -/
private lemma rewrite_aux :
    ∀ d : V, ∀ w, IsSemitermVec L (len w) 0 w → CutFreeDerivation (∅ : Theory L) d →
      CutFreeDerivable (∅ : Theory L) (fvSubstImage (L := L) w (fstIdx d)) := by
  have hP : 𝚷ᴬ_[2].DefinablePred fun d : V ↦ ∀ w, IsSemitermVec L (len w) 0 w →
      CutFreeDerivation (∅ : Theory L) d →
      CutFreeDerivable (∅ : Theory L) (fvSubstImage (L := L) w (fstIdx d)) := by
    apply HierarchySymbol.Definable.all
    exact HierarchySymbol.Definable.of_lt (C := 𝚺ᴬ_[1]) (by definability) (by simp)
  intro d
  refine InductionOnHierarchy.order_induction_sigma 𝚷 2 hP ?_ d
  intro d ih w hw hd
  have hsF := hd.isFormulaSet
  rcases hd.case.2 with (⟨s, p, rfl, hp, hnp⟩ | ⟨s, rfl, hv⟩ |
    ⟨s, p, q, dp, dq, rfl, hpq, hdp, hdq⟩ | ⟨s, p, q, d₀, rfl, hpq, hd₀⟩ |
    ⟨s, p, d₀, rfl, hp, hd₀⟩ | ⟨s, p, t, d₀, rfl, hp, ht, hd₀⟩ |
    ⟨s, d₀, rfl, hsub, hd₀⟩ | ⟨s, d₀, rfl, rfl, hd₀⟩ | ⟨s, p, rfl, -, hT⟩)
  · rw [fstIdx_axL] at hsF ⊢
    exact rewrite_axL hw hsF hp hnp
  · rw [fstIdx_verumIntro] at hsF ⊢
    exact .verum (formulaSet_fvSubstImage hw hsF)
      (by simpa using fvSubst_mem_fvSubstImage (L := L) (w := w) hv)
  · rw [fstIdx_andIntro] at hsF ⊢
    exact rewrite_and ih hw hsF hpq hdp hdq
  · rw [fstIdx_orIntro] at hsF ⊢
    exact rewrite_or ih hw hsF hpq hd₀
  · rw [fstIdx_allIntro] at hsF ⊢
    exact rewrite_all ih hw hsF hp hd₀
  · rw [fstIdx_exsIntro] at hsF ⊢
    exact rewrite_exs ih hw hsF hp ht hd₀
  · rw [fstIdx_wkRule] at hsF ⊢
    refine .wk (formulaSet_fvSubstImage hw hsF) ?_ (ih d₀ (d_lt_wkRule _ _) w hw hd₀)
    intro x hx
    obtain ⟨q, hq, rfl⟩ := mem_fvSubstImage_iff.mp hx
    exact fvSubst_mem_fvSubstImage (hsub hq)
  · rw [fstIdx_shiftRule]
    exact rewrite_shift ih hw hd₀
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

variable (L) in
/-- Universal inversion holds for every cut-free derivation coded below `d`. -/
private def InvertsAllBelow (d : V) : Prop :=
  ∀ d₀ < d, ∀ t₀ p₀ s₀ : V, IsTerm L t₀ →
    CutFreeDerivationOf (∅ : Theory L) d₀ (insert (^∀ p₀) s₀) →
    CutFreeDerivable (∅ : Theory L) (insert (substs1 L t₀ p₀) s₀)

section invertAll

variable {t p s : V}

private lemma inversion_all_axL {r : V} (ht : IsTerm L t) (hpF : IsSemiformula L 1 p)
    (hfs : IsFormulaSet L (insert (^∀ p) s)) (hrs : r ∈ insert (^∀ p) s)
    (hnrs : neg L r ∈ insert (^∀ p) s) :
    CutFreeDerivable (∅ : Theory L) (insert (substs1 L t p) s) := by
  have hsF : IsFormulaSet L s := fun x hx ↦ hfs x (by simp [hx])
  have hT : IsFormulaSet L (insert (substs1 L t p) s) := by simp [hsF, hpF.substs1 ht]
  by_cases hex : ^∃ (neg L p) ∈ s
  · have e : substs1 L t (neg L p) = neg L (substs1 L t p) :=
      substs_neg hpF (by simp [ht] : IsSemitermVec L 1 0 (?[t] : V))
    exact .ex_m (p := neg L p) (by simp [hex]) ht
      (.em (by simp [hT, hpF.neg.substs1 ht]) (substs1 L t p) (by simp) (by rw [← e]; simp))
  · have hr : r ≠ ^∀ p := by
      rintro rfl
      rw [neg_all hpF.isUFormula] at hnrs
      exact hex (mem_of_mem_insert_of_ne hnrs (by simp [qqAll, qqExs]))
    have hnr : neg L r ≠ ^∀ p := by
      intro h
      have : r = ^∃ (neg L p) := by
        rw [← (hfs r hrs).isUFormula.neg_neg, h, neg_all hpF.isUFormula]
      exact hex (mem_of_mem_insert_of_ne (this ▸ hrs) (by simp [qqAll, qqExs]))
    exact .em hT r (by simp [mem_of_mem_insert_of_ne hrs hr])
      (by simp [mem_of_mem_insert_of_ne hnrs hnr])

private lemma inversion_all_verum (ht : IsTerm L t) (hpF : IsSemiformula L 1 p)
    (hsF : IsFormulaSet L s) (hv : ^⊤ ∈ insert (^∀ p) s) :
    CutFreeDerivable (∅ : Theory L) (insert (substs1 L t p) s) :=
  .verum (by simp [hsF, hpF.substs1 ht])
    (by simp [mem_of_mem_insert_of_ne hv (by simp [qqVerum, qqAll])])

private lemma inversion_all_and {a b dp dq : V}
    (ih : InvertsAllBelow L (Bootstrapping.andIntro (insert (^∀ p) s) a b dp dq)) (ht : IsTerm L t)
    (hab : a ^⋏ b ∈ insert (^∀ p) s)
    (hdp : CutFreeDerivationOf (∅ : Theory L) dp (insert a (insert (^∀ p) s)))
    (hdq : CutFreeDerivationOf (∅ : Theory L) dq (insert b (insert (^∀ p) s))) :
    CutFreeDerivable (∅ : Theory L) (insert (substs1 L t p) s) := by
  rw [insert_comm a] at hdp
  rw [insert_comm b] at hdq
  have hep := ih dp (dp_lt_andIntro _ _ _ _ _) t p _ ht hdp
  have heq := ih dq (dq_lt_andIntro _ _ _ _ _) t p _ ht hdq
  rw [insert_comm] at hep heq
  exact .and_m (by simp [mem_of_mem_insert_of_ne hab (by simp [qqAnd, qqAll])]) hep heq

private lemma inversion_all_or {a b d₀ : V}
    (ih : InvertsAllBelow L (Bootstrapping.orIntro (insert (^∀ p) s) a b d₀)) (ht : IsTerm L t)
    (hab : a ^⋎ b ∈ insert (^∀ p) s)
    (hd₀ : CutFreeDerivationOf (∅ : Theory L) d₀ (insert a (insert b (insert (^∀ p) s)))) :
    CutFreeDerivable (∅ : Theory L) (insert (substs1 L t p) s) := by
  rw [insert_comm b, insert_comm a] at hd₀
  have he := ih d₀ (d_lt_orIntro _ _ _ _) t p _ ht hd₀
  rw [insert_comm _ a, insert_comm _ b] at he
  exact .or_m (by simp [mem_of_mem_insert_of_ne hab (by simp [qqOr, qqAll])]) he

private lemma inversion_all_exs {a u d₀ : V}
    (ih : InvertsAllBelow L (Bootstrapping.exsIntro (insert (^∀ p) s) a u d₀)) (ht : IsTerm L t)
    (ha : ^∃ a ∈ insert (^∀ p) s) (hu : IsTerm L u)
    (hd₀ : CutFreeDerivationOf (∅ : Theory L) d₀ (insert (substs1 L u a) (insert (^∀ p) s))) :
    CutFreeDerivable (∅ : Theory L) (insert (substs1 L t p) s) := by
  rw [insert_comm] at hd₀
  have he := ih d₀ (d_lt_exsIntro _ _ _ _) t p _ ht hd₀
  rw [insert_comm] at he
  exact .ex_m (by simp [mem_of_mem_insert_of_ne ha (by simp [qqAll, qqExs])]) hu he

private lemma inversion_all_wk {d₀ : V}
    (ih : InvertsAllBelow L (Bootstrapping.wkRule (insert (^∀ p) s) d₀)) (ht : IsTerm L t)
    (hpF : IsSemiformula L 1 p) (hsF : IsFormulaSet L s)
    (hsub : fstIdx d₀ ⊆ insert (^∀ p) s) (hd₀ : CutFreeDerivation (∅ : Theory L) d₀) :
    CutFreeDerivable (∅ : Theory L) (insert (substs1 L t p) s) := by
  have hT : IsFormulaSet L (insert (substs1 L t p) s) := by simp [hsF, hpF.substs1 ht]
  by_cases hA : ^∀ p ∈ fstIdx d₀
  · refine .wk hT ?_ (ih d₀ (d_lt_wkRule _ _) t p (bitRemove (^∀ p) (fstIdx d₀)) ht
      ⟨(insert_remove hA).symm, hd₀⟩)
    intro x hx
    rcases mem_bitInsert_iff.mp hx with rfl | hx
    · simp
    · have hx' := mem_bitRemove_iff.mp hx
      simp [mem_of_mem_insert_of_ne (hsub hx'.2) hx'.1]
  · refine .wk hT ?_ ⟨d₀, rfl, hd₀⟩
    intro x hx
    simp [mem_of_mem_insert_of_ne (hsub hx) (by rintro rfl; exact hA hx)]

end invertAll

section

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺2] {t p s : V}

private lemma inversion_all_all {a d₀ : V}
    (ih : InvertsAllBelow L (Bootstrapping.allIntro (insert (^∀ p) s) a d₀))
    (ht : IsTerm L t) (hpF : IsSemiformula L 1 p) (hsF : IsFormulaSet L s)
    (ha : ^∀ a ∈ insert (^∀ p) s)
    (hd₀ : CutFreeDerivationOf (∅ : Theory L) d₀
      (insert (free L a) (setShift L (insert (^∀ p) s)))) :
    CutFreeDerivable (∅ : Theory L) (insert (substs1 L t p) s) := by
  rw [mem_setShift_insert, shift_all hpF.isUFormula, insert_comm] at hd₀
  by_cases hap : a = p
  · rw [hap] at hd₀
    have he := ih d₀ (s_lt_allIntro _ _ _) ^&0 (shift L p) _ (by simp) hd₀
    rw [← free, insert_insert_self] at he
    exact CutFreeDerivable.substs1_of_free ht hpF hsF he
  · have e₁ : substs1 L (termShift L t) (shift L p) = shift L (substs1 L t p) := by
      rw [substs1, substs1, shift_substs hpF (by simp [ht] : IsSemitermVec L 1 0 (?[t] : V))]
      simp [ht.isUTerm]
    have he := ih d₀ (s_lt_allIntro _ _ _) (termShift L t) (shift L p) _ ht.termShift hd₀
    rw [e₁, insert_comm, ← mem_setShift_insert] at he
    exact .all_m (by simp [mem_of_mem_insert_of_ne ha (by simpa using hap)]) he

private lemma inversion_all_shift {d₀ : V}
    (ih : InvertsAllBelow L (Bootstrapping.shiftRule (insert (^∀ p) s) d₀))
    (ht : IsTerm L t) (hpF : IsSemiformula L 1 p) (hsF : IsFormulaSet L s)
    (hsh : insert (^∀ p) s = setShift L (fstIdx d₀)) (hd₀ : CutFreeDerivation (∅ : Theory L) d₀) :
    CutFreeDerivable (∅ : Theory L) (insert (substs1 L t p) s) := by
  have hT : IsFormulaSet L (insert (substs1 L t p) s) := by simp [hsF, hpF.substs1 ht]
  have hΔ := hd₀.isFormulaSet
  obtain ⟨r, hr, hre⟩ :=
    mem_setShift_iff.mp (show ^∀ p ∈ setShift L (fstIdx d₀) by rw [← hsh]; simp)
  obtain ⟨p₀, -, rfl, rfl⟩ := exists_all_of_shift_eq_all (hΔ _ hr).isUFormula hre.symm
  have hp₀ : IsSemiformula L 1 p₀ := by simpa using hΔ _ hr
  have h := CutFreeDerivable.shift_substs1_of_fvar ht hp₀
    (le_of_lt <| lt_of_lt_of_le (lt_trans (by simp) (lt_of_mem hr)) (fstIdx_le d₀))
    (fun x hx ↦ hΔ x (mem_bitRemove_iff.mp hx).2)
    (le_trans (le_of_subset fun x hx ↦ (mem_bitRemove_iff.mp hx).2) (fstIdx_le d₀))
    (ih d₀ (d_lt_shiftRule _ _) ^&d₀ p₀ (bitRemove (^∀ p₀) (fstIdx d₀)) (by simp)
      ⟨(insert_remove hr).symm, hd₀⟩)
  rw [setShift_bitRemove hΔ (hΔ _ hr).isUFormula, shift_all hp₀.isUFormula, ← hsh] at h
  refine .wk hT ?_ h
  intro x hx
  rcases mem_bitInsert_iff.mp hx with rfl | hx
  · simp
  · have hx' := mem_bitRemove_iff.mp hx
    simp [mem_of_mem_insert_of_ne hx'.2 hx'.1]

/-- Universal inversion for an end-sequent whose universal body and rest are bounded by the
derivation code. -/
private lemma inversion_all_aux :
    ∀ d : V, ∀ t, ∀ p ≤ d, ∀ s ≤ d, IsTerm L t →
      CutFreeDerivationOf (∅ : Theory L) d (insert (^∀ p) s) →
      CutFreeDerivable (∅ : Theory L) (insert (substs1 L t p) s) := by
  have hP : 𝚷ᴬ_[2].DefinablePred fun d : V ↦ ∀ t, ∀ p ≤ d, ∀ s ≤ d, IsTerm L t →
      CutFreeDerivationOf (∅ : Theory L) d (insert (^∀ p) s) →
      CutFreeDerivable (∅ : Theory L) (insert (substs1 L t p) s) := by
    apply HierarchySymbol.Definable.all
    exact HierarchySymbol.Definable.of_lt (C := 𝚺ᴬ_[1]) (by definability) (by simp)
  intro d
  refine InductionOnHierarchy.order_induction_sigma 𝚷 2 hP ?_ d
  intro d ih
  rintro t p - s - ht ⟨hd1, hd2⟩
  have ih' : InvertsAllBelow L d := fun d₀ hd₀ t₀ p₀ s₀ ht₀ h ↦
    ih d₀ hd₀ t₀ p₀ (all_bounds h.1).1 s₀ (all_bounds h.1).2 ht₀ h
  have hfs : IsFormulaSet L (insert (^∀ p) s) := hd1 ▸ hd2.isFormulaSet
  have hpF : IsSemiformula L 1 p := by simpa using hfs (^∀ p) (by simp)
  have hsF : IsFormulaSet L s := fun x hx ↦ hfs x (by simp [hx])
  rcases hd2.case.2 with (⟨Γ, r, rfl, hrs, hnrs⟩ | ⟨Γ, rfl, hv⟩ |
    ⟨Γ, a, b, dp, dq, rfl, hab, hdp, hdq⟩ | ⟨Γ, a, b, d₀, rfl, hab, hd₀⟩ |
    ⟨Γ, a, d₀, rfl, ha, hd₀⟩ | ⟨Γ, a, u, d₀, rfl, ha, hu, hd₀⟩ |
    ⟨Γ, d₀, rfl, hsub, hd₀⟩ | ⟨Γ, d₀, rfl, hsh, hd₀⟩ | ⟨Γ, r, rfl, -, hr⟩)
  · rw [fstIdx_axL] at hd1
    subst hd1
    exact inversion_all_axL ht hpF hfs hrs hnrs
  · rw [fstIdx_verumIntro] at hd1
    subst hd1
    exact inversion_all_verum ht hpF hsF hv
  · rw [fstIdx_andIntro] at hd1
    subst hd1
    exact inversion_all_and ih' ht hab hdp hdq
  · rw [fstIdx_orIntro] at hd1
    subst hd1
    exact inversion_all_or ih' ht hab hd₀
  · rw [fstIdx_allIntro] at hd1
    subst hd1
    exact inversion_all_all ih' ht hpF hsF ha hd₀
  · rw [fstIdx_exsIntro] at hd1
    subst hd1
    exact inversion_all_exs ih' ht ha hu hd₀
  · rw [fstIdx_wkRule] at hd1
    subst hd1
    exact inversion_all_wk ih' ht hpF hsF hsub hd₀
  · rw [fstIdx_shiftRule] at hd1
    subst hd1
    exact inversion_all_shift ih' ht hpF hsF hsh hd₀
  · exact absurd hr (not_mem_empty_Δ₁Class r)

/-- Inversion for the universal rule: a cut-free derivation of a sequent containing `^∀ p` yields,
for every closed term `t`, a cut-free derivation of the sequent with the instance of `p` at `t` in
place of `^∀ p`.
- [Bus98, Ch. I §2.4] -/
theorem inversion_all {p s t d : V} (ht : IsTerm L t)
    (hd : CutFreeDerivationOf (∅ : Theory L) d (insert (^∀ p) s)) :
    CutFreeDerivable (∅ : Theory L) (insert (substs1 L t p) s) :=
  inversion_all_aux d t p (all_bounds hd.1).1 s (all_bounds hd.1).2 ht hd

end

end CutFreeDerivation

end FFL.FirstOrder.Arithmetic.Bootstrapping
