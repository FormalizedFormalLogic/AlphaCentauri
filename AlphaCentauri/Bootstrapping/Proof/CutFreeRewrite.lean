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

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

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

/-- The rest of an end-sequent split off by `insert` is bounded by the proof code. -/
private lemma le_of_fstIdx_eq_insert {d x s : V} (h : fstIdx d = insert x s) : s ≤ d :=
  le_trans (le_of_subset (by rw [h]; exact susbset_insert x s)) (fstIdx_le d)

/-- The body and the rest of an end-sequent containing a universal formula are bounded by the
proof code. -/
private lemma all_bounds {d p s : V} (h : fstIdx d = insert (^∀ p) s) : p ≤ d ∧ s ≤ d := by
  have hp : ^∀ p ∈ fstIdx d := by rw [h]; simp
  exact ⟨le_of_lt <| lt_of_lt_of_le (lt_trans (by simp) (lt_of_mem hp)) (fstIdx_le d),
    le_of_fstIdx_eq_insert h⟩

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
  sorry

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
  sorry

/-- From the instance of `p` at a free variable `^&M` above the codes of `p` and of the sequent,
the instance of the shift of `p` at a closed term beside the shifted sequent. -/
private lemma shift_substs1_of_fvar {M t p s : V} (ht : IsTerm L t) (hp : IsSemiformula L 1 p)
    (hpM : p ≤ M) (hs : IsFormulaSet L s) (hsM : s ≤ M)
    (h : CutFreeDerivable (∅ : Theory L) (insert (substs1 L ^&M p) s)) :
    CutFreeDerivable (∅ : Theory L) (insert (substs1 L t (shift L p)) (setShift L s)) := by
  sorry

end

end CutFreeDerivable

namespace CutFreeDerivation

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺2]

/-- The $\Pi_2$ form of the universal inversion that the course-of-values induction proves. -/
private lemma inversion_all_aux :
    ∀ d : V, ∀ t, ∀ p ≤ d, ∀ s ≤ d, IsTerm L t →
      CutFreeDerivationOf (∅ : Theory L) d (insert (^∀ p) s) →
      CutFreeDerivable (∅ : Theory L) (insert (substs1 L t p) s) := by
  sorry

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
