module

public import AlphaCentauri.Bootstrapping.Proof.Inversion
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Induction
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.LeastWitness

/-!
# Cut elimination for the internal calculus

In every model of $\mathsf{I}\Sigma_1$, a cut on a formula of complexity at most `r` between two
derivations of cut rank at most `r` over the empty theory can be replaced by a derivation of cut
rank at most `r`. Hence the cut rank of a derivation over the empty theory can be lowered step by
step, and every internal derivation over the empty theory has a cut-free counterpart with the same
end-sequent.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic
namespace Bootstrapping

open PeanoMinus ISigma0 ISigma1 InternalMeasures

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

variable (L) in
/-- `p` has complexity zero or is existential. -/
private def IsZeroOrExs (p : V) : Prop := formulaComplexity L p = 0 ∨ ∃ a < p, p = ^∃ a

private lemma isZeroOrExs_shift_iff {p : V} (hp : IsUFormula L p) :
    IsZeroOrExs L (shift L p) ↔ IsZeroOrExs L p := by
  unfold IsZeroOrExs
  rw [formulaComplexity_shift hp]
  apply or_congr_right
  constructor
  · rintro ⟨a, -, ha⟩
    obtain ⟨a₀, rfl, -⟩ := exists_eq_exs_of_shift_eq hp ha
    exact ⟨a₀, by simp, rfl⟩
  · rintro ⟨a, -, rfl⟩
    have ha : IsUFormula L a := by simpa using hp
    exact ⟨shift L a, by simp [shift_exs ha], shift_exs ha⟩

/-! ### Bounds on the premises of the cut reduction -/

/-- `s` together with every code up to `d`. -/
private noncomputable def widen (d s : V) : V := s ∪ under (d + 1)

private instance : 𝚺ᴬ₁-Function₂ (widen : V → V → V) := by
  unfold widen
  definability

private lemma subset_widen (d s : V) : s ⊆ widen d s := fun _ hx ↦ mem_cup_iff.mpr (.inl hx)

private lemma insert_subset_widen {a d s : V} (ha : a ≤ d) : insert a s ⊆ widen d s := by
  intro x hx
  rcases mem_bitInsert_iff.mp hx with rfl | hx
  · exact mem_cup_iff.mpr (.inr (mem_under_iff.mpr (lt_succ_iff_le.mpr ha)))
  · exact subset_widen d s hx

private lemma insert_insert_subset_widen {a b d s : V} (ha : a ≤ d) (hb : b ≤ d) :
    insert a (insert b s) ⊆ widen d s := by
  intro x hx
  rcases mem_bitInsert_iff.mp hx with rfl | hx
  · exact mem_cup_iff.mpr (.inr (mem_under_iff.mpr (lt_succ_iff_le.mpr ha)))
  · exact insert_subset_widen hb hx

private lemma wkRule_le_wkRule {S S' e : V} (h : S ⊆ S') : wkRule S e ≤ wkRule S' e := by
  unfold wkRule
  exact add_le_add_left (pair_le_pair (le_of_subset h) le_rfl) 1

variable (L) in
/-- The cut formulas at the premises: the cut formula itself, its shift, and every code up to
`d`. -/
private noncomputable def formulaBound (d p : V) : V := p + shift L p + d

variable (L) in
/-- The contexts at the premises: contexts enlarged by codes up to `d`, their shifts so enlarged,
and the image of the context under the inverse of `freshVec (s + d)`. -/
private noncomputable def contextBound (d s : V) : V :=
  widen d s + widen d (setShift L s) + fvSubstImage (L := L) (freshVecInverse (s + d)) s

variable (L) in
/-- The partner derivations at the premises: weakenings of the partner and of its shift, and the
image `ρ ⟪w, e⟫` of the partner under the inverse `w` of `freshVec (s + d)`. -/
private noncomputable def partnerBound (ρ : V → V) (d p s e : V) : V :=
  wkRule (insert (neg L p) (widen d s)) e +
    wkRule (insert (neg L (shift L p)) (widen d (setShift L s)))
      (shiftRule (setShift L (fstIdx e)) e) +
    ρ ⟪freshVecInverse (s + d), e⟫

private lemma partnerBound_definable {ρ : V → V} (hρ : 𝚺ᴬ₁-Function₁ ρ) :
    𝚺ᴬ₁-Function₄ (partnerBound L ρ) := by
  have h₁ : 𝚺ᴬ₁-Function₄ fun d p s e : V ↦ wkRule (insert (neg L p) (widen d s)) e := by
    definability
  have h₂ : 𝚺ᴬ₁-Function₄ fun d p s e : V ↦ wkRule (insert (neg L (shift L p))
      (widen d (setShift L s))) (shiftRule (setShift L (fstIdx e)) e) := by
    definability
  have h₃ : 𝚺ᴬ₁-Function₄ fun (d _ s e : V) ↦ ρ ⟪freshVecInverse (s + d), e⟫ := by
    definability
  unfold partnerBound
  definability

variable (L) in
/-- `y` codes a derivation of cut rank at most `r` of the image under `π₁ x` of the end-sequent of
`π₂ x`, whenever `π₂ x` codes a derivation of cut rank at most `r` and `π₁ x` a vector of terms. -/
private def IsRewriting (r x y : V) : Prop :=
  RankedDerivation (∅ : Theory L) r (π₂ x) → IsSemitermVec L (len (π₁ x)) 0 (π₁ x) →
    RankedDerivationOf (∅ : Theory L) r y (fvSubstImage (L := L) (π₁ x) (fstIdx (π₂ x)))

private lemma exists_rewriting (r : V) :
    ∃ ρ : V → V, (𝚺ᴬ₁-Function₁ ρ) ∧ ∀ x, IsRewriting L r x (ρ x) := by
  apply ISigma1.exists_sigma1Function_of_forall_exists (by unfold IsRewriting; definability)
  intro x
  by_cases h : RankedDerivation (∅ : Theory L) r (π₂ x) ∧ IsSemitermVec L (len (π₁ x)) 0 (π₁ x)
  · obtain ⟨y, hy⟩ := RankedDerivable.rewrite (fun p hp ↦ absurd hp (not_mem_empty_Δ₁Class p))
      h.2 ⟨π₂ x, rfl, h.1⟩
    exact ⟨y, fun _ _ ↦ hy⟩
  · exact ⟨0, fun h₁ h₂ ↦ absurd ⟨h₁, h₂⟩ h⟩

/-! ### The cut reduction -/

section cutAux

variable {r : V}

private lemma RankedDerivationOf.weaken {e S s : V} (hS : IsFormulaSet L S) (hsub : s ⊆ S)
    (he : RankedDerivationOf (∅ : Theory L) r e s) :
    RankedDerivationOf (∅ : Theory L) r (wkRule S e) S :=
  ⟨by simp, Derivation.wkRule hS hsub ⟨he.1, he.2.1⟩, by simp [he.2.2]⟩

/-- Weakening the end-sequent `insert x s` of a derivation by `a` beside `x`. -/
private lemma RankedDerivationOf.wk_insert {e x a s : V} (ha : IsFormula L a)
    (he : RankedDerivationOf (∅ : Theory L) r e (insert x s)) :
    RankedDerivationOf (∅ : Theory L) r (wkRule (insert x (insert a s)) e)
      (insert x (insert a s)) := by
  have hs := IsFormulaSet.insert_iff.mp he.isFormulaSet
  exact he.weaken (by simp [hs.1, hs.2, ha])
    (insert_subset_insert_of_subset x (susbset_insert a s))

/-- Weakening the end-sequent `insert x s` of a derivation by `a` and `b` beside `x`. -/
private lemma RankedDerivationOf.wk_insert_insert {e x a b s : V} (ha : IsFormula L a)
    (hb : IsFormula L b) (he : RankedDerivationOf (∅ : Theory L) r e (insert x s)) :
    RankedDerivationOf (∅ : Theory L) r (wkRule (insert x (insert a (insert b s))) e)
      (insert x (insert a (insert b s))) := by
  have hs := IsFormulaSet.insert_iff.mp he.isFormulaSet
  exact he.weaken (by simp [hs.1, hs.2, ha, hb]) (insert_subset_insert_of_subset x
    fun y hy ↦ susbset_insert a _ (susbset_insert b s hy))

variable (L) in
/-- The cut reduction holds for every derivation coded below `d`, with cut formula, context and
partner derivation bounded by `bp`, `bs` and `be`. -/
private def CutBelow (r d bp bs be : V) : Prop :=
  ∀ d₀ < d, ∀ q ≤ bp, ∀ s₀ ≤ bs, ∀ e₀ ≤ be, formulaComplexity L q ≤ r → IsZeroOrExs L q →
    RankedDerivation (∅ : Theory L) r d₀ → fstIdx d₀ ⊆ insert q s₀ →
    RankedDerivationOf (∅ : Theory L) r e₀ (insert (neg L q) s₀) →
    RankedDerivable (∅ : Theory L) r s₀

variable {ρ : V → V} {p s e : V}

private lemma le_formulaBound (d p : V) : p ≤ formulaBound L d p :=
  le_trans le_self_add le_self_add

private lemma le_contextBound_insert {a d : V} (ha : a ≤ d) : insert a s ≤ contextBound L d s :=
  le_trans (le_of_subset (insert_subset_widen ha)) (le_trans le_self_add le_self_add)

private lemma le_contextBound_insert_insert {a b d : V} (ha : a ≤ d) (hb : b ≤ d) :
    insert a (insert b s) ≤ contextBound L d s :=
  le_trans (le_of_subset (insert_insert_subset_widen ha hb)) (le_trans le_self_add le_self_add)

private lemma le_partnerBound_insert {a d : V} (ha : a ≤ d) :
    wkRule (insert (neg L p) (insert a s)) e ≤ partnerBound L ρ d p s e :=
  le_trans (wkRule_le_wkRule (insert_subset_insert_of_subset _ (insert_subset_widen ha)))
    (le_trans le_self_add le_self_add)

private lemma le_contextBound_insert_setShift {a d : V} (ha : a ≤ d) :
    insert a (setShift L s) ≤ contextBound L d s :=
  le_trans (le_of_subset (insert_subset_widen ha)) (le_trans le_add_self le_self_add)

private lemma le_partnerBound_shift {a d : V} (ha : a ≤ d) :
    wkRule (insert (neg L (shift L p)) (insert a (setShift L s)))
      (shiftRule (setShift L (fstIdx e)) e) ≤ partnerBound L ρ d p s e :=
  le_trans (wkRule_le_wkRule (insert_subset_insert_of_subset _ (insert_subset_widen ha)))
    (le_trans le_add_self le_self_add)

private lemma le_partnerBound_insert_insert {a b d : V} (ha : a ≤ d) (hb : b ≤ d) :
    wkRule (insert (neg L p) (insert a (insert b s))) e ≤ partnerBound L ρ d p s e :=
  le_trans (wkRule_le_wkRule
    (insert_subset_insert_of_subset _ (insert_insert_subset_widen ha hb)))
    (le_trans le_self_add le_self_add)

private lemma le_of_mem_fstIdx {x d₀ d : V} (hx : x ∈ fstIdx d₀) (hd₀ : d₀ < d) : x ≤ d :=
  le_of_lt (lt_of_lt_of_le (lt_of_mem hx) (le_trans (fstIdx_le_self d₀) (le_of_lt hd₀)))

private lemma mem_of_mem_insert_of_isZeroOrExs {x : V} (hpg : IsZeroOrExs L p)
    (hx : x ∈ insert p s) (h₀ : formulaComplexity L x ≠ 0) (h₁ : ∀ a, x ≠ ^∃ a) : x ∈ s := by
  apply mem_of_mem_insert_of_ne hx
  rintro rfl
  rcases hpg with h | ⟨a, -, rfl⟩
  · exact h₀ h
  · exact h₁ a rfl

private lemma cut_aux_axL {Γ q : V} (hΓF : IsFormulaSet L Γ) (hsF : IsFormulaSet L s)
    (hpF : IsFormula L p) (hq : q ∈ Γ) (hnq : neg L q ∈ Γ) (hsub : Γ ⊆ insert p s)
    (he : RankedDerivationOf (∅ : Theory L) r e (insert (neg L p) s)) :
    RankedDerivable (∅ : Theory L) r s := by
  by_cases hn : neg L p ∈ s
  · rw [insert_eq_self_of_mem hn] at he
    exact ⟨e, he⟩
  · have h₁ : q ≠ p := by
      rintro rfl
      exact hn (mem_of_mem_insert_of_ne (hsub hnq) (neg_ne_self hpF.isUFormula))
    have h₂ : neg L q ≠ p := by
      intro h
      have hqp : q = neg L p := by rw [← h, (hΓF q hq).isUFormula.neg_neg]
      exact hn (hqp ▸ mem_of_mem_insert_of_ne (hsub hq) (hqp ▸ neg_ne_self hpF.isUFormula))
    exact .em hsF _ (mem_of_mem_insert_of_ne (hsub hq) h₁) (mem_of_mem_insert_of_ne (hsub hnq) h₂)

private lemma cut_aux_verum {Γ : V} (hsF : IsFormulaSet L s) (hv : ^⊤ ∈ Γ)
    (hsub : Γ ⊆ insert p s) (he : RankedDerivationOf (∅ : Theory L) r e (insert (neg L p) s)) :
    RankedDerivable (∅ : Theory L) r s := by
  by_cases hv' : (^⊤ : V) ∈ s
  · exact .verum hsF hv'
  · obtain rfl : (^⊤ : V) = p := (mem_bitInsert_iff.mp (hsub hv)).resolve_right hv'
    rw [neg_verum] at he
    exact RankedDerivable.of_insert_falsum ⟨e, he⟩

private lemma cut_aux_and {Γ a b da db : V}
    (ih : CutBelow L r (andIntro Γ a b da db) (formulaBound L (andIntro Γ a b da db) p)
      (contextBound L (andIntro Γ a b da db) s) (partnerBound L ρ (andIntro Γ a b da db) p s e))
    (hpc : formulaComplexity L p ≤ r) (hpg : IsZeroOrExs L p) (hΓF : IsFormulaSet L Γ)
    (hab : a ^⋏ b ∈ Γ) (hda : RankedDerivationOf (∅ : Theory L) r da (insert a Γ))
    (hdb : RankedDerivationOf (∅ : Theory L) r db (insert b Γ)) (hsub : Γ ⊆ insert p s)
    (he : RankedDerivationOf (∅ : Theory L) r e (insert (neg L p) s)) :
    RankedDerivable (∅ : Theory L) r s := by
  have habF : IsFormula L a ∧ IsFormula L b := by simpa using hΓF _ hab
  have hab' : a ^⋏ b ∈ s := mem_of_mem_insert_of_isZeroOrExs hpg (hsub hab)
    (by simp [habF.1.isUFormula, habF.2.isUFormula]) (by simp [qqAnd, qqExs])
  have ha : a ≤ andIntro Γ a b da db :=
    le_of_mem_fstIdx (by rw [hda.1]; simp) (dp_lt_andIntro _ _ _ _ _)
  have hb : b ≤ andIntro Γ a b da db :=
    le_of_mem_fstIdx (by rw [hdb.1]; simp) (dq_lt_andIntro _ _ _ _ _)
  exact .and_m hab'
    (ih da (dp_lt_andIntro _ _ _ _ _) p (le_formulaBound _ p) _ (le_contextBound_insert ha) _
      (le_partnerBound_insert ha) hpc hpg hda.2
      (by rw [hda.1]; exact insert_subset_insert_insert hsub)
      (RankedDerivationOf.wk_insert habF.1 he))
    (ih db (dq_lt_andIntro _ _ _ _ _) p (le_formulaBound _ p) _ (le_contextBound_insert hb) _
      (le_partnerBound_insert hb) hpc hpg hdb.2
      (by rw [hdb.1]; exact insert_subset_insert_insert hsub)
      (RankedDerivationOf.wk_insert habF.2 he))


private lemma cut_aux_or {Γ a b d₀ : V}
    (ih : CutBelow L r (orIntro Γ a b d₀) (formulaBound L (orIntro Γ a b d₀) p)
      (contextBound L (orIntro Γ a b d₀) s) (partnerBound L ρ (orIntro Γ a b d₀) p s e))
    (hpc : formulaComplexity L p ≤ r) (hpg : IsZeroOrExs L p) (hΓF : IsFormulaSet L Γ)
    (hab : a ^⋎ b ∈ Γ) (hd₀ : RankedDerivationOf (∅ : Theory L) r d₀ (insert a (insert b Γ)))
    (hsub : Γ ⊆ insert p s) (he : RankedDerivationOf (∅ : Theory L) r e (insert (neg L p) s)) :
    RankedDerivable (∅ : Theory L) r s := by
  have habF : IsFormula L a ∧ IsFormula L b := by simpa using hΓF _ hab
  have hab' : a ^⋎ b ∈ s := mem_of_mem_insert_of_isZeroOrExs hpg (hsub hab)
    (by simp [habF.1.isUFormula, habF.2.isUFormula]) (by simp [qqOr, qqExs])
  have ha : a ≤ orIntro Γ a b d₀ := le_of_mem_fstIdx (by rw [hd₀.1]; simp) (d_lt_orIntro _ _ _ _)
  have hb : b ≤ orIntro Γ a b d₀ := le_of_mem_fstIdx (by rw [hd₀.1]; simp) (d_lt_orIntro _ _ _ _)
  exact .or_m hab' <| ih d₀ (d_lt_orIntro _ _ _ _) p (le_formulaBound _ p) _
    (le_contextBound_insert_insert ha hb) _ (le_partnerBound_insert_insert ha hb) hpc hpg hd₀.2
    (by rw [hd₀.1]; exact insert_subset_insert_insert (insert_subset_insert_insert hsub))
    (RankedDerivationOf.wk_insert_insert habF.1 habF.2 he)

private lemma cut_aux_all {Γ a d₀ : V}
    (ih : CutBelow L r (allIntro Γ a d₀) (formulaBound L (allIntro Γ a d₀) p)
      (contextBound L (allIntro Γ a d₀) s) (partnerBound L ρ (allIntro Γ a d₀) p s e))
    (hpc : formulaComplexity L p ≤ r) (hpg : IsZeroOrExs L p) (hpF : IsFormula L p)
    (hΓF : IsFormulaSet L Γ) (ha : ^∀ a ∈ Γ)
    (hd₀ : RankedDerivationOf (∅ : Theory L) r d₀ (insert (free L a) (setShift L Γ)))
    (hsub : Γ ⊆ insert p s) (he : RankedDerivationOf (∅ : Theory L) r e (insert (neg L p) s)) :
    RankedDerivable (∅ : Theory L) r s := by
  have haF : IsSemiformula L 1 a := by simpa using hΓF _ ha
  have ha' : ^∀ a ∈ s := mem_of_mem_insert_of_isZeroOrExs hpg (hsub ha)
    (by simp [haF.isUFormula]) (by simp [qqAll, qqExs])
  have hfree : IsFormula L (free L a) := (IsFormulaSet.insert_iff.mp hd₀.isFormulaSet).1
  have hfa : free L a ≤ allIntro Γ a d₀ :=
    le_of_mem_fstIdx (by rw [hd₀.1]; simp) (s_lt_allIntro _ _ _)
  have hsh : RankedDerivationOf (∅ : Theory L) r (shiftRule (setShift L (fstIdx e)) e)
      (insert (neg L (shift L p)) (setShift L s)) :=
    ⟨by rw [fstIdx_shiftRule, he.1, mem_setShift_insert, shift_neg hpF],
      Derivation.shiftRule ⟨rfl, he.2.1⟩, by simp [he.2.2]⟩
  exact .all_m ha' <| ih d₀ (s_lt_allIntro _ _ _) (shift L p) (le_trans le_add_self le_self_add) _
    (le_contextBound_insert_setShift hfa) _ (le_partnerBound_shift hfa)
    (by rwa [formulaComplexity_shift hpF.isUFormula])
    ((isZeroOrExs_shift_iff hpF.isUFormula).mpr hpg) hd₀.2
    (by
      rw [hd₀.1]
      apply insert_subset_insert_insert
      rw [← mem_setShift_insert]
      exact setShift_subset_setShift hsub)
    (RankedDerivationOf.wk_insert hfree hsh)

private lemma cut_aux_exs {Γ a t d₀ : V}
    (ih : CutBelow L r (exsIntro Γ a t d₀) (formulaBound L (exsIntro Γ a t d₀) p)
      (contextBound L (exsIntro Γ a t d₀) s) (partnerBound L ρ (exsIntro Γ a t d₀) p s e))
    (hpc : formulaComplexity L p ≤ r) (hpg : IsZeroOrExs L p) (hΓF : IsFormulaSet L Γ)
    (ha : ^∃ a ∈ Γ) (ht : IsTerm L t)
    (hd₀ : RankedDerivationOf (∅ : Theory L) r d₀ (insert (substs1 L t a) Γ))
    (hsub : Γ ⊆ insert p s) (he : RankedDerivationOf (∅ : Theory L) r e (insert (neg L p) s)) :
    RankedDerivable (∅ : Theory L) r s := by
  have haF : IsSemiformula L 1 a := by simpa using hΓF _ ha
  have hx : substs1 L t a ≤ exsIntro Γ a t d₀ :=
    le_of_mem_fstIdx (by rw [hd₀.1]; simp) (d_lt_exsIntro _ _ _ _)
  have h₁ := ih d₀ (d_lt_exsIntro _ _ _ _) p (le_formulaBound _ p) _ (le_contextBound_insert hx) _
    (le_partnerBound_insert hx) hpc hpg hd₀.2
    (by rw [hd₀.1]; exact insert_subset_insert_insert hsub)
    (RankedDerivationOf.wk_insert (haF.substs1 ht) he)
  by_cases hap : ^∃ a = p
  · subst hap
    rw [neg_ex haF.isUFormula] at he
    rw [formulaComplexity_ex haF.isUFormula] at hpc
    have h₂ := RankedDerivation.inversion_all ht he
    rw [show substs1 L t (neg L a) = neg L (substs1 L t a) from
      substs_neg haF (by simp [ht] : IsSemitermVec L 1 0 (?[t] : V))] at h₂
    exact .cut (by rw [fomulaComplexity_substs1 haF ht]; exact lt_of_lt_of_le (by simp) hpc) h₁ h₂
  · exact .ex_m (mem_of_mem_insert_of_ne (hsub ha) hap) ht h₁

private lemma cut_aux_shift {d₀ : V} (hρ : ∀ x, IsRewriting L r x (ρ x))
    (ih : CutBelow L r (shiftRule (setShift L (fstIdx d₀)) d₀)
      (formulaBound L (shiftRule (setShift L (fstIdx d₀)) d₀) p)
      (contextBound L (shiftRule (setShift L (fstIdx d₀)) d₀) s)
      (partnerBound L ρ (shiftRule (setShift L (fstIdx d₀)) d₀) p s e))
    (hpc : formulaComplexity L p ≤ r) (hpg : IsZeroOrExs L p) (hsF : IsFormulaSet L s)
    (hd₀ : RankedDerivation (∅ : Theory L) r d₀) (hsub : setShift L (fstIdx d₀) ⊆ insert p s)
    (he : RankedDerivationOf (∅ : Theory L) r e (insert (neg L p) s)) :
    RankedDerivable (∅ : Theory L) r s := by
  set d := shiftRule (setShift L (fstIdx d₀)) d₀
  by_cases hp' : p ∈ setShift L (fstIdx d₀)
  · obtain ⟨p₀, hp₀, rfl⟩ := mem_setShift_iff.mp hp'
    have hΔ := hd₀.isFormulaSet
    have hp₀F : IsFormula L p₀ := hΔ p₀ hp₀
    obtain ⟨hw, hvw, hwv⟩ := freshVecInverse_spec (L := L) (s + d)
    have hΔN : fstIdx d₀ ≤ s + d :=
      le_trans (le_trans (fstIdx_le_self d₀) (le_of_lt (d_lt_shiftRule _ _))) le_add_self
    have hback : ∀ q, IsFormula L q → q ≤ s + d →
        fvSubst L (freshVecInverse (s + d)) (shift L q) = q := by
      intro q hq hqN
      rw [← fvSubst_eq_shift (by simp) (fun x hx ↦ nth_freshVec_of_lt hx) hq hqN]
      exact fvSubst_fvSubst_eq_self (isSemitermVec_freshVec (s + d)) hvw hq hqN
    have he' := hρ ⟪freshVecInverse (s + d), e⟫ (by simpa using he.2) (by simpa using hw)
    simp only [pi₁_pair, pi₂_pair] at he'
    rw [he.1, fvSubstImage_insert, fvSubst_neg hw hp₀F.shift,
      hback _ hp₀F (le_trans (le_of_lt (lt_of_mem hp₀)) hΔN)] at he'
    have h₂ : fstIdx d₀ ⊆ insert p₀ (fvSubstImage (L := L) (freshVecInverse (s + d)) s) := by
      intro x hx
      have hxN : x ≤ s + d := le_trans (le_of_lt (lt_of_mem hx)) hΔN
      rcases mem_bitInsert_iff.mp (hsub (shift_mem_setShift hx)) with h | h
      · rw [shift_inj (hΔ x hx).isUFormula hp₀F.isUFormula h]
        simp
      · exact mem_bitInsert_iff.mpr <| Or.inr <|
          mem_fvSubstImage_iff.mpr ⟨_, h, (hback x (hΔ x hx) hxN).symm⟩
    have h := ih d₀ (d_lt_shiftRule _ _) p₀
      (le_trans (le_of_mem_fstIdx hp₀ (d_lt_shiftRule _ _)) le_add_self) _
      le_add_self _ le_add_self
      (by rwa [formulaComplexity_shift hp₀F.isUFormula] at hpc)
      ((isZeroOrExs_shift_iff hp₀F.isUFormula).mp hpg) hd₀ h₂ he'
    have h₃ := RankedDerivable.rewrite (fun q hq ↦ absurd hq (not_mem_empty_Δ₁Class q))
      (isSemitermVec_freshVec (s + d)) h
    rwa [fvSubstImage_fvSubstImage_eq_self hw hwv hsF le_self_add] at h₃
  · exact .wk hsF (fun x hx ↦ mem_of_mem_insert_of_ne (hsub hx) (by rintro rfl; exact hp' hx))
      (.shift_m ⟨d₀, rfl, hd₀⟩)

private lemma cut_aux_cut {Γ q d₁ d₂ : V}
    (ih : CutBelow L r (cutRule Γ q d₁ d₂) (formulaBound L (cutRule Γ q d₁ d₂) p)
      (contextBound L (cutRule Γ q d₁ d₂) s) (partnerBound L ρ (cutRule Γ q d₁ d₂) p s e))
    (hpc : formulaComplexity L p ≤ r) (hpg : IsZeroOrExs L p) (hq : formulaComplexity L q < r)
    (hd₁ : RankedDerivationOf (∅ : Theory L) r d₁ (insert q Γ))
    (hd₂ : RankedDerivationOf (∅ : Theory L) r d₂ (insert (neg L q) Γ)) (hsub : Γ ⊆ insert p s)
    (he : RankedDerivationOf (∅ : Theory L) r e (insert (neg L p) s)) :
    RankedDerivable (∅ : Theory L) r s := by
  have hqF : IsFormula L q := (IsFormulaSet.insert_iff.mp hd₁.isFormulaSet).1
  have hq₁ : q ≤ cutRule Γ q d₁ d₂ :=
    le_of_mem_fstIdx (by rw [hd₁.1]; simp) (d₁_lt_cutRule _ _ _ _)
  have hq₂ : neg L q ≤ cutRule Γ q d₁ d₂ :=
    le_of_mem_fstIdx (by rw [hd₂.1]; simp) (d₂_lt_cutRule _ _ _ _)
  exact .cut hq
    (ih d₁ (d₁_lt_cutRule _ _ _ _) p (le_formulaBound _ p) _ (le_contextBound_insert hq₁) _
      (le_partnerBound_insert hq₁) hpc hpg hd₁.2
      (by rw [hd₁.1]; exact insert_subset_insert_insert hsub) (RankedDerivationOf.wk_insert hqF he))
    (ih d₂ (d₂_lt_cutRule _ _ _ _) p (le_formulaBound _ p) _ (le_contextBound_insert hq₂) _
      (le_partnerBound_insert hq₂) hpc hpg hd₂.2
      (by rw [hd₂.1]; exact insert_subset_insert_insert hsub)
      (RankedDerivationOf.wk_insert hqF.neg he))

end cutAux

/-- A cut on a formula `p` of complexity at most `r` that has complexity zero or is existential,
where the end-sequent of a derivation of cut rank at most `r` is covered by `p` beside the context,
is replaced by a derivation of cut rank at most `r`. -/
private lemma cut_aux (r : V) :
    ∀ d p s e : V, formulaComplexity L p ≤ r → IsZeroOrExs L p →
      RankedDerivation (∅ : Theory L) r d → fstIdx d ⊆ insert p s →
      RankedDerivationOf (∅ : Theory L) r e (insert (neg L p) s) →
      RankedDerivable (∅ : Theory L) r s := by
  obtain ⟨ρ, hρ, hρR⟩ := exists_rewriting (L := L) r
  have hfy : 𝚺ᴬ₁-Function₄ fun d p (_ _ : V) ↦ formulaBound L d p := by
    unfold formulaBound
    definability
  have hfz : 𝚺ᴬ₁-Function₄ fun d (_ : V) s (_ : V) ↦ contextBound L d s := by
    unfold contextBound
    definability
  apply bounded_all_sigma1_order_induction₃ hfy hfz (partnerBound_definable (L := L) hρ)
    (P := fun d p s e ↦ formulaComplexity L p ≤ r → IsZeroOrExs L p →
      RankedDerivation (∅ : Theory L) r d → fstIdx d ⊆ insert p s →
      RankedDerivationOf (∅ : Theory L) r e (insert (neg L p) s) →
      RankedDerivable (∅ : Theory L) r s) (by unfold IsZeroOrExs; definability)
  intro d p s e ih hpc hpg hd hsub he
  have ih' : CutBelow L r d (formulaBound L d p) (contextBound L d s)
      (partnerBound L ρ d p s e) := ih
  have hsF : IsFormulaSet L s := (IsFormulaSet.insert_iff.mp he.isFormulaSet).2
  have hpF : IsFormula L p := (IsFormulaSet.insert_iff.mp he.isFormulaSet).1.elim_neg
  have hΓF := hd.isFormulaSet
  rcases hd.case.2 with (⟨Γ, q, rfl, hq, hnq⟩ | ⟨Γ, rfl, hv⟩ |
    ⟨Γ, a, b, da, db, rfl, hab, hda, hdb⟩ | ⟨Γ, a, b, d₀, rfl, hab, hd₀⟩ |
    ⟨Γ, a, d₀, rfl, ha, hd₀⟩ | ⟨Γ, a, t, d₀, rfl, ha, ht, hd₀⟩ |
    ⟨Γ, d₀, rfl, hΓ, hd₀⟩ | ⟨Γ, d₀, rfl, rfl, hd₀⟩ | ⟨Γ, q, d₁, d₂, rfl, hq, hd₁, hd₂⟩ |
    ⟨Γ, q, rfl, -, hT⟩)
  · rw [fstIdx_axL] at hsub hΓF
    exact cut_aux_axL hΓF hsF hpF hq hnq hsub he
  · rw [fstIdx_verumIntro] at hsub
    exact cut_aux_verum hsF hv hsub he
  · rw [fstIdx_andIntro] at hsub hΓF
    exact cut_aux_and ih' hpc hpg hΓF hab hda hdb hsub he
  · rw [fstIdx_orIntro] at hsub hΓF
    exact cut_aux_or ih' hpc hpg hΓF hab hd₀ hsub he
  · rw [fstIdx_allIntro] at hsub hΓF
    exact cut_aux_all ih' hpc hpg hpF hΓF ha hd₀ hsub he
  · rw [fstIdx_exsIntro] at hsub hΓF
    exact cut_aux_exs ih' hpc hpg hΓF ha ht hd₀ hsub he
  · rw [fstIdx_wkRule] at hsub
    exact ih' d₀ (d_lt_wkRule _ _) p (le_formulaBound _ p) s
      (le_trans (le_of_subset (subset_widen _ s)) (le_trans le_self_add le_self_add)) e
      (le_trans (le_of_lt (d_lt_wkRule _ _)) (le_trans le_self_add le_self_add)) hpc hpg hd₀
      (fun x hx ↦ hsub (hΓ hx)) he
  · rw [fstIdx_shiftRule] at hsub
    exact cut_aux_shift hρR ih' hpc hpg hsF hd₀ hsub he
  · rw [fstIdx_cutRule] at hsub
    exact cut_aux_cut ih' hpc hpg hq hd₁ hd₂ hsub he
  · exact absurd hT (not_mem_empty_Δ₁Class q)

/-! ### Lowering the cut rank -/

variable {r : V}

/-- A cut on a conjunction of complexity at most `r` between derivations of cut rank at most `r`
becomes two cuts on its conjuncts. -/
private lemma cut_and {q q' s : V} (hc : formulaComplexity L (q ^⋏ q') ≤ r)
    (h₁ : RankedDerivable (∅ : Theory L) r (insert (q ^⋏ q') s))
    (h₂ : RankedDerivable (∅ : Theory L) r (insert (neg L (q ^⋏ q')) s)) :
    RankedDerivable (∅ : Theory L) r s := by
  have hqF : IsFormula L q ∧ IsFormula L q' := by
    simpa using (IsFormulaSet.insert_iff.mp h₁.isFormulaSet).1
  rw [neg_and hqF.1.isUFormula hqF.2.isUFormula] at h₂
  rw [formulaComplexity_and hqF.1.isUFormula hqF.2.isUFormula] at hc
  obtain ⟨d₁, hd₁⟩ := h₁
  obtain ⟨d₂, hd₂⟩ := h₂
  obtain ⟨e₂, he₂⟩ := RankedDerivation.inversion_and (Or.inr rfl) hd₁
  have h₃ : RankedDerivable (∅ : Theory L) r (insert (neg L q) s) :=
    .cut (lt_of_lt_of_le (lt_max_succ_right _ _) hc) ⟨_, RankedDerivationOf.wk_insert hqF.1.neg he₂⟩
      (by rw [insert_comm]; exact RankedDerivation.inversion_or hd₂)
  exact .cut (lt_of_lt_of_le (lt_max_succ_left _ _) hc)
    (RankedDerivation.inversion_and (Or.inl rfl) hd₁) h₃

private lemma cut_of_isZeroOrExs {p s : V} (hp : formulaComplexity L p ≤ r) (hpg : IsZeroOrExs L p)
    (h₁ : RankedDerivable (∅ : Theory L) r (insert p s))
    (h₂ : RankedDerivable (∅ : Theory L) r (insert (neg L p) s)) :
    RankedDerivable (∅ : Theory L) r s := by
  obtain ⟨d₁, hd₁⟩ := h₁
  obtain ⟨d₂, hd₂⟩ := h₂
  exact cut_aux r d₁ p s d₂ hp hpg hd₁.2 (by rw [hd₁.1]) hd₂

/-- A cut on a formula of complexity at most `r` between derivations of cut rank at most `r` over
the empty theory is replaced by a derivation of cut rank at most `r`.
- [Bus98, Lemma 2.4.2.1] -/
theorem RankedDerivable.cut_of_le {p s : V} (hp : formulaComplexity L p ≤ r)
    (h₁ : RankedDerivable (∅ : Theory L) r (insert p s))
    (h₂ : RankedDerivable (∅ : Theory L) r (insert (neg L p) s)) :
    RankedDerivable (∅ : Theory L) r s := by
  have hpF : IsUFormula L p := (IsFormulaSet.insert_iff.mp h₁.isFormulaSet).1.isUFormula
  rcases hpF.case with (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl |
    ⟨q, q', hq, hq', rfl⟩ | ⟨q, q', hq, hq', rfl⟩ | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
  · exact cut_of_isZeroOrExs hp (.inl (by simp [hR, hv])) h₁ h₂
  · exact cut_of_isZeroOrExs hp (.inl (by simp [hR, hv])) h₁ h₂
  · exact cut_of_isZeroOrExs hp (.inl (by simp)) h₁ h₂
  · exact cut_of_isZeroOrExs hp (.inl (by simp)) h₁ h₂
  · exact cut_and hp h₁ h₂
  · rw [neg_or hq hq'] at h₂
    apply cut_and (by simpa [hq, hq', hq.neg, hq'.neg] using hp) h₂
    rw [neg_and hq.neg hq'.neg, hq.neg_neg, hq'.neg_neg]
    exact h₁
  · rw [neg_all hq] at h₂
    exact cut_of_isZeroOrExs (by simpa [hq, hq.neg] using hp) (.inr ⟨neg L q, by simp, rfl⟩) h₂
      (by rwa [neg_ex hq.neg, hq.neg_neg])
  · exact cut_of_isZeroOrExs hp (.inr ⟨q, by simp, rfl⟩) h₁ h₂

/-- A derivation of cut rank at most `r + 1` over the empty theory has a counterpart of cut rank
at most `r` with the same end-sequent.
- [Bus98, Lemma 2.4.2.2] -/
theorem RankedDerivable.of_succ {s : V} (h : RankedDerivable (∅ : Theory L) (r + 1) s) :
    RankedDerivable (∅ : Theory L) r s := by
  obtain ⟨d, rfl, hd, hr⟩ := h
  revert hr
  apply Derivation.induction1 𝚺
    (P := fun d ↦ cutRank L d ≤ r + 1 → RankedDerivable (∅ : Theory L) r (fstIdx d)) ?_ hd
  · intro s hs p hp hn _
    simpa using RankedDerivable.em hs p hp hn
  · intro s hs hv _
    simpa using RankedDerivable.verum hs hv
  · intro s _ p q dp dq hpq hdp hdq ihp ihq hr
    simp only [cutRank_andIntro, max_le_iff] at hr
    simpa using RankedDerivable.and_m hpq (hdp.1 ▸ ihp hr.1) (hdq.1 ▸ ihq hr.2)
  · intro s _ p q d hpq hd ih hr
    simpa using RankedDerivable.or_m hpq (hd.1 ▸ ih (by simpa using hr))
  · intro s _ p d hp hd ih hr
    simpa using RankedDerivable.all_m hp (hd.1 ▸ ih (by simpa using hr))
  · intro s _ p t d hp ht hd ih hr
    simpa using RankedDerivable.ex_m hp ht (hd.1 ▸ ih (by simpa using hr))
  · intro s hs d hsd _ ih hr
    simpa using RankedDerivable.wk hs hsd (ih (by simpa using hr))
  · rintro s _ d rfl _ ih hr
    simpa using (ih (by simpa using hr)).shift_m
  · intro s _ p d₁ d₂ hd₁ hd₂ ih₁ ih₂ hr
    simp only [cutRank_cutRule, max_le_iff] at hr
    simpa using RankedDerivable.cut_of_le (le_of_add_le_add_right hr.2) (hd₁.1 ▸ ih₁ hr.1.1)
      (hd₂.1 ▸ ih₂ hr.1.2)
  · intro s _ p _ hT
    exact absurd hT (not_mem_empty_Δ₁Class p)
  · definability

/-- Cut elimination: every sequent derivable over the empty theory is cut-free derivable.
- [Bus98, Theorem 2.4.2]
- [AB05, Theorem 152] -/
theorem Derivable.cutFree {s : V} (h : Derivable (∅ : Theory L) s) :
    CutFreeDerivable (∅ : Theory L) s := by
  obtain ⟨d, rfl, hd⟩ := h
  have key : ∀ j ≤ cutRank L d, RankedDerivable (∅ : Theory L) (cutRank L d - j) (fstIdx d) := by
    intro j
    induction j using ISigma1.sigma1_succ_induction
    · definability
    case zero => exact fun _ ↦ ⟨d, rfl, hd, by simp⟩
    case succ j ih =>
      intro hj
      apply RankedDerivable.of_succ
      rw [← sub_sub, sub_add_self_of_le (le_tsub_of_add_le_left hj)]
      exact ih (le_trans le_self_add hj)
  exact RankedDerivable.iff_cutFreeDerivable.mp (by simpa using key _ le_rfl)

/-- The cut rule is admissible in the cut-free calculus over the empty theory.
- [Bus98, Lemma 2.4.2.1] -/
theorem CutFreeDerivable.cut {p s : V} (h₁ : CutFreeDerivable (∅ : Theory L) (insert p s))
    (h₂ : CutFreeDerivable (∅ : Theory L) (insert (neg L p) s)) :
    CutFreeDerivable (∅ : Theory L) s :=
  Derivable.cutFree (.cut p h₁.toDerivable h₂.toDerivable)

end Bootstrapping
end FFL.FirstOrder.Arithmetic
