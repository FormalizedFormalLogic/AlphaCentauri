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
  sorry

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
