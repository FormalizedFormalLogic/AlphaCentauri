module

public import AlphaCentauri.Bootstrapping.Syntax.Iteration
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Basic

/-!
# Derivations under a block of universal quantifiers

If `p` follows from `q` in the internal calculus once the variables bound by a block of universal
quantifiers are replaced by free variables, then the block over `p` follows from the block over
`q`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

/-- If the free instance of `p` follows from that of `q`, then `^∀ p` follows from `^∀ q`. -/
lemma Derivable.neg_all_all {p q : V} (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q)
    (h : Derivable T (insert (neg L (free L q)) ({free L p} : V))) :
    Derivable T (insert (neg L (^∀ q)) ({^∀ p} : V)) := by
  have he : substs1 L ^&0 (neg L (Bootstrapping.shift L q)) = neg L (free L q) :=
    substs_neg hq.shift (m := 0) (by simp)
  rw [neg_all hq.isUFormula]
  apply Derivable.all_m (p := p) (by simp)
  apply Derivable.ex_m (p := neg L (Bootstrapping.shift L q)) (t := ^&0) ?_ (by simp)
  · rw [he]
    apply Derivable.wk ?_ ?_ h
    · simp [hp, hq]
    · intro x hx
      simp only [mem_bitInsert_iff, mem_singleton_iff] at hx ⊢
      tauto
  · simp [shift_neg hq, shift_exs hq.neg.isUFormula]

/-- Opening the outermost quantifier of `qqAlls (subst L v' r) i`, where `v'` keeps the innermost
`i + 1` bound variables of `r` and replaces the others by free variables, with the eigenvariable
`^&0`. -/
private lemma free_qqAlls_subst {m i v v' r : V} (hr : IsSemiformula L m r)
    (hsr : Bootstrapping.shift L r = r) (hvl : len v = m)
    (hv : ∀ x < m, (x < i → v.[x] = ^#x) ∧ (i ≤ x → v.[x] = ^&(x - i))) (hv'l : len v' = m)
    (hv' : ∀ x < m, (x < i + 1 → v'.[x] = ^#x) ∧ (i + 1 ≤ x → v'.[x] = ^&(x - (i + 1)))) :
    free L (qqAlls (subst L v' r) i) = qqAlls (subst L v r) i := by
  have hv's : IsSemitermVec L m (i + 1) v' := IsSemitermVec.iff.mpr ⟨hv'l, fun x hx ↦ by
    rcases lt_or_ge x (i + 1) with h | h
    · simp [(hv' x hx).1 h, h]
    · simp [(hv' x hx).2 h]⟩
  obtain ⟨u, hul, hu⟩ := sigmaOne_skolem_vec
    (R := fun x y : V ↦ (x < i → y = ^#x) ∧ (i ≤ x → y = ^&0)) (by definability) (l := i + 1)
    (fun x _ ↦ by
      by_cases hx : x < i
      · exact ⟨^#x, fun _ ↦ rfl, fun h ↦ absurd hx (not_lt.mpr h)⟩
      · exact ⟨^&0, fun h ↦ absurd h hx, fun _ ↦ rfl⟩)
  have hus : IsSemitermVec L (i + 1) i u := IsSemitermVec.iff.mpr ⟨hul, fun x hx ↦ by
    rcases lt_or_ge x i with h | h
    · simp [(hu x hx).1 h, h]
    · simp [(hu x hx).2 h]⟩
  rw [free_qqAlls (hr.subst hv's).isUFormula hul (fun x hx ↦ (hu x (lt_trans hx (by simp))).1 hx)
    ((hu i (by simp)).2 le_rfl), shift_substs hr hv's, hsr, substs_substs hr hus hv's.termShiftVec]
  congr 2
  apply nth_ext' m (by simp [hv's.termShiftVec.isUTerm]) hvl
  intro x hx
  rw [nth_termSubstVec hv's.termShiftVec.isUTerm hx, nth_termShiftVec hv's.isUTerm hx]
  rcases lt_trichotomy x i with hxi | rfl | hxi
  · rw [(hv' x hx).1 (lt_trans hxi (by simp)), termShift_bvar, termSubst_bvar,
      (hu x (lt_trans hxi (by simp))).1 hxi, (hv x hx).1 hxi]
  · rw [(hv' x hx).1 (by simp), termShift_bvar, termSubst_bvar, (hu x (by simp)).2 le_rfl,
      (hv x hx).2 le_rfl, tsub_self]
  · obtain ⟨j, rfl⟩ := exists_add_of_le (succ_le_iff_lt.mpr hxi)
    rw [(hv' _ hx).2 (by simp), termShift_fvar, termSubst_fvar, (hv _ hx).2 (by simp)]
    congr 1
    rw [add_tsub_cancel_left, add_assoc, add_tsub_cancel_left, add_comm]

/-- If `p` follows from `q` once their `m` bound variables are replaced by the free variables
`^&0, …, ^&(m - 1)`, then `qqAlls p m` follows from `qqAlls q m`. -/
theorem Derivable.neg_qqAlls_qqAlls {m p q : V} (hp : IsSemiformula L m p)
    (hq : IsSemiformula L m q) (hsp : Bootstrapping.shift L p = p)
    (hsq : Bootstrapping.shift L q = q)
    (h : Derivable T (insert (neg L (subst L (fvarVec m) q)) ({subst L (fvarVec m) p} : V))) :
    Derivable T (insert (neg L (qqAlls q m)) ({qqAlls p m} : V)) := by
  suffices ∀ i ≤ m, ∃ v, (len v = m ∧ ∀ x < m, (x < i → v.[x] = ^#x) ∧ (i ≤ x → v.[x] = ^&(x - i)))
      ∧ Derivable T (insert (neg L (qqAlls (subst L v q) i)) ({qqAlls (subst L v p) i} : V)) by
    obtain ⟨v, ⟨hvl, hv⟩, hd⟩ := this m le_rfl
    have hvm : IsSemitermVec L m m v :=
      IsSemitermVec.iff.mpr ⟨hvl, fun x hx ↦ by simp [(hv x hx).1 hx, hx]⟩
    rwa [subst_eq_self hp hvm fun x hx ↦ (hv x hx).1 hx,
      subst_eq_self hq hvm fun x hx ↦ (hv x hx).1 hx] at hd
  intro i
  induction i using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro _
    exact ⟨fvarVec m, ⟨len_fvarVec m, fun x hx ↦ ⟨by simp, fun _ ↦ by simp [nth_fvarVec m x hx]⟩⟩,
      by simpa using h⟩
  case succ i ih =>
    intro hi
    obtain ⟨v, ⟨hvl, hv⟩, hd⟩ := ih (le_trans (by simp) hi)
    obtain ⟨v', hv'l, hv'⟩ := sigmaOne_skolem_vec
      (R := fun x y : V ↦ (x < i + 1 → y = ^#x) ∧ (i + 1 ≤ x → y = ^&(x - (i + 1))))
      (by definability) (l := m) (fun x _ ↦ by
        by_cases hx : x < i + 1
        · exact ⟨^#x, fun _ ↦ rfl, fun h ↦ absurd hx (not_lt.mpr h)⟩
        · exact ⟨^&(x - (i + 1)), fun h ↦ absurd h hx, fun _ ↦ rfl⟩)
    have hv's : IsSemitermVec L m (i + 1) v' := IsSemitermVec.iff.mpr ⟨hv'l, fun x hx ↦ by
      rcases lt_or_ge x (i + 1) with h | h
      · simp [(hv' x hx).1 h, h]
      · simp [(hv' x hx).2 h]⟩
    have hs (r : V) (hr : IsSemiformula L m r) : IsSemiformula L 1 (qqAlls (subst L v' r) i) :=
      IsSemiformula.qqAlls (by simpa [add_comm] using hr.subst hv's)
    refine ⟨v', ⟨hv'l, hv'⟩, ?_⟩
    rw [qqAlls_succ, qqAlls_succ]
    apply Derivable.neg_all_all (hs p hp) (hs q hq)
    rwa [free_qqAlls_subst hp hsp hvl hv hv'l hv', free_qqAlls_subst hq hsq hvl hv hv'l hv']

end FFL.FirstOrder.Arithmetic.Bootstrapping
