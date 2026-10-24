module

public import AlphaCentauri.Bootstrapping.Proof.Substitution
public import AlphaCentauri.ToFoundation.TypedProof
public import Foundation.Meta.ClProver

/-!
# Existential elimination in the internal calculus

Internal `∃`-elimination with fresh eigenvariables, iterated over a finite conjunction of
existential hypotheses. For a formula code `d` and a bound `m`, the coded set `negDomSet L d m`
collects the negations of the instances `substs1 L (^&i) d` with `i < m`. The module records its
membership, definability, behaviour under successor and shift, and the internal existential
elimination rule with the free variables of the instances as eigenvariables.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Conjunctions of existential hypotheses -/

section existsElim

open scoped FFL.FirstOrder.Arithmetic

section

variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

lemma Derivable.insert_neg_of_imp {s : V} {φ ψ : Formula V L}
    (h : Derivable T (insert (φ 🡒 ψ).val s)) :
    Derivable T (insert (∼φ).val (insert ψ.val s)) := by
  have hs : IsFormulaSet L s := (IsFormulaSet.insert_iff.mp h.isFormulaSet).2
  have d : T.internalize V ⊢!ᵈᵉʳ insert (φ 🡒 ψ) ⟨s, hs⟩ :=
    Derivable.toTDerivation _ (by simpa using! h)
  have d' : T.internalize V ⊢!ᵈᵉʳ insert (∼φ) (insert ψ ⟨s, hs⟩) :=
    TDerivation.orInv (by simpa [Semiformula.imp_def] using d)
  simpa using! d'.toDerivable

lemma Semiformula.val_subst_fvar {φ : Semiformula V L 1} {u : V} :
    (φ.subst ![(Semiterm.fvar u : Semiterm V L 0)]).val = substs1 L ^&u φ.val := by
  simp [substs1]

/-- If `T` proves `⋀ᵢ ψᵢ(uᵢ) 🡒 Y` for every assignment `u` of free variables, and each `∃¹ ψᵢ` is
derivable under `s`, then `Y` is derivable under `s`.
- [HP98, Theorem I.4.9] -/
theorem Derivable.conj_exs_elim
    (hT : ∀ p ∈ T.Δ₁Class (V := V), Bootstrapping.shift L p = p) {k : ℕ}
    (ψ : Fin k → Semiformula V L 1) (Y : Formula V L) {s : V} (hs : IsFormulaSet L s)
    (hY : ∀ u : Fin k → V, T.internalize V ⊢
      Matrix.conj (fun i ↦ (ψ i).subst ![Semiterm.fvar (u i)]) 🡒 Y)
    (h : ∀ i, Derivable T (insert (∃¹ ψ i).val s)) :
    Derivable T (insert Y.val s) := by
  induction k generalizing Y with
  | zero =>
    have h₁ : T.internalize V ⊢ ⊤ 🡒 Y := hY fun i ↦ i.elim0
    exact Derivable.of_tprovable hs (by cl_prover [h₁])
  | succ k ih =>
    obtain ⟨u₀, hsu, hpu⟩ : ∃ u₀ : V, insert Y.val s ≤ u₀ ∧ (ψ 0).val ≤ u₀ :=
      ⟨(ψ 0).val + insert Y.val s, le_add_self, le_self_add⟩
    have e : ∀ f : Fin (k + 1) → Formula V L,
        Matrix.conj f = f 0 ⋏ Matrix.conj (fun i ↦ f i.succ) := fun _ ↦ rfl
    have hY' : ∀ u : Fin k → V, T.internalize V ⊢
        Matrix.conj (fun i ↦ (ψ i.succ).subst ![Semiterm.fvar (u i)]) 🡒
          (ψ 0).subst ![Semiterm.fvar u₀] 🡒 Y := by
      intro u
      have h₀ := hY (Fin.cons u₀ u)
      rw [e] at h₀
      simp only [Fin.cons_zero, Fin.cons_succ] at h₀
      cl_prover [h₀]
    have h₁ : Derivable T (insert (((ψ 0).subst ![Semiterm.fvar u₀]) 🡒 Y).val s) :=
      ih (fun i ↦ ψ i.succ) _ hY' (fun i ↦ h i.succ)
    have h₂ : Derivable T (insert (neg L (substs1 L ^&u₀ (ψ 0).val)) (insert Y.val s)) := by
      have h₂' := Derivable.insert_neg_of_imp h₁
      rwa [Semiformula.val_neg, Semiformula.val_subst_fvar] at h₂'
    have h₃ : Derivable T (insert (neg L (^∃ (ψ 0).val)) (insert Y.val s)) :=
      Derivable.neg_exs_of_fresh hT hsu hpu (by simp) h₂
    have hF : IsFormulaSet L (insert (∃¹ ψ 0).val (insert Y.val s)) := by
      simp [hs]
    have h₄ : Derivable T (insert (∃¹ ψ 0).val (insert Y.val s)) :=
      Derivable.wk hF (by intro x; simp; tauto) (h 0)
    exact Derivable.cut (∃¹ ψ 0).val h₄ h₃

end

end existsElim

/-! ## Negated instances over a bounded index set -/

section negDomSet

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

open PeanoMinus ISigma0 ISigma1

variable {L : Language} [L.Encodable] [L.LORDefinable]

section shiftSubsts1

lemma shift_substs1_qqFvar {p j : V} (hp : IsSemiformula L 1 p) :
    shift L (substs1 L (^&j) p) = substs1 L (^&(j + 1)) (shift L p) := by
  have hv : IsSemitermVec L 1 (0 : V) ?[^&j] := by simp
  rw [substs1, shift_substs hp hv]
  congr 1
  apply nth_ext' 1 (by simp) (by simp)
  intro i hi
  rcases (show i = 0 by simpa using hi)
  simp

lemma shift_neg_substs1_qqFvar {d j : V} (hd : IsSemiformula L 1 d) (hds : shift L d = d) :
    shift L (neg L (substs1 L (^&j) d)) = neg L (substs1 L (^&(j + 1)) d) := by
  rw [shift_neg (IsSemiformula.substs1 (n := 0) (by simp) hd), shift_substs1_qqFvar hd, hds]

lemma fvSubst_freshVec_neg_substs1_qqFvar {d i j : V} (hd : IsSemiformula L 1 d)
    (hds : shift L d = d) (hij : i < j) :
    fvSubst L (freshVec j) (neg L (substs1 L (^&i) d)) = neg L (substs1 L (^&(i + 1)) d) := by
  have hw : IsSemitermVec L (len (freshVec j : V)) 0 (freshVec j) := isSemitermVec_freshVec j
  have ht : IsSemiterm L 0 (^&i) := by simp
  have hil : i < len (freshVec j : V) := by
    rw [len_freshVec]
    exact lt_trans hij (by simp)
  rw [fvSubst_neg hw (IsSemiformula.substs1 ht hd), fvSubst_substs1 hw ht hd, termFvSubst_fvar,
    ite_eq_left hil, nth_freshVec_of_lt hij, fvSubst_eq_self_of_shift hd hds]

end shiftSubsts1

section negDomSet

variable (L) in
/-- `negDomSet L d m` is the coded set of the negations of the instances `substs1 L (^&i) d`
for `i < m`. -/
noncomputable def negDomSet (d m : V) : V := by
  letI : 𝚺ᴬ₁-Function₁ (fun i : V ↦ neg L (substs1 L (^&i) d)) := by definability
  exact hfsImage (fun i : V ↦ neg L (substs1 L (^&i) d)) (under m)

lemma mem_negDomSet_iff {d m x : V} :
    x ∈ negDomSet L d m ↔ ∃ i < m, x = neg L (substs1 L (^&i) d) := by
  let _ : 𝚺ᴬ₁-Function₁ (fun i : V ↦ neg L (substs1 L (^&i) d)) := by definability
  change x ∈ hfsImage (fun i : V ↦ neg L (substs1 L (^&i) d)) (under m) ↔ _
  rw [mem_hfsImage_iff]
  simp only [mem_under_iff]

variable (L) in
/-- The $\Sigma_1$ graph of `negDomSet`; argument order `(t, d, m)`, `t = negDomSet d m`. -/
noncomputable def negDomSetGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “y d m. (∀ z ∈' y, ∃ i < m, ∃ fi, !qqFvarDef fi i ∧ ∃ s, !(substs1Graph L) s fi d ∧
      !(negGraph L) z s) ∧
    (∀ i < m, ∃ fi, !qqFvarDef fi i ∧ ∃ s, !(substs1Graph L) s fi d ∧ ∃ z, !(negGraph L) z s ∧
      z ∈ y)”

section graph

private lemma negDomSet_graph (t d m : V) :
    t = negDomSet L d m ↔ (∀ z ∈ t, ∃ i < m, z = neg L (substs1 L (^&i) d)) ∧
      (∀ i < m, neg L (substs1 L (^&i) d) ∈ t) := by
  constructor
  · rintro rfl
    exact ⟨fun z hz ↦ mem_negDomSet_iff.mp hz, fun i hi ↦ mem_negDomSet_iff.mpr ⟨i, hi, rfl⟩⟩
  · rintro ⟨h₁, h₂⟩
    apply mem_ext
    intro z
    constructor
    · intro hz
      exact mem_negDomSet_iff.mpr (h₁ z hz)
    · intro hz
      obtain ⟨i, hi, rfl⟩ := mem_negDomSet_iff.mp hz
      exact h₂ i hi

instance negDomSet.defined : 𝚺ᴬ₁-Function₂[V] negDomSet L via negDomSetGraph L :=
  .mk fun v ↦ by simp [negDomSetGraph, negDomSet_graph]

instance negDomSet.definable : 𝚺ᴬ₁-Function₂[V] negDomSet L :=
  negDomSet.defined.to_definable

instance negDomSet.definable' {Γ : SigmaPiDelta} {m : ℕ} : Γᴬ_[m + 1]-Function₂[V] negDomSet L :=
  negDomSet.definable.of_sigmaOne

end graph

@[simp] lemma negDomSet_zero (d : V) : negDomSet L d 0 = ∅ := by
  apply mem_ext
  intro x
  simp [mem_negDomSet_iff]

lemma negDomSet_succ (d m : V) :
    negDomSet L d (m + 1) = insert (neg L (substs1 L (^&m) d)) (negDomSet L d m) := by
  apply mem_ext
  intro x
  simp only [mem_negDomSet_iff, mem_bitInsert_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with h | rfl
    · exact Or.inr ⟨i, h, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨m, by simp, rfl⟩
    · exact ⟨i, lt_trans hi (by simp), rfl⟩

lemma negDomSet_mono {d m m' : V} (h : m ≤ m') : negDomSet L d m ⊆ negDomSet L d m' := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_negDomSet_iff.mp hx
  exact mem_negDomSet_iff.mpr ⟨i, lt_of_lt_of_le hi h, rfl⟩

lemma IsFormulaSet.negDomSet {d : V} (hd : IsSemiformula L 1 d) (m : V) :
    IsFormulaSet L (negDomSet L d m) := by
  intro p hp
  obtain ⟨i, _, rfl⟩ := mem_negDomSet_iff.mp hp
  exact (IsSemiformula.substs1 (n := 0) (by simp) hd).neg

lemma negDomSet_succ_eq_insert_setShift {d : V} (hd : IsSemiformula L 1 d)
    (hds : Bootstrapping.shift L d = d) (m : V) :
    negDomSet L d (m + 1) = insert (neg L (substs1 L (^&0) d)) (setShift L (negDomSet L d m)) := by
  apply mem_ext
  intro x
  simp only [mem_negDomSet_iff, mem_bitInsert_iff, mem_setShift_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases zero_or_succ i with rfl | ⟨j, rfl⟩
    · exact Or.inl rfl
    · have hj : j < m := by simpa using hi
      exact Or.inr ⟨neg L (substs1 L (^&j) d), ⟨j, hj, rfl⟩,
        (shift_neg_substs1_qqFvar hd hds).symm⟩
  · rintro (rfl | ⟨y, ⟨j, hj, rfl⟩, rfl⟩)
    · exact ⟨0, by simp, rfl⟩
    · exact ⟨j + 1, by simpa using hj, (shift_neg_substs1_qqFvar hd hds)⟩

lemma fvSubstImage_freshVec_negDomSet {d : V} (hd : IsSemiformula L 1 d)
    (hds : Bootstrapping.shift L d = d) (j : V) :
    fvSubstImage (L := L) (freshVec j) (negDomSet L d j) = setShift L (negDomSet L d j) := by
  apply mem_ext
  intro x
  rw [mem_fvSubstImage_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨i, hi, rfl⟩ := mem_negDomSet_iff.mp hq
    rw [fvSubst_freshVec_neg_substs1_qqFvar hd hds hi]
    exact mem_setShift_iff.mpr ⟨neg L (substs1 L (^&i) d), mem_negDomSet_iff.mpr ⟨i, hi, rfl⟩,
      (shift_neg_substs1_qqFvar hd hds).symm⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_setShift_iff.mp hx
    obtain ⟨i, hi, rfl⟩ := mem_negDomSet_iff.mp hy
    exact ⟨neg L (substs1 L (^&i) d), mem_negDomSet_iff.mpr ⟨i, hi, rfl⟩,
      (shift_neg_substs1_qqFvar hd hds).trans (fvSubst_freshVec_neg_substs1_qqFvar hd hds hi).symm⟩

lemma fvSubstImage_union (w s₁ s₂ : V) :
    fvSubstImage (L := L) w (s₁ ∪ s₂) =
      fvSubstImage (L := L) w s₁ ∪ fvSubstImage (L := L) w s₂ := by
  apply mem_ext
  intro x
  simp only [mem_fvSubstImage_iff, mem_cup_iff]
  constructor
  · rintro ⟨q, hq | hq, rfl⟩
    · exact Or.inl ⟨q, hq, rfl⟩
    · exact Or.inr ⟨q, hq, rfl⟩
  · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact ⟨q, Or.inl hq, rfl⟩
    · exact ⟨q, Or.inr hq, rfl⟩

section freshShift

lemma fvSubst_freshVec_shift {n q u j : V} (hq : IsSemiformula L n q) (hqu : q ≤ u)
    (huj : u < j) :
    fvSubst L (freshVec j) (shift L q) = shift L (shift L q) := by
  have hfu : IsSemitermVec L (len (freshVec u : V)) 0 (freshVec u) := isSemitermVec_freshVec u
  have hfu' : IsSemitermVec L (u + 1) 0 (freshVec u) := by simpa using hfu
  let v : V := termShiftVec L (u + 1) (freshVec u)
  have hvlen : len v = u + 1 := by simp [v, hfu'.isUTerm]
  have hvx : ∀ x < u, v.[x] = ^&(x + 1 + 1) := by
    intro x hx
    simp [v, nth_termShiftVec hfu'.isUTerm (lt_trans hx (by simp)), nth_freshVec_of_lt hx]
  have h1 : fvSubst L (freshVec j) (shift L q) = fvSubst L v q := by
    refine fvSubst_shift (u := u)
      (fun x hx ↦ ⟨by rw [hvlen]; exact lt_trans hx (by simp), ?_⟩) hq hqu
    have hx1 : x + 1 < j := lt_of_le_of_lt (succ_le_iff_lt.mpr hx) huj
    have hxl1 : x + 1 < len (freshVec j : V) := by rw [len_freshVec]; exact lt_trans hx1 (by simp)
    rw [hvx x hx, termFvSubst_fvar, ite_eq_left hxl1, nth_freshVec_of_lt hx1]
  have h2 : shift L q = fvSubst L (freshVec u) q :=
    (fvSubst_eq_shift (by simp) (fun _ hx ↦ nth_freshVec_of_lt hx) hq hqu).symm
  rw [h1, h2, shift_fvSubst (hfu.weaken (by simp)) hq]
  refine (fvSubst_shift (u := u)
    (fun x hx ↦ ⟨by rw [hvlen]; exact lt_trans hx (by simp), ?_⟩) hq hqu).symm
  have hxl : x < len (freshVec u : V) := by rw [len_freshVec]; exact lt_trans hx (by simp)
  have hxl' : x + 1 < len (^&0 ∷ termShiftVec L (len (freshVec u : V)) (freshVec u) : V) := by
    rw [len_adjoin, len_termShiftVec hfu.isUTerm]; simpa using hxl
  rw [hvx x hx, termFvSubst_fvar, ite_eq_left hxl',
    nth_adjoin_succ, nth_termShiftVec hfu.isUTerm hxl, nth_freshVec_of_lt hx, termShift_fvar]

lemma fvSubst_freshVec_free {p u j : V} (hp : IsSemiformula L 1 p) (hpu : p ≤ u) (huj : u < j) :
    fvSubst L (freshVec j) (free L p) = shift L (free L p) := by
  have hj : (0 : V) < j := lt_of_le_of_lt zero_le huj
  rw [free, substs1, fvSubst_subst (n := 1) (m := 0) (isSemitermVec_freshVec j) (by simp) hp.shift,
    fvSubst_freshVec_shift hp hpu huj, shift_substs (m := 0) hp.shift (by simp)]
  congr 1
  apply nth_ext' 1 (by simp) (by simp)
  intro i hi
  rcases (show i = 0 by simpa using hi)
  simpa [termFvSubst_fvar, hj] using nth_freshVec_of_lt hj

end freshShift

end negDomSet

section elim

variable {T : Theory L} [T.Δ₁]

/-- If `Δ` has a fresh eigenvariable at every `j` in `[m, m')`, then the derivability of `Δ`
together with the negated instances `negDomSet L d m'` yields that together with
`negDomSet L d m`, provided `d` is provable as an existential formula. -/
theorem Derivable.elim_negDomSet (hT : ∀ p ∈ T.Δ₁Class (V := V), Bootstrapping.shift L p = p)
    {d : V} (hd : IsSemiformula L 1 d) (hds : Bootstrapping.shift L d = d)
    (hne : Provable T (^∃ d)) {Δ m m' : V} (hΔ : IsFormulaSet L Δ) (hm : m ≤ m')
    (hfresh : ∀ j, m ≤ j → j < m' →
      fvSubstImage (L := L) (freshVec j) Δ = Bootstrapping.setShift L Δ)
    (h : Derivable T (Δ ∪ negDomSet L d m')) : Derivable T (Δ ∪ negDomSet L d m) := by
  have key : ∀ i, ∀ j, j ≤ m' → m ≤ j → j + i = m' → Derivable T (Δ ∪ negDomSet L d j) := by
    intro i
    induction i using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      intro j _ _ hj
      rw [add_zero] at hj
      rw [hj]
      exact h
    case succ i ih =>
      intro j hjm' hmj hj
      have h₁ : j < m' := by rw [← hj]; simp
      have h₂ : j + 1 ≤ m' := by rw [← hj]; simp
      have h₃ : j + 1 + i = m' := by rw [← hj, add_assoc, add_comm 1 i]
      have h₄ : Derivable T (Δ ∪ negDomSet L d (j + 1)) :=
        ih (j + 1) h₂ (le_trans hmj (by simp)) h₃
      rw [negDomSet_succ] at h₄
      have h₅ : Derivable T (insert (neg L (substs1 L (^&j) d)) (Δ ∪ negDomSet L d j)) :=
        Derivable.ofSetEq (fun x ↦ by simp only [mem_cup_iff, mem_bitInsert_iff]; tauto) h₄
      have h₆ : fvSubstImage (L := L) (freshVec j) (Δ ∪ negDomSet L d j) =
          setShift L (Δ ∪ negDomSet L d j) := by
        rw [fvSubstImage_union, hfresh j hmj h₁, fvSubstImage_freshVec_negDomSet hd hds,
          mem_setShift_union]
      have h₇ : fvSubst L (freshVec j) d = Bootstrapping.shift L d := by
        rw [hds]
        exact fvSubst_eq_self_of_shift hd hds
      have h₈ : Derivable T (insert (neg L (^∃ d)) (Δ ∪ negDomSet L d j)) :=
        Derivable.neg_exs_of_free hT (isSemitermVec_freshVec j) (by simp) (by simp) h₆ h₇ hd h₅
      have h₉ : IsFormulaSet L (insert (^∃ d) (Δ ∪ negDomSet L d j)) :=
        IsFormulaSet.insert_iff.mpr ⟨(IsFormulaSet.insert_iff.mp hne.toDerivable.isFormulaSet).1,
          IsFormulaSet.union.mpr ⟨hΔ, IsFormulaSet.negDomSet hd j⟩⟩
      have h₁₀ : Derivable T (insert (^∃ d) (Δ ∪ negDomSet L d j)) :=
        Derivable.wk h₉ (by intro x hx; simp_all) hne.toDerivable
      exact Derivable.cut (^∃ d) h₁₀ h₈
  exact key (m' - m) m hm (le_refl m) (add_tsub_cancel_of_le hm)

end elim

end negDomSet

end FFL.FirstOrder.Arithmetic.Bootstrapping
