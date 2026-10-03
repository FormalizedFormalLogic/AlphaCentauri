module

public import AlphaCentauri.Bootstrapping.Proof.CutElimination
public import AlphaCentauri.Bootstrapping.PartialTruth.Combination
public import AlphaCentauri.ToFoundation.Set

/-!
# Soundness of pure logic for the readable truth

`IsFalseBlock k D e` says that `e` is a block of existential quantifiers over a closed matrix in
the class `IsReadable k D` whose instances by closed terms are all false under `ReadableTruth k D`.
In every model of `𝗜𝚺⁺(k + 1)`, a sequent consisting of such formulas has no cut-free derivation
in pure logic, and in every model that also satisfies `𝗜𝚺⁺2` it has no derivation in pure logic at
all.

## References

- [HP98, Theorem I.4.33]
- [Kay91, Exercise 10.8]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open PeanoMinus ISigma0 ISigma1
open Arithmetic (numeral numeral_semiterm)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Partial instances of blocks -/

/-- `IsPartialInstance E r φ`: `φ` is obtained from a member `qqExss χ m` of `E`, whose matrix `χ`
is not existential, by instantiating the outermost `m - r` existential quantifiers with closed
terms. -/
def IsPartialInstance (E r φ : V) : Prop :=
  ∃ m χ, qqExss χ m ∈ E ∧ IsSemiformula ℒₒᵣ m χ ∧ (∀ p < χ, χ ≠ ^∃ p) ∧ r ≤ m ∧
    ∃ w, IsSemitermVec ℒₒᵣ m r w ∧ (∀ i < r, w.[i] = ^#i) ∧
      (∀ i < m, r ≤ i → IsSemiterm ℒₒᵣ 0 w.[i]) ∧ φ = qqExss (subst ℒₒᵣ w χ) r

section partialInstance

variable {E : V}

instance IsPartialInstance.definable :
    𝚺ᴬ₁-Relation₃ (IsPartialInstance : V → V → V → Prop) := by
  unfold IsPartialInstance
  definability

instance IsPartialInstance.definable' (m : ℕ) :
    𝚺ᴬ_[m + 1]-Relation₃ (IsPartialInstance : V → V → V → Prop) := by
  rcases m with _ | m
  · exact IsPartialInstance.definable
  · exact IsPartialInstance.definable.of_lt (by simp)

lemma IsPartialInstance.of_mem {m χ : V} (hχ : IsSemiformula ℒₒᵣ m χ) (hmax : ∀ p, χ ≠ ^∃ p)
    (h : qqExss χ m ∈ E) : IsPartialInstance E m (qqExss χ m) := by
  obtain ⟨w, hwl, hw⟩ := sigmaOne_skolem_vec (R := fun i y : V ↦ y = ^#i) (by definability)
    (l := m) (fun i _ ↦ ⟨_, rfl⟩)
  have hwv : IsSemitermVec ℒₒᵣ m m w :=
    IsSemitermVec.iff.mpr ⟨hwl, fun i hi ↦ by simp [hw i hi, hi]⟩
  exact ⟨m, χ, h, hχ, fun p _ ↦ hmax p, le_rfl, w, hwv, hw,
    fun i hi hmi ↦ absurd hi (not_lt.mpr hmi), by rw [subst_eq_self hχ hwv hw]⟩

lemma IsPartialInstance.isFormula {r φ : V} (h : IsPartialInstance E r φ) :
    IsFormula ℒₒᵣ φ := by
  obtain ⟨m, χ, -, hχ, -, -, w, hw, -, -, rfl⟩ := h
  exact IsSemiformula.qqExss (by simpa using hχ.subst hw)

lemma IsPartialInstance.succ {r φ : V} (h : IsPartialInstance E (r + 1) φ) :
    ∃ p, φ = ^∃ p ∧ IsSemiformula ℒₒᵣ 1 p ∧
      ∀ t, IsSemiterm ℒₒᵣ 0 t → IsPartialInstance E r (substs1 ℒₒᵣ t p) := by
  obtain ⟨m, χ, hmem, hχ, hmax, hrm, w, hw, hwb, hwc, rfl⟩ := h
  have hχw : IsSemiformula ℒₒᵣ (r + 1) (subst ℒₒᵣ w χ) := hχ.subst hw
  refine ⟨qqExss (subst ℒₒᵣ w χ) r, qqExss_succ _ _, IsSemiformula.qqExss (by rwa [add_comm]), ?_⟩
  intro t ht
  obtain ⟨v, hvl, hvb, hvr⟩ := exists_vec_bvar_term r t
  have hvs : IsSemitermVec ℒₒᵣ (r + 1) r v := by
    refine IsSemitermVec.iff.mpr ⟨hvl, ?_⟩
    intro i hi
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with hir | rfl
    · simp [hvb i hir, hir]
    · rw [hvr]
      exact IsSemiterm.def.mpr ⟨ht.isUTerm, le_trans (IsSemiterm.def.mp ht).2 (by simp)⟩
  have hrm' : r < m := lt_of_lt_of_le (by simp) hrm
  rw [substs1_qqExss ht hχw hvl hvb hvr, substs_substs hχ hvs hw]
  refine ⟨m, χ, hmem, hχ, hmax, hrm'.le, termSubstVec ℒₒᵣ m v w, hvs.termSubstVec hw, ?_, ?_, rfl⟩
  · intro i hi
    rw [nth_termSubstVec hw.isUTerm (lt_trans hi hrm'), hwb i (lt_trans hi (by simp)),
      termSubst_bvar, hvb i hi]
  · intro i hi hri
    rw [nth_termSubstVec hw.isUTerm hi]
    rcases eq_or_lt_of_le hri with rfl | hri
    · rwa [hwb r (by simp), termSubst_bvar, hvr]
    · rw [termSubst_eq_self (hwc i hi (succ_le_iff_lt.mpr hri)) (by simp)]
      exact hwc i hi (succ_le_iff_lt.mpr hri)

end partialInstance

/-! ### Blocks with false instances -/

/-- `IsFalseBlock k D e`: `e` is a block `qqExss χ m` of existential quantifiers over a matrix `χ`
that has no free variables, is not existential, and belongs to `IsReadable k D`, such that every
instance of `χ` by closed terms is false under `ReadableTruth k D`. -/
def IsFalseBlock (k D : ℕ) (e : V) : Prop :=
  ∃ m χ, e = qqExss χ m ∧ IsSemiformula ℒₒᵣ m χ ∧ shift ℒₒᵣ χ = χ ∧ (∀ p, χ ≠ ^∃ p) ∧
    IsReadable k D χ ∧ ∀ w, IsSemitermVec ℒₒᵣ m 0 w → ¬ReadableTruth k D (subst ℒₒᵣ w χ)

lemma IsFalseBlock.isFormula {k D : ℕ} {e : V} (h : IsFalseBlock k D e) : IsFormula ℒₒᵣ e := by
  obtain ⟨m, χ, rfl, hχ, -⟩ := h
  exact IsSemiformula.qqExss (by simpa using hχ)

lemma IsFalseBlock.shift_eq {k D : ℕ} {e : V} (h : IsFalseBlock k D e) : shift ℒₒᵣ e = e := by
  obtain ⟨m, χ, rfl, hχ, hs, -⟩ := h
  rw [shift_qqExss hχ.isUFormula, hs]

/-- `φ` is readable or a partial instance of a block of `E`. -/
private def Admissible (k D : ℕ) (E φ : V) : Prop :=
  IsReadable k D φ ∨ ∃ r, IsPartialInstance E r φ

/-- Some formula of `s` is true under `f`, and its value under `f` is not a partial instance of a
block of `E` with a quantifier left. -/
private def HasWitness (k D : ℕ) (E s f : V) : Prop :=
  ∃ ψ ∈ s, (∀ r, ¬IsPartialInstance E (r + 1) (fvAssign f ψ)) ∧ ReadableSatisfaction k D ψ f

section falseBlock

variable {k D : ℕ} {E : V}

lemma IsPartialInstance.zero (hE : ∀ e ∈ E, IsFalseBlock k D e) {φ : V}
    (h : IsPartialInstance E 0 φ) : IsReadable k D φ ∧ ¬ReadableTruth k D φ := by
  obtain ⟨m, χ, hmem, hχ, hmax, -, w, hw, -, -, rfl⟩ := h
  obtain ⟨m', χ', he, -, -, hmax', hr, hf⟩ := hE _ hmem
  obtain ⟨rfl, rfl⟩ := qqExss_inj (fun a ha ↦ hmax a (by simp [ha]) ha) hmax' he
  exact ⟨by simpa using hr.subst hw hχ, by simpa using hf w hw⟩

private lemma not_isPartialInstance_succ {φ : V} (h : ∀ p, φ ≠ ^∃ p) (r : V) :
    ¬IsPartialInstance E (r + 1) φ := by
  intro hr
  obtain ⟨p, rfl, -⟩ := hr.succ
  exact h p rfl

private lemma isReadable_of_admissible (hE : ∀ e ∈ E, IsFalseBlock k D e) {φ : V}
    (h : Admissible k D E φ) (hN : ∀ r, ¬IsPartialInstance E (r + 1) φ) : IsReadable k D φ := by
  rcases h with h | ⟨r, hr⟩
  · exact h
  · rcases zero_or_succ r with rfl | ⟨r, rfl⟩
    · exact (hr.zero hE).1
    · exact absurd hr (hN r)

private lemma admissible_insert {p s f : V} (hp : Admissible k D E (fvAssign f p))
    (hs : ∀ ψ ∈ s, Admissible k D E (fvAssign f ψ)) :
    ∀ ψ ∈ insert p s, Admissible k D E (fvAssign f ψ) := by
  intro ψ hψ
  rcases mem_bitInsert_iff.mp hψ with rfl | hψ
  · exact hp
  · exact hs ψ hψ

private lemma hasWitness_of_insert {p s f : V} (h : HasWitness k D E (insert p s) f)
    (hp : ¬ReadableSatisfaction k D p f) : HasWitness k D E s f := by
  obtain ⟨ψ, hψ, hψN, hψT⟩ := h
  rcases mem_bitInsert_iff.mp hψ with rfl | hψ
  · exact absurd hψT hp
  · exact ⟨ψ, hψ, hψN, hψT⟩

private lemma hasWitness_of_and (hE : ∀ e ∈ E, IsFalseBlock k D e) {s p q f : V}
    (hs : IsFormulaSet ℒₒᵣ s) (hpq : p ^⋏ q ∈ s) (hadm : ∀ ψ ∈ s, Admissible k D E (fvAssign f ψ))
    (ihp : (∀ ψ ∈ insert p s, Admissible k D E (fvAssign f ψ)) → HasWitness k D E (insert p s) f)
    (ihq : (∀ ψ ∈ insert q s, Admissible k D E (fvAssign f ψ)) → HasWitness k D E (insert q s) f) :
    HasWitness k D E s f := by
  have hF : IsFormula ℒₒᵣ p ∧ IsFormula ℒₒᵣ q := by simpa using hs _ hpq
  have e : fvAssign f (p ^⋏ q) = fvAssign f p ^⋏ fvAssign f q :=
    fvAssign_and hF.1.isUFormula hF.2.isUFormula
  have hN : ∀ r, ¬IsPartialInstance E (r + 1) (fvAssign f (p ^⋏ q)) :=
    not_isPartialInstance_succ (by rw [e]; simp [qqAnd, qqExs])
  have hR := isReadable_of_admissible hE (hadm _ hpq) hN
  rw [e] at hR
  by_cases ht : ReadableSatisfaction k D (p ^⋏ q) f
  · exact ⟨_, hpq, hN, ht⟩
  rw [ReadableSatisfaction, e, ReadableTruth.and_iff hR hF.1.isUFormula.fvAssign
    hF.2.isUFormula.fvAssign, not_and_or] at ht
  rcases ht with ht | ht
  · exact hasWitness_of_insert (ihp (admissible_insert (.inl hR.of_and.1) hadm)) ht
  · exact hasWitness_of_insert (ihq (admissible_insert (.inl hR.of_and.2) hadm)) ht

private lemma hasWitness_of_or (hE : ∀ e ∈ E, IsFalseBlock k D e) {s p q f : V}
    (hs : IsFormulaSet ℒₒᵣ s) (hpq : p ^⋎ q ∈ s) (hadm : ∀ ψ ∈ s, Admissible k D E (fvAssign f ψ))
    (ih : (∀ ψ ∈ insert p (insert q s), Admissible k D E (fvAssign f ψ)) →
      HasWitness k D E (insert p (insert q s)) f) :
    HasWitness k D E s f := by
  have hF : IsFormula ℒₒᵣ p ∧ IsFormula ℒₒᵣ q := by simpa using hs _ hpq
  have e : fvAssign f (p ^⋎ q) = fvAssign f p ^⋎ fvAssign f q :=
    fvAssign_or hF.1.isUFormula hF.2.isUFormula
  have hN : ∀ r, ¬IsPartialInstance E (r + 1) (fvAssign f (p ^⋎ q)) :=
    not_isPartialInstance_succ (by rw [e]; simp [qqOr, qqExs])
  have hR := isReadable_of_admissible hE (hadm _ hpq) hN
  rw [e] at hR
  by_cases ht : ReadableSatisfaction k D (p ^⋎ q) f
  · exact ⟨_, hpq, hN, ht⟩
  rw [ReadableSatisfaction, e, ReadableTruth.or_iff hR hF.1.isUFormula.fvAssign
    hF.2.isUFormula.fvAssign, not_or] at ht
  exact hasWitness_of_insert (hasWitness_of_insert
    (ih (admissible_insert (.inl hR.of_or.1) (admissible_insert (.inl hR.of_or.2) hadm))) ht.1) ht.2

private lemma hasWitness_of_all (hE : ∀ e ∈ E, IsFalseBlock k D e) {s p f : V}
    (hs : IsFormulaSet ℒₒᵣ s) (hp : ^∀ p ∈ s) (hadm : ∀ ψ ∈ s, Admissible k D E (fvAssign f ψ))
    (ih : ∀ g, (∀ ψ ∈ insert (free ℒₒᵣ p) (setShift ℒₒᵣ s), Admissible k D E (fvAssign g ψ)) →
      HasWitness k D E (insert (free ℒₒᵣ p) (setShift ℒₒᵣ s)) g) :
    HasWitness k D E s f := by
  have hpF : IsSemiformula ℒₒᵣ 1 p := by simpa using hs _ hp
  have e : fvAssign f (^∀ p) = ^∀ (fvAssign f p) := fvAssign_all hpF.isUFormula
  have hN : ∀ r, ¬IsPartialInstance E (r + 1) (fvAssign f (^∀ p)) :=
    not_isPartialInstance_succ (by rw [e]; simp [qqAll, qqExs])
  have hR := isReadable_of_admissible hE (hadm _ hp) hN
  rw [e] at hR
  by_cases ht : ReadableSatisfaction k D (^∀ p) f
  · exact ⟨_, hp, hN, ht⟩
  rw [ReadableSatisfaction, e, ReadableTruth.all_iff hR hpF.fvAssign, not_forall] at ht
  obtain ⟨x, hx⟩ := ht
  have hsh : ∀ q ∈ s, fvAssign (x ∷ f) (shift ℒₒᵣ q) = fvAssign f q := by
    intro q hq
    exact fvAssign_shift (hs q hq).isUFormula
  have hfree : fvAssign (x ∷ f) (free ℒₒᵣ p) = substs1 ℒₒᵣ (numeral x) (fvAssign f p) :=
    fvAssign_free hpF
  have hadm' : ∀ ψ ∈ insert (free ℒₒᵣ p) (setShift ℒₒᵣ s),
      Admissible k D E (fvAssign (x ∷ f) ψ) := by
    apply admissible_insert
    · rw [hfree]
      exact .inl (hR.substs1_of_all (numeral_semiterm 0 x) hpF.fvAssign)
    · intro ψ hψ
      obtain ⟨q, hq, rfl⟩ := mem_setShift_iff.mp hψ
      rw [hsh q hq]
      exact hadm q hq
  obtain ⟨ψ, hψ, hψN, hψT⟩ :=
    hasWitness_of_insert (ih (x ∷ f) hadm') (by rwa [ReadableSatisfaction, hfree])
  obtain ⟨q, hq, rfl⟩ := mem_setShift_iff.mp hψ
  rw [hsh q hq] at hψN
  exact ⟨q, hq, hψN, ReadableSatisfaction.shift_iff.mp hψT⟩

private lemma hasWitness_of_exs_of_isPartialInstance (hE : ∀ e ∈ E, IsFalseBlock k D e)
    {s p t f q r : V} (hpq : fvAssign f p = q) (ht : IsSemiterm ℒₒᵣ 0 t)
    (hinst : ∀ u, IsSemiterm ℒₒᵣ 0 u → IsPartialInstance E r (substs1 ℒₒᵣ u q))
    (et : fvAssign f (substs1 ℒₒᵣ t p) = substs1 ℒₒᵣ (termFvAssign f t) (fvAssign f p))
    (hadm : ∀ ψ ∈ s, Admissible k D E (fvAssign f ψ))
    (ih : (∀ ψ ∈ insert (substs1 ℒₒᵣ t p) s, Admissible k D E (fvAssign f ψ)) →
      HasWitness k D E (insert (substs1 ℒₒᵣ t p) s) f) :
    HasWitness k D E s f := by
  have hnew : IsPartialInstance E r (fvAssign f (substs1 ℒₒᵣ t p)) := by
    rw [et, hpq]
    exact hinst _ ht.termFvAssign
  obtain ⟨ψ, hψ, hψN, hψT⟩ := ih (admissible_insert (.inr ⟨r, hnew⟩) hadm)
  rcases mem_bitInsert_iff.mp hψ with rfl | hψ
  · rcases zero_or_succ r with rfl | ⟨r, rfl⟩
    · exact absurd hψT (hnew.zero hE).2
    · exact absurd hnew (hψN r)
  · exact ⟨ψ, hψ, hψN, hψT⟩

private lemma hasWitness_of_exs (hE : ∀ e ∈ E, IsFalseBlock k D e) {s p t f : V}
    (hs : IsFormulaSet ℒₒᵣ s) (hp : ^∃ p ∈ s) (ht : IsTerm ℒₒᵣ t)
    (hadm : ∀ ψ ∈ s, Admissible k D E (fvAssign f ψ))
    (ih : (∀ ψ ∈ insert (substs1 ℒₒᵣ t p) s, Admissible k D E (fvAssign f ψ)) →
      HasWitness k D E (insert (substs1 ℒₒᵣ t p) s) f) :
    HasWitness k D E s f := by
  have hpF : IsSemiformula ℒₒᵣ 1 p := by simpa using hs _ hp
  have e : fvAssign f (^∃ p) = ^∃ (fvAssign f p) := fvAssign_exs hpF.isUFormula
  have et : fvAssign f (substs1 ℒₒᵣ t p) = substs1 ℒₒᵣ (termFvAssign f t) (fvAssign f p) :=
    fvAssign_substs1 ht hpF
  by_cases hφ : ∃ r, IsPartialInstance E (r + 1) (fvAssign f (^∃ p))
  · obtain ⟨r, hr⟩ := hφ
    obtain ⟨q, hq, -, hinst⟩ := hr.succ
    rw [e, qqExs_inj] at hq
    exact hasWitness_of_exs_of_isPartialInstance hE hq ht hinst et hadm ih
  rw [not_exists] at hφ
  have hR := isReadable_of_admissible hE (hadm _ hp) hφ
  rw [e] at hR
  have hnew : IsReadable k D (fvAssign f (substs1 ℒₒᵣ t p)) := by
    rw [et]
    exact hR.substs1_of_exs ht.termFvAssign hpF.fvAssign
  obtain ⟨ψ, hψ, hψN, hψT⟩ := ih (admissible_insert (.inl hnew) hadm)
  rcases mem_bitInsert_iff.mp hψ with rfl | hψ
  · rw [ReadableSatisfaction, et] at hψT
    refine ⟨_, hp, hφ, ?_⟩
    rw [ReadableSatisfaction, e]
    exact ReadableTruth.exs_of_substs1 hR hpF.fvAssign ht.termFvAssign hψT
  · exact ⟨ψ, hψ, hψN, hψT⟩

private lemma hasWitness_of_shift {Γ f : V} (hΓ : IsFormulaSet ℒₒᵣ Γ)
    (hadm : ∀ ψ ∈ setShift ℒₒᵣ Γ, Admissible k D E (fvAssign f ψ))
    (ih : ∀ g, (∀ ψ ∈ Γ, Admissible k D E (fvAssign g ψ)) → HasWitness k D E Γ g) :
    HasWitness k D E (setShift ℒₒᵣ Γ) f := by
  obtain ⟨b, g, hfg⟩ : ∃ b g : V, ∀ i, f.[i] = (b ∷ g).[i] := by
    rcases adjoin_cases f with rfl | ⟨b, g, rfl⟩
    · refine ⟨0, 0, ?_⟩
      intro i
      rcases zero_or_succ i with rfl | ⟨i, rfl⟩ <;> simp
    · exact ⟨b, g, fun _ ↦ rfl⟩
  have hsh : ∀ q ∈ Γ, fvAssign f (shift ℒₒᵣ q) = fvAssign g q := by
    intro q hq
    rw [fvAssign_congr hfg, fvAssign_shift (hΓ q hq).isUFormula]
  have hadm' : ∀ ψ ∈ Γ, Admissible k D E (fvAssign g ψ) := by
    intro ψ hψ
    rw [← hsh ψ hψ]
    exact hadm _ (shift_mem_setShift hψ)
  obtain ⟨ψ, hψ, hψN, hψT⟩ := ih g hadm'
  exact ⟨_, shift_mem_setShift hψ, by rwa [hsh ψ hψ],
    (ReadableSatisfaction.congr hfg).mpr (ReadableSatisfaction.shift_iff.mpr hψT)⟩

private lemma hasWitness_definable :
    𝚷ᴬ_[k + 1].DefinablePred fun d : V ↦ ∀ f, CutFreeDerivation (∅ : Theory ℒₒᵣ) d →
      (∀ ψ ∈ fstIdx d, Admissible k D E (fvAssign f ψ)) → HasWitness k D E (fstIdx d) f := by
  unfold Admissible HasWitness
  definability

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺(k + 1)]

private lemma IsPartialInstance.readableTruth_neg (hE : ∀ e ∈ E, IsFalseBlock k D e) {r φ : V}
    (h : IsPartialInstance E r φ) (hn : IsReadable k D (neg ℒₒᵣ φ)) :
    ReadableTruth k D (neg ℒₒᵣ φ) := by
  have hP : 𝚷ᴬ_[k + 1].DefinablePred fun r : V ↦ ∀ φ, IsPartialInstance E r φ →
      IsReadable k D (neg ℒₒᵣ φ) → ReadableTruth k D (neg ℒₒᵣ φ) := by
    definability
  refine InductionOnHierarchy.succ_induction_sigma 𝚷 (k + 1) hP ?_ ?_ r φ h hn
  · intro φ h hn
    obtain ⟨hr, hf⟩ := h.zero hE
    exact (ReadableTruth.neg_iff hr hn h.isFormula.isUFormula).mpr hf
  · intro r ih φ h hn
    obtain ⟨p, rfl, hp, hinst⟩ := h.succ
    rw [neg_ex hp.isUFormula] at hn ⊢
    apply (ReadableTruth.all_iff hn hp.neg).mpr
    intro x
    have e : substs1 ℒₒᵣ (numeral x) (neg ℒₒᵣ p) = neg ℒₒᵣ (substs1 ℒₒᵣ (numeral x) p) :=
      substs_neg hp (by simp : IsSemitermVec ℒₒᵣ 1 0 (?[numeral x] : V))
    have hx := hn.substs1_of_all (m := 0) (numeral_semiterm 0 x) hp.neg
    rw [e] at hx ⊢
    exact ih _ (hinst _ (numeral_semiterm 0 x)) hx

private lemma hasWitness_of_axL (hE : ∀ e ∈ E, IsFalseBlock k D e) {s p f : V}
    (hs : IsFormulaSet ℒₒᵣ s) (hp : p ∈ s) (hnp : neg ℒₒᵣ p ∈ s)
    (hadm : ∀ ψ ∈ s, Admissible k D E (fvAssign f ψ)) :
    HasWitness k D E s f := by
  have hpU : IsUFormula ℒₒᵣ (fvAssign f p) := (hs p hp).isUFormula.fvAssign
  have e : fvAssign f (neg ℒₒᵣ p) = neg ℒₒᵣ (fvAssign f p) := fvAssign_neg (hs p hp).isUFormula
  have h₂ := hadm _ hnp
  rw [e] at h₂
  by_cases h₁ : ∃ r, IsPartialInstance E (r + 1) (fvAssign f p)
  · obtain ⟨r, hr⟩ := h₁
    obtain ⟨q, hq, hqF, -⟩ := hr.succ
    have hN : ∀ r, ¬IsPartialInstance E (r + 1) (neg ℒₒᵣ (fvAssign f p)) :=
      not_isPartialInstance_succ (by rw [hq, neg_ex hqF.isUFormula]; simp [qqAll, qqExs])
    refine ⟨_, hnp, by rwa [e], ?_⟩
    rw [ReadableSatisfaction, e]
    exact hr.readableTruth_neg hE (isReadable_of_admissible hE h₂ hN)
  rw [not_exists] at h₁
  have hR₁ := isReadable_of_admissible hE (hadm p hp) h₁
  by_cases h₂' : ∃ r, IsPartialInstance E (r + 1) (neg ℒₒᵣ (fvAssign f p))
  · obtain ⟨r, hr⟩ := h₂'
    have h := hr.readableTruth_neg hE (by rwa [hpU.neg_neg])
    rw [hpU.neg_neg] at h
    exact ⟨p, hp, h₁, h⟩
  rw [not_exists] at h₂'
  have hR₂ := isReadable_of_admissible hE h₂ h₂'
  by_cases ht : ReadableSatisfaction k D p f
  · exact ⟨p, hp, h₁, ht⟩
  refine ⟨_, hnp, by rwa [e], ?_⟩
  rw [ReadableSatisfaction, e]
  exact (ReadableTruth.neg_iff hR₁ hR₂ hpU).mpr ht

private lemma hasWitness_aux (hE : ∀ e ∈ E, IsFalseBlock k D e) :
    ∀ d f : V, CutFreeDerivation (∅ : Theory ℒₒᵣ) d →
      (∀ ψ ∈ fstIdx d, Admissible k D E (fvAssign f ψ)) → HasWitness k D E (fstIdx d) f := by
  intro d
  refine InductionOnHierarchy.order_induction_sigma 𝚷 (k + 1) hasWitness_definable ?_ d
  intro d ih f hd hadm
  have ih' : ∀ d₀ < d, ∀ s, CutFreeDerivationOf (∅ : Theory ℒₒᵣ) d₀ s → ∀ g,
      (∀ ψ ∈ s, Admissible k D E (fvAssign g ψ)) → HasWitness k D E s g := by
    rintro d₀ hd₀ s ⟨rfl, hd₀'⟩ g hg
    exact ih d₀ hd₀ g hd₀' hg
  have hs := hd.isFormulaSet
  rcases hd.case.2 with (⟨s, p, rfl, hp, hnp⟩ | ⟨s, rfl, hv⟩ |
    ⟨s, p, q, dp, dq, rfl, hpq, hdp, hdq⟩ | ⟨s, p, q, d₀, rfl, hpq, hd₀⟩ |
    ⟨s, p, d₀, rfl, hp, hd₀⟩ | ⟨s, p, t, d₀, rfl, hp, ht, hd₀⟩ |
    ⟨s, d₀, rfl, hsub, hd₀⟩ | ⟨s, d₀, rfl, rfl, hd₀⟩ | ⟨s, p, rfl, -, hT⟩)
  · rw [fstIdx_axL] at hs hadm ⊢
    exact hasWitness_of_axL hE hs hp hnp hadm
  · rw [fstIdx_verumIntro] at hadm ⊢
    exact ⟨_, hv, not_isPartialInstance_succ (by rw [fvAssign_verum]; simp [qqVerum, qqExs]),
      by simp⟩
  · rw [fstIdx_andIntro] at hs hadm ⊢
    exact hasWitness_of_and hE hs hpq hadm (ih' dp (dp_lt_andIntro _ _ _ _ _) _ hdp f)
      (ih' dq (dq_lt_andIntro _ _ _ _ _) _ hdq f)
  · rw [fstIdx_orIntro] at hs hadm ⊢
    exact hasWitness_of_or hE hs hpq hadm (ih' d₀ (d_lt_orIntro _ _ _ _) _ hd₀ f)
  · rw [fstIdx_allIntro] at hs hadm ⊢
    exact hasWitness_of_all hE hs hp hadm (ih' d₀ (s_lt_allIntro _ _ _) _ hd₀)
  · rw [fstIdx_exsIntro] at hs hadm ⊢
    exact hasWitness_of_exs hE hs hp ht hadm (ih' d₀ (d_lt_exsIntro _ _ _ _) _ hd₀ f)
  · rw [fstIdx_wkRule] at hadm ⊢
    obtain ⟨ψ, hψ, hψN, hψT⟩ := ih d₀ (d_lt_wkRule _ _) f hd₀ (fun ψ hψ ↦ hadm ψ (hsub hψ))
    exact ⟨ψ, hsub hψ, hψN, hψT⟩
  · rw [fstIdx_shiftRule] at hadm ⊢
    exact hasWitness_of_shift hd₀.isFormulaSet hadm (ih d₀ (d_lt_shiftRule _ _) · hd₀)
  · exact absurd hT (not_mem_empty_Δ₁Class p)

/-- If, under the assignment `f`, every formula of a sequent derivable in pure logic without cuts
is readable or a partial instance of a block of `E`, then some formula of the sequent is true under
`f`, and its value under `f` is not a partial instance of a block of `E` with a quantifier left. -/
private theorem CutFreeDerivable.exists_readableSatisfaction (hE : ∀ e ∈ E, IsFalseBlock k D e)
    {s f : V} (h : CutFreeDerivable (∅ : Theory ℒₒᵣ) s)
    (hs : ∀ ψ ∈ s, IsReadable k D (fvAssign f ψ) ∨ ∃ r, IsPartialInstance E r (fvAssign f ψ)) :
    ∃ ψ ∈ s, (∀ r, ¬IsPartialInstance E (r + 1) (fvAssign f ψ)) ∧
      ReadableSatisfaction k D ψ f := by
  obtain ⟨d, rfl, hd⟩ := h
  exact hasWitness_aux hE d f hd hs

/-- A sequent of blocks of existential quantifiers whose readable matrices have only false
instances has no cut-free derivation in pure logic.
- [HP98, Theorem I.4.33]
- [Kay91, Exercise 10.8] -/
theorem not_cutFreeDerivable_of_isFalseBlock (hE : ∀ e ∈ E, IsFalseBlock k D e) :
    ¬CutFreeDerivable (∅ : Theory ℒₒᵣ) E := by
  intro h
  have key : ∀ e ∈ E, fvAssign 0 e = e ∧ ∃ m, IsPartialInstance E m e := by
    intro e he
    obtain ⟨m, χ, rfl, hχ, hsh, hmax, -, -⟩ := hE e he
    exact ⟨by rw [fvAssign_qqExss hχ.isUFormula, fvAssign_eq_self hχ.isUFormula hsh],
      m, .of_mem hχ hmax he⟩
  obtain ⟨e, he, hN, hT⟩ := h.exists_readableSatisfaction hE (f := 0) (by
    intro e he
    rw [(key e he).1]
    exact .inr (key e he).2)
  obtain ⟨hfix, m, hm⟩ := key e he
  rw [hfix] at hN
  rw [ReadableSatisfaction, hfix] at hT
  rcases zero_or_succ m with rfl | ⟨m, rfl⟩
  · exact (hm.zero hE).2 hT
  · exact hN m hm

/-- A sequent of blocks of existential quantifiers whose readable matrices have only false
instances has no derivation in pure logic.
- [HP98, Theorem I.4.33]
- [Kay91, Exercise 10.8] -/
theorem not_derivable_of_isFalseBlock [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺2] (hE : ∀ e ∈ E, IsFalseBlock k D e) :
    ¬Derivable (∅ : Theory ℒₒᵣ) E :=
  fun h ↦ not_cutFreeDerivable_of_isFalseBlock hE h.cutFree

end falseBlock

end FFL.FirstOrder.Arithmetic.Bootstrapping
