module

public import AlphaCentauri.Bootstrapping.Proof.CutElimination
public import AlphaCentauri.Bootstrapping.PartialTruth.Combination

/-!
# Soundness of pure logic for the readable truth

`IsFalseBlock k D e` says that `e` is a block of existential quantifiers over a closed matrix in
the class `IsReadable k D` whose instances by closed terms are all false. In every model of
`𝗜𝚺⁺ (k + 1)`, a sequent consisting of such formulas has no cut-free derivation in pure logic, and
in every model that also satisfies `𝗜𝚺⁺2` it has no derivation at all.

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

/-! ### Iterated existential quantifier -/

section qqExss

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- The primitive recursion blueprint of `qqExss`. -/
def qqExss.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. !qqExsDef y ih”

/-- The primitive recursion construction of `qqExss`. -/
noncomputable def qqExss.construction : PR.Construction V qqExss.blueprint where
  zero := fun x ↦ x 0
  succ := fun _ _ ih ↦ ^∃ ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, qqExs]

/-- `qqExss p k = ^∃ ^∃ ⋯ ^∃ p`, with `k` existential quantifiers. -/
noncomputable def qqExss (p k : V) : V := qqExss.construction.result ![p] k

@[simp] lemma qqExss_zero (p : V) : qqExss p 0 = p := by simp [qqExss, qqExss.construction]

@[simp] lemma qqExss_succ (p k : V) : qqExss p (k + 1) = ^∃ (qqExss p k) := by
  simp [qqExss, qqExss.construction]

/-- The $\Sigma_1$ semisentence defining `qqExss`. -/
def _root_.FFL.FirstOrder.Arithmetic.qqExssDef : 𝚺ᴬ₁.Semisentence 3 :=
  qqExss.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance qqExss.defined : 𝚺ᴬ₁-Function₂ (qqExss : V → V → V) via qqExssDef := .mk
  fun v ↦ by simp [qqExss.construction.result_defined_iff, qqExssDef]; rfl

instance qqExss.definable : 𝚺ᴬ₁-Function₂ (qqExss : V → V → V) := qqExss.defined.to_definable

instance qqExss.definable' {Γ : Polarity} {m : ℕ} :
    Γᴬ-[m + 1]-Function₂ (qqExss : V → V → V) := qqExss.definable.of_sigmaOne

lemma qqExss_exs (p k : V) : qqExss (^∃ p) k = ^∃ (qqExss p k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqExss_succ, ih, qqExss_succ]

lemma qqExss_succ' (p k : V) : qqExss p (k + 1) = qqExss (^∃ p) k := by
  rw [qqExss_succ, qqExss_exs]

@[simp] lemma isUFormula_qqExss {p k : V} : IsUFormula L (qqExss p k) ↔ IsUFormula L p := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqExss_succ, IsUFormula.ex, ih]

lemma IsSemiformula.qqExss {n k p : V} (h : IsSemiformula L (n + k) p) :
    IsSemiformula L n (qqExss p k) := by
  induction k using ISigma1.pi1_succ_induction generalizing n
  · definability
  case zero => simpa using h
  case succ k ih =>
    rw [qqExss_succ, IsSemiformula.exs]
    exact ih (by rwa [add_right_comm, add_assoc])

/-- Two blocks of existential quantifiers over matrices that are not existential coincide only if
their lengths and their matrices do. -/
lemma qqExss_inj {p q m n : V} (hp : ∀ a, p ≠ ^∃ a) (hq : ∀ a, q ≠ ^∃ a)
    (h : qqExss p m = qqExss q n) : m = n ∧ p = q := by
  induction m using ISigma1.pi1_succ_induction generalizing n
  · definability
  case zero =>
    rcases zero_or_succ n with rfl | ⟨n, rfl⟩
    · simpa using h
    · exact absurd (by simpa using h) (hp _)
  case succ m ih =>
    rcases zero_or_succ n with rfl | ⟨n, rfl⟩
    · exact absurd (by simpa using h.symm) (hq _)
    · obtain ⟨rfl, rfl⟩ := ih (by simpa using h)
      exact ⟨rfl, rfl⟩

end qqExss

lemma fvAssign_qqExss {f p : V} (hp : IsUFormula ℒₒᵣ p) (k : V) :
    fvAssign f (qqExss p k) = qqExss (fvAssign f p) k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqExss_succ, fvAssign_exs (by simpa using hp), ih, qqExss_succ]

/-- A closed term is fixed by the shift of bound variables. -/
lemma termBShift_eq_self {L : Language} [L.Encodable] [L.LORDefinable] {t : V}
    (ht : IsSemiterm L 0 t) : termBShift L t = t := by
  simpa [substs_nil ht] using bShift_substs ht (w := 0) (m := 0) (by simp)

/-- Instantiating the outermost quantifier of `qqExss q r` with a closed term `t` instantiates the
outermost bound variable of `q`. -/
lemma substs1_qqExss {t q v r : V} (ht : IsSemiterm ℒₒᵣ 0 t) (hq : IsSemiformula ℒₒᵣ (r + 1) q)
    (hv : len v = r + 1) (hvb : ∀ i < r, v.[i] = ^#i) (hvr : v.[r] = t) :
    substs1 ℒₒᵣ t (qqExss q r) = qqExss (subst ℒₒᵣ v q) r := by
  induction r using ISigma1.pi1_succ_induction generalizing q v
  · definability
  case zero =>
    have : v = ?[t] := nth_ext' 1 (by simpa using hv) (by simp) (by
      intro i hi
      obtain rfl : i = 0 := by simpa using hi
      simpa using hvr)
    simp [substs1, this]
  case succ r ih =>
    obtain ⟨v', hv'l, hv'⟩ := sigmaOne_skolem_vec
      (R := fun i y : V ↦ (i < r → y = ^#i) ∧ (r ≤ i → y = t)) (by definability) (l := r + 1)
      (fun i _ ↦ by
        by_cases hi : i < r
        · exact ⟨^#i, fun _ ↦ rfl, fun h ↦ absurd hi (not_lt.mpr h)⟩
        · exact ⟨t, fun h ↦ absurd h hi, fun _ ↦ rfl⟩)
    have hv'u : IsUTermVec ℒₒᵣ (r + 1) v' := ⟨hv'l.symm, fun i hi ↦ by
      by_cases hir : i < r
      · simp [(hv' i hi).1 hir]
      · simpa [(hv' i hi).2 (not_lt.mp hir)] using ht.isUTerm⟩
    have hqv : qVec ℒₒᵣ v' = v := by
      apply nth_ext' (r + 1 + 1) (len_qVec hv'u) hv
      intro i hi
      rcases zero_or_succ i with rfl | ⟨i, rfl⟩
      · simp [qVec, hvb 0 (by simp)]
      · have hi : i < r + 1 := by simpa using hi
        rw [qVec, nth_adjoin_succ, hv'l, nth_termBShiftVec hv'u hi]
        rcases lt_or_ge i r with hir | hir
        · simp [(hv' i hi).1 hir, hvb (i + 1) (by simpa using hir)]
        · obtain rfl : i = r := le_antisymm (lt_succ_iff_le.mp hi) hir
          rw [(hv' i hi).2 le_rfl, termBShift_eq_self ht, hvr]
    rw [qqExss_succ', ih (by simpa using hq) hv'l (fun i hi ↦ (hv' i (lt_trans hi (by simp))).1 hi)
      ((hv' r (by simp)).2 le_rfl), substs_ex hq.isUFormula, qqExss_exs, ← qqExss_succ, hqv]

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
    𝚺ᴬ-[m + 1]-Relation₃ (IsPartialInstance : V → V → V → Prop) := by
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
  obtain ⟨v, hvl, hv⟩ := sigmaOne_skolem_vec
    (R := fun i y : V ↦ (i < r → y = ^#i) ∧ (r ≤ i → y = t)) (by definability) (l := r + 1)
    (fun i _ ↦ by
      by_cases hi : i < r
      · exact ⟨^#i, fun _ ↦ rfl, fun h ↦ absurd hi (not_lt.mpr h)⟩
      · exact ⟨t, fun h ↦ absurd h hi, fun _ ↦ rfl⟩)
  have hvs : IsSemitermVec ℒₒᵣ (r + 1) r v := IsSemitermVec.iff.mpr ⟨hvl, fun i hi ↦ by
    by_cases hir : i < r
    · simp [(hv i hi).1 hir, hir]
    · rw [(hv i hi).2 (not_lt.mp hir)]
      exact IsSemiterm.def.mpr ⟨ht.isUTerm, le_trans (IsSemiterm.def.mp ht).2 (by simp)⟩⟩
  have hrm' : r < m := lt_of_lt_of_le (by simp) hrm
  rw [substs1_qqExss ht hχw hvl (fun i hi ↦ (hv i (lt_trans hi (by simp))).1 hi)
    ((hv r (by simp)).2 le_rfl), substs_substs hχ hvs hw]
  refine ⟨m, χ, hmem, hχ, hmax, hrm'.le, termSubstVec ℒₒᵣ m v w, hvs.termSubstVec hw, ?_, ?_, rfl⟩
  · intro i hi
    rw [nth_termSubstVec hw.isUTerm (lt_trans hi hrm'), hwb i (lt_trans hi (by simp)),
      termSubst_bvar, (hv i (lt_trans hi (by simp))).1 hi]
  · intro i hi hri
    rw [nth_termSubstVec hw.isUTerm hi]
    rcases eq_or_lt_of_le hri with rfl | hri
    · rwa [hwb r (by simp), termSubst_bvar, (hv r (by simp)).2 le_rfl]
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

section falseBlock

variable {k D : ℕ} {E : V}

lemma IsPartialInstance.zero (hE : ∀ e ∈ E, IsFalseBlock k D e) {φ : V}
    (h : IsPartialInstance E 0 φ) : IsReadable k D φ ∧ ¬ReadableTruth k D φ := by
  obtain ⟨m, χ, hmem, hχ, hmax, -, w, hw, -, -, rfl⟩ := h
  obtain ⟨m', χ', he, -, -, hmax', hr, hf⟩ := hE _ hmem
  obtain ⟨rfl, rfl⟩ := qqExss_inj (fun a ha ↦ hmax a (by simp [ha]) ha) hmax' he
  exact ⟨by simpa using hr.subst hw hχ, by simpa using hf w hw⟩

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺(k + 1)]

/-- The negation of a partial instance of a block of `E` is true whenever it is readable. -/
lemma IsPartialInstance.readableTruth_neg (hE : ∀ e ∈ E, IsFalseBlock k D e) {r φ : V}
    (h : IsPartialInstance E r φ) (hn : IsReadable k D (neg ℒₒᵣ φ)) :
    ReadableTruth k D (neg ℒₒᵣ φ) := by
  have hP : 𝚷ᴬ-[k + 1].DefinablePred fun r : V ↦ ∀ φ, IsPartialInstance E r φ →
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

end falseBlock

end FFL.FirstOrder.Arithmetic.Bootstrapping
