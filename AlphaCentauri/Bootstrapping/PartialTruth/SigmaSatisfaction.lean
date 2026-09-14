module

public import AlphaCentauri.Bootstrapping.Prenex
public import AlphaCentauri.Bootstrapping.PartialTruth.BoundedSatisfaction

/-!
# Satisfaction for prenex $\Sigma_n$ and $\Pi_n$ formulas

This module defines satisfaction predicates for the internally coded strict prenex hierarchy and
proves their definability, Tarski conditions, duality, monotonicity, and substitution laws.

- [HP98, Definition I.1.74]
- [HP98, Theorem I.1.75(1)] -/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

mutual
  /-- `SigmaSatisfaction n z e` says that the strict prenex $\Sigma_n$ formula `z` is satisfied by
  `e`. -/
  def SigmaSatisfaction : ℕ → V → V → Prop
    | 0 => BoundedSatisfaction
    | n + 1 => fun z e ↦
        ∃ k q, z = qqExss q k ∧ IsStrictPi n q ∧
          ∃ w, len w = k ∧ PiSatisfaction n q (vecAppend w e)

  /-- `PiSatisfaction n z e` says that the strict prenex $\Pi_n$ formula `z` is satisfied by `e`. -/
  def PiSatisfaction : ℕ → V → V → Prop
    | 0 => BoundedSatisfaction
    | n + 1 => fun z e ↦
        IsStrictPi (n + 1) z ∧ IsUFormula ℒₒᵣ z ∧ ¬SigmaSatisfaction (n + 1) (neg ℒₒᵣ z) e
end

/-- The $\Pi_{m + 1}$ formula for `PiSatisfaction (m + 1)` associated with a formula for
`SigmaSatisfaction (m + 1)`. -/
noncomputable def piOfSigma (m : ℕ) (σ : 𝚺-[m + 1].Semisentence 2) :
    𝚷-[m + 1].Semisentence 2 := .mkPi
  “z e. !(isStrictPi (m + 1)).pi z ∧ !(isUFormula ℒₒᵣ).pi z ∧
    ∀ nz, !(negGraph ℒₒᵣ).val nz z → ¬!σ.val nz e”
  (by
    have h1 : Hierarchy 𝚷 (m + 1) (isStrictPi (m + 1)).pi.val :=
      (isStrictPi (m + 1)).pi.pi_prop.mono (Nat.le_add_left 1 m)
    have h2 : Hierarchy 𝚷 (m + 1) (isUFormula ℒₒᵣ).pi.val :=
      (isUFormula ℒₒᵣ).pi.pi_prop.mono (Nat.le_add_left 1 m)
    have h3 : Hierarchy 𝚺 (m + 1) (negGraph ℒₒᵣ).val :=
      (negGraph ℒₒᵣ).sigma_prop.mono (Nat.le_add_left 1 m)
    have h4 : Hierarchy 𝚺 (m + 1) σ.val := σ.sigma_prop
    simp [h1, h2, h3, h4])

/-- The $\Sigma_{m + 2}$ formula for `SigmaSatisfaction (m + 2)` associated with a formula for
`PiSatisfaction (m +
1)`. -/
noncomputable def sigmaOfPi (m : ℕ) (π : 𝚷-[m + 1].Semisentence 2) :
    𝚺-[m + 2].Semisentence 2 := .mkSigma
  “z e. ∃ k q w e', !qqExssDef z q k ∧ !(isStrictPi (m + 1)).val q ∧ !lenDef k w ∧
    !vecAppendDef e' w e ∧ !π.val q e'”
  (by
    have h1 : Hierarchy 𝚺 (m + 2) qqExssDef.val :=
      qqExssDef.sigma_prop.mono (show 1 ≤ m + 2 by omega)
    have h2 : Hierarchy 𝚺 (m + 2) (isStrictPi (m + 1)).val :=
      (isStrictPi (m + 1)).sigma.sigma_prop.mono (show 1 ≤ m + 2 by omega)
    have h3 : Hierarchy 𝚺 (m + 2) lenDef.val :=
      lenDef.sigma_prop.mono (show 1 ≤ m + 2 by omega)
    have h4 : Hierarchy 𝚺 (m + 2) vecAppendDef.val :=
      vecAppendDef.sigma_prop.mono (show 1 ≤ m + 2 by omega)
    have h5 : Hierarchy 𝚺 (m + 2) π.val := π.pi_prop.accum 𝚺
    simp [h1, h2, h3, h4, h5])

/-- The $\Sigma_1$ formula for `SigmaSatisfaction 1`. -/
noncomputable def sigmaZero : 𝚺-[1].Semisentence 2 := .mkSigma
  “z e. ∃ k q w e', !qqExssDef z q k ∧ !(isStrictPi 0).val q ∧ !lenDef k w ∧
    !vecAppendDef e' w e ∧ !boundedSatisfaction.val q e'”
  (by
    have h1 : Hierarchy 𝚺 1 qqExssDef.val := qqExssDef.sigma_prop
    have h2 : Hierarchy 𝚺 1 (isStrictPi 0).val := (isStrictPi 0).sigma.sigma_prop
    have h3 : Hierarchy 𝚺 1 lenDef.val := lenDef.sigma_prop
    have h4 : Hierarchy 𝚺 1 vecAppendDef.val := vecAppendDef.sigma_prop
    have h5 : Hierarchy 𝚺 1 boundedSatisfaction.val :=
      HierarchySymbol.Semiformula.val_sigma boundedSatisfaction ▸
        boundedSatisfaction.sigma.sigma_prop
    simp [h1, h2, h3, h4, h5])

/-- The $\Sigma_{n + 1}$ formula defining `SigmaSatisfaction (n + 1)`, with arguments `(z, e)`. -/
noncomputable def sigmaSatisfaction : (n : ℕ) → 𝚺-[n + 1].Semisentence 2
  | 0 => sigmaZero
  | n + 1 => sigmaOfPi n (piOfSigma n (sigmaSatisfaction n))

/-- The $\Pi_{n + 1}$ formula defining `PiSatisfaction (n + 1)`, with arguments `(z, e)`. -/
noncomputable def piSatisfaction (n : ℕ) :
    𝚷-[n + 1].Semisentence 2 := piOfSigma n (sigmaSatisfaction n)

private lemma sigmaSatisfaction_succ (n : ℕ) :
    sigmaSatisfaction (n + 1) = sigmaOfPi n (piSatisfaction n) := rfl

private lemma piDefined_of_sigmaDefined {m : ℕ} {σ : 𝚺-[m + 1].Semisentence 2}
    (hσ : 𝚺-[m + 1]-Relation (SigmaSatisfaction (m + 1) : V → V → Prop) via σ) :
    𝚷-[m + 1]-Relation (PiSatisfaction (m + 1) : V → V → Prop) via piOfSigma m σ := .mk fun v ↦ by
  have := hσ
  simp [piOfSigma, PiSatisfaction]

private lemma sigmaDefined_of_piDefined {m : ℕ} {π : 𝚷-[m + 1].Semisentence 2}
    (hπ : 𝚷-[m + 1]-Relation (PiSatisfaction (m + 1) : V → V → Prop) via π) :
    𝚺-[m + 2]-Relation (SigmaSatisfaction (m + 2) : V → V →
      Prop) via sigmaOfPi m π := .mk fun v ↦ by
  have := hπ
  simp [sigmaOfPi, SigmaSatisfaction]

private lemma sigmaZero_defined :
    𝚺-[1]-Relation (SigmaSatisfaction 1 : V → V → Prop) via sigmaZero := .mk fun v ↦ by
  simp [sigmaZero, SigmaSatisfaction, PiSatisfaction]

private lemma sigmaDefined : ∀ n : ℕ, 𝚺-[n + 1]-Relation (SigmaSatisfaction (n + 1) : V → V →
  Prop) via sigmaSatisfaction n
  | 0 => sigmaZero_defined
  | n + 1 => by
    rw [sigmaSatisfaction_succ]
    exact sigmaDefined_of_piDefined (piDefined_of_sigmaDefined (sigmaDefined n))

/-- The formula `sigmaSatisfaction n` defines satisfaction for strict prenex $\Sigma_{n + 1}$
formulas. -/
instance SigmaSatisfaction.defined (n : ℕ) :
    𝚺-[n + 1]-Relation (SigmaSatisfaction (n + 1) : V → V →
      Prop) via sigmaSatisfaction n := sigmaDefined n

/-- The formula `piSatisfaction n` defines satisfaction for strict prenex $\Pi_{n + 1}$ formulas. -/
instance PiSatisfaction.defined (n : ℕ) :
    𝚷-[n + 1]-Relation (PiSatisfaction (n + 1) : V → V → Prop) via piSatisfaction n :=
  piDefined_of_sigmaDefined (sigmaDefined n)

/-- Satisfaction for strict prenex $\Sigma_{n + 1}$ formulas is definable at level $\Sigma_{n + 1}$. -/
instance SigmaSatisfaction.definable (n : ℕ) :
    𝚺-[n + 1]-Relation (SigmaSatisfaction (n + 1) : V → V → Prop) :=
  (SigmaSatisfaction.defined n).to_definable

/-- Satisfaction for strict prenex $\Pi_{n + 1}$ formulas is definable at level $\Pi_{n + 1}$. -/
instance PiSatisfaction.definable (n : ℕ) :
    𝚷-[n + 1]-Relation (PiSatisfaction (n + 1) : V → V → Prop) :=
  (PiSatisfaction.defined n).to_definable

@[simp] lemma SigmaSatisfaction.zero : SigmaSatisfaction 0 = (BoundedSatisfaction : V → V →
  Prop) := by simp [SigmaSatisfaction]

@[simp] lemma PiSatisfaction.zero : PiSatisfaction 0 = (BoundedSatisfaction : V → V →
  Prop) := by simp [PiSatisfaction]

/-! ## Tarski conditions

- [HP98, Definition I.1.74]
- [HP98, Theorem I.1.75(2)] -/

section
variable {n : ℕ} {z e : V}

private lemma sigmaSatisfaction_succ_iff :
    SigmaSatisfaction (n + 1) z e ↔ ∃ k q, z = qqExss q k ∧ IsStrictPi n q ∧
      ∃ w, len w = k ∧ PiSatisfaction n q (vecAppend w e) := by rw [SigmaSatisfaction]

private lemma piSatisfaction_succ_iff :
    PiSatisfaction (n + 1) z e ↔ IsStrictPi (n + 1) z ∧ IsUFormula ℒₒᵣ z ∧
      ¬SigmaSatisfaction (n + 1) (neg ℒₒᵣ z) e := by rw [PiSatisfaction]

theorem PiSatisfaction.dom (h : PiSatisfaction n z e) :
    IsStrictPi n z ∧ IsUFormula ℒₒᵣ z := by
  match n with
  | 0 => exact BoundedSatisfaction.dom (by simpa using h)
  | _ + 1 => exact ⟨(piSatisfaction_succ_iff.mp h).1, (piSatisfaction_succ_iff.mp h).2.1⟩

theorem SigmaSatisfaction.dom (h : SigmaSatisfaction n z e) :
    IsStrictSigma n z ∧ IsUFormula ℒₒᵣ z := by
  match n with
  | 0 => exact BoundedSatisfaction.dom (by simpa using h)
  | _ + 1 =>
    obtain ⟨k, q, rfl, hq, w, -, hsat⟩ := sigmaSatisfaction_succ_iff.mp h
    exact ⟨⟨k, q, rfl, hq⟩, isUFormula_qqExss.mpr (PiSatisfaction.dom hsat).2⟩

theorem PiSatisfaction.neg_iff (hz : IsStrictSigma n z)
    (hz' : IsUFormula ℒₒᵣ z) : PiSatisfaction n (neg ℒₒᵣ z) e ↔ ¬SigmaSatisfaction n z e := by
  match n with
  | 0 => simpa using BoundedSatisfaction.neg_iff hz hz'
  | _ + 1 =>
    rw [piSatisfaction_succ_iff, IsUFormula.neg_neg hz']
    simp [IsStrictSigma.neg hz' hz, hz']

theorem SigmaSatisfaction.neg_iff (hz : IsStrictPi n z)
    (hz' : IsUFormula ℒₒᵣ z) : SigmaSatisfaction n (neg ℒₒᵣ z) e ↔ ¬PiSatisfaction n z e := by
  match n with
  | 0 => simpa using BoundedSatisfaction.neg_iff hz hz'
  | _ + 1 =>
    rw [piSatisfaction_succ_iff (z := z)]
    simp [hz, hz']

end

/-! ### Maximal existential blocks

The prenex classes do not determine the decomposition `z = qqExss q k` a code admits, so the
definition of `SigmaSatisfaction (n + 1)` has to be shown independent of it. The tool is the
*maximal*
existential block of a code, the decomposition whose matrix does not itself begin with an
existential quantifier: every other decomposition is an initial segment of it.

- [HP98, Lemma I.1.69]
- [HP98, Lemma I.1.68(2)] -/

private lemma qqExss_cancel (k : V) :
    ∀ p p' j : V, qqExss p k = qqExss p' (k + j) → p = qqExss p' j := by
  induction k using ISigma1.pi1_succ_induction
  · definability
  case zero => intro p p' j h; simpa using h
  case succ k ih =>
    intro p p' j h
    rw [qqExss_succ, add_right_comm k 1 j, qqExss_succ, qqExs_inj] at h
    exact ih p p' j h

private lemma exists_ex_block (z : V) : ∃ K M, z = qqExss M K ∧ ∀ p : V, M ≠ ^∃ p := by
  have H : ∀ z : V, ∃ K ≤ z, ∃ M ≤ z, z = qqExss M K ∧ ∀ p < M, M ≠ ^∃ p := by
    intro z
    induction z using ISigma1.sigma1_order_induction
    · definability
    case ind z ih =>
      by_cases hz : ∃ p < z, z = ^∃ p
      · obtain ⟨p, hp, rfl⟩ := hz
        obtain ⟨K, hK, M, hM, rfl, hM'⟩ := ih p hp
        exact ⟨K + 1, le_trans (add_le_add hK (le_refl 1)) (succ_le_qqExs _),
          M, le_trans hM (le_of_lt hp), by rw [qqExss_succ], hM'⟩
      · exact ⟨0, by simp, z, by simp, by simp, fun p hp h ↦ hz ⟨p, hp, h⟩⟩
  obtain ⟨K, -, M, -, h, hM⟩ := H z
  exact ⟨K, M, h, fun p hp ↦ hM p (hp ▸ lt_exists p) hp⟩

private lemma ex_block_dominates {z M K q k : V} (hMK : z = qqExss M K)
    (hM : ∀ p : V, M ≠ ^∃ p) (hqk : z = qqExss q k) : ∃ j, K = k + j ∧ q = qqExss M j := by
  rcases le_total k K with h | h
  · obtain ⟨j, rfl⟩ := exists_add_of_le h
    exact ⟨j, rfl, qqExss_cancel k q M j (by rw [← hqk, hMK])⟩
  · obtain ⟨j, rfl⟩ := exists_add_of_le h
    have hMq : M = qqExss q j := qqExss_cancel K M q j (by rw [← hMK, hqk])
    rcases zero_or_succ j with rfl | ⟨j, rfl⟩
    · exact ⟨0, by simp, by simpa using hMq.symm⟩
    · exact absurd hMq (by rw [qqExss_succ]; exact hM _)

private lemma isStrictSigma_of_isStrictPi_ex {n : ℕ} {p : V} (h : IsStrictPi (n + 1) (^∃ p)) :
    IsStrictSigma n (^∃ p) := by
  obtain ⟨k, q, heq, hq⟩ := h
  rcases zero_or_succ k with rfl | ⟨k, rfl⟩
  · rw [qqAlls_zero] at heq; exact heq ▸ hq
  · rw [qqAlls_succ] at heq; simp [qqExs, qqAll, pair_ext_iff] at heq

/-- The maximal existential block of a $\Delta_0$ code has length at most one, and its matrix is
$\Delta_0$: a $\Delta_0$ code begins with at most one existential quantifier, the one of a bounded
existential quantification. -/
private lemma isBounded_ex_block {z M K : V} (hz : IsBounded z) (hMK : z = qqExss M K)
    (hM : ∀ p : V, M ≠ ^∃ p) : IsBounded M ∧ K ≤ 1 := by
  rcases zero_or_succ K with rfl | ⟨K, rfl⟩
  · rw [qqExss_zero] at hMK; exact ⟨hMK ▸ hz, by simp⟩
  · rw [qqExss_succ] at hMK
    subst hMK
    obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, heq⟩ := IsBounded.of_ex hz
    rcases zero_or_succ K with rfl | ⟨K, rfl⟩
    · rw [qqExss_zero] at heq
      subst heq
      refine ⟨IsBounded.and_iff.mpr ⟨?_, hq⟩, by simp⟩
      rw [Arithmetic.qqLT]; exact IsBounded.rel
    · rw [qqExss_succ] at heq
      simp [qqExs, qqAnd, pair_ext_iff] at heq

private lemma isStrictPi_ex_block : ∀ (n : ℕ) (z M K : V), IsStrictSigma (n + 1) z →
    z = qqExss M K → (∀ p : V, M ≠ ^∃ p) → IsStrictPi n M
  | 0, _, M, _, hz, hMK, hM => by
    obtain ⟨k, q, hqk, hq⟩ := hz
    obtain ⟨j, -, rfl⟩ := ex_block_dominates hMK hM hqk
    exact (isBounded_ex_block hq rfl hM).1
  | n + 1, _, M, _, hz, hMK, hM => by
    obtain ⟨k, q, hqk, hq⟩ := hz
    obtain ⟨j, -, rfl⟩ := ex_block_dominates hMK hM hqk
    rcases zero_or_succ j with rfl | ⟨j, rfl⟩
    · simpa using hq
    · have hs : IsStrictSigma n (qqExss M (j + 1)) := by
        rw [qqExss_succ] at hq ⊢
        exact isStrictSigma_of_isStrictPi_ex hq
      match n with
      | 0 => exact IsStrictPi.of_bounded (isBounded_ex_block hs rfl hM).1
      | n + 1 =>
        exact IsStrictPi.mono (by omega)
          (isStrictPi_ex_block n (qqExss M (j + 1)) M (j + 1) hs rfl hM)

/-! ### Vector blocks -/

private lemma vecAppend_assoc (u v e : V) :
    vecAppend (vecAppend u v) e = vecAppend u (vecAppend v e) := by
  induction u using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin x u ih => simp [ih]

private lemma exists_vecAppend_singleton {k w : V} (h : len w = k + 1) :
    ∃ u x, len u = k ∧ w = vecAppend u ?[x] := by
  have H : ∀ w : V, w ≠ 0 → ∃ u ≤ w, ∃ x ≤ w, len u + 1 = len w ∧ w = vecAppend u ?[x] := by
    intro w
    induction w using adjoin_ISigma1.sigma1_succ_induction
    · definability
    case nil => simp
    case adjoin y w ih =>
      intro _
      rcases eq_or_ne w 0 with rfl | hw
      · exact ⟨0, by simp, y, le_of_lt (lt_adjoin y 0), by simp⟩
      · obtain ⟨u, hu, x, hx, hlen, heq⟩ := ih hw
        exact ⟨y ∷ u, adjoin_le_adjoin (le_refl y) hu, x,
          le_trans hx (le_of_lt (lt_adjoin' y w)), by simp [hlen], by simp [← heq]⟩
  obtain ⟨u, -, x, -, hlen, heq⟩ := H w (by rintro rfl; simp at h)
  exact ⟨u, x, add_right_cancel (hlen.trans h), heq⟩

/-! ### The $\Delta_0$ existential condition

- [HP98, Theorem I.1.70(iv)] -/

private lemma boundedSatisfaction_ex_iff {p e : V} (h : IsBounded (^∃ p)) :
    BoundedSatisfaction (^∃ p) e ↔ ∃ x, BoundedSatisfaction p (x ∷ e) := by
  obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ := IsBounded.of_ex h
  have hlt : ∀ x : V, BoundedSatisfaction (Arithmetic.qqLT (qqBvar 0) (termBShift ℒₒᵣ t)) (x ∷ e) ↔
      x < termVal e t := fun x ↦ by
    rw [BoundedSatisfaction.lt_iff (by simp) ht.termBShift]
    simp [termVal_termBShift ht x e]
  rw [show (^∃ ((Arithmetic.qqLT (qqBvar 0) (termBShift ℒₒᵣ t)) ^⋏ q) : V)
      = qqBex (termBShift ℒₒᵣ t) q from rfl, BoundedSatisfaction.bex_iff ht]
  constructor
  · rintro ⟨x, hx, hsat⟩
    exact ⟨x, BoundedSatisfaction.and_iff.mpr ⟨(hlt x).mpr hx, hsat⟩⟩
  · rintro ⟨x, hsat⟩
    obtain ⟨h₁, h₂⟩ := BoundedSatisfaction.and_iff.mp hsat
    exact ⟨x, (hlt x).mp h₁, h₂⟩

/-! ### The block characterization

Satisfaction is defined through *some* decomposition of the code into an existential block over
a strict $\Pi_n$ matrix. `BlockSatisfaction` says that the *maximal* block computes it, which makes
the
definition independent of the decomposition; the Tarski conditions all follow from it, and it is
itself proved by recursion on the level, since a matrix that still begins with an existential
quantifier belongs to a lower level.

- [HP98, Theorem I.1.75(2)]
- [HP98, Theorem I.1.75(2)(v)]
- [HP98, Theorem I.1.75(2)(v′)] -/

/-- Strict $\Sigma_{n + 1}$ satisfaction of `z` is witnessed over the maximal existential block of
`z`. -/
private def BlockSatisfaction (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (n : ℕ) : Prop :=
  ∀ z M K e : V, IsStrictSigma (n + 1) z → IsUFormula ℒₒᵣ z → z = qqExss M K →
    (∀ p : V, M ≠ ^∃ p) → (SigmaSatisfaction (n + 1) z e ↔ ∃ w, len w = K ∧
      PiSatisfaction n M (vecAppend w e))

private lemma of_Pi0 (hB : BlockSatisfaction V 0) {z e : V} (hz : IsBounded z)
    (hz' : IsUFormula ℒₒᵣ z) : SigmaSatisfaction 1 z e ↔ PiSatisfaction 0 z e := by
  constructor
  · intro h
    obtain ⟨K, M, hMK, hM⟩ := exists_ex_block z
    obtain ⟨w, hw, hsat⟩ := (hB z M K e (IsStrictSigma.of_pi hz) hz' hMK hM).mp h
    obtain ⟨hMd, hK1⟩ := isBounded_ex_block hz hMK hM
    rcases zero_or_succ K with rfl | ⟨K, rfl⟩
    · rw [qqExss_zero] at hMK
      rw [len_zero_iff_eq_nil.mp hw] at hsat
      simpa [hMK] using hsat
    · have hK : K = 0 := by simpa using hK1
      subst hK
      rw [qqExss_succ, qqExss_zero] at hMK
      obtain ⟨x, rfl⟩ := eq_singleton_iff_len_eq_one.mp (by simpa using hw)
      have h0 : BoundedSatisfaction M (x ∷ e) := by simpa using hsat
      simpa [hMK] using (boundedSatisfaction_ex_iff (hMK ▸ hz)).mpr ⟨x, h0⟩
  · intro h
    exact sigmaSatisfaction_succ_iff.mpr ⟨0, z, by simp, hz, 0, by simp, by simpa using h⟩

private lemma mono_step : ∀ (n : ℕ), (∀ m ≤ n, BlockSatisfaction V m) →
    (∀ z e : V, IsStrictSigma n z → IsUFormula ℒₒᵣ z →
      (SigmaSatisfaction n z e ↔ SigmaSatisfaction (n + 1) z e)) ∧
    (∀ z e : V, IsStrictPi n z → IsUFormula ℒₒᵣ z → (PiSatisfaction n z e ↔
      PiSatisfaction (n + 1) z e)) := by
  intro n
  induction n with
  | zero =>
    intro hB
    have hsig : ∀ z e : V, IsStrictSigma 0 z → IsUFormula ℒₒᵣ z →
        (SigmaSatisfaction 0 z e ↔ SigmaSatisfaction 1 z e) := fun z e hz hz' ↦ by
      simpa using (of_Pi0 (hB 0 le_rfl) hz hz').symm
    exact ⟨hsig, fun z e hz hz' ↦ by
      rw [show (PiSatisfaction 0 z e ↔ ¬SigmaSatisfaction 0 (neg ℒₒᵣ z) e) by
          rw [SigmaSatisfaction.neg_iff hz hz']; simp,
        show (PiSatisfaction 1 z e ↔ ¬SigmaSatisfaction 1 (neg ℒₒᵣ z) e) by
          rw [SigmaSatisfaction.neg_iff (IsStrictPi.mono (Nat.le_succ 0) hz) hz']; simp,
        hsig (neg ℒₒᵣ z) e (IsStrictPi.neg hz' hz) hz'.neg]⟩
  | succ n ih =>
    intro hB
    have hpin := (ih fun i hi ↦ hB i (by omega)).2
    have hsig : ∀ z e : V, IsStrictSigma (n + 1) z → IsUFormula ℒₒᵣ z →
        (SigmaSatisfaction (n + 1) z e ↔ SigmaSatisfaction (n + 2) z e) := fun z e hz hz' ↦ by
      obtain ⟨K, M, hMK, hM⟩ := exists_ex_block z
      have hMu : IsUFormula ℒₒᵣ M := isUFormula_qqExss.mp (hMK ▸ hz')
      have hMpi : IsStrictPi n M := isStrictPi_ex_block n z M K hz hMK hM
      rw [hB n (by omega) z M K e hz hz' hMK hM,
        hB (n + 1) le_rfl z M K e (IsStrictSigma.mono (by omega) hz) hz' hMK hM]
      exact exists_congr fun w ↦ and_congr_right fun _ ↦ hpin M _ hMpi hMu
    exact ⟨hsig, fun z e hz hz' ↦ by
      rw [show (PiSatisfaction (n + 1) z e ↔ ¬SigmaSatisfaction (n + 1) (neg ℒₒᵣ z) e) by
          rw [SigmaSatisfaction.neg_iff hz hz']; simp,
        show (PiSatisfaction (n + 2) z e ↔ ¬SigmaSatisfaction (n + 2) (neg ℒₒᵣ z) e) by
          rw [SigmaSatisfaction.neg_iff (IsStrictPi.mono (Nat.le_succ _) hz) hz']; simp,
        hsig (neg ℒₒᵣ z) e (IsStrictPi.neg hz' hz) hz'.neg]⟩

private lemma of_pi_step : ∀ (n : ℕ), (∀ m ≤ n, BlockSatisfaction V m) →
    (∀ z e : V, IsStrictPi n z → IsUFormula ℒₒᵣ z → (SigmaSatisfaction (n + 1) z e ↔
      PiSatisfaction n z e)) ∧
    (∀ z e : V, IsStrictSigma n z → IsUFormula ℒₒᵣ z →
      (PiSatisfaction (n + 1) z e ↔ SigmaSatisfaction n z e)) := by
  intro n
  induction n with
  | zero =>
    intro hB
    exact ⟨fun z e hz hz' ↦ of_Pi0 (hB 0 le_rfl) hz hz',
      fun z e hz hz' ↦ by
        rw [show (PiSatisfaction 1 z e ↔ ¬SigmaSatisfaction 1 (neg ℒₒᵣ z) e) by
            rw [SigmaSatisfaction.neg_iff (IsStrictPi.of_sigma hz) hz']; simp,
          of_Pi0 (hB 0 le_rfl) (IsStrictSigma.neg hz' hz) hz'.neg,
          PiSatisfaction.neg_iff hz hz']
        simp⟩
  | succ n ih =>
    intro hB
    have hsig : ∀ z e : V, IsStrictPi (n + 1) z → IsUFormula ℒₒᵣ z →
        (SigmaSatisfaction (n + 2) z e ↔ PiSatisfaction (n + 1) z e) := by
      intro z e hz hz'
      constructor
      · intro h
        obtain ⟨K, M, hMK, hM⟩ := exists_ex_block z
        have hMu : IsUFormula ℒₒᵣ M := isUFormula_qqExss.mp (hMK ▸ hz')
        obtain ⟨w, hw, hsat⟩ :=
          (hB (n + 1) le_rfl z M K e (IsStrictSigma.of_pi hz) hz' hMK hM).mp h
        rcases zero_or_succ K with rfl | ⟨K, rfl⟩
        · rw [qqExss_zero] at hMK
          rw [len_zero_iff_eq_nil.mp hw] at hsat
          simpa [hMK] using hsat
        · have hzex : z = ^∃ (qqExss M K) := by rw [hMK, qqExss_succ]
          have hzs : IsStrictSigma n z := by
            rw [hzex] at hz ⊢
            exact isStrictSigma_of_isStrictPi_ex hz
          refine ((ih fun i hi ↦ hB i (by omega)).2 z e hzs hz').mpr ?_
          match n with
          | 0 =>
            obtain ⟨hMd, hK1⟩ := isBounded_ex_block hzs hMK hM
            have hK : K = 0 := by simpa using hK1
            subst hK
            rw [qqExss_zero] at hzex
            obtain ⟨x, rfl⟩ := eq_singleton_iff_len_eq_one.mp (by simpa using hw)
            have h0 : BoundedSatisfaction M (x ∷ e) := by
              simpa using ((ih fun i hi ↦ hB i (by omega)).2 M (x ∷ e) hMd hMu).mp
                (by simpa using hsat)
            simpa [hzex] using (boundedSatisfaction_ex_iff (hzex ▸ hzs)).mpr ⟨x, h0⟩
          | n + 1 =>
            have hMpi : IsStrictPi n M := isStrictPi_ex_block n z M (K + 1) hzs hMK hM
            have h1 := (mono_step n fun i hi ↦ hB i (by omega)).2
            have h2 := (mono_step (n + 1) fun i hi ↦ hB i (by omega)).2
            refine (hB n (by omega) z M (K + 1) e hzs hz' hMK hM).mpr ⟨w, hw, ?_⟩
            rw [h1 M _ hMpi hMu, h2 M _ (IsStrictPi.mono (by omega) hMpi) hMu]
            exact hsat
      · intro h
        exact sigmaSatisfaction_succ_iff.mpr ⟨0, z, by simp, hz, 0, by simp, by simpa using h⟩
    exact ⟨hsig, fun z e hz hz' ↦ by
      rw [show (PiSatisfaction (n + 2) z e ↔ ¬SigmaSatisfaction (n + 2) (neg ℒₒᵣ z) e) by
          rw [SigmaSatisfaction.neg_iff (IsStrictPi.of_sigma hz) hz']; simp,
        hsig (neg ℒₒᵣ z) e (IsStrictSigma.neg hz' hz) hz'.neg, PiSatisfaction.neg_iff hz hz']
      simp⟩

private lemma blockSatisfaction : ∀ n : ℕ, BlockSatisfaction V n := fun n ↦ by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z M K e hz hz' hMK hM
    have hMu : IsUFormula ℒₒᵣ M := isUFormula_qqExss.mp (hMK ▸ hz')
    have hMpi : IsStrictPi n M := isStrictPi_ex_block n z M K hz hMK hM
    refine ⟨fun h ↦ ?_, fun ⟨w, hw, hsat⟩ ↦ sigmaSatisfaction_succ_iff.mpr ⟨K, M, hMK, hMpi, w, hw,
      hsat⟩⟩
    obtain ⟨k, q, hqk, hq, w, hw, hsat⟩ := sigmaSatisfaction_succ_iff.mp h
    obtain ⟨j, rfl, rfl⟩ := ex_block_dominates hMK hM hqk
    rcases zero_or_succ j with rfl | ⟨j, rfl⟩
    · exact ⟨w, by simpa using hw, by simpa using hsat⟩
    · have hqex : (^∃ (qqExss M j) : V) = qqExss M (j + 1) := (qqExss_succ M j).symm
      rw [qqExss_succ] at hq hsat
      match n with
      | 0 =>
        obtain ⟨-, hj⟩ := isBounded_ex_block hq hqex hM
        have hj0 : j = 0 := by simpa using hj
        subst hj0
        rw [qqExss_zero] at hq hsat
        obtain ⟨x, hx⟩ := (boundedSatisfaction_ex_iff hq).mp (by simpa using hsat)
        exact ⟨x ∷ w, by simp [hw], by simpa using hx⟩
      | m + 1 =>
        have hqU : IsUFormula ℒₒᵣ (^∃ (qqExss M j) : V) := by
          rw [hqex]; exact isUFormula_qqExss.mpr hMu
        have hqs : IsStrictSigma m (^∃ (qqExss M j) : V) := isStrictSigma_of_isStrictPi_ex hq
        have hsat' : SigmaSatisfaction m (^∃ (qqExss M j) : V) (vecAppend w e) :=
          ((of_pi_step m fun i hi ↦ ih i (by omega)).2 _ _ hqs hqU).mp hsat
        match m with
        | 0 =>
          obtain ⟨hMd, hj'⟩ := isBounded_ex_block hqs hqex hM
          have hj0 : j = 0 := by simpa using hj'
          subst hj0
          rw [qqExss_zero] at hqs hsat'
          obtain ⟨x, hx⟩ := (boundedSatisfaction_ex_iff hqs).mp (by simpa using hsat')
          refine ⟨x ∷ w, by simp [hw], ?_⟩
          refine ((of_pi_step 0 fun i hi ↦ ih i (by omega)).2 M _ hMd hMu).mpr ?_
          simpa using hx
        | m + 1 =>
          have hMpi' : IsStrictPi m M :=
            isStrictPi_ex_block m _ M (j + 1) hqs hqex hM
          obtain ⟨u, hu, husat⟩ :=
            (ih m (by omega) _ M (j + 1) (vecAppend w e) hqs hqU hqex hM).mp hsat'
          refine ⟨vecAppend u w, by rw [len_vecAppend, hu, hw, add_comm], ?_⟩
          rw [vecAppend_assoc]
          have h1 := (mono_step m fun i hi ↦ ih i (by omega)).2 M
            (vecAppend u (vecAppend w e)) hMpi' hMu
          have h2 := (mono_step (m + 1) fun i hi ↦ ih i (by omega)).2 M
            (vecAppend u (vecAppend w e)) (IsStrictPi.mono (by omega) hMpi') hMu
          exact h2.mp (h1.mp husat)

section
variable {n : ℕ} {z e : V}

theorem SigmaSatisfaction.of_pi (hz : IsStrictPi n z) (hz' : IsUFormula ℒₒᵣ z) :
    SigmaSatisfaction (n + 1) z e ↔ PiSatisfaction n z e :=
  (of_pi_step n fun m _ ↦ blockSatisfaction m).1 z e hz hz'

theorem PiSatisfaction.of_sigma (hz : IsStrictSigma n z) (hz' : IsUFormula ℒₒᵣ z) :
    PiSatisfaction (n + 1) z e ↔ SigmaSatisfaction n z e :=
  (of_pi_step n fun m _ ↦ blockSatisfaction m).2 z e hz hz'

end

private lemma exs_iff_aux {n : ℕ} {p e : V} (hp : IsStrictSigma (n + 1) p)
    (hp' : IsUFormula ℒₒᵣ p) : SigmaSatisfaction (n + 1) (^∃ p) e ↔ ∃ x,
      SigmaSatisfaction (n + 1) p (x ∷ e) := by
  obtain ⟨K, M, hMK, hM⟩ := exists_ex_block p
  have h1 : SigmaSatisfaction (n + 1) (^∃ p) e ↔ ∃ w, len w = K + 1 ∧
    PiSatisfaction n M (vecAppend w e) :=
    blockSatisfaction n (^∃ p) M (K + 1) e (IsStrictSigma.exs hp) (by simp [hp'])
      (by rw [qqExss_succ, ← hMK]) hM
  have h2 : ∀ x : V, SigmaSatisfaction (n + 1) p (x ∷ e) ↔
      ∃ u, len u = K ∧ PiSatisfaction n M (vecAppend u (x ∷ e)) :=
    fun x ↦ blockSatisfaction n p M K (x ∷ e) hp hp' hMK hM
  rw [h1]
  constructor
  · rintro ⟨w, hw, hsat⟩
    obtain ⟨u, x, hu, rfl⟩ := exists_vecAppend_singleton hw
    refine ⟨x, (h2 x).mpr ⟨u, hu, ?_⟩⟩
    rw [vecAppend_assoc] at hsat
    simpa using hsat
  · rintro ⟨x, hx⟩
    obtain ⟨u, hu, hsat⟩ := (h2 x).mp hx
    refine ⟨vecAppend u ?[x], by simp [hu], ?_⟩
    rw [vecAppend_assoc]
    simpa using hsat

section
variable {n : ℕ} {p e : V}

theorem SigmaSatisfaction.exs_iff : SigmaSatisfaction (n + 1) (^∃ p) e ↔ ∃ x,
  SigmaSatisfaction (n + 1) p (x ∷ e) := by
  by_cases hp : IsStrictSigma (n + 1) p ∧ IsUFormula ℒₒᵣ p
  · exact exs_iff_aux hp.1 hp.2
  · refine ⟨fun h ↦ ?_, fun ⟨_, hx⟩ ↦ absurd hx.dom hp⟩
    obtain ⟨hs, hu⟩ := h.dom
    exact absurd ⟨IsStrictSigma.of_exs hs, by simpa using hu⟩ hp

theorem PiSatisfaction.all_iff : PiSatisfaction (n + 1) (^∀ p) e ↔ ∀ x,
  PiSatisfaction (n + 1) p (x ∷ e) := by
  constructor
  · intro h
    obtain ⟨hs, hu, hns⟩ := piSatisfaction_succ_iff.mp h
    have hup : IsUFormula ℒₒᵣ p := by simpa using hu
    rw [neg_all hup, SigmaSatisfaction.exs_iff] at hns
    exact fun x ↦ piSatisfaction_succ_iff.mpr ⟨IsStrictPi.of_all hs, hup, fun hc ↦ hns ⟨x, hc⟩⟩
  · intro h
    obtain ⟨hsp, hup, -⟩ := piSatisfaction_succ_iff.mp (h 0)
    refine piSatisfaction_succ_iff.mpr ⟨IsStrictPi.all hsp, by simp [hup], ?_⟩
    rw [neg_all hup, SigmaSatisfaction.exs_iff]
    rintro ⟨x, hx⟩
    exact (piSatisfaction_succ_iff.mp (h x)).2.2 hx

end

section
variable {m n : ℕ} (h : m ≤ n) {z e : V}
include h

theorem SigmaSatisfaction.mono (hz : IsStrictSigma m z) (hz' : IsUFormula ℒₒᵣ z) :
    SigmaSatisfaction m z e ↔ SigmaSatisfaction n z e := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    exact ih.trans
      ((mono_step n fun i _ ↦ blockSatisfaction i).1 z e (IsStrictSigma.mono hn hz) hz')

theorem PiSatisfaction.mono (hz : IsStrictPi m z) (hz' : IsUFormula ℒₒᵣ z) :
    PiSatisfaction m z e ↔ PiSatisfaction n z e := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    exact ih.trans ((mono_step n fun i _ ↦ blockSatisfaction i).2 z e (IsStrictPi.mono hn hz) hz')

end

/-! ### Substitution under a quantifier block

- [HP98, 1.64(5)]
- [HP98, Lemma I.1.69]
- [HP98, 1.64(4)]
- [HP98, Theorem I.1.75(2)] -/

namespace QVecIter

/-- Primitive-recursive blueprint for iterating the quantifier lift of a substitution vector. -/
noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. !(qVecGraph ℒₒᵣ) y ih”

/-- Primitive-recursive construction iterating the quantifier lift of a substitution vector. -/
noncomputable def construction : PR.Construction V blueprint where
  zero := fun x ↦ x 0
  succ := fun _ _ ih ↦ qVec ℒₒᵣ ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  -- Letting `simp` apply `Semiformula.eval_substs` here overflows memory on Lean v4.33.1.
  succ_defined := .mk fun v ↦ by
    simp only [blueprint, HierarchySymbol.Semiformula.val_mkSigma]
    rw [Semiformula.eval_substs]
    simp [(qVec.defined (L := ℒₒᵣ) (V := V)).df]

end QVecIter

/-- `qVecIter w k` is the substitution vector `w` lifted past `k` quantifiers. -/
noncomputable def qVecIter (w k : V) : V := QVecIter.construction.result ![w] k

@[simp] lemma qVecIter_zero (w : V) : qVecIter w 0 = w := by
  simp [qVecIter, QVecIter.construction]

@[simp] lemma qVecIter_succ (w k : V) : qVecIter w (k + 1) = qVec ℒₒᵣ (qVecIter w k) := by
  simp [qVecIter, QVecIter.construction]

/-- Defining formula for the iterated quantifier lift. -/
noncomputable def _root_.FFL.FirstOrder.Arithmetic.qVecIterDef : 𝚺₁.Semisentence 3 :=
  QVecIter.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

/-- The iterated quantifier lift is $\Sigma_1$-definable. -/
instance qVecIter_defined : 𝚺₁-Function₂ (qVecIter : V → V → V) via qVecIterDef := .mk
  fun v ↦ by simp [QVecIter.construction.result_defined_iff, qVecIterDef]; rfl

/-- The $\Sigma_1$ definability instance for the iterated quantifier lift. -/
instance qVecIter_definable : 𝚺₁-Function₂ (qVecIter : V → V → V) := qVecIter_defined.to_definable

/-- The iterated quantifier lift is definable at every positive hierarchy level. -/
instance qVecIter_definable' (Γ m) : Γ-[m + 1]-Function₂ (qVecIter : V → V → V) :=
  qVecIter_definable.of_sigmaOne

private lemma isSemitermVec_qVecIter {m l w : V} (hw : IsSemitermVec ℒₒᵣ m l w) (k : V) :
    IsSemitermVec ℒₒᵣ (m + k) (l + k) (qVecIter w k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using hw
  case succ k ih =>
    rw [qVecIter_succ, ← add_assoc, ← add_assoc]
    exact ih.qVec

private lemma qVecIter_qVec (w k : V) :
    qVecIter (qVec ℒₒᵣ w) k = qVec ℒₒᵣ (qVecIter w k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qVecIter_succ, ih, qVecIter_succ]

private lemma substs_qqExss {p : V} (hp : IsUFormula ℒₒᵣ p) (k : V) :
    ∀ w : V, subst ℒₒᵣ w (qqExss p k) = qqExss (subst ℒₒᵣ (qVecIter w k) p) k := by
  induction k using ISigma1.pi1_succ_induction
  · definability
  case zero => intro w; simp
  case succ k ih =>
    intro w
    rw [qqExss_succ, substs_ex (isUFormula_qqExss.mpr hp), ih (qVec ℒₒᵣ w), qVecIter_qVec,
      qVecIter_succ, qqExss_succ]

private lemma substs_qqAlls {p : V} (hp : IsUFormula ℒₒᵣ p) (k : V) :
    ∀ w : V, subst ℒₒᵣ w (qqAlls p k) = qqAlls (subst ℒₒᵣ (qVecIter w k) p) k := by
  induction k using ISigma1.pi1_succ_induction
  · definability
  case zero => intro w; simp
  case succ k ih =>
    intro w
    rw [qqAlls_succ, substs_all (isUFormula_qqAlls.mpr hp), ih (qVec ℒₒᵣ w), qVecIter_qVec,
      qVecIter_succ, qqAlls_succ]

private lemma isSemiformula_qqExss {p : V} (k : V) :
    ∀ n : V, (IsSemiformula ℒₒᵣ n (qqExss p k) ↔ IsSemiformula ℒₒᵣ (n + k) p) := by
  induction k using ISigma1.pi1_succ_induction
  · definability
  case zero => intro n; simp
  case succ k ih => intro n; rw [qqExss_succ, IsSemiformula.exs, ih, add_assoc, add_comm 1 k]

private lemma isSemiformula_qqAlls {p : V} (k : V) :
    ∀ n : V, (IsSemiformula ℒₒᵣ n (qqAlls p k) ↔ IsSemiformula ℒₒᵣ (n + k) p) := by
  induction k using ISigma1.pi1_succ_induction
  · definability
  case zero => intro n; simp
  case succ k ih => intro n; rw [qqAlls_succ, IsSemiformula.all, ih, add_assoc, add_comm 1 k]

private lemma termValVec_qVecIter {m l w e : V} (hw : IsSemitermVec ℒₒᵣ m l w) (k : V) :
    ∀ v : V, len v = k →
      termValVec (vecAppend v e) (m + k) (qVecIter w k) = vecAppend v (termValVec e m w) := by
  induction k using ISigma1.pi1_succ_induction
  · definability
  case zero => intro v hv; rw [len_zero_iff_eq_nil.mp hv]; simp
  case succ k ih =>
    intro v hv
    rcases nil_or_adjoin v with rfl | ⟨x, v, rfl⟩
    · simp at hv
    · rw [vecAppend_adjoin, qVecIter_succ, ← add_assoc,
        termValVec_qVec (isSemitermVec_qVecIter hw k), ih v (by simpa using hv),
        vecAppend_adjoin]

private lemma isStrict_subst : ∀ (n : ℕ) (m l w p : V), IsSemitermVec ℒₒᵣ m l w →
    IsSemiformula ℒₒᵣ m p →
    (IsStrictSigma n p → IsStrictSigma n (subst ℒₒᵣ w p)) ∧
    (IsStrictPi n p → IsStrictPi n (subst ℒₒᵣ w p))
  | 0, _, _, _, _, hw, hp => ⟨fun h ↦ IsBounded.subst hw hp h, fun h ↦ IsBounded.subst hw hp h⟩
  | n + 1, m, l, w, p, hw, hp => by
    constructor
    · rintro ⟨k, q, rfl, hq⟩
      have hqp : IsSemiformula ℒₒᵣ (m + k) q := (isSemiformula_qqExss k m).mp hp
      refine ⟨k, subst ℒₒᵣ (qVecIter w k) q, substs_qqExss hqp.isUFormula k w, ?_⟩
      exact (isStrict_subst n (m + k) (l + k) (qVecIter w k) q
        (isSemitermVec_qVecIter hw k) hqp).2 hq
    · rintro ⟨k, q, rfl, hq⟩
      have hqp : IsSemiformula ℒₒᵣ (m + k) q := (isSemiformula_qqAlls k m).mp hp
      refine ⟨k, subst ℒₒᵣ (qVecIter w k) q, substs_qqAlls hqp.isUFormula k w, ?_⟩
      exact (isStrict_subst n (m + k) (l + k) (qVecIter w k) q
        (isSemitermVec_qVecIter hw k) hqp).1 hq

private lemma not_ex_subst {M : V} (hM : IsUFormula ℒₒᵣ M) (h : ∀ p : V, M ≠ ^∃ p) (w r : V) :
    subst ℒₒᵣ w M ≠ ^∃ r := by
  rcases hM.case with ⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl |
    ⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, -, rfl⟩
  · rw [substs_rel hR hv]; simp [qqRel, qqExs, pair_ext_iff]
  · rw [substs_nrel hR hv]; simp [qqNRel, qqExs, pair_ext_iff]
  · rw [substs_verum]; simp [qqVerum, qqExs, pair_ext_iff]
  · rw [substs_falsum]; simp [qqFalsum, qqExs, pair_ext_iff]
  · rw [substs_and hp hq]; simp [qqAnd, qqExs, pair_ext_iff]
  · rw [substs_or hp hq]; simp [qqOr, qqExs, pair_ext_iff]
  · rw [substs_all hp]; simp [qqAll, qqExs, pair_ext_iff]
  · exact absurd rfl (h p)

theorem SigmaSatisfaction.subst {n : ℕ} {m l w p e : V} (hw : IsSemitermVec ℒₒᵣ m l w)
    (hp : IsSemiformula ℒₒᵣ m p) (hp' : IsStrictSigma n p) :
    SigmaSatisfaction n (Bootstrapping.subst ℒₒᵣ w p) e ↔
      SigmaSatisfaction n p (termValVec e m w) := by
  induction n generalizing m l w p e with
  | zero => simpa using BoundedSatisfaction.subst hw hp hp'
  | succ n ih =>
    have hpi : ∀ {m l w q e' : V}, IsSemitermVec ℒₒᵣ m l w → IsSemiformula ℒₒᵣ m q →
        IsStrictPi n q →
        (PiSatisfaction n (Bootstrapping.subst ℒₒᵣ w q) e' ↔
          PiSatisfaction n q (termValVec e' m w)) := by
      intro m l w q e' hw hq hq'
      have hsq : IsStrictPi n (Bootstrapping.subst ℒₒᵣ w q) :=
        (isStrict_subst n m l w q hw hq).2 hq'
      rw [show (PiSatisfaction n (Bootstrapping.subst ℒₒᵣ w q) e' ↔
            ¬SigmaSatisfaction n (neg ℒₒᵣ (Bootstrapping.subst ℒₒᵣ w q)) e') by
          rw [SigmaSatisfaction.neg_iff hsq (hq.subst hw).isUFormula]; simp,
        ← substs_neg hq hw,
        ih hw (by simp [hq]) (IsStrictPi.neg hq.isUFormula hq'),
        SigmaSatisfaction.neg_iff hq' hq.isUFormula]
      simp
    obtain ⟨K, M, hMK, hM⟩ := exists_ex_block p
    have hMs : IsSemiformula ℒₒᵣ (m + K) M := (isSemiformula_qqExss K m).mp (hMK ▸ hp)
    have hMpi : IsStrictPi n M := isStrictPi_ex_block n p M K hp' hMK hM
    have hsubst : Bootstrapping.subst ℒₒᵣ w p
        = qqExss (Bootstrapping.subst ℒₒᵣ (qVecIter w K) M) K := by
      rw [hMK, substs_qqExss hMs.isUFormula K w]
    rw [blockSatisfaction n (Bootstrapping.subst ℒₒᵣ w p) _ K e
        ((isStrict_subst (n + 1) m l w p hw hp).1 hp') (hp.subst hw).isUFormula hsubst
        (not_ex_subst hMs.isUFormula hM _),
      blockSatisfaction n p M K (termValVec e m w) hp' hp.isUFormula hMK hM]
    refine exists_congr fun v ↦ and_congr_right fun hv ↦ ?_
    rw [hpi (isSemitermVec_qVecIter hw K) hMs hMpi, termValVec_qVecIter hw K v hv]

/-! ## Satisfaction under an externally supplied vector

- [HP98, Remark I.1.77]
- [HP98, Definition I.1.78(2)] -/

/-- `sigmaSatisfactionVec n k` defines `SigmaSatisfaction (n + 1)` under its `k` free variables. -/
noncomputable def sigmaSatisfactionVec (n k : ℕ) : 𝚺-[n + 1].Semisentence (k + 1) := .mkSigma
  “p. ∃ e, !lenDef ↑k e ∧
    (⋀ i, ∃ z, !nthDef z e ↑(i : Fin k).val ∧ z = #i.succ.succ.succ) ∧
    !(sigmaSatisfaction n).val p e”
  (by simp [lenDef.sigma_prop.mono (Nat.le_add_left 1 n),
    nthDef.sigma_prop.mono (Nat.le_add_left 1 n)])

theorem sigmaSatisfactionVec.defined (n k : ℕ) :
    𝚺-[n + 1].Defined
      (fun v : Fin (k + 1) → V ↦ SigmaSatisfaction (n + 1) (v 0) (matrixToVec (v ·.succ)))
      (sigmaSatisfactionVec n k) := .mk fun v ↦ by
  simp only [sigmaSatisfactionVec, Nat.succ_eq_add_one, Nat.reduceAdd,
    HierarchySymbol.Semiformula.val_mkSigma,
    Semiformula.eval_ex, LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp₂,
    Semiterm.val_operator, Matrix.comp₀, Structure.numeral_eq_numeral, numeral_eq_natCast_app,
      Semiterm.val_bvar,
    Matrix.cons_val_zero, HierarchySymbol.Defined.iff, Fin.isValue, Fin.Fin1.eq_one,
      Fin.succ_zero_eq_one,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.conj_hom_prop, Matrix.comp₃,
      Fin.succ_one_eq_two,
    Matrix.cons_app_two, Semiformula.eval_operator, Matrix.cons_val_succ, Structure.eq_iff_eq,
    LogicalConnective.Prop.and_eq, exists_eq_left]
  constructor
  · rintro ⟨x, hlen, hnth, hsat⟩
    have hx : x = matrixToVec (v ·.succ) := by
      apply nth_ext' (k : V) hlen.symm (by simp)
      intro i hi
      obtain ⟨j, rfl⟩ := lt_numeral_iff.mp (by simpa [← numeral_eq_natCast_app] using hi)
      simp [numeral_eq_natCast_app, hnth j]
    rwa [hx] at hsat
  · intro hsat
    exact ⟨matrixToVec (v ·.succ), by simp, fun i ↦ matrixToVec_nth _ i, hsat⟩

end FFL.FirstOrder.Arithmetic.Bootstrapping
