module

public import AlphaCentauri.Bootstrapping.Prenex
public import AlphaCentauri.Bootstrapping.PartialTruth.SatZero

/-!
# Satisfaction for prenex `𝚺-[n]` and `𝚷-[n]` formulas

This module defines satisfaction predicates for the internally coded strict prenex hierarchy and
proves their definability, Tarski conditions, duality, monotonicity, and substitution laws.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

mutual
  /-- `SatSigma n z e` says that the strict prenex `𝚺-[n]` formula `z` is satisfied by `e`.
  - [HP98, Definition I.1.74] -/
  def SatSigma : ℕ → V → V → Prop
    | 0 => SatZero
    | n + 1 => fun z e ↦
        ∃ k q, z = qqExss q k ∧ IsStrictPi n q ∧
          ∃ w, len w = k ∧ SatPi n q (vecAppend w e)

  /-- `SatPi n z e` says that the strict prenex `𝚷-[n]` formula `z` is satisfied by `e`.
  - [HP98, Definition I.1.74] -/
  def SatPi : ℕ → V → V → Prop
    | 0 => SatZero
    | n + 1 => fun z e ↦
        IsStrictPi (n + 1) z ∧ IsUFormula ℒₒᵣ z ∧ ¬SatSigma (n + 1) (neg ℒₒᵣ z) e
end

/-- The `𝚷-[m + 1]` formula for `SatPi (m + 1)` associated with a formula for `SatSigma (m + 1)`.
- [HP98, Definition I.1.74] -/
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

/-- The `𝚺-[m + 2]` formula for `SatSigma (m + 2)` associated with a formula for `SatPi (m + 1)`.
- [HP98, Definition I.1.74] -/
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

/-- The `𝚺₁` formula for `SatSigma 1`.
- [HP98, Definition I.1.74] -/
noncomputable def sigmaZero : 𝚺-[1].Semisentence 2 := .mkSigma
  “z e. ∃ k q w e', !qqExssDef z q k ∧ !(isStrictPi 0).val q ∧ !lenDef k w ∧
    !vecAppendDef e' w e ∧ !satZero.val q e'”
  (by
    have h1 : Hierarchy 𝚺 1 qqExssDef.val := qqExssDef.sigma_prop
    have h2 : Hierarchy 𝚺 1 (isStrictPi 0).val := (isStrictPi 0).sigma.sigma_prop
    have h3 : Hierarchy 𝚺 1 lenDef.val := lenDef.sigma_prop
    have h4 : Hierarchy 𝚺 1 vecAppendDef.val := vecAppendDef.sigma_prop
    have h5 : Hierarchy 𝚺 1 satZero.val :=
      HierarchySymbol.Semiformula.val_sigma satZero ▸ satZero.sigma.sigma_prop
    simp [h1, h2, h3, h4, h5])

/-- The `𝚺-[n + 1]` formula defining `SatSigma (n + 1)`, with arguments `(z, e)`.
- [HP98, Definition I.1.74]
- [HP98, Theorem I.1.75(1)] -/
noncomputable def satSigma : (n : ℕ) → 𝚺-[n + 1].Semisentence 2
  | 0 => sigmaZero
  | n + 1 => sigmaOfPi n (piOfSigma n (satSigma n))

/-- The `𝚷-[n + 1]` formula defining `SatPi (n + 1)`, with arguments `(z, e)`.
- [HP98, Definition I.1.74]
- [HP98, Theorem I.1.75(1)] -/
noncomputable def satPi (n : ℕ) : 𝚷-[n + 1].Semisentence 2 := piOfSigma n (satSigma n)

/-- `satPi` unfolds to `piOfSigma` applied to `satSigma` at the same level.
- [HP98, Definition I.1.74] -/
private lemma satSigma_succ (n : ℕ) : satSigma (n + 1) = sigmaOfPi n (satPi n) := rfl

/-- `piOfSigma m σ` defines `SatPi (m + 1)` when `σ` defines `SatSigma (m + 1)`.
- [HP98, Theorem I.1.75(1)] -/
private lemma piDefined_of_sigmaDefined {m : ℕ} {σ : 𝚺-[m + 1].Semisentence 2}
    (hσ : 𝚺-[m + 1]-Relation (SatSigma (m + 1) : V → V → Prop) via σ) :
    𝚷-[m + 1]-Relation (SatPi (m + 1) : V → V → Prop) via piOfSigma m σ := .mk fun v ↦ by
  have := hσ
  simp [piOfSigma, SatPi]

/-- `sigmaOfPi m π` defines `SatSigma (m + 2)` when `π` defines `SatPi (m + 1)`.
- [HP98, Theorem I.1.75(1)] -/
private lemma sigmaDefined_of_piDefined {m : ℕ} {π : 𝚷-[m + 1].Semisentence 2}
    (hπ : 𝚷-[m + 1]-Relation (SatPi (m + 1) : V → V → Prop) via π) :
    𝚺-[m + 2]-Relation (SatSigma (m + 2) : V → V → Prop) via sigmaOfPi m π := .mk fun v ↦ by
  have := hπ
  simp [sigmaOfPi, SatSigma]

/-- Definedness of `sigmaZero` for `SatSigma 1`.
- [HP98, Theorem I.1.75(1)] -/
private lemma sigmaZero_defined :
    𝚺-[1]-Relation (SatSigma 1 : V → V → Prop) via sigmaZero := .mk fun v ↦ by
  simp [sigmaZero, SatSigma, SatPi]

/-- Definedness of `satSigma n` for `SatSigma (n + 1)`.
- [HP98, Theorem I.1.75(1)] -/
private lemma sigmaDefined : ∀ n : ℕ, 𝚺-[n + 1]-Relation (SatSigma (n + 1) : V → V → Prop) via satSigma n
  | 0 => sigmaZero_defined
  | n + 1 => by
    rw [satSigma_succ]
    exact sigmaDefined_of_piDefined (piDefined_of_sigmaDefined (sigmaDefined n))

/-- The formula `satSigma n` defines satisfaction for strict prenex `𝚺-[n + 1]` formulas.
- [HP98, Theorem I.1.75(1)] -/
instance SatSigma.defined (n : ℕ) :
    𝚺-[n + 1]-Relation (SatSigma (n + 1) : V → V → Prop) via satSigma n := sigmaDefined n

/-- The formula `satPi n` defines satisfaction for strict prenex `𝚷-[n + 1]` formulas.
- [HP98, Theorem I.1.75(1)] -/
instance SatPi.defined (n : ℕ) :
    𝚷-[n + 1]-Relation (SatPi (n + 1) : V → V → Prop) via satPi n :=
  piDefined_of_sigmaDefined (sigmaDefined n)

/-- Satisfaction for strict prenex `𝚺-[n + 1]` formulas is definable at level `𝚺-[n + 1]`.
- [HP98, Theorem I.1.75(1)] -/
instance SatSigma.definable (n : ℕ) :
    𝚺-[n + 1]-Relation (SatSigma (n + 1) : V → V → Prop) :=
  (SatSigma.defined n).to_definable

/-- Satisfaction for strict prenex `𝚷-[n + 1]` formulas is definable at level `𝚷-[n + 1]`.
- [HP98, Theorem I.1.75(1)] -/
instance SatPi.definable (n : ℕ) :
    𝚷-[n + 1]-Relation (SatPi (n + 1) : V → V → Prop) :=
  (SatPi.defined n).to_definable

/-- At level zero, strict `Σ` satisfaction is `Δ₀` satisfaction.
- [HP98, Definition I.1.74] -/
@[simp] lemma SatSigma.zero : SatSigma 0 = (SatZero : V → V → Prop) := by simp [SatSigma]

/-- At level zero, strict `Π` satisfaction is `Δ₀` satisfaction.
- [HP98, Definition I.1.74] -/
@[simp] lemma SatPi.zero : SatPi 0 = (SatZero : V → V → Prop) := by simp [SatPi]

/-! ## Tarski conditions -/

section
variable {n : ℕ} {z e : V}

/-- Unfolding of strict `Σ` satisfaction at a positive level.
- [HP98, Definition I.1.74] -/
private lemma satSigma_succ_iff :
    SatSigma (n + 1) z e ↔ ∃ k q, z = qqExss q k ∧ IsStrictPi n q ∧
      ∃ w, len w = k ∧ SatPi n q (vecAppend w e) := by rw [SatSigma]

/-- Unfolding of strict `Π` satisfaction at a positive level.
- [HP98, Definition I.1.74] -/
private lemma satPi_succ_iff :
    SatPi (n + 1) z e ↔ IsStrictPi (n + 1) z ∧ IsUFormula ℒₒᵣ z ∧
      ¬SatSigma (n + 1) (neg ℒₒᵣ z) e := by rw [SatPi]

/-- Strict `𝚷-[n]` satisfaction implies membership in its syntactic domain.
- [HP98, Theorem I.1.75(2)] -/
theorem SatPi.dom (h : SatPi n z e) :
    IsStrictPi n z ∧ IsUFormula ℒₒᵣ z := by
  match n with
  | 0 => exact SatZero.dom (by simpa using h)
  | _ + 1 => exact ⟨(satPi_succ_iff.mp h).1, (satPi_succ_iff.mp h).2.1⟩

/-- Strict `𝚺-[n]` satisfaction implies membership in its syntactic domain.
- [HP98, Theorem I.1.75(2)] -/
theorem SatSigma.dom (h : SatSigma n z e) :
    IsStrictSigma n z ∧ IsUFormula ℒₒᵣ z := by
  match n with
  | 0 => exact SatZero.dom (by simpa using h)
  | _ + 1 =>
    obtain ⟨k, q, rfl, hq, w, -, hsat⟩ := satSigma_succ_iff.mp h
    exact ⟨⟨k, q, rfl, hq⟩, isUFormula_qqExss.mpr (SatPi.dom hsat).2⟩

/-- `𝚷-[n]` satisfaction of a negated strict `𝚺-[n]` formula is failure of `𝚺-[n]` satisfaction.
- [HP98, Theorem I.1.75(2)] -/
theorem SatPi.neg_iff (hz : IsStrictSigma n z)
    (hz' : IsUFormula ℒₒᵣ z) : SatPi n (neg ℒₒᵣ z) e ↔ ¬SatSigma n z e := by
  match n with
  | 0 => simpa using SatZero.neg_iff hz hz'
  | _ + 1 =>
    rw [satPi_succ_iff, IsUFormula.neg_neg hz']
    simp [IsStrictSigma.neg hz' hz, hz']

/-- `𝚺-[n]` satisfaction of a negated strict `𝚷-[n]` formula is failure of `𝚷-[n]` satisfaction.
- [HP98, Theorem I.1.75(2)] -/
theorem SatSigma.neg_iff (hz : IsStrictPi n z)
    (hz' : IsUFormula ℒₒᵣ z) : SatSigma n (neg ℒₒᵣ z) e ↔ ¬SatPi n z e := by
  match n with
  | 0 => simpa using SatZero.neg_iff hz hz'
  | _ + 1 =>
    rw [satPi_succ_iff (z := z)]
    simp [hz, hz']

end

/-! ### Maximal existential blocks

The prenex classes do not determine the decomposition `z = qqExss q k` a code admits, so the
definition of `SatSigma (n + 1)` has to be shown independent of it. The tool is the *maximal*
existential block of a code, the decomposition whose matrix does not itself begin with an
existential quantifier: every other decomposition is an initial segment of it. -/

/-- Cancelling an outer existential block common to two decompositions.
- [HP98, Lemma I.1.69] -/
private lemma qqExss_cancel (k : V) :
    ∀ p p' j : V, qqExss p k = qqExss p' (k + j) → p = qqExss p' j := by
  induction k using ISigma1.pi1_succ_induction
  · definability
  case zero => intro p p' j h; simpa using h
  case succ k ih =>
    intro p p' j h
    rw [qqExss_succ, add_right_comm k 1 j, qqExss_succ, qqExs_inj] at h
    exact ih p p' j h

/-- Every code is an existential block over a code that does not itself begin with an
existential quantifier.
- [HP98, Lemma I.1.69] -/
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

/-- The maximal existential block dominates every other decomposition.
- [HP98, Lemma I.1.69] -/
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

/-- A strict `𝚷-[n + 1]` code beginning with an existential quantifier has an empty universal block,
hence is already strict `𝚺-[n]`.
- [HP98, Lemma I.1.69] -/
private lemma isStrictSigma_of_isStrictPi_ex {n : ℕ} {p : V} (h : IsStrictPi (n + 1) (^∃ p)) :
    IsStrictSigma n (^∃ p) := by
  obtain ⟨k, q, heq, hq⟩ := h
  rcases zero_or_succ k with rfl | ⟨k, rfl⟩
  · rw [qqAlls_zero] at heq; exact heq ▸ hq
  · rw [qqAlls_succ] at heq; simp [qqExs, qqAll, pair_ext_iff] at heq

/-- The maximal existential block of a `Δ₀` code has length at most one, and its matrix is
`Δ₀`: a `Δ₀` code begins with at most one existential quantifier, the one of a bounded
existential quantification.
- [HP98, Lemma I.1.68(2)] -/
private lemma isDelta0_ex_block {z M K : V} (hz : IsDelta0 z) (hMK : z = qqExss M K)
    (hM : ∀ p : V, M ≠ ^∃ p) : IsDelta0 M ∧ K ≤ 1 := by
  rcases zero_or_succ K with rfl | ⟨K, rfl⟩
  · rw [qqExss_zero] at hMK; exact ⟨hMK ▸ hz, by simp⟩
  · rw [qqExss_succ] at hMK
    subst hMK
    obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, heq⟩ := IsDelta0.of_ex hz
    rcases zero_or_succ K with rfl | ⟨K, rfl⟩
    · rw [qqExss_zero] at heq
      subst heq
      refine ⟨IsDelta0.and_iff.mpr ⟨?_, hq⟩, by simp⟩
      rw [Arithmetic.qqLT]; exact IsDelta0.rel
    · rw [qqExss_succ] at heq
      simp [qqExs, qqAnd, pair_ext_iff] at heq

/-- The matrix of the maximal existential block of a strict `𝚺-[n + 1]` code is strict `𝚷-[n]`.
- [HP98, Lemma I.1.69] -/
private lemma isStrictPi_ex_block : ∀ (n : ℕ) (z M K : V), IsStrictSigma (n + 1) z →
    z = qqExss M K → (∀ p : V, M ≠ ^∃ p) → IsStrictPi n M
  | 0, _, M, _, hz, hMK, hM => by
    obtain ⟨k, q, hqk, hq⟩ := hz
    obtain ⟨j, -, rfl⟩ := ex_block_dominates hMK hM hqk
    exact (isDelta0_ex_block hq rfl hM).1
  | n + 1, _, M, _, hz, hMK, hM => by
    obtain ⟨k, q, hqk, hq⟩ := hz
    obtain ⟨j, -, rfl⟩ := ex_block_dominates hMK hM hqk
    rcases zero_or_succ j with rfl | ⟨j, rfl⟩
    · simpa using hq
    · have hs : IsStrictSigma n (qqExss M (j + 1)) := by
        rw [qqExss_succ] at hq ⊢
        exact isStrictSigma_of_isStrictPi_ex hq
      match n with
      | 0 => exact IsStrictPi.of_delta0 (isDelta0_ex_block hs rfl hM).1
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

/-! ### The `Δ₀` existential condition -/

/-- Satisfaction of a `Δ₀` code that begins with an existential quantifier is existential
satisfaction of its body: the guard of the bounded quantifier is part of that body.
- [HP98, Theorem I.1.70(iv)] -/
private lemma satZero_ex_iff {p e : V} (h : IsDelta0 (^∃ p)) :
    SatZero (^∃ p) e ↔ ∃ x, SatZero p (x ∷ e) := by
  obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ := IsDelta0.of_ex h
  have hlt : ∀ x : V, SatZero (Arithmetic.qqLT (qqBvar 0) (termBShift ℒₒᵣ t)) (x ∷ e) ↔
      x < termVal e t := fun x ↦ by
    rw [SatZero.lt_iff (by simp) ht.termBShift]
    simp [termVal_termBShift ht x e]
  rw [show (^∃ ((Arithmetic.qqLT (qqBvar 0) (termBShift ℒₒᵣ t)) ^⋏ q) : V)
      = qqBex (termBShift ℒₒᵣ t) q from rfl, SatZero.bex_iff ht]
  constructor
  · rintro ⟨x, hx, hsat⟩
    exact ⟨x, SatZero.and_iff.mpr ⟨(hlt x).mpr hx, hsat⟩⟩
  · rintro ⟨x, hsat⟩
    obtain ⟨h₁, h₂⟩ := SatZero.and_iff.mp hsat
    exact ⟨x, (hlt x).mp h₁, h₂⟩

/-! ### The block characterization

Satisfaction is defined through *some* decomposition of the code into an existential block over
a strict `𝚷-[n]` matrix. `BlockSat` says that the *maximal* block computes it, which makes the
definition independent of the decomposition; the Tarski conditions all follow from it, and it is
itself proved by recursion on the level, since a matrix that still begins with an existential
quantifier belongs to a lower level. -/

/-- Strict `𝚺-[n + 1]` satisfaction of `z` is witnessed over the maximal existential block of `z`.
- [HP98, Theorem I.1.75(2)] -/
private def BlockSat (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (n : ℕ) : Prop :=
  ∀ z M K e : V, IsStrictSigma (n + 1) z → IsUFormula ℒₒᵣ z → z = qqExss M K →
    (∀ p : V, M ≠ ^∃ p) → (SatSigma (n + 1) z e ↔ ∃ w, len w = K ∧ SatPi n M (vecAppend w e))

/-- An empty existential block at level zero: a `Δ₀` code is `𝚺-[1]`-satisfied exactly when it is
`Δ₀`-satisfied.
- [HP98, Theorem I.1.75(2)(v)] -/
private lemma of_pi_zero (hB : BlockSat V 0) {z e : V} (hz : IsDelta0 z)
    (hz' : IsUFormula ℒₒᵣ z) : SatSigma 1 z e ↔ SatPi 0 z e := by
  constructor
  · intro h
    obtain ⟨K, M, hMK, hM⟩ := exists_ex_block z
    obtain ⟨w, hw, hsat⟩ := (hB z M K e (IsStrictSigma.of_pi hz) hz' hMK hM).mp h
    obtain ⟨hMd, hK1⟩ := isDelta0_ex_block hz hMK hM
    rcases zero_or_succ K with rfl | ⟨K, rfl⟩
    · rw [qqExss_zero] at hMK
      rw [len_zero_iff_eq_nil.mp hw] at hsat
      simpa [hMK] using hsat
    · have hK : K = 0 := by simpa using hK1
      subst hK
      rw [qqExss_succ, qqExss_zero] at hMK
      obtain ⟨x, rfl⟩ := eq_singleton_iff_len_eq_one.mp (by simpa using hw)
      have h0 : SatZero M (x ∷ e) := by simpa using hsat
      simpa [hMK] using (satZero_ex_iff (hMK ▸ hz)).mpr ⟨x, h0⟩
  · intro h
    exact satSigma_succ_iff.mpr ⟨0, z, by simp, hz, 0, by simp, by simpa using h⟩

/-- Level monotonicity by one step, `Σ` and `Π` at once, from the block characterization at
levels up to `n`.
- [HP98, Theorem I.1.75(2)] -/
private lemma mono_step : ∀ (n : ℕ), (∀ m ≤ n, BlockSat V m) →
    (∀ z e : V, IsStrictSigma n z → IsUFormula ℒₒᵣ z →
      (SatSigma n z e ↔ SatSigma (n + 1) z e)) ∧
    (∀ z e : V, IsStrictPi n z → IsUFormula ℒₒᵣ z → (SatPi n z e ↔ SatPi (n + 1) z e)) := by
  intro n
  induction n with
  | zero =>
    intro hB
    have hsig : ∀ z e : V, IsStrictSigma 0 z → IsUFormula ℒₒᵣ z →
        (SatSigma 0 z e ↔ SatSigma 1 z e) := fun z e hz hz' ↦ by
      simpa using (of_pi_zero (hB 0 le_rfl) hz hz').symm
    exact ⟨hsig, fun z e hz hz' ↦ by
      rw [show (SatPi 0 z e ↔ ¬SatSigma 0 (neg ℒₒᵣ z) e) by
          rw [SatSigma.neg_iff hz hz']; simp,
        show (SatPi 1 z e ↔ ¬SatSigma 1 (neg ℒₒᵣ z) e) by
          rw [SatSigma.neg_iff (IsStrictPi.mono (Nat.le_succ 0) hz) hz']; simp,
        hsig (neg ℒₒᵣ z) e (IsStrictPi.neg hz' hz) hz'.neg]⟩
  | succ n ih =>
    intro hB
    have hpin := (ih fun i hi ↦ hB i (by omega)).2
    have hsig : ∀ z e : V, IsStrictSigma (n + 1) z → IsUFormula ℒₒᵣ z →
        (SatSigma (n + 1) z e ↔ SatSigma (n + 2) z e) := fun z e hz hz' ↦ by
      obtain ⟨K, M, hMK, hM⟩ := exists_ex_block z
      have hMu : IsUFormula ℒₒᵣ M := isUFormula_qqExss.mp (hMK ▸ hz')
      have hMpi : IsStrictPi n M := isStrictPi_ex_block n z M K hz hMK hM
      rw [hB n (by omega) z M K e hz hz' hMK hM,
        hB (n + 1) le_rfl z M K e (IsStrictSigma.mono (by omega) hz) hz' hMK hM]
      exact exists_congr fun w ↦ and_congr_right fun _ ↦ hpin M _ hMpi hMu
    exact ⟨hsig, fun z e hz hz' ↦ by
      rw [show (SatPi (n + 1) z e ↔ ¬SatSigma (n + 1) (neg ℒₒᵣ z) e) by
          rw [SatSigma.neg_iff hz hz']; simp,
        show (SatPi (n + 2) z e ↔ ¬SatSigma (n + 2) (neg ℒₒᵣ z) e) by
          rw [SatSigma.neg_iff (IsStrictPi.mono (Nat.le_succ _) hz) hz']; simp,
        hsig (neg ℒₒᵣ z) e (IsStrictPi.neg hz' hz) hz'.neg]⟩

/-- The empty-block conditions, `Σ` and `Π` at once, from the block characterization at levels
up to `n`.
- [HP98, Theorem I.1.75(2)(v)]
- [HP98, Theorem I.1.75(2)(v′)] -/
private lemma of_pi_step : ∀ (n : ℕ), (∀ m ≤ n, BlockSat V m) →
    (∀ z e : V, IsStrictPi n z → IsUFormula ℒₒᵣ z → (SatSigma (n + 1) z e ↔ SatPi n z e)) ∧
    (∀ z e : V, IsStrictSigma n z → IsUFormula ℒₒᵣ z →
      (SatPi (n + 1) z e ↔ SatSigma n z e)) := by
  intro n
  induction n with
  | zero =>
    intro hB
    exact ⟨fun z e hz hz' ↦ of_pi_zero (hB 0 le_rfl) hz hz',
      fun z e hz hz' ↦ by
        rw [show (SatPi 1 z e ↔ ¬SatSigma 1 (neg ℒₒᵣ z) e) by
            rw [SatSigma.neg_iff (IsStrictPi.of_sigma hz) hz']; simp,
          of_pi_zero (hB 0 le_rfl) (IsStrictSigma.neg hz' hz) hz'.neg,
          SatPi.neg_iff hz hz']
        simp⟩
  | succ n ih =>
    intro hB
    have hsig : ∀ z e : V, IsStrictPi (n + 1) z → IsUFormula ℒₒᵣ z →
        (SatSigma (n + 2) z e ↔ SatPi (n + 1) z e) := by
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
            obtain ⟨hMd, hK1⟩ := isDelta0_ex_block hzs hMK hM
            have hK : K = 0 := by simpa using hK1
            subst hK
            rw [qqExss_zero] at hzex
            obtain ⟨x, rfl⟩ := eq_singleton_iff_len_eq_one.mp (by simpa using hw)
            have h0 : SatZero M (x ∷ e) := by
              simpa using ((ih fun i hi ↦ hB i (by omega)).2 M (x ∷ e) hMd hMu).mp
                (by simpa using hsat)
            simpa [hzex] using (satZero_ex_iff (hzex ▸ hzs)).mpr ⟨x, h0⟩
          | n + 1 =>
            have hMpi : IsStrictPi n M := isStrictPi_ex_block n z M (K + 1) hzs hMK hM
            have h1 := (mono_step n fun i hi ↦ hB i (by omega)).2
            have h2 := (mono_step (n + 1) fun i hi ↦ hB i (by omega)).2
            refine (hB n (by omega) z M (K + 1) e hzs hz' hMK hM).mpr ⟨w, hw, ?_⟩
            rw [h1 M _ hMpi hMu, h2 M _ (IsStrictPi.mono (by omega) hMpi) hMu]
            exact hsat
      · intro h
        exact satSigma_succ_iff.mpr ⟨0, z, by simp, hz, 0, by simp, by simpa using h⟩
    exact ⟨hsig, fun z e hz hz' ↦ by
      rw [show (SatPi (n + 2) z e ↔ ¬SatSigma (n + 2) (neg ℒₒᵣ z) e) by
          rw [SatSigma.neg_iff (IsStrictPi.of_sigma hz) hz']; simp,
        hsig (neg ℒₒᵣ z) e (IsStrictSigma.neg hz' hz) hz'.neg, SatPi.neg_iff hz hz']
      simp⟩

/-- The block characterization, by recursion on the level.
- [HP98, Theorem I.1.75(2)] -/
private lemma blockSat : ∀ n : ℕ, BlockSat V n := fun n ↦ by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z M K e hz hz' hMK hM
    have hMu : IsUFormula ℒₒᵣ M := isUFormula_qqExss.mp (hMK ▸ hz')
    have hMpi : IsStrictPi n M := isStrictPi_ex_block n z M K hz hMK hM
    refine ⟨fun h ↦ ?_, fun ⟨w, hw, hsat⟩ ↦ satSigma_succ_iff.mpr ⟨K, M, hMK, hMpi, w, hw, hsat⟩⟩
    obtain ⟨k, q, hqk, hq, w, hw, hsat⟩ := satSigma_succ_iff.mp h
    obtain ⟨j, rfl, rfl⟩ := ex_block_dominates hMK hM hqk
    rcases zero_or_succ j with rfl | ⟨j, rfl⟩
    · exact ⟨w, by simpa using hw, by simpa using hsat⟩
    · have hqex : (^∃ (qqExss M j) : V) = qqExss M (j + 1) := (qqExss_succ M j).symm
      rw [qqExss_succ] at hq hsat
      match n with
      | 0 =>
        obtain ⟨-, hj⟩ := isDelta0_ex_block hq hqex hM
        have hj0 : j = 0 := by simpa using hj
        subst hj0
        rw [qqExss_zero] at hq hsat
        obtain ⟨x, hx⟩ := (satZero_ex_iff hq).mp (by simpa using hsat)
        exact ⟨x ∷ w, by simp [hw], by simpa using hx⟩
      | m + 1 =>
        have hqU : IsUFormula ℒₒᵣ (^∃ (qqExss M j) : V) := by
          rw [hqex]; exact isUFormula_qqExss.mpr hMu
        have hqs : IsStrictSigma m (^∃ (qqExss M j) : V) := isStrictSigma_of_isStrictPi_ex hq
        have hsat' : SatSigma m (^∃ (qqExss M j) : V) (vecAppend w e) :=
          ((of_pi_step m fun i hi ↦ ih i (by omega)).2 _ _ hqs hqU).mp hsat
        match m with
        | 0 =>
          obtain ⟨hMd, hj'⟩ := isDelta0_ex_block hqs hqex hM
          have hj0 : j = 0 := by simpa using hj'
          subst hj0
          rw [qqExss_zero] at hqs hsat'
          obtain ⟨x, hx⟩ := (satZero_ex_iff hqs).mp (by simpa using hsat')
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

/-- An empty existential block reads a strict `𝚷-[n]` formula as a `𝚺-[n + 1]` formula.
- [HP98, Theorem I.1.75(2)(v)] -/
theorem SatSigma.of_pi (hz : IsStrictPi n z) (hz' : IsUFormula ℒₒᵣ z) :
    SatSigma (n + 1) z e ↔ SatPi n z e :=
  (of_pi_step n fun m _ ↦ blockSat m).1 z e hz hz'

/-- An empty universal block reads a strict `𝚺-[n]` formula as a `𝚷-[n + 1]` formula.
- [HP98, Theorem I.1.75(2)(v′)] -/
theorem SatPi.of_sigma (hz : IsStrictSigma n z) (hz' : IsUFormula ℒₒᵣ z) :
    SatPi (n + 1) z e ↔ SatSigma n z e :=
  (of_pi_step n fun m _ ↦ blockSat m).2 z e hz hz'

end

/-- Satisfaction of an existential formula is existential satisfaction of its body, for a body
that lies in the domain: peeling the quantifier shortens the maximal block by one.
- [HP98, Theorem I.1.75(2)(v)] -/
private lemma exs_iff_aux {n : ℕ} {p e : V} (hp : IsStrictSigma (n + 1) p)
    (hp' : IsUFormula ℒₒᵣ p) : SatSigma (n + 1) (^∃ p) e ↔ ∃ x, SatSigma (n + 1) p (x ∷ e) := by
  obtain ⟨K, M, hMK, hM⟩ := exists_ex_block p
  have h1 : SatSigma (n + 1) (^∃ p) e ↔ ∃ w, len w = K + 1 ∧ SatPi n M (vecAppend w e) :=
    blockSat n (^∃ p) M (K + 1) e (IsStrictSigma.exs hp) (by simp [hp'])
      (by rw [qqExss_succ, ← hMK]) hM
  have h2 : ∀ x : V, SatSigma (n + 1) p (x ∷ e) ↔
      ∃ u, len u = K ∧ SatPi n M (vecAppend u (x ∷ e)) :=
    fun x ↦ blockSat n p M K (x ∷ e) hp hp' hMK hM
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

/-- Satisfaction of an existential formula is existential satisfaction of its body.
- [HP98, Theorem I.1.75(2)(v)] -/
theorem SatSigma.exs_iff : SatSigma (n + 1) (^∃ p) e ↔ ∃ x, SatSigma (n + 1) p (x ∷ e) := by
  by_cases hp : IsStrictSigma (n + 1) p ∧ IsUFormula ℒₒᵣ p
  · exact exs_iff_aux hp.1 hp.2
  · refine ⟨fun h ↦ ?_, fun ⟨_, hx⟩ ↦ absurd hx.dom hp⟩
    obtain ⟨hs, hu⟩ := h.dom
    exact absurd ⟨IsStrictSigma.of_exs hs, by simpa using hu⟩ hp

/-- Satisfaction of a universal formula is universal satisfaction of its body.
- [HP98, Theorem I.1.75(2)(v′)] -/
theorem SatPi.all_iff : SatPi (n + 1) (^∀ p) e ↔ ∀ x, SatPi (n + 1) p (x ∷ e) := by
  constructor
  · intro h
    obtain ⟨hs, hu, hns⟩ := satPi_succ_iff.mp h
    have hup : IsUFormula ℒₒᵣ p := by simpa using hu
    rw [neg_all hup, SatSigma.exs_iff] at hns
    exact fun x ↦ satPi_succ_iff.mpr ⟨IsStrictPi.of_all hs, hup, fun hc ↦ hns ⟨x, hc⟩⟩
  · intro h
    obtain ⟨hsp, hup, -⟩ := satPi_succ_iff.mp (h 0)
    refine satPi_succ_iff.mpr ⟨IsStrictPi.all hsp, by simp [hup], ?_⟩
    rw [neg_all hup, SatSigma.exs_iff]
    rintro ⟨x, hx⟩
    exact (satPi_succ_iff.mp (h x)).2.2 hx

end

section
variable {m n : ℕ} (h : m ≤ n) {z e : V}
include h

/-- Satisfaction of a strict `𝚺-[m]` formula is stable when viewed at a higher `Σ` level.
- [HP98, Theorem I.1.75(2)(v)] -/
theorem SatSigma.mono (hz : IsStrictSigma m z) (hz' : IsUFormula ℒₒᵣ z) :
    SatSigma m z e ↔ SatSigma n z e := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    exact ih.trans ((mono_step n fun i _ ↦ blockSat i).1 z e (IsStrictSigma.mono hn hz) hz')

/-- Satisfaction of a strict `𝚷-[m]` formula is stable when viewed at a higher `Π` level.
- [HP98, Theorem I.1.75(2)(v′)] -/
theorem SatPi.mono (hz : IsStrictPi m z) (hz' : IsUFormula ℒₒᵣ z) :
    SatPi m z e ↔ SatPi n z e := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    exact ih.trans ((mono_step n fun i _ ↦ blockSat i).2 z e (IsStrictPi.mono hn hz) hz')

end

/-! ### Substitution under a quantifier block -/

namespace QVecIter

/-- Primitive-recursive blueprint for iterating the quantifier lift of a substitution vector.
- [HP98, 1.64(5)] -/
noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. !(qVecGraph ℒₒᵣ) y ih”

/-- Primitive-recursive construction iterating the quantifier lift of a substitution vector.
- [HP98, 1.64(5)] -/
noncomputable def construction : PR.Construction V blueprint where
  zero := fun x ↦ x 0
  succ := fun _ _ ih ↦ qVec ℒₒᵣ ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, (qVec.defined (L := ℒₒᵣ) (V := V)).df]

end QVecIter

/-- `qVecIter w k` is the substitution vector `w` lifted past `k` quantifiers.
- [HP98, 1.64(5)] -/
noncomputable def qVecIter (w k : V) : V := QVecIter.construction.result ![w] k

/-- Lifting past no quantifier leaves the vector unchanged.
- [HP98, 1.64(5)] -/
@[simp] lemma qVecIter_zero (w : V) : qVecIter w 0 = w := by
  simp [qVecIter, QVecIter.construction]

/-- One more quantifier applies one more lift.
- [HP98, 1.64(5)] -/
@[simp] lemma qVecIter_succ (w k : V) : qVecIter w (k + 1) = qVec ℒₒᵣ (qVecIter w k) := by
  simp [qVecIter, QVecIter.construction]

/-- Defining formula for the iterated quantifier lift.
- [HP98, 1.64(5)] -/
noncomputable def _root_.LO.FirstOrder.Arithmetic.qVecIterDef : 𝚺₁.Semisentence 3 :=
  QVecIter.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

/-- The iterated quantifier lift is `𝚺₁`-definable.
- [HP98, 1.64(5)] -/
instance qVecIter_defined : 𝚺₁-Function₂ (qVecIter : V → V → V) via qVecIterDef := .mk
  fun v ↦ by simp [QVecIter.construction.result_defined_iff, qVecIterDef]; rfl

/-- The `𝚺₁` definability instance for the iterated quantifier lift.
- [HP98, 1.64(5)] -/
instance qVecIter_definable : 𝚺₁-Function₂ (qVecIter : V → V → V) := qVecIter_defined.to_definable

/-- The iterated quantifier lift is definable at every positive hierarchy level.
- [HP98, 1.64(5)] -/
instance qVecIter_definable' (Γ m) : Γ-[m + 1]-Function₂ (qVecIter : V → V → V) :=
  qVecIter_definable.of_sigmaOne

/-- The iterated lift of a semiterm vector is a semiterm vector for the extended arities.
- [HP98, 1.64(5)] -/
private lemma isSemitermVec_qVecIter {m l w : V} (hw : IsSemitermVec ℒₒᵣ m l w) (k : V) :
    IsSemitermVec ℒₒᵣ (m + k) (l + k) (qVecIter w k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using hw
  case succ k ih =>
    rw [qVecIter_succ, ← add_assoc, ← add_assoc]
    exact ih.qVec

/-- Lifting past a quantifier commutes with iterating the lift.
- [HP98, 1.64(5)] -/
private lemma qVecIter_qVec (w k : V) :
    qVecIter (qVec ℒₒᵣ w) k = qVec ℒₒᵣ (qVecIter w k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qVecIter_succ, ih, qVecIter_succ]

/-- Substituting into an existential block substitutes the iterated lift into its matrix.
- [HP98, 1.64(5)] -/
private lemma substs_qqExss {p : V} (hp : IsUFormula ℒₒᵣ p) (k : V) :
    ∀ w : V, subst ℒₒᵣ w (qqExss p k) = qqExss (subst ℒₒᵣ (qVecIter w k) p) k := by
  induction k using ISigma1.pi1_succ_induction
  · definability
  case zero => intro w; simp
  case succ k ih =>
    intro w
    rw [qqExss_succ, substs_ex (isUFormula_qqExss.mpr hp), ih (qVec ℒₒᵣ w), qVecIter_qVec,
      qVecIter_succ, qqExss_succ]

/-- Substituting into a universal block substitutes the iterated lift into its matrix.
- [HP98, 1.64(5)] -/
private lemma substs_qqAlls {p : V} (hp : IsUFormula ℒₒᵣ p) (k : V) :
    ∀ w : V, subst ℒₒᵣ w (qqAlls p k) = qqAlls (subst ℒₒᵣ (qVecIter w k) p) k := by
  induction k using ISigma1.pi1_succ_induction
  · definability
  case zero => intro w; simp
  case succ k ih =>
    intro w
    rw [qqAlls_succ, substs_all (isUFormula_qqAlls.mpr hp), ih (qVec ℒₒᵣ w), qVecIter_qVec,
      qVecIter_succ, qqAlls_succ]

/-- Being a semiformula under an existential block is being one for the extended arity.
- [HP98, 1.64(5)] -/
private lemma isSemiformula_qqExss {p : V} (k : V) :
    ∀ n : V, (IsSemiformula ℒₒᵣ n (qqExss p k) ↔ IsSemiformula ℒₒᵣ (n + k) p) := by
  induction k using ISigma1.pi1_succ_induction
  · definability
  case zero => intro n; simp
  case succ k ih => intro n; rw [qqExss_succ, IsSemiformula.exs, ih, add_assoc, add_comm 1 k]

/-- Being a semiformula under a universal block is being one for the extended arity.
- [HP98, 1.64(5)] -/
private lemma isSemiformula_qqAlls {p : V} (k : V) :
    ∀ n : V, (IsSemiformula ℒₒᵣ n (qqAlls p k) ↔ IsSemiformula ℒₒᵣ (n + k) p) := by
  induction k using ISigma1.pi1_succ_induction
  · definability
  case zero => intro n; simp
  case succ k ih => intro n; rw [qqAlls_succ, IsSemiformula.all, ih, add_assoc, add_comm 1 k]

/-- Evaluating the vector lifted past a block extends the evaluated substitution by the
witnesses of the block.
- [HP98, 1.64(5)] -/
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

/-- The strict prenex classes are closed under substitution.
- [HP98, Lemma I.1.69] -/
private lemma isStrict_subst : ∀ (n : ℕ) (m l w p : V), IsSemitermVec ℒₒᵣ m l w →
    IsSemiformula ℒₒᵣ m p →
    (IsStrictSigma n p → IsStrictSigma n (subst ℒₒᵣ w p)) ∧
    (IsStrictPi n p → IsStrictPi n (subst ℒₒᵣ w p))
  | 0, _, _, _, _, hw, hp => ⟨fun h ↦ IsDelta0.subst hw hp h, fun h ↦ IsDelta0.subst hw hp h⟩
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

/-- Substitution does not create a leading existential quantifier.
- [HP98, 1.64(4)] -/
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

/-- Strict `𝚺-[n]` satisfaction commutes with substitution of a coded vector of terms.
- [HP98, Theorem I.1.75(2)] -/
theorem SatSigma.subst {n : ℕ} {m l w p e : V} (hw : IsSemitermVec ℒₒᵣ m l w)
    (hp : IsSemiformula ℒₒᵣ m p) (hp' : IsStrictSigma n p) :
    SatSigma n (Bootstrapping.subst ℒₒᵣ w p) e ↔ SatSigma n p (termValVec e m w) := by
  induction n generalizing m l w p e with
  | zero => simpa using SatZero.subst hw hp hp'
  | succ n ih =>
    have hpi : ∀ {m l w q e' : V}, IsSemitermVec ℒₒᵣ m l w → IsSemiformula ℒₒᵣ m q →
        IsStrictPi n q →
        (SatPi n (Bootstrapping.subst ℒₒᵣ w q) e' ↔ SatPi n q (termValVec e' m w)) := by
      intro m l w q e' hw hq hq'
      have hsq : IsStrictPi n (Bootstrapping.subst ℒₒᵣ w q) :=
        (isStrict_subst n m l w q hw hq).2 hq'
      rw [show (SatPi n (Bootstrapping.subst ℒₒᵣ w q) e' ↔
            ¬SatSigma n (neg ℒₒᵣ (Bootstrapping.subst ℒₒᵣ w q)) e') by
          rw [SatSigma.neg_iff hsq (hq.subst hw).isUFormula]; simp,
        ← substs_neg hq hw,
        ih hw (by simp [hq]) (IsStrictPi.neg hq.isUFormula hq'),
        SatSigma.neg_iff hq' hq.isUFormula]
      simp
    obtain ⟨K, M, hMK, hM⟩ := exists_ex_block p
    have hMs : IsSemiformula ℒₒᵣ (m + K) M := (isSemiformula_qqExss K m).mp (hMK ▸ hp)
    have hMpi : IsStrictPi n M := isStrictPi_ex_block n p M K hp' hMK hM
    have hsubst : Bootstrapping.subst ℒₒᵣ w p
        = qqExss (Bootstrapping.subst ℒₒᵣ (qVecIter w K) M) K := by
      rw [hMK, substs_qqExss hMs.isUFormula K w]
    rw [blockSat n (Bootstrapping.subst ℒₒᵣ w p) _ K e
        ((isStrict_subst (n + 1) m l w p hw hp).1 hp') (hp.subst hw).isUFormula hsubst
        (not_ex_subst hMs.isUFormula hM _),
      blockSat n p M K (termValVec e m w) hp' hp.isUFormula hMK hM]
    refine exists_congr fun v ↦ and_congr_right fun hv ↦ ?_
    rw [hpi (isSemitermVec_qVecIter hw K) hMs hMpi, termValVec_qVecIter hw K v hv]

/-! ## Satisfaction under an externally supplied vector -/

/-- `satSigmaVec n k` defines `SatSigma (n + 1)` under its `k` free variables.

- [HP98, Remark I.1.77]
- [HP98, Definition I.1.78(2)] -/
noncomputable def satSigmaVec (n k : ℕ) : 𝚺-[n + 1].Semisentence (k + 1) := .mkSigma
  “p. ∃ e, !lenDef ↑k e ∧
    (⋀ i, ∃ z, !nthDef z e ↑(i : Fin k).val ∧ z = #i.succ.succ.succ) ∧
    !(satSigma n).val p e”
  (by simp [lenDef.sigma_prop.mono (Nat.le_add_left 1 n),
    nthDef.sigma_prop.mono (Nat.le_add_left 1 n)])

/-- The formula `satSigmaVec n k` defines strict `𝚺-[n + 1]` satisfaction under its variables.
- [HP98, Remark I.1.77]
- [HP98, Definition I.1.78(2)] -/
theorem satSigmaVec.defined (n k : ℕ) :
    𝚺-[n + 1].Defined
      (fun v : Fin (k + 1) → V ↦ SatSigma (n + 1) (v 0) (matrixToVec (v ·.succ)))
      (satSigmaVec n k) := .mk fun v ↦ by
  simp only [satSigmaVec, Nat.succ_eq_add_one, Nat.reduceAdd, HierarchySymbol.Semiformula.val_mkSigma,
    Semiformula.eval_ex, LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp₂,
    Semiterm.val_operator, Matrix.comp₀, Structure.numeral_eq_numeral, numeral_eq_natCast_app, Semiterm.val_bvar,
    Matrix.cons_val_zero, HierarchySymbol.Defined.iff, Fin.isValue, Fin.Fin1.eq_one, Fin.succ_zero_eq_one,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.conj_hom_prop, Matrix.comp₃, Fin.succ_one_eq_two,
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

end LO.FirstOrder.Arithmetic.Bootstrapping
