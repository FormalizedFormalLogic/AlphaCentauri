module

public import AlphaCentauri.Hierarchy.StrictHierarchy
public import AlphaCentauri.Bootstrapping.Delta0

/-!
# Internal prenex classes

This module codes blocks of existential quantifiers and vector concatenation inside arithmetic.
It also defines internal predicates for the strict prenex hierarchy.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Iterated existential quantification -/

section qqExss

/-- Primitive-recursive blueprint for iterated existential quantification.
- [HP98, Lemma I.1.69] -/
def qqExss.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. !qqExsDef y ih”

/-- Primitive-recursive construction of iterated existential quantification.
- [HP98, Lemma I.1.69] -/
noncomputable def qqExss.construction : PR.Construction V qqExss.blueprint where
  zero := fun x ↦ x 0
  succ := fun _ _ ih ↦ ^∃ ih
  zero_defined := .mk fun v ↦ by simp [qqExss.blueprint]
  succ_defined := .mk fun v ↦ by simp [qqExss.blueprint, qqExs]

/-- `qqExss p k` prefixes `p` with `k` existential quantifiers.
- [HP98, Lemma I.1.69] -/
noncomputable def qqExss (p k : V) : V := qqExss.construction.result ![p] k

/-- Iterating existential quantification zero times leaves the formula unchanged.
- [HP98, Lemma I.1.69] -/
@[simp] lemma qqExss_zero (p : V) : qqExss p 0 = p := by
  simp [qqExss, qqExss.construction]

/-- One more iteration prefixes a coded existential quantifier.
- [HP98, Lemma I.1.69] -/
@[simp] lemma qqExss_succ (p k : V) : qqExss p (k + 1) = ^∃ (qqExss p k) := by
  simp [qqExss, qqExss.construction]

/-- Defining formula for iterated existential quantification.
- [HP98, Lemma I.1.69] -/
def _root_.FFL.FirstOrder.Arithmetic.qqExssDef : 𝚺₁.Semisentence 3 :=
  qqExss.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

/-- Iterated existential quantification is `𝚺₁`-definable.
- [HP98, Lemma I.1.69] -/
instance qqExss_defined : 𝚺₁-Function₂ (qqExss : V → V → V) via qqExssDef := .mk
  fun v ↦ by simp [qqExss.construction.result_defined_iff, qqExssDef]; rfl

/-- The `𝚺₁` definability instance for iterated existential quantification.
- [HP98, Lemma I.1.69] -/
instance qqExss_definable : 𝚺₁-Function₂ (qqExss : V → V → V) :=
  qqExss_defined.to_definable

/-- Iterated existential quantification is definable at every positive hierarchy level.
- [HP98, Lemma I.1.69] -/
instance qqExss_definable' (Γ) : Γ-[m + 1]-Function₂ (qqExss : V → V → V) :=
  qqExss_definable.of_sigmaOne

/-- One existential quantifier does not exceed the formula it quantifies.
- [HP98, Lemma I.1.69] -/
lemma le_qqExs (p : V) : p ≤ ^∃ p := le_of_lt (lt_exists p)

/-- A successor step still fits below one existential quantifier.
- [HP98, Lemma I.1.69] -/
lemma succ_le_qqExs (p : V) : p + 1 ≤ ^∃ p := by
  simp only [qqExs]; exact add_le_add (le_pair_right _ _) (le_refl 1)

/-- A formula code does not exceed the result of prefixing existential quantifiers.
- [HP98, Lemma I.1.69] -/
@[simp] lemma le_qqExss (p k : V) : p ≤ qqExss p k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    refine le_trans ih ?_
    rw [qqExss_succ]
    exact le_qqExs _

/-- The block length does not exceed the code of the prefixed formula.
- [HP98, Lemma I.1.69] -/
@[simp] lemma index_le_qqExss (p k : V) : k ≤ qqExss p k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    rw [qqExss_succ]
    exact le_trans (add_le_add ih (le_refl 1)) (succ_le_qqExs _)

variable {L : Language} [L.Encodable] [L.LORDefinable] in
/-- Prefixing existential quantifiers preserves being a coded untyped formula.
- [HP98, Lemma I.1.69] -/
@[simp] lemma isUFormula_qqExss {p k : V} : IsUFormula L (qqExss p k) ↔ IsUFormula L p := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqExss_succ, IsUFormula.ex, ih]

/-- Negation turns a coded existential block into a universal block.
- [HP98, Lemma I.1.69] -/
lemma neg_qqExss {p k : V} (hp : IsUFormula ℒₒᵣ p) :
    neg ℒₒᵣ (qqExss p k) = qqAlls (neg ℒₒᵣ p) k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    rw [qqExss_succ, neg_ex (isUFormula_qqExss.mpr hp), ih, qqAlls_succ]

/-- Negation turns a coded universal block into an existential block.
- [HP98, Lemma I.1.69] -/
lemma neg_qqAlls {p k : V} (hp : IsUFormula ℒₒᵣ p) :
    neg ℒₒᵣ (qqAlls p k) = qqExss (neg ℒₒᵣ p) k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    rw [qqAlls_succ, neg_all (isUFormula_qqAlls.mpr hp), ih, qqExss_succ]

end qqExss

/-! ## Vector append -/

section vecAppend

namespace VecAppend

def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y w. y = w”
  adjoin := .mkSigma “y x xs ih w. !adjoinDef y x ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil param := param 0
  adjoin (_ x _ ih) := x ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end VecAppend

/-- `vecAppend v w` is the coded vector obtained by placing `v` before `w`. -/
noncomputable def vecAppend (v w : V) : V := VecAppend.construction.result ![w] v

@[simp] lemma vecAppend_nil (w : V) : vecAppend 0 w = w := by
  simp [vecAppend, VecAppend.construction]

@[simp] lemma vecAppend_adjoin (x v w : V) : vecAppend (x ∷ v) w = x ∷ vecAppend v w := by
  simp [vecAppend, VecAppend.construction]

def _root_.FFL.FirstOrder.Arithmetic.vecAppendDef : 𝚺₁.Semisentence 3 :=
  VecAppend.blueprint.resultDef

instance vecAppend_defined : 𝚺₁-Function₂ (vecAppend : V → V → V) via vecAppendDef :=
  VecAppend.construction.result_defined

instance vecAppend_definable : 𝚺₁-Function₂ (vecAppend : V → V → V) :=
  vecAppend_defined.to_definable

instance vecAppend_definable' (Γ m) : Γ-[m + 1]-Function₂ (vecAppend : V → V → V) :=
  vecAppend_definable.of_sigmaOne

@[simp] lemma len_vecAppend (v w : V) : len (vecAppend v w) = len v + len w := by
  induction v using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin x v ih => simp [vecAppend_adjoin, ih, add_right_comm]

lemma nth_vecAppend_of_lt {v w i : V} (hi : i < len v) : (vecAppend v w).[i] = v.[i] := by
  induction v using adjoin_ISigma1.pi1_succ_induction generalizing i
  · definability
  case nil => simp at hi
  case adjoin x v ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simp only [vecAppend_adjoin, nth_adjoin_succ]
      exact ih (by simpa using hi)

lemma nth_vecAppend_of_le {v w i : V} (hi : len v ≤ i) :
    (vecAppend v w).[i] = w.[i - len v] := by
  induction v using adjoin_ISigma1.pi1_succ_induction generalizing i
  · definability
  case nil => simp
  case adjoin x v ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp at hi
    · simp only [vecAppend_adjoin, nth_adjoin_succ, len_adjoin]
      rw [ih (by simpa using hi), add_tsub_add_eq_tsub_right]

end vecAppend

/-! ## Internal prenex classes -/

mutual
  /-- `IsStrictSigma n p` says that `p` codes a strict prenex `𝚺-[n]` formula.
  - [HP98, Lemma I.1.69] -/
  def IsStrictSigma : ℕ → V → Prop
    | 0 => IsDelta0
    | n + 1 => fun p ↦ ∃ k q, p = qqExss q k ∧ IsStrictPi n q

  /-- `IsStrictPi n p` says that `p` codes a strict prenex `𝚷-[n]` formula.
  - [HP98, Lemma I.1.69] -/
  def IsStrictPi : ℕ → V → Prop
    | 0 => IsDelta0
    | n + 1 => fun p ↦ ∃ k q, p = qqAlls q k ∧ IsStrictSigma n q
end

mutual
  /-- A `𝚫₁` recognizer for internally coded strict prenex `𝚺-[n]` formulas.
  - [HP98, Lemma I.1.69(1)] -/
  noncomputable def isStrictSigma : ℕ → 𝚫₁.Semisentence 1
    | 0 => isDelta0
    | n + 1 => .mkDelta
        (.mkSigma “p. ∃ k < p + 1, ∃ q < p + 1, !qqExssDef p q k ∧ !(isStrictPi n).sigma q”)
        (.mkPi “p. ∃ k < p + 1, ∃ q < p + 1, (∀ y, !qqExssDef y q k → y = p) ∧ !(isStrictPi n).pi q”)

  /-- A `𝚫₁` recognizer for internally coded strict prenex `𝚷-[n]` formulas.
  - [HP98, Lemma I.1.69(1)] -/
  noncomputable def isStrictPi : ℕ → 𝚫₁.Semisentence 1
    | 0 => isDelta0
    | n + 1 => .mkDelta
        (.mkSigma “p. ∃ k < p + 1, ∃ q < p + 1, !qqAllsDef p q k ∧ !(isStrictSigma n).sigma q”)
        (.mkPi “p. ∃ k < p + 1, ∃ q < p + 1, (∀ y, !qqAllsDef y q k → y = p) ∧ !(isStrictSigma n).pi q”)
end

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- Both parts of a coded quantifier block are bounded by the code of the block itself.
- [HP98, Lemma I.1.69(1)] -/
private lemma exists_block_iff {f : V → V → V} (hmatrix : ∀ q k : V, q ≤ f q k)
    (hlength : ∀ q k : V, k ≤ f q k) (P : V → Prop) (p : V) :
    (∃ k ≤ p, ∃ q ≤ p, p = f q k ∧ P q) ↔ ∃ k q, p = f q k ∧ P q :=
  ⟨fun ⟨k, _, q, _, h⟩ ↦ ⟨k, q, h⟩,
    fun ⟨k, q, heq, hq⟩ ↦ ⟨k, heq ▸ hlength q k, q, heq ▸ hmatrix q k, heq, hq⟩⟩

mutual
  /-- The strict prenex `𝚺-[n]` recognizer defines `IsStrictSigma n`.
  - [HP98, Lemma I.1.69(1)] -/
  instance IsStrictSigma.defined :
      ∀ n : ℕ, 𝚫₁-Predicate (IsStrictSigma n : V → Prop) via isStrictSigma n
    | 0 => IsDelta0.defined
    | n + 1 =>
      have : 𝚫₁-Predicate (IsStrictPi n : V → Prop) via isStrictPi n := IsStrictPi.defined n
      .mk ⟨fun v ↦ by simp [isStrictSigma, HierarchySymbol.Semiformula.val_sigma, eq_comm],
        fun v ↦ by
          simpa [isStrictSigma, IsStrictSigma, lt_succ_iff_le] using
            exists_block_iff le_qqExss index_le_qqExss (IsStrictPi n) (v 0)⟩

  /-- The strict prenex `𝚷-[n]` recognizer defines `IsStrictPi n`.
  - [HP98, Lemma I.1.69(1)] -/
  instance IsStrictPi.defined :
      ∀ n : ℕ, 𝚫₁-Predicate (IsStrictPi n : V → Prop) via isStrictPi n
    | 0 => IsDelta0.defined
    | n + 1 =>
      have : 𝚫₁-Predicate (IsStrictSigma n : V → Prop) via isStrictSigma n :=
        IsStrictSigma.defined n
      .mk ⟨fun v ↦ by simp [isStrictPi, HierarchySymbol.Semiformula.val_sigma, eq_comm],
        fun v ↦ by
          simpa [isStrictPi, IsStrictPi, lt_succ_iff_le] using
            exists_block_iff le_qqAlls index_le_qqAlls (IsStrictSigma n) (v 0)⟩
end

/-- Internal strict prenex `𝚺-[n]` membership is `𝚫₁`-definable.
- [HP98, Lemma I.1.69(1)] -/
instance IsStrictSigma.definable (n : ℕ) : 𝚫₁-Predicate (IsStrictSigma n : V → Prop) :=
  (IsStrictSigma.defined n).to_definable

/-- Internal strict prenex `𝚷-[n]` membership is `𝚫₁`-definable.
- [HP98, Lemma I.1.69(1)] -/
instance IsStrictPi.definable (n : ℕ) : 𝚫₁-Predicate (IsStrictPi n : V → Prop) :=
  (IsStrictPi.defined n).to_definable

/-- A strict `𝚷-[n]` formula belongs to the next strict `Σ` level.
- [HP98, Lemma I.1.69] -/
lemma IsStrictSigma.of_pi {n : ℕ} {p : V} (h : IsStrictPi n p) : IsStrictSigma (n + 1) p :=
  ⟨0, p, (qqExss_zero p).symm, h⟩

/-- A strict `𝚺-[n]` formula belongs to the next strict `Π` level.
- [HP98, Lemma I.1.69] -/
lemma IsStrictPi.of_sigma {n : ℕ} {p : V} (h : IsStrictSigma n p) : IsStrictPi (n + 1) p :=
  ⟨0, p, (qqAlls_zero p).symm, h⟩

/-- A strict `𝚺-[n + 1]` class is closed under existential quantification.
- [HP98, Lemma I.1.69] -/
lemma IsStrictSigma.exs {n : ℕ} {p : V} (h : IsStrictSigma (n + 1) p) :
    IsStrictSigma (n + 1) (^∃ p) := by
  obtain ⟨k, q, rfl, hq⟩ := h
  exact ⟨k + 1, q, (qqExss_succ q k).symm, hq⟩

/-- A strict `𝚷-[n + 1]` class is closed under universal quantification.
- [HP98, Lemma I.1.69] -/
lemma IsStrictPi.all {n : ℕ} {p : V} (h : IsStrictPi (n + 1) p) :
    IsStrictPi (n + 1) (^∀ p) := by
  obtain ⟨k, q, rfl, hq⟩ := h
  exact ⟨k + 1, q, (qqAlls_succ q k).symm, hq⟩

mutual
  /-- An internally `Δ₀` formula is strict `𝚺-[n]` at every level.
  - [HP98, Lemma I.1.69] -/
  lemma IsStrictSigma.of_delta0 : ∀ {n : ℕ} {p : V}, IsDelta0 p → IsStrictSigma n p
    | 0,     _, h => h
    | _ + 1, _, h => IsStrictSigma.of_pi (IsStrictPi.of_delta0 h)

  /-- An internally `Δ₀` formula is strict `𝚷-[n]` at every level.
  - [HP98, Lemma I.1.69] -/
  lemma IsStrictPi.of_delta0 : ∀ {n : ℕ} {p : V}, IsDelta0 p → IsStrictPi n p
    | 0,     _, h => h
    | _ + 1, _, h => IsStrictPi.of_sigma (IsStrictSigma.of_delta0 h)
end

mutual
  /-- Internal strict `Σ` classes are monotone in the hierarchy level.
  - [HP98, Lemma I.1.69] -/
  lemma IsStrictSigma.mono : ∀ {m n : ℕ}, m ≤ n → ∀ {p : V}, IsStrictSigma m p → IsStrictSigma n p
    | 0,     _,     _,  _, h => IsStrictSigma.of_delta0 h
    | _ + 1, 0,     hn, _, _ => absurd hn (by omega)
    | _ + 1, _ + 1, hn, _, h => by
      obtain ⟨k, q, rfl, hq⟩ := h
      exact ⟨k, q, rfl, IsStrictPi.mono (by omega) hq⟩

  /-- Internal strict `Π` classes are monotone in the hierarchy level.
  - [HP98, Lemma I.1.69] -/
  lemma IsStrictPi.mono : ∀ {m n : ℕ}, m ≤ n → ∀ {p : V}, IsStrictPi m p → IsStrictPi n p
    | 0,     _,     _,  _, h => IsStrictPi.of_delta0 h
    | _ + 1, 0,     hn, _, _ => absurd hn (by omega)
    | _ + 1, _ + 1, hn, _, h => by
      obtain ⟨k, q, rfl, hq⟩ := h
      exact ⟨k, q, rfl, IsStrictSigma.mono (by omega) hq⟩
end

/-- The body of a `Δ₀` code of an existential quantification is strict `𝚺-[1]`.
- [HP98, Lemma I.1.69] -/
private lemma isStrictSigma_one_of_isDelta0_exs {p : V} (h : IsDelta0 (^∃ p)) :
    IsStrictSigma 1 p := by
  obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ := IsDelta0.of_ex h
  have h₁ : IsDelta0 (Arithmetic.qqLT (qqBvar 0) (termBShift ℒₒᵣ t)) := by
    rw [Arithmetic.qqLT]; exact IsDelta0.rel
  exact IsStrictSigma.of_pi (IsDelta0.and_iff.mpr ⟨h₁, hq⟩)

/-- The body of a `Δ₀` code of a universal quantification is strict `𝚷-[1]`.
- [HP98, Lemma I.1.69] -/
private lemma isStrictPi_one_of_isDelta0_alls {p : V} (h : IsDelta0 (^∀ p)) :
    IsStrictPi 1 p := by
  obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ := IsDelta0.of_all h
  have h₁ : IsDelta0 (Arithmetic.qqNLT (qqBvar 0) (termBShift ℒₒᵣ t)) := by
    rw [Arithmetic.qqNLT]; exact IsDelta0.nrel
  exact IsStrictPi.of_sigma (IsDelta0.or_iff.mpr ⟨h₁, hq⟩)

mutual
  /-- Removing a leading existential from a strict `𝚷-[n]` code lands in strict `𝚺-[n + 1]`.
  - [HP98, Lemma I.1.69] -/
  private lemma IsStrictPi.of_exs_aux :
      ∀ {n : ℕ} {p : V}, IsStrictPi n (^∃ p) → IsStrictSigma (n + 1) p
    | 0,     _, h => isStrictSigma_one_of_isDelta0_exs h
    | _ + 1, _, h => by
      obtain ⟨k, q, heq, hq⟩ := h
      rcases zero_or_succ k with (rfl | ⟨k, rfl⟩)
      · rw [qqAlls_zero] at heq; subst heq
        exact IsStrictSigma.mono (by omega) (IsStrictSigma.of_exs_aux hq)
      · rw [qqAlls_succ] at heq; simp [qqExs, qqAll, pair_ext_iff] at heq

  /-- Removing a leading existential from a strict `𝚺-[n]` code lands in strict `𝚺-[n + 1]`.
  - [HP98, Lemma I.1.69] -/
  private lemma IsStrictSigma.of_exs_aux :
      ∀ {n : ℕ} {p : V}, IsStrictSigma n (^∃ p) → IsStrictSigma (n + 1) p
    | 0,     _, h => isStrictSigma_one_of_isDelta0_exs h
    | _ + 1, _, h => by
      obtain ⟨k, q, heq, hq⟩ := h
      rcases zero_or_succ k with (rfl | ⟨k, rfl⟩)
      · rw [qqExss_zero] at heq; subst heq
        exact IsStrictSigma.mono (by omega) (IsStrictPi.of_exs_aux hq)
      · rw [qqExss_succ] at heq
        simp only [qqExs_inj] at heq
        exact ⟨k, q, heq, IsStrictPi.mono (by omega) hq⟩
end

mutual
  /-- Removing a leading universal from a strict `𝚺-[n]` code lands in strict `𝚷-[n + 1]`.
  - [HP98, Lemma I.1.69] -/
  private lemma IsStrictSigma.of_all_aux :
      ∀ {n : ℕ} {p : V}, IsStrictSigma n (^∀ p) → IsStrictPi (n + 1) p
    | 0,     _, h => isStrictPi_one_of_isDelta0_alls h
    | _ + 1, _, h => by
      obtain ⟨k, q, heq, hq⟩ := h
      rcases zero_or_succ k with (rfl | ⟨k, rfl⟩)
      · rw [qqExss_zero] at heq; subst heq
        exact IsStrictPi.mono (by omega) (IsStrictPi.of_all_aux hq)
      · rw [qqExss_succ] at heq; simp [qqExs, qqAll, pair_ext_iff] at heq

  /-- Removing a leading universal from a strict `𝚷-[n]` code lands in strict `𝚷-[n + 1]`.
  - [HP98, Lemma I.1.69] -/
  private lemma IsStrictPi.of_all_aux :
      ∀ {n : ℕ} {p : V}, IsStrictPi n (^∀ p) → IsStrictPi (n + 1) p
    | 0,     _, h => isStrictPi_one_of_isDelta0_alls h
    | _ + 1, _, h => by
      obtain ⟨k, q, heq, hq⟩ := h
      rcases zero_or_succ k with (rfl | ⟨k, rfl⟩)
      · rw [qqAlls_zero] at heq; subst heq
        exact IsStrictPi.mono (by omega) (IsStrictSigma.of_all_aux hq)
      · rw [qqAlls_succ] at heq
        simp only [qqAll_inj] at heq
        exact ⟨k, q, heq, IsStrictSigma.mono (by omega) hq⟩
end

/-- Removing a leading existential preserves a strict positive-level `Σ` class.
- [HP98, Lemma I.1.69] -/
lemma IsStrictSigma.of_exs {n : ℕ} {p : V} (h : IsStrictSigma (n + 1) (^∃ p)) :
    IsStrictSigma (n + 1) p := by
  obtain ⟨k, q, heq, hq⟩ := h
  rcases zero_or_succ k with (rfl | ⟨k, rfl⟩)
  · rw [qqExss_zero] at heq; subst heq
    exact IsStrictPi.of_exs_aux hq
  · rw [qqExss_succ] at heq
    simp only [qqExs_inj] at heq
    exact ⟨k, q, heq, hq⟩

/-- Removing a leading universal preserves a strict positive-level `Π` class.
- [HP98, Lemma I.1.69] -/
lemma IsStrictPi.of_all {n : ℕ} {p : V} (h : IsStrictPi (n + 1) (^∀ p)) :
    IsStrictPi (n + 1) p := by
  obtain ⟨k, q, heq, hq⟩ := h
  rcases zero_or_succ k with (rfl | ⟨k, rfl⟩)
  · rw [qqAlls_zero] at heq; subst heq
    exact IsStrictSigma.of_all_aux hq
  · rw [qqAlls_succ] at heq
    simp only [qqAll_inj] at heq
    exact ⟨k, q, heq, hq⟩

mutual
  /-- Negation sends internally coded strict `𝚺-[n]` formulas to strict `𝚷-[n]` formulas.
  - [HP98, Lemma I.1.69] -/
  lemma IsStrictSigma.neg :
      ∀ {n : ℕ} {p : V}, IsUFormula ℒₒᵣ p → IsStrictSigma n p → IsStrictPi n (neg ℒₒᵣ p)
    | 0,     _, hp, h => IsDelta0.neg hp h
    | _ + 1, _, hp, h => by
      obtain ⟨k, q, rfl, hq⟩ := h
      have hq' : IsUFormula ℒₒᵣ q := isUFormula_qqExss.mp hp
      exact ⟨k, neg ℒₒᵣ q, neg_qqExss hq', IsStrictPi.neg hq' hq⟩

  /-- Negation sends internally coded strict `𝚷-[n]` formulas to strict `𝚺-[n]` formulas.
  - [HP98, Lemma I.1.69] -/
  lemma IsStrictPi.neg :
      ∀ {n : ℕ} {p : V}, IsUFormula ℒₒᵣ p → IsStrictPi n p → IsStrictSigma n (neg ℒₒᵣ p)
    | 0,     _, hp, h => IsDelta0.neg hp h
    | _ + 1, _, hp, h => by
      obtain ⟨k, q, rfl, hq⟩ := h
      have hq' : IsUFormula ℒₒᵣ q := isUFormula_qqAlls.mp hp
      exact ⟨k, neg ℒₒᵣ q, neg_qqAlls hq', IsStrictSigma.neg hq' hq⟩
end

/-! ## Agreement with the external strict hierarchy on quoted formulas -/

/-- The internal strict class selected by a polarity.
- [HP98, Lemma I.1.69] -/
-- Indexed by polarity so a single induction on a `StrictHierarchy` derivation proves the `Σ`
-- and `Π` cases at once.
private def IsStrictClass : Polarity → ℕ → V → Prop
  | .sigma, s, p => IsStrictSigma s p
  | .pi, s, p => IsStrictPi s p

/-- A formula in an external strict class has a code in the matching internal strict class.
- [HP98, Lemma I.1.69] -/
private lemma isStrictClass_quote {Γ : Polarity} {s n : ℕ} {ψ : ArithmeticSemiproposition n}
    (h : StrictHierarchy Γ s ψ) : IsStrictClass Γ s (⌜ψ⌝ : V) := by
  induction h with
  | @zero Γ₀ n₀ φ₀ hφ₀ =>
    rcases Γ₀ with _ | _
    · exact (isDelta0_quote_iff_s φ₀).mpr hφ₀
    · exact (isDelta0_quote_iff_s φ₀).mpr hφ₀
  | @ofAlt Γ₀ s₀ n₀ φ₀ _ ih =>
    rcases Γ₀ with _ | _
    · exact IsStrictSigma.of_pi ih
    · exact IsStrictPi.of_sigma ih
  | exs _ ih =>
    show IsStrictSigma _ _
    rw [Semiformula.quote_ex]
    exact IsStrictSigma.exs ih
  | all _ ih =>
    show IsStrictPi _ _
    rw [Semiformula.quote_all]
    exact IsStrictPi.all ih

/-- A formula whose code is existentially quantified is itself existentially quantified.
- [HP98, Lemma I.1.69] -/
private lemma exists_ex_of_quote_eq_qqExs {n : ℕ} (ψ : ArithmeticSemiproposition n) {p : ℕ}
    (h : (⌜ψ⌝ : ℕ) = ^∃ p) :
    ∃ ψ' : ArithmeticSemiproposition (n + 1), ψ = ∃¹ ψ' ∧ (⌜ψ'⌝ : ℕ) = p := by
  induction ψ using Semiformula.rec' with
  | hexs φ _ => exact ⟨φ, rfl, by simpa using h⟩
  | _ => simp [qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqAll, qqExs] at h

/-- A formula whose code is universally quantified is itself universally quantified.
- [HP98, Lemma I.1.69] -/
private lemma exists_all_of_quote_eq_qqAll {n : ℕ} (ψ : ArithmeticSemiproposition n) {p : ℕ}
    (h : (⌜ψ⌝ : ℕ) = ^∀ p) :
    ∃ ψ' : ArithmeticSemiproposition (n + 1), ψ = ∀¹ ψ' ∧ (⌜ψ'⌝ : ℕ) = p := by
  induction ψ using Semiformula.rec' with
  | hall φ _ => exact ⟨φ, rfl, by simpa using h⟩
  | _ => simp [qqVerum, qqFalsum, qqRel, qqNRel, qqAnd, qqOr, qqExs, qqAll] at h

/-- A quoted formula whose code is a block of `k` existentials over a strict `Πₛ` code is strict
`Σₛ₊₁`.
- [HP98, Lemma I.1.69] -/
private lemma strictHierarchy_sigma_of_quote_eq_qqExss {s : ℕ}
    (ih : ∀ {n : ℕ} (ψ : ArithmeticSemiproposition n),
      IsStrictPi s (⌜ψ⌝ : ℕ) → StrictHierarchy 𝚷 s ψ) :
    ∀ (k : ℕ) {n : ℕ} (ψ : ArithmeticSemiproposition n) (q : ℕ),
      (⌜ψ⌝ : ℕ) = qqExss q k → IsStrictPi s q → StrictHierarchy 𝚺 (s + 1) ψ
  | 0,     _, ψ, _, heq, hq => by
    rw [qqExss_zero] at heq; subst heq
    exact .ofAlt (ih ψ hq)
  | k + 1, _, ψ, q, heq, hq => by
    rw [qqExss_succ] at heq
    obtain ⟨ψ', rfl, heq'⟩ := exists_ex_of_quote_eq_qqExs ψ heq
    exact .exs (strictHierarchy_sigma_of_quote_eq_qqExss ih k ψ' q heq' hq)

/-- A quoted formula whose code is a block of `k` universals over a strict `Σₛ` code is strict
`Πₛ₊₁`.
- [HP98, Lemma I.1.69] -/
private lemma strictHierarchy_pi_of_quote_eq_qqAlls {s : ℕ}
    (ih : ∀ {n : ℕ} (ψ : ArithmeticSemiproposition n),
      IsStrictSigma s (⌜ψ⌝ : ℕ) → StrictHierarchy 𝚺 s ψ) :
    ∀ (k : ℕ) {n : ℕ} (ψ : ArithmeticSemiproposition n) (q : ℕ),
      (⌜ψ⌝ : ℕ) = qqAlls q k → IsStrictSigma s q → StrictHierarchy 𝚷 (s + 1) ψ
  | 0,     _, ψ, _, heq, hq => by
    rw [qqAlls_zero] at heq; subst heq
    exact .ofAlt (ih ψ hq)
  | k + 1, _, ψ, q, heq, hq => by
    rw [qqAlls_succ] at heq
    obtain ⟨ψ', rfl, heq'⟩ := exists_all_of_quote_eq_qqAll ψ heq
    exact .all (strictHierarchy_pi_of_quote_eq_qqAlls ih k ψ' q heq' hq)

mutual
  /-- Internal strict `Σₛ` recognition implies external strict `Σₛ` membership.
  - [HP98, Lemma I.1.69] -/
  private lemma strictHierarchy_sigma_of_isStrictSigma_nat :
      ∀ (s : ℕ) {n : ℕ} (ψ : ArithmeticSemiproposition n),
        IsStrictSigma s (⌜ψ⌝ : ℕ) → StrictHierarchy 𝚺 s ψ
    | 0,     _, ψ, h => .zero ((isDelta0_quote_iff_s ψ).mp h)
    | s + 1, _, ψ, h => by
      obtain ⟨k, q, heq, hq⟩ := h
      exact strictHierarchy_sigma_of_quote_eq_qqExss
        (strictHierarchy_pi_of_isStrictPi_nat s) k ψ q heq hq

  /-- Internal strict `Πₛ` recognition implies external strict `Πₛ` membership.
  - [HP98, Lemma I.1.69] -/
  private lemma strictHierarchy_pi_of_isStrictPi_nat :
      ∀ (s : ℕ) {n : ℕ} (ψ : ArithmeticSemiproposition n),
        IsStrictPi s (⌜ψ⌝ : ℕ) → StrictHierarchy 𝚷 s ψ
    | 0,     _, ψ, h => .zero ((isDelta0_quote_iff_s ψ).mp h)
    | s + 1, _, ψ, h => by
      obtain ⟨k, q, heq, hq⟩ := h
      exact strictHierarchy_pi_of_quote_eq_qqAlls
        (strictHierarchy_sigma_of_isStrictSigma_nat s) k ψ q heq hq
end

/-- Internal strict `Σₛ` recognition over the standard model agrees with the external class.
- [HP98, Lemma I.1.69] -/
private lemma isStrictSigma_quote_iff_nat {s n : ℕ} (ψ : ArithmeticSemiproposition n) :
    IsStrictSigma s (⌜ψ⌝ : ℕ) ↔ StrictHierarchy 𝚺 s ψ :=
  ⟨strictHierarchy_sigma_of_isStrictSigma_nat s ψ, fun h ↦ isStrictClass_quote h⟩

/-- Internal strict `Πₛ` recognition over the standard model agrees with the external class.
- [HP98, Lemma I.1.69] -/
private lemma isStrictPi_quote_iff_nat {s n : ℕ} (ψ : ArithmeticSemiproposition n) :
    IsStrictPi s (⌜ψ⌝ : ℕ) ↔ StrictHierarchy 𝚷 s ψ :=
  ⟨strictHierarchy_pi_of_isStrictPi_nat s ψ, fun h ↦ isStrictClass_quote h⟩

/-- Internal strict `Σₛ` recognition agrees with the external class on quoted formulas.
- [HP98, Lemma I.1.69] -/
lemma isStrictSigma_quote_iff_s {s n : ℕ} (ψ : ArithmeticSemiproposition n) :
    IsStrictSigma s (⌜ψ⌝ : V) ↔ StrictHierarchy 𝚺 s ψ :=
  have h : V ⊧/![(⌜ψ⌝ : V)] (isStrictSigma s).val ↔ ℕ ⊧/![(⌜ψ⌝ : ℕ)] (isStrictSigma s).val := by
    simpa [Semiformula.coe_quote_eq_quote, Matrix.constant_eq_singleton]
      using models_iff_of_Delta1 (V := V) (σ := isStrictSigma s)
        (IsStrictSigma.defined (V := ℕ) s).proper (IsStrictSigma.defined (V := V) s).proper
        (e := ![⌜ψ⌝])
  by simpa [(IsStrictSigma.defined (V := V) s).df, (IsStrictSigma.defined (V := ℕ) s).df,
    isStrictSigma_quote_iff_nat] using h

/-- Internal strict `Πₛ` recognition agrees with the external class on quoted formulas.
- [HP98, Lemma I.1.69] -/
lemma isStrictPi_quote_iff_s {s n : ℕ} (ψ : ArithmeticSemiproposition n) :
    IsStrictPi s (⌜ψ⌝ : V) ↔ StrictHierarchy 𝚷 s ψ :=
  have h : V ⊧/![(⌜ψ⌝ : V)] (isStrictPi s).val ↔ ℕ ⊧/![(⌜ψ⌝ : ℕ)] (isStrictPi s).val := by
    simpa [Semiformula.coe_quote_eq_quote, Matrix.constant_eq_singleton]
      using models_iff_of_Delta1 (V := V) (σ := isStrictPi s)
        (IsStrictPi.defined (V := ℕ) s).proper (IsStrictPi.defined (V := V) s).proper
        (e := ![⌜ψ⌝])
  by simpa [(IsStrictPi.defined (V := V) s).df, (IsStrictPi.defined (V := ℕ) s).df,
    isStrictPi_quote_iff_nat] using h

/-- Internal strict `Σₛ` recognition agrees with the external class on quoted semisentences.
- [HP98, Lemma I.1.69] -/
lemma isStrictSigma_quote_iff {n k : ℕ} (ψ : ArithmeticSemisentence k) :
    IsStrictSigma n (⌜ψ⌝ : V) ↔ StrictHierarchy 𝚺 n ψ := by
  simp [Sentence.quote_def, isStrictSigma_quote_iff_s]

/-- Internal strict `Πₛ` recognition agrees with the external class on quoted semisentences.
- [HP98, Lemma I.1.69] -/
lemma isStrictPi_quote_iff {n k : ℕ} (ψ : ArithmeticSemisentence k) :
    IsStrictPi n (⌜ψ⌝ : V) ↔ StrictHierarchy 𝚷 n ψ := by
  simp [Sentence.quote_def, isStrictPi_quote_iff_s]

end FFL.FirstOrder.Arithmetic.Bootstrapping
