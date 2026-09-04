module

public import AlphaCentauri.Hierarchy.Prenex
public import AlphaCentauri.Bootstrapping.Delta0

/-!
# Internal prenex classes

This module codes blocks of existential quantifiers and vector concatenation inside arithmetic.
It also defines internal predicates for the strict prenex hierarchy.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

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
def _root_.LO.FirstOrder.Arithmetic.qqExssDef : 𝚺₁.Semisentence 3 :=
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

/-- Vector-recursion blueprint for appending two coded vectors.
- No source; this is a routine coding construction. -/
def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y w. y = w”
  adjoin := .mkSigma “y x xs ih w. !adjoinDef y x ih”

/-- Vector-recursive construction for appending two coded vectors.
- No source; this is a routine coding construction. -/
noncomputable def construction : VecRec.Construction V blueprint where
  nil param := param 0
  adjoin (_ x _ ih) := x ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end VecAppend

/-- `vecAppend v w` is the coded vector obtained by placing `v` before `w`.
- No source; this is a routine coding construction. -/
noncomputable def vecAppend (v w : V) : V := VecAppend.construction.result ![w] v

/-- Appending to the empty coded vector returns the second vector.
- No source; this is a routine coding fact. -/
@[simp] lemma vecAppend_nil (w : V) : vecAppend 0 w = w := by
  simp [vecAppend, VecAppend.construction]

/-- Appending preserves the head of a nonempty coded vector.
- No source; this is a routine coding fact. -/
@[simp] lemma vecAppend_adjoin (x v w : V) : vecAppend (x ∷ v) w = x ∷ vecAppend v w := by
  simp [vecAppend, VecAppend.construction]

/-- Defining formula for appending coded vectors.
- No source; this is a routine coding construction. -/
def _root_.LO.FirstOrder.Arithmetic.vecAppendDef : 𝚺₁.Semisentence 3 :=
  VecAppend.blueprint.resultDef

/-- Appending coded vectors is `𝚺₁`-definable.
- No source; this is a routine coding construction. -/
instance vecAppend_defined : 𝚺₁-Function₂ (vecAppend : V → V → V) via vecAppendDef :=
  VecAppend.construction.result_defined

/-- The `𝚺₁` definability instance for appending coded vectors.
- No source; this is a routine coding construction. -/
instance vecAppend_definable : 𝚺₁-Function₂ (vecAppend : V → V → V) :=
  vecAppend_defined.to_definable

/-- Appending coded vectors is definable at every positive hierarchy level.
- No source; this is a routine coding construction. -/
instance vecAppend_definable' (Γ m) : Γ-[m + 1]-Function₂ (vecAppend : V → V → V) :=
  vecAppend_definable.of_sigmaOne

/-- The length of an appended vector is the sum of the component lengths.
- No source; this is a routine coding fact. -/
@[simp] lemma len_vecAppend (v w : V) : len (vecAppend v w) = len v + len w := by
  induction v using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin x v ih => simp [vecAppend_adjoin, ih, add_right_comm]

/-- An index below the first length reads from the first appended vector.
- No source; this is a routine coding fact. -/
lemma nth_vecAppend_of_lt {v w i : V} (hi : i < len v) : (vecAppend v w).[i] = v.[i] := by
  induction v using adjoin_ISigma1.pi1_succ_induction generalizing i
  · definability
  case nil => simp at hi
  case adjoin x v ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simp only [vecAppend_adjoin, nth_adjoin_succ]
      exact ih (by simpa using hi)

/-- An index beyond the first length reads from the second appended vector.
- No source; this is a routine coding fact. -/
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
  /-- `IsStrictSigma n p` says that `p` codes a strict prenex `Σₙ` formula.
  - [HP98, Lemma I.1.69] -/
  def IsStrictSigma : ℕ → V → Prop
    | 0 => IsDelta0
    | n + 1 => fun p ↦ ∃ k q, p = qqExss q k ∧ IsStrictPi n q

  /-- `IsStrictPi n p` says that `p` codes a strict prenex `Πₙ` formula.
  - [HP98, Lemma I.1.69] -/
  def IsStrictPi : ℕ → V → Prop
    | 0 => IsDelta0
    | n + 1 => fun p ↦ ∃ k q, p = qqAlls q k ∧ IsStrictSigma n q
end

mutual
  /-- A `𝚫₁` recognizer for internally coded strict prenex `Σₙ` formulas.
  - [HP98, Lemma I.1.69(1)] -/
  noncomputable def isStrictSigma : ℕ → 𝚫₁.Semisentence 1
    | 0 => isDelta0
    | n + 1 => .mkDelta
        (.mkSigma “p. ∃ k < p + 1, ∃ q < p + 1, !qqExssDef p q k ∧ !(isStrictPi n).sigma q”)
        (.mkPi “p. ∃ k < p + 1, ∃ q < p + 1, (∀ y, !qqExssDef y q k → y = p) ∧ !(isStrictPi n).pi q”)

  /-- A `𝚫₁` recognizer for internally coded strict prenex `Πₙ` formulas.
  - [HP98, Lemma I.1.69(1)] -/
  noncomputable def isStrictPi : ℕ → 𝚫₁.Semisentence 1
    | 0 => isDelta0
    | n + 1 => .mkDelta
        (.mkSigma “p. ∃ k < p + 1, ∃ q < p + 1, !qqAllsDef p q k ∧ !(isStrictSigma n).sigma q”)
        (.mkPi “p. ∃ k < p + 1, ∃ q < p + 1, (∀ y, !qqAllsDef y q k → y = p) ∧ !(isStrictSigma n).pi q”)
end

/-- Joint `𝚫₁`-definedness of the strict prenex `Σₙ`/`Πₙ` recognizers, by recursion on `n`.
- [HP98, Lemma I.1.69(1)] -/
private theorem isStrictSigmaPi_defined :
    ∀ n : ℕ, (𝚫₁-Predicate (IsStrictSigma n : V → Prop) via isStrictSigma n) ∧
      (𝚫₁-Predicate (IsStrictPi n : V → Prop) via isStrictPi n)
  | 0 => ⟨IsDelta0.defined, IsDelta0.defined⟩
  | n + 1 => by
    obtain ⟨hsig, hpi⟩ := isStrictSigmaPi_defined n
    have := hsig
    have := hpi
    refine ⟨.mk ⟨?_, ?_⟩, .mk ⟨?_, ?_⟩⟩
    · intro v
      simp [isStrictSigma, HierarchySymbol.Semiformula.val_sigma, eq_comm]
    · intro v
      suffices h : (∃ k ≤ v 0, ∃ q ≤ v 0, v 0 = qqExss q k ∧ IsStrictPi n q) ↔
          ∃ k q, v 0 = qqExss q k ∧ IsStrictPi n q by
        simpa [isStrictSigma, IsStrictSigma, lt_succ_iff_le] using h
      constructor
      · rintro ⟨k, -, q, -, heq, hq⟩
        exact ⟨k, q, heq, hq⟩
      · rintro ⟨k, q, heq, hq⟩
        exact ⟨k, heq ▸ index_le_qqExss q k, q, heq ▸ le_qqExss q k, heq, hq⟩
    · intro v
      simp [isStrictPi, HierarchySymbol.Semiformula.val_sigma, eq_comm]
    · intro v
      suffices h : (∃ k ≤ v 0, ∃ q ≤ v 0, v 0 = qqAlls q k ∧ IsStrictSigma n q) ↔
          ∃ k q, v 0 = qqAlls q k ∧ IsStrictSigma n q by
        simpa [isStrictPi, IsStrictPi, lt_succ_iff_le] using h
      constructor
      · rintro ⟨k, -, q, -, heq, hq⟩
        exact ⟨k, q, heq, hq⟩
      · rintro ⟨k, q, heq, hq⟩
        exact ⟨k, heq ▸ index_le_qqAlls q k, q, heq ▸ le_qqAlls q k, heq, hq⟩

/-- The strict prenex `Σₙ` recognizer defines `IsStrictSigma n`.
- [HP98, Lemma I.1.69(1)] -/
instance IsStrictSigma.defined (n : ℕ) :
    𝚫₁-Predicate (IsStrictSigma n : V → Prop) via isStrictSigma n :=
  (isStrictSigmaPi_defined n).1

/-- The strict prenex `Πₙ` recognizer defines `IsStrictPi n`.
- [HP98, Lemma I.1.69(1)] -/
instance IsStrictPi.defined (n : ℕ) :
    𝚫₁-Predicate (IsStrictPi n : V → Prop) via isStrictPi n :=
  (isStrictSigmaPi_defined n).2

/-- Internal strict prenex `Σₙ` membership is `𝚫₁`-definable.
- [HP98, Lemma I.1.69(1)] -/
instance IsStrictSigma.definable (n : ℕ) : 𝚫₁-Predicate (IsStrictSigma n : V → Prop) :=
  (IsStrictSigma.defined n).to_definable

/-- Internal strict prenex `Πₙ` membership is `𝚫₁`-definable.
- [HP98, Lemma I.1.69(1)] -/
instance IsStrictPi.definable (n : ℕ) : 𝚫₁-Predicate (IsStrictPi n : V → Prop) :=
  (IsStrictPi.defined n).to_definable

/-- A strict `Πₙ` formula belongs to the next strict `Σ` level via an empty block.
- [HP98, Lemma I.1.69] -/
lemma IsStrictSigma.of_pi {n : ℕ} {p : V} (h : IsStrictPi n p) : IsStrictSigma (n + 1) p :=
  ⟨0, p, (qqExss_zero p).symm, h⟩

/-- A strict `Σₙ` formula belongs to the next strict `Π` level via an empty block.
- [HP98, Lemma I.1.69] -/
lemma IsStrictPi.of_sigma {n : ℕ} {p : V} (h : IsStrictSigma n p) : IsStrictPi (n + 1) p :=
  ⟨0, p, (qqAlls_zero p).symm, h⟩

/-- A strict `Σₙ₊₁` class is closed under existential quantification.
- [HP98, Lemma I.1.69] -/
lemma IsStrictSigma.exs {n : ℕ} {p : V} (h : IsStrictSigma (n + 1) p) :
    IsStrictSigma (n + 1) (^∃ p) := by
  obtain ⟨k, q, rfl, hq⟩ := h
  exact ⟨k + 1, q, (qqExss_succ q k).symm, hq⟩

/-- A strict `Πₙ₊₁` class is closed under universal quantification.
- [HP98, Lemma I.1.69] -/
lemma IsStrictPi.all {n : ℕ} {p : V} (h : IsStrictPi (n + 1) p) :
    IsStrictPi (n + 1) (^∀ p) := by
  obtain ⟨k, q, rfl, hq⟩ := h
  exact ⟨k + 1, q, (qqAlls_succ q k).symm, hq⟩

/-- Every internally `Δ₀` formula belongs to the internal strict `Σ`/`Π` classes at every level,
by repeatedly climbing through the empty-block embeddings `of_pi`/`of_sigma`.
- [HP98, Lemma I.1.69] -/
private theorem isStrictDelta0 :
    ∀ m : ℕ, (∀ p : V, IsDelta0 p → IsStrictSigma m p) ∧ (∀ p : V, IsDelta0 p → IsStrictPi m p)
  | 0 => ⟨fun _ h => h, fun _ h => h⟩
  | m + 1 =>
    have ⟨ihS, ihP⟩ := isStrictDelta0 m
    ⟨fun p h => IsStrictSigma.of_pi (ihP p h), fun p h => IsStrictPi.of_sigma (ihS p h)⟩

/-- Joint monotonicity of the internal strict `Σ`/`Π` classes in their level, by induction on the
lower level: a witness at level `m + 1` reduces to the same fact for its inner `Π`/`Σ` witness at
level `m`.
- [HP98, Lemma I.1.69] -/
private theorem isStrictMono :
    ∀ m : ℕ, (∀ n, m ≤ n → ∀ p : V, IsStrictSigma m p → IsStrictSigma n p) ∧
      (∀ n, m ≤ n → ∀ p : V, IsStrictPi m p → IsStrictPi n p)
  | 0 => ⟨fun n _ p h => (isStrictDelta0 n).1 p h, fun n _ p h => (isStrictDelta0 n).2 p h⟩
  | m + 1 =>
    have ⟨ihS, ihP⟩ := isStrictMono m
    ⟨fun n hn p h => by
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        obtain ⟨k, q, rfl, hq⟩ := h
        exact ⟨k, q, rfl, ihP n' (by omega) q hq⟩,
      fun n hn p h => by
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        obtain ⟨k, q, rfl, hq⟩ := h
        exact ⟨k, q, rfl, ihS n' (by omega) q hq⟩⟩

/-- Internal strict `Σ` classes are monotone in the hierarchy level.
- [HP98, Lemma I.1.69] -/
lemma IsStrictSigma.mono {m n : ℕ} (h : m ≤ n) {p : V} :
    IsStrictSigma m p → IsStrictSigma n p := (isStrictMono m).1 n h p

/-- Internal strict `Π` classes are monotone in the hierarchy level.
- [HP98, Lemma I.1.69] -/
lemma IsStrictPi.mono {m n : ℕ} (h : m ≤ n) {p : V} :
    IsStrictPi m p → IsStrictPi n p := (isStrictMono m).2 n h p

/-- Joint auxiliary facts for peeling a leading existential quantifier off an internal strict
`Π`/`Σ` code, by induction on the level: the block length in the witnessing equation is either
positive (in which case the quantifier is peeled off directly) or zero (in which case the level
drops by one, bottoming out in a `Δ₀` argument using `IsDelta0.of_ex`).
- [HP98, Lemma I.1.69] -/
private theorem isStrictExs_aux :
    ∀ n : ℕ, (∀ p : V, IsStrictPi n (^∃ p) → IsStrictSigma (n + 1) p) ∧
      (∀ p : V, IsStrictSigma n (^∃ p) → IsStrictSigma (n + 1) p)
  | 0 => by
    have base : ∀ p : V, IsDelta0 (^∃ p) → IsStrictSigma 1 p := by
      intro p h
      obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ := IsDelta0.of_ex h
      have hlt : IsDelta0 (Arithmetic.qqLT (qqBvar 0) (termBShift ℒₒᵣ t)) := by
        rw [Arithmetic.qqLT]; exact IsDelta0.rel
      exact IsStrictSigma.of_pi (IsDelta0.and_iff.mpr ⟨hlt, hq⟩)
    exact ⟨base, base⟩
  | n + 1 => by
    have ⟨ihA, ihB⟩ := isStrictExs_aux n
    refine ⟨fun p h => ?_, fun p h => ?_⟩
    · obtain ⟨k', q', heq, hq'⟩ := h
      rcases zero_or_succ k' with (rfl | ⟨k', rfl⟩)
      · rw [qqAlls_zero] at heq
        subst heq
        exact IsStrictSigma.mono (by omega) (ihB p hq')
      · rw [qqAlls_succ] at heq
        simp [qqExs, qqAll, pair_ext_iff] at heq
    · obtain ⟨k, q, heq, hq⟩ := h
      rcases zero_or_succ k with (rfl | ⟨k, rfl⟩)
      · rw [qqExss_zero] at heq
        subst heq
        exact IsStrictSigma.mono (by omega) (ihA p hq)
      · rw [qqExss_succ] at heq
        simp only [qqExs_inj] at heq
        exact ⟨k, q, heq, IsStrictPi.mono (by omega) hq⟩

/-- Joint auxiliary facts for peeling a leading universal quantifier off an internal strict
`Σ`/`Π` code, dual to `isStrictExs_aux`.
- [HP98, Lemma I.1.69] -/
private theorem isStrictAll_aux :
    ∀ n : ℕ, (∀ p : V, IsStrictSigma n (^∀ p) → IsStrictPi (n + 1) p) ∧
      (∀ p : V, IsStrictPi n (^∀ p) → IsStrictPi (n + 1) p)
  | 0 => by
    have base : ∀ p : V, IsDelta0 (^∀ p) → IsStrictPi 1 p := by
      intro p h
      obtain ⟨u, q, ⟨t, ht, rfl⟩, hq, rfl⟩ := IsDelta0.of_all h
      have hlt : IsDelta0 (Arithmetic.qqNLT (qqBvar 0) (termBShift ℒₒᵣ t)) := by
        rw [Arithmetic.qqNLT]; exact IsDelta0.nrel
      exact IsStrictPi.of_sigma (IsDelta0.or_iff.mpr ⟨hlt, hq⟩)
    exact ⟨base, base⟩
  | n + 1 => by
    have ⟨ihA, ihB⟩ := isStrictAll_aux n
    refine ⟨fun p h => ?_, fun p h => ?_⟩
    · obtain ⟨k', q', heq, hq'⟩ := h
      rcases zero_or_succ k' with (rfl | ⟨k', rfl⟩)
      · rw [qqExss_zero] at heq
        subst heq
        exact IsStrictPi.mono (by omega) (ihB p hq')
      · rw [qqExss_succ] at heq
        simp [qqExs, qqAll, pair_ext_iff] at heq
    · obtain ⟨k, q, heq, hq⟩ := h
      rcases zero_or_succ k with (rfl | ⟨k, rfl⟩)
      · rw [qqAlls_zero] at heq
        subst heq
        exact IsStrictPi.mono (by omega) (ihA p hq)
      · rw [qqAlls_succ] at heq
        simp only [qqAll_inj] at heq
        exact ⟨k, q, heq, IsStrictSigma.mono (by omega) hq⟩

/-- Removing a leading existential preserves a strict positive-level `Σ` class.
- [HP98, Lemma I.1.69] -/
lemma IsStrictSigma.of_exs {n : ℕ} {p : V} (h : IsStrictSigma (n + 1) (^∃ p)) :
    IsStrictSigma (n + 1) p := by
  obtain ⟨k, q, heq, hq⟩ := h
  rcases zero_or_succ k with (rfl | ⟨k, rfl⟩)
  · rw [qqExss_zero] at heq
    subst heq
    exact (isStrictExs_aux n).1 p hq
  · rw [qqExss_succ] at heq
    simp only [qqExs_inj] at heq
    exact ⟨k, q, heq, hq⟩

/-- Removing a leading universal preserves a strict positive-level `Π` class.
- [HP98, Lemma I.1.69] -/
lemma IsStrictPi.of_all {n : ℕ} {p : V} (h : IsStrictPi (n + 1) (^∀ p)) :
    IsStrictPi (n + 1) p := by
  obtain ⟨k, q, heq, hq⟩ := h
  rcases zero_or_succ k with (rfl | ⟨k, rfl⟩)
  · rw [qqAlls_zero] at heq
    subst heq
    exact (isStrictAll_aux n).1 p hq
  · rw [qqAlls_succ] at heq
    simp only [qqAll_inj] at heq
    exact ⟨k, q, heq, hq⟩

/-- Joint fact that negation exchanges the internal strict `Σₙ`/`Πₙ` classes, by induction on the
level, using `neg_qqExss`/`neg_qqAlls` to commute negation past the quantifier block.
- [HP98, Lemma I.1.69] -/
private theorem isStrictNeg :
    ∀ n : ℕ, (∀ p : V, IsUFormula ℒₒᵣ p → IsStrictSigma n p → IsStrictPi n (neg ℒₒᵣ p)) ∧
      (∀ p : V, IsUFormula ℒₒᵣ p → IsStrictPi n p → IsStrictSigma n (neg ℒₒᵣ p))
  | 0 => ⟨fun _ hp h => IsDelta0.neg hp h, fun _ hp h => IsDelta0.neg hp h⟩
  | n + 1 =>
    have ⟨ihS, ihP⟩ := isStrictNeg n
    ⟨fun p hp h => by
        obtain ⟨k, q, rfl, hq⟩ := h
        have hqf : IsUFormula ℒₒᵣ q := isUFormula_qqExss.mp hp
        exact ⟨k, neg ℒₒᵣ q, neg_qqExss hqf, ihP q hqf hq⟩,
      fun p hp h => by
        obtain ⟨k, q, rfl, hq⟩ := h
        have hqf : IsUFormula ℒₒᵣ q := isUFormula_qqAlls.mp hp
        exact ⟨k, neg ℒₒᵣ q, neg_qqAlls hqf, ihS q hqf hq⟩⟩

/-- Negation sends internally coded strict `Σₙ` formulas to strict `Πₙ` formulas.
- [HP98, Lemma I.1.69] -/
lemma IsStrictSigma.neg {n : ℕ} {p : V} (hp : IsUFormula ℒₒᵣ p) :
    IsStrictSigma n p → IsStrictPi n (neg ℒₒᵣ p) := (isStrictNeg n).1 p hp

/-- Negation sends internally coded strict `Πₙ` formulas to strict `Σₙ` formulas.
- [HP98, Lemma I.1.69] -/
lemma IsStrictPi.neg {n : ℕ} {p : V} (hp : IsUFormula ℒₒᵣ p) :
    IsStrictPi n p → IsStrictSigma n (neg ℒₒᵣ p) := (isStrictNeg n).2 p hp

/-- Internal strict `Σₙ` recognition agrees with the external class on quoted formulas.
- [HP98, Lemma I.1.69] -/
axiom isStrictSigma_quote_iff {n k : ℕ} (ψ : ArithmeticSemisentence k) :
    IsStrictSigma n (⌜ψ⌝ : V) ↔ StrictHierarchy 𝚺 n ψ

/-- Internal strict `Πₙ` recognition agrees with the external class on quoted formulas.
- [HP98, Lemma I.1.69] -/
axiom isStrictPi_quote_iff {n k : ℕ} (ψ : ArithmeticSemisentence k) :
    IsStrictPi n (⌜ψ⌝ : V) ↔ StrictHierarchy 𝚷 n ψ

end LO.FirstOrder.Arithmetic.Bootstrapping
