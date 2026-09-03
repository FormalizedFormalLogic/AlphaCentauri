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

/-- A formula code does not exceed the result of prefixing existential quantifiers.
- [HP98, Lemma I.1.69] -/
@[simp] lemma le_qqExss (p k : V) : p ≤ qqExss p k := sorry

/-- The block length does not exceed the code of the prefixed formula.
- [HP98, Lemma I.1.69] -/
@[simp] lemma index_le_qqExss (p k : V) : k ≤ qqExss p k := sorry

variable {L : Language} [L.Encodable] [L.LORDefinable] in
/-- Prefixing existential quantifiers preserves being a coded untyped formula.
- [HP98, Lemma I.1.69] -/
@[simp] lemma isUFormula_qqExss {p k : V} : IsUFormula L (qqExss p k) ↔ IsUFormula L p :=
  sorry

/-- Negation turns a coded existential block into a universal block.
- [HP98, Lemma I.1.69] -/
lemma neg_qqExss {p k : V} (hp : IsUFormula ℒₒᵣ p) :
    neg ℒₒᵣ (qqExss p k) = qqAlls (neg ℒₒᵣ p) k := sorry

/-- Negation turns a coded universal block into an existential block.
- [HP98, Lemma I.1.69] -/
lemma neg_qqAlls {p k : V} (hp : IsUFormula ℒₒᵣ p) :
    neg ℒₒᵣ (qqAlls p k) = qqExss (neg ℒₒᵣ p) k := sorry

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
@[simp] lemma len_vecAppend (v w : V) : len (vecAppend v w) = len v + len w := sorry

/-- An index below the first length reads from the first appended vector.
- No source; this is a routine coding fact. -/
lemma nth_vecAppend_of_lt {v w i : V} (hi : i < len v) : (vecAppend v w).[i] = v.[i] :=
  sorry

/-- An index beyond the first length reads from the second appended vector.
- No source; this is a routine coding fact. -/
lemma nth_vecAppend_of_le {v w i : V} (hi : len v ≤ i) :
    (vecAppend v w).[i] = w.[i - len v] := sorry

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

/-- A `𝚫₁` recognizer for internally coded strict prenex `Σₙ` formulas.
- [HP98, Lemma I.1.69(1)] -/
noncomputable def isStrictSigma (n : ℕ) : 𝚫₁.Semisentence 1 := sorry

/-- A `𝚫₁` recognizer for internally coded strict prenex `Πₙ` formulas.
- [HP98, Lemma I.1.69(1)] -/
noncomputable def isStrictPi (n : ℕ) : 𝚫₁.Semisentence 1 := sorry

/-- The strict prenex `Σₙ` recognizer defines `IsStrictSigma n`.
- [HP98, Lemma I.1.69(1)] -/
instance IsStrictSigma.defined (n : ℕ) :
    𝚫₁-Predicate (IsStrictSigma n : V → Prop) via isStrictSigma n := sorry

/-- The strict prenex `Πₙ` recognizer defines `IsStrictPi n`.
- [HP98, Lemma I.1.69(1)] -/
instance IsStrictPi.defined (n : ℕ) :
    𝚫₁-Predicate (IsStrictPi n : V → Prop) via isStrictPi n := sorry

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
    IsStrictSigma (n + 1) (^∃ p) := sorry

/-- A strict `Πₙ₊₁` class is closed under universal quantification.
- [HP98, Lemma I.1.69] -/
lemma IsStrictPi.all {n : ℕ} {p : V} (h : IsStrictPi (n + 1) p) :
    IsStrictPi (n + 1) (^∀ p) := sorry

/-- Removing a leading existential preserves a strict positive-level `Σ` class.
- [HP98, Lemma I.1.69] -/
lemma IsStrictSigma.of_exs {n : ℕ} {p : V} (h : IsStrictSigma (n + 1) (^∃ p)) :
    IsStrictSigma (n + 1) p := sorry

/-- Removing a leading universal preserves a strict positive-level `Π` class.
- [HP98, Lemma I.1.69] -/
lemma IsStrictPi.of_all {n : ℕ} {p : V} (h : IsStrictPi (n + 1) (^∀ p)) :
    IsStrictPi (n + 1) p := sorry

/-- Internal strict `Σ` classes are monotone in the hierarchy level.
- [HP98, Lemma I.1.69] -/
lemma IsStrictSigma.mono {m n : ℕ} (h : m ≤ n) {p : V} :
    IsStrictSigma m p → IsStrictSigma n p := sorry

/-- Internal strict `Π` classes are monotone in the hierarchy level.
- [HP98, Lemma I.1.69] -/
lemma IsStrictPi.mono {m n : ℕ} (h : m ≤ n) {p : V} :
    IsStrictPi m p → IsStrictPi n p := sorry

/-- Negation sends internally coded strict `Σₙ` formulas to strict `Πₙ` formulas.
- [HP98, Lemma I.1.69] -/
lemma IsStrictSigma.neg {n : ℕ} {p : V} (hp : IsUFormula ℒₒᵣ p) :
    IsStrictSigma n p → IsStrictPi n (neg ℒₒᵣ p) := sorry

/-- Negation sends internally coded strict `Πₙ` formulas to strict `Σₙ` formulas.
- [HP98, Lemma I.1.69] -/
lemma IsStrictPi.neg {n : ℕ} {p : V} (hp : IsUFormula ℒₒᵣ p) :
    IsStrictPi n p → IsStrictSigma n (neg ℒₒᵣ p) := sorry

/-- Internal strict `Σₙ` recognition agrees with the external class on quoted formulas.
- [HP98, Lemma I.1.69] -/
lemma isStrictSigma_quote_iff {n k : ℕ} (ψ : ArithmeticSemisentence k) :
    IsStrictSigma n (⌜ψ⌝ : V) ↔ StrictHierarchy 𝚺 n ψ := sorry

/-- Internal strict `Πₙ` recognition agrees with the external class on quoted formulas.
- [HP98, Lemma I.1.69] -/
lemma isStrictPi_quote_iff {n k : ℕ} (ψ : ArithmeticSemisentence k) :
    IsStrictPi n (⌜ψ⌝ : V) ↔ StrictHierarchy 𝚷 n ψ := sorry

end LO.FirstOrder.Arithmetic.Bootstrapping
