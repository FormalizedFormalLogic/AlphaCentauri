module

public import AlphaCentauri.Model.OpenInduction
public import AlphaCentauri.NumberTheory.FermatLastTheorem
public import AlphaCentauri.Schemata.BoundedInduction
public import AlphaCentauri.ToFoundation.FirstOrder.BinderNotation
public import AlphaCentauri.ToFoundation.FirstOrder.Fvar
public import AlphaCentauri.ToFoundation.FirstOrder.Rew
public import AlphaCentauri.ToFoundation.FirstOrder.Semiformula
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.LeastNumberPrinciple
public import AlphaCentauri.ToMathlib.OpenPredicate.AddMonoidHomToInt
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Functions
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import AlphaCentauri.Schemata.DeltaInduction

/-!
# Elementary number theory in weak arithmetic

- Quadratic residues: Smith's open questions on quadratic residues and on primes of the form
  $x^2 + ny^2$ over $\mathsf{I}\mathsf{E}_1$ and $\mathsf{I}\Delta_0$, each stated as the
  provability of a sentence. For a prime $q$, the Legendre symbol $(a/q)$ is $1$ exactly when
  `quadraticResidue` holds of $a$ and $q$, and $-1$ exactly when $q \nmid a$ and it fails. The
  questions are open, so their affirmative answers are stated as propositions, one for each
  theory. With the counting principle $\mathrm{Count}_2(\Delta_0)$ adjoined,
  $\mathsf{I}\Delta_0$ proves quadratic reciprocity and its supplementary laws.
- Euclidean division: over $\mathsf{PA}^-$, division with remainder for co-prime pairs is
  equivalent to division with remainder for all pairs with a non-zero divisor.
- Direct summands: for a nonstandard model $V$ of $\mathsf{I}\mathsf{E}_1$, every additive
  homomorphism from the ring of differences of $V$ to $\mathbb{Z}$ is zero, so $\mathbb{Z}$ is
  not a direct summand of its additive group. Carl proved this over $\mathsf{I}\mathsf{E}_2$ and
  asked whether $\mathsf{I}\mathsf{E}_1$ suffices.
- The irrationality of $\sqrt{2}$: $\mathsf{IOpen}$ together with Bézout's theorem
  proves it, while $\mathsf{IOpen}$ alone does not. In the non-negative part of the
  $\mathbb{Z}$-ring of real polynomials with integer constant term, $x = \sqrt{2} X$ and $y = X$
  satisfy $x^2 = 2 y^2$ with $y \ne 0$. Since the irrationality of $\sqrt{2}$ is a universal
  sentence, $\mathsf{IOpen}$ does not prove it.

- [Smi93, §6]
- [Jer10, Theorem 5.7]
- [Kat26b, Theorem 2, Corollary 4]
- [Vis26, Open Question 8.29]
- [Car16, Theorem 4]
- [She64]
- [DAq05, §2]
- [Wil78]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- `a` is a quadratic residue modulo `m`: `a` is coprime to `m` and `x² ≡ a (mod m)` has a
solution.
- [Smi93, §3] -/
def quadraticResidue : ArithmeticSemisentence 2 :=
  “a m. (∀ d, d ∣ a → d ∣ m → d = 1) ∧ ∃ x k, x * x = a + k * m ∨ a = x * x + k * m”

/-- `-1` has a `k`-th root modulo `m`: `xᵏ ≡ -1 (mod m)` has a solution.
- [Smi93, Lemma 3.2, Question 5.3] -/
def negOneHasRoot (k : ℕ) : ArithmeticSemisentence 1 :=
  “m. ∃ x, m ∣ x ^' k + 1”

/-- `q` is of the form `x² + n y²`.
- [Smi93, §4] -/
def squareAddMulSquare (n : ℕ) : ArithmeticSemisentence 1 := “q. ∃ x y, q = x * x + ↑n * y * y”

/-- $(-1/q) = 1$ for every prime $q \equiv 1 \pmod 4$.
- [Smi93, Question 5.1] -/
def quadraticResidueNegOne : ArithmeticSentence :=
  “∀ q, !isPrime q → (∃ k, q = 4 * k + 1) → !(negOneHasRoot 2) q”

/-- $\mathsf{I}\mathsf{E}_1$ proves that $(-1/q) = 1$ for every prime $q \equiv 1 \pmod 4$. An
open problem; Jeřábek states that his proof of the supplementary laws of quadratic reciprocity
can be formalized in $\mathsf{I}\mathsf{E}_1 + \mathrm{Count}_2(\nabla_1)$.
- [Smi93, Question 5.1]
- [Jer21, Chapter 0, §2.2] -/
def ProvableQuadraticResidueNegOneIE1 : Prop := 𝗜𝗘₁ ⊢ quadraticResidueNegOne

/-- $\mathsf{I}\Delta_0$ proves that $(-1/q) = 1$ for every prime $q \equiv 1 \pmod 4$. An open
problem; $\mathsf{I}\Delta_0 + \Delta_0\mathrm{EQ}$ and
$\mathsf{I}\Delta_0 + \mathrm{Count}_2(\Delta_0)$ prove it.
- [Smi93, Question 5.1]
- [BI91, Theorem 3.5]
- [Jer10, Theorem 5.7] -/
def ProvableQuadraticResidueNegOneISigma0 : Prop := 𝗜𝚺₀ ⊢ quadraticResidueNegOne

/-- The converse of [Smi93, Theorem 3.11] for the odd prime `p`: for every odd
prime $q \ne p$, $(q/p) = 1$ implies $(p/q) = 1$ unless $p \equiv q \equiv 3 \pmod 4$, in which
case $(p/q) = -1$ implies $(q/p) = 1$.
- [Smi93, Theorem 3.11, Question 5.2] -/
def quadraticReciprocityConverse (p : ℕ) : ArithmeticSentence :=
  “∀ q, !isPrime q → q ≠ 2 → q ≠ ↑p →
    ((∃ k, ↑p = 4 * k + 3) ∧ (∃ k, q = 4 * k + 3) →
      ¬!quadraticResidue ↑p q → !quadraticResidue q ↑p) ∧
    (¬((∃ k, ↑p = 4 * k + 3) ∧ (∃ k, q = 4 * k + 3)) →
      !quadraticResidue q ↑p → !quadraticResidue ↑p q)”

/-- $\mathsf{I}\mathsf{E}_1$ proves the converse of [Smi93, Theorem 3.11] for each standard odd
prime `p`. An open problem; it follows from quadratic reciprocity, and Jeřábek states that his
proof of quadratic reciprocity and its supplementary laws can be formalized in
$\mathsf{I}\mathsf{E}_1 + \mathrm{Count}_2(\nabla_1)$.
- [Smi93, Theorem 3.11, Question 5.2]
- [Jer21, Chapter 0, §2.2] -/
def ProvableQuadraticReciprocityConverseIE1 : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → 𝗜𝗘₁ ⊢ quadraticReciprocityConverse p

/-- $\mathsf{I}\Delta_0$ proves the converse of [Smi93, Theorem 3.11] for each standard odd prime
`p`. An open problem; $\mathsf{I}\Delta_0 + \mathrm{Count}_2(\Delta_0)$ proves it.
- [Smi93, Theorem 3.11, Question 5.2]
- [Jer10, Theorem 5.7] -/
def ProvableQuadraticReciprocityConverseISigma0 : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → 𝗜𝚺₀ ⊢ quadraticReciprocityConverse p

/-- Quadratic reciprocity: for distinct odd primes $p$ and $q$, $(p/q) = (q/p)$ unless
$p \equiv q \equiv 3 \pmod 4$, in which case $(p/q) = -(q/p)$.
- [Smi93, Question 5.2] -/
def quadraticReciprocity : ArithmeticSentence :=
  “∀ p q, !isPrime p → !isPrime q → p ≠ 2 → q ≠ 2 → p ≠ q →
    ((∃ k, p = 4 * k + 3) ∧ (∃ k, q = 4 * k + 3) →
      (!quadraticResidue p q ↔ ¬!quadraticResidue q p)) ∧
    (¬((∃ k, p = 4 * k + 3) ∧ (∃ k, q = 4 * k + 3)) →
      (!quadraticResidue p q ↔ !quadraticResidue q p))”

/-- $\mathsf{I}\mathsf{E}_1$ proves quadratic reciprocity for arbitrary, possibly nonstandard,
primes. An open problem; $\mathsf{I}\Delta_0 + \mathrm{Count}_2(\Delta_0)$ proves it, and
Jeřábek states that his proof of quadratic reciprocity and its supplementary laws can be
formalized in $\mathsf{I}\mathsf{E}_1 + \mathrm{Count}_2(\nabla_1)$.
- [Smi93, Question 5.2]
- [Jer10, Theorem 5.7]
- [Jer21, Chapter 0, §2.2] -/
def ProvableQuadraticReciprocityIE1 : Prop := 𝗜𝗘₁ ⊢ quadraticReciprocity

/-- If $m - 1 = 2^r s$ with $s$ odd, then $-1$ has no $2^r$-th root modulo $m$. Smith prints the
hypothesis as $m = 2^r s$; the case $r = 2$ is $m \equiv 5 \pmod 8$, and the case $r = 1$ is
[Smi93, Lemma 3.2].
- [Smi93, Lemma 3.2, Question 5.3] -/
def noRootNegOne (r : ℕ) : ArithmeticSentence :=
  “∀ m, (∃ k, m = ↑(2 ^ (r + 1)) * k + ↑(2 ^ r + 1)) → ¬!(negOneHasRoot (2 ^ r)) m”

/-- $\mathsf{I}\mathsf{E}_1$ proves that $-1$ has no $2^r$-th root modulo any $m$ with
$m - 1 = 2^r s$, $s$ odd, for each standard $r \ge 2$. An open problem.
- [Smi93, Question 5.3] -/
def ProvableNoRootNegOneIE1 : Prop := ∀ r : ℕ, 2 ≤ r → 𝗜𝗘₁ ⊢ noRootNegOne r

/-- $\mathsf{I}\Delta_0$ proves that $-1$ has no $2^r$-th root modulo any $m$ with
$m - 1 = 2^r s$, $s$ odd, for each standard $r \ge 2$. An open problem.
- [Smi93, Question 5.3] -/
def ProvableNoRootNegOneISigma0 : Prop := ∀ r : ℕ, 2 ≤ r → 𝗜𝚺₀ ⊢ noRootNegOne r

/-- A prime $q \nmid 4n$ is of the form $x^2 + ny^2$ if and only if $q \bmod 4n$ lies in `S`.
- [Smi93, Question 5.4] -/
noncomputable def squareAddMulSquareIff (n : ℕ) (S : Finset ℕ) : ArithmeticSentence :=
  let residue : ArithmeticSemisentence 1 := ⩖ r ∈ S, “q. ∃ k, q = ↑(4 * n) * k + ↑r”
  “∀ q, !isPrime q → ¬q ∣ ↑(4 * n) → (!(squareAddMulSquare n) q ↔ !residue q)”

/-- For $n > 4$, $\mathsf{I}\mathsf{E}_1$ proves each characterization of the primes of the form
$x^2 + ny^2$ by a congruence modulo $4n$ that holds in $\mathbb{N}$. Smith asks what can be said
of these primes for $n > 4$, where $(-n/q) = 1$ no longer suffices; under this reading the
question is open.
- [Smi93, Question 5.4] -/
def ProvableSquareAddMulSquareIffIE1 : Prop :=
  ∀ (n : ℕ) (S : Finset ℕ), 4 < n → (∀ r ∈ S, r < 4 * n) →
    (∀ p : ℕ, p.Prime → ¬p ∣ 4 * n → ((∃ x y, p = x * x + n * y * y) ↔ p % (4 * n) ∈ S)) →
    𝗜𝗘₁ ⊢ squareAddMulSquareIff n S

/-- Division with remainder by any non-zero divisor. -/
def euclideanDivision : ArithmeticSentence :=
  “∀ a b, a ≠ 0 → ∃ q r, r < a ∧ b = a * q + r”

/-- Division with remainder for co-prime pairs. -/
def coprimeEuclideanDivision : ArithmeticSentence :=
  “∀ a b, (∃ c d, a * d = b * c + 1) → ∃ q r, r < a ∧ b = a * q + r”

noncomputable section

open Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {s t x y : V}

/-- - [Kat26b, Theorem 2] -/
lemma exists_div_of_exists_div_mul_add (hs : s < t)
    (h : ∃ q r, r < t * x ∧ t * y + s = t * x * q + r) : ∃ q r, r < x ∧ y = x * q + r := by
  rcases h with ⟨q, u, hu, e⟩
  have hxq : x * q ≤ y := by
    by_contra hlt
    have h₁ : t * (y + 1) ≤ t * (x * q) := mul_le_mul_left (lt_iff_succ_le.mp (not_le.mp hlt))
    have h₂ : t * (x * q) ≤ t * y + s := by rw [← mul_assoc, e]; exact le_self_add
    have h₃ : t * y + t ≤ t * y + s := by simpa [mul_add] using h₁.trans h₂
    exact absurd (le_of_add_le_add_left h₃) (not_le.mpr hs)
  obtain ⟨r, hr⟩ := exists_add_of_le hxq
  use q, r
  and_intros
  · by_contra hxr
    have h₁ : t * (x * q) + (t * r + s) = t * (x * q) + u := by
      rw [← add_assoc, ← mul_add, ← hr, e, mul_assoc]
    have h₂ : t * x ≤ u := (mul_le_mul_left (not_lt.mp hxr)).trans
      (le_self_add.trans (add_left_cancel h₁).le)
    exact absurd hu (not_lt.mpr h₂)
  · exact hr

/-- - [Kat26b, Corollary 3] -/
lemma exists_coprime_sq_mul_add_one (hx : 1 < x) (hy : 0 < y) :
    ∃ c d, x * x * d = (x * y + 1) * c + 1 := by
  obtain ⟨z, hz⟩ := exists_add_of_le (pos_iff_one_le.mp (mul_pos (zero_lt_one.trans hx) hy))
  use z, y * y
  calc x * x * (y * y) = (x * y) * (x * y) := by ring
    _ = (1 + z) * (1 + z) := by rw [← hz]
    _ = (1 + z + 1) * z + 1 := by ring
    _ = _ := by rw [← hz]

lemma models_coprimeEuclideanDivision_iff_models_euclideanDivision :
    V↓[ℒₒᵣ] ⊧ coprimeEuclideanDivision ↔ V↓[ℒₒᵣ] ⊧ euclideanDivision := by
  suffices (∀ a b c d : V, a * d = b * c + 1 → ∃ q r, r < a ∧ b = a * q + r) ↔
      ∀ a b : V, a ≠ 0 → ∃ q r, r < a ∧ b = a * q + r by
    simpa [models_iff, coprimeEuclideanDivision, euclideanDivision] using this
  constructor
  · intro H x y hx
    rcases eq_or_ne y 0 with rfl | hy
    · use 0, 0
      and_intros <;> simp [pos_iff_ne_zero.mpr hx]
    rcases eq_or_ne x 1 with rfl | hx1
    · use y, 0
      simp
    have hx1 : 1 < x := lt_of_le_of_ne (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hx)) hx1.symm
    obtain ⟨c, d, h⟩ := exists_coprime_sq_mul_add_one hx1 (pos_iff_ne_zero.mpr hy)
    obtain ⟨q, r, hr, e⟩ := H (x * x) (x * y + 1) c d h
    apply exists_div_of_exists_div_mul_add (s := 1) (t := x) hx1
    use q, r
  · intro H a b c d h
    apply H a b
    rintro rfl
    simp at h

end

/-- - [Kat26b, Corollary 4] -/
theorem coprimeEuclideanDivision_iff_euclideanDivision :
    𝗣𝗔⁻ ⊢ coprimeEuclideanDivision 🡘 euclideanDivision :=
  complete.{0} _ _ fun (V : Type) _ _ ↦ by
    simpa using models_coprimeEuclideanDivision_iff_models_euclideanDivision (V := V)

section DirectSummand

open RingOfDifferences OpenPredicate

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗘₁] (hV : ∃ x : V, ∀ n : ℕ, (n : V) < x)

include hV

/-- Every additive homomorphism from the ring of differences of a nonstandard model of
$\mathsf{I}\mathsf{E}_1$ to $\mathbb{Z}$ is zero.
- [Car16, Lemma 5] -/
lemma addMonoidHom_eq_zero_IE1 (f : RingOfDifferences V →+ ℤ) : f = 0 := by
  apply leastNumberPrinciple_of_models_induction.addMonoidHom_eq_zero
  obtain ⟨x, hx⟩ := hV
  use of x
  intro n
  simpa using of_lt_of.2 (hx n)

/-- $\mathbb{Z}$ is not a direct summand of the additive group of the ring of differences of a
nonstandard model of $\mathsf{I}\mathsf{E}_1$.
- [Car16, Theorem 4] -/
theorem not_int_directSummand_IE1 :
    ¬∃ (f : RingOfDifferences V →+ ℤ) (s : ℤ →+ RingOfDifferences V), f.comp s = .id ℤ := by
  rintro ⟨f, s, h⟩
  simpa [addMonoidHom_eq_zero_IE1 hV f] using DFunLike.congr_fun h 1

end DirectSummand

end FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder

open Polynomial Semiformula

/-- The irrationality of $\sqrt{2}$: $x^2 = 2 y^2$ implies $y = 0$. -/
def Arithmetic.irrationalSqrtTwo : ArithmeticSentence := “∀ x y, x * x = 2 * (y * y) → y = 0”

/-- $\mathsf{IOpen}$ does not prove the irrationality of $\sqrt{2}$.
- [She64]
- [DAq05, §2]
- [Wil78] -/
theorem not_provable_irrationalSqrtTwo_IOpen : 𝗜𝗢𝗽𝗲𝗻 ⊬ Arithmetic.irrationalSqrtTwo := by
  rw [show Arithmetic.irrationalSqrtTwo =
      ∀¹* (“y x. x * x = 2 * (y * y) → y = 0” : ArithmeticSemisentence 2) by
    simp [Arithmetic.irrationalSqrtTwo, allClosure_succ]]
  have := IntegerConstantPolynomial.models_ZRing ℝ
  have hy : 0 ≤ IntegerConstantPolynomial.X ℝ := by
    rw [LeadingCoeffOrder.nonneg_iff]
    simp [IntegerConstantPolynomial.X]
  let x : IntegerConstantPolynomial ℝ :=
    ⟨C (Real.sqrt 2) * Polynomial.X, IntegerConstantPolynomial.mem_iff.mpr ⟨0, by simp⟩⟩
  have hx : 0 ≤ x := by
    rw [LeadingCoeffOrder.nonneg_iff]
    simp [x]
  apply Arithmetic.not_provable_IOpen_allClosure (M := Nonneg (IntegerConstantPolynomial ℝ))
    (e := ![⟨_, hy⟩, ⟨x, hx⟩]) (by simp)
  simp only [Evalb, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
    LogicalConnective.HomClass.map_imply, eval_operator, Matrix.comp₂, Semiterm.val_operator,
    Semiterm.val_bvar, Matrix.cons_val_one, Fin.Fin1.eq_one, Matrix.cons_val_fin_one,
    Tarski.Structure.Mul.mul, Nonneg.mk_mul_mk, Matrix.comp₀, Tarski.Structure.numeral_eq_numeral,
    Arithmetic.numeral_two_eq_two, Matrix.cons_val_zero, Tarski.Structure.eq_iff_eq,
    ORingStructure.zero_eq_zero, Nonneg.mk_eq_zero, LogicalConnective.Prop.arrow_eq, not_imp]
  and_intros
  · have h₁ : C (Real.sqrt 2) * C (Real.sqrt 2) = (2 : ℝ[X]) := by
      rw [← C_mul, Real.mul_self_sqrt (by norm_num)]
      exact map_ofNat C 2
    have h₂ : ((2 : IntegerConstantPolynomial ℝ) : ℝ[X]) = 2 :=
      map_ofNat (IntegerConstantPolynomial ℝ).subtype 2
    apply Subtype.ext
    apply Subtype.ext
    simp only [x, IntegerConstantPolynomial.X, Subring.coe_mul, Nonneg.coe_mul]
    rw [Nonneg.coe_ofNat_foundation, h₂]
    linear_combination (Polynomial.X * Polynomial.X) * h₁
  · apply ne_of_gt
    simpa using IntegerConstantPolynomial.natCast_lt_X (K := ℝ) 0

namespace Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

lemma false_of_mul_self_eq_two_mul_of_bezout {x y : V} (hbez : V↓[ℒₒᵣ] ⊧ bezout) (hy : y ≠ 0)
    (h : x * x = 2 * (y * y)) : False := by
  replace hbez : ∀ x y : V, y ≠ 0 → ∃ z s t, s * y = t * x + z ∧ z ∣ x ∧ z ∣ y := by
    simpa [models_iff, bezout] using hbez
  obtain ⟨z, s, t, e, ⟨x', rfl⟩, ⟨y', rfl⟩⟩ := hbez x y hy
  have hz : z ≠ 0 := by rintro rfl; simp at hy
  have h₁ : x' * x' = 2 * (y' * y') := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hz)
    grind
  have h₂ : s * y' = t * x' + 1 := by
    apply mul_left_cancel₀ hz
    grind
  obtain ⟨a, rfl⟩ : 2 ∣ x' := (two_prime (V := V)).dvd_of_dvd_pow (n := 2) ⟨y' * y', by grind⟩
  have h₃ : y' * y' = 2 * (a * a) := by
    apply mul_left_cancel₀ (two_ne_zero (α := V))
    grind
  obtain ⟨b, rfl⟩ : 2 ∣ y' := (two_prime (V := V)).dvd_of_dvd_pow (n := 2) ⟨a * a, by grind⟩
  have h₄ : (1 + t * (2 * a)) % 2 = 0 := mod_eq_zero_iff_dvd.mpr ⟨s * b, by grind⟩
  simp [mod_add_remove_right_of_dvd (b := t * (2 * a)) (m := 2) ⟨t * a, by grind⟩ (by simp)] at h₄

/-- $\mathsf{IOpen} + \mathrm{Bez}$ proves the irrationality of $\sqrt{2}$.
- [DAq05, §2]
- [Smi92b, Theorem 1.14] -/
theorem provable_irrationalSqrtTwo_IOpen_bezout :
    insert bezout 𝗜𝗢𝗽𝗲𝗻 ⊢ irrationalSqrtTwo := by
  have : 𝗜𝗢𝗽𝗲𝗻 ⪯ insert bezout 𝗜𝗢𝗽𝗲𝗻 := Entailment.WeakerThan.ofSubset (Set.subset_insert _ _)
  have : 𝗘𝗤 ℒₒᵣ ⪯ insert bezout 𝗜𝗢𝗽𝗲𝗻 :=
    Entailment.WeakerThan.trans (𝓣 := 𝗜𝗢𝗽𝗲𝗻) inferInstance inferInstance
  apply complete
  intro (V : Type) _ hV
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := insert bezout 𝗜𝗢𝗽𝗲𝗻) hV
  suffices ∀ x y : V, x * x = 2 * (y * y) → y = 0 by
    simpa [models_iff, irrationalSqrtTwo]
  intro x y h
  by_contra hy
  exact false_of_mul_self_eq_two_mul_of_bezout
    (models_of_mem (T := insert bezout 𝗜𝗢𝗽𝗲𝗻) (Set.mem_insert _ _)) hy h

/-- $\mathsf{IOpen}$ is strictly weaker than $\mathsf{IOpen} + \mathrm{Bez}$.
- [DAq05, §2]
- [Smi92b, Theorem 1.14] -/
theorem IOpen_strictlyWeakerThan_IOpen_bezout : 𝗜𝗢𝗽𝗲𝗻 ⪱ insert bezout 𝗜𝗢𝗽𝗲𝗻 := by
  constructor
  · exact Entailment.WeakerThan.ofSubset (Set.subset_insert _ _)
  · intro h
    exact not_provable_irrationalSqrtTwo_IOpen (h.pbl provable_irrationalSqrtTwo_IOpen_bezout)

end Arithmetic

end FFL.FirstOrder
