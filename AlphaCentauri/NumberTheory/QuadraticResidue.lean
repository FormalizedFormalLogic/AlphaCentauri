module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Functions
public import Mathlib.Data.Nat.Prime.Defs
public import AlphaCentauri.Schemata.BoundedInduction

/-!
# Quadratic residues in $\mathsf{I}\mathsf{E}_1$ and $\mathsf{I}\Delta_0$

Smith's open questions on quadratic residues and on primes of the form $x^2 + ny^2$ over
$\mathsf{I}\mathsf{E}_1$ and $\mathsf{I}\Delta_0$, each stated as the provability of a sentence.
For a prime $q$, the Legendre symbol $(a/q)$ is $1$ exactly when `quadraticResidue` holds of
$a$ and $q$, and $-1$ exactly when $q \nmid a$ and it fails. The questions are open, so the
affirmative answers are axioms, one for each theory, so that neither carries the debt of the
other. With the counting principle $\mathrm{Count}_2(\Delta_0)$ adjoined, $\mathsf{I}\Delta_0$
proves quadratic reciprocity and its supplementary laws.

- [Smi93, §6]
- [Jer10, Theorem 5.7]
- [MM89]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- `a` is a quadratic residue modulo `m`: `a` is coprime to `m` and `x² ≡ a (mod m)` has a
solution.
- [Smi93, §3] -/
def quadraticResidue : ArithmeticSemisentence 2 :=
  “a m. (∀ d, d ∣ a → d ∣ m → d = 1) ∧ ∃ x k, x * x = a + k * m ∨ a = x * x + k * m”

/-- Every odd prime has a quadratic nonresidue.
- [Smi93, §1] -/
def existsQuadraticNonresidue : ArithmeticSentence :=
  “∀ q, !isPrime q → q ≠ 2 → ∃ a, ¬q ∣ a ∧ ¬!quadraticResidue a q”

/-- $\mathsf{I}\mathsf{E}_1$ proves that every odd prime has a quadratic nonresidue. An open
problem.
- [Smi93, §1] -/
axiom provable_existsQuadraticNonresidue_IE1 : 𝗜𝗘₁ ⊢ existsQuadraticNonresidue

/-- $\mathsf{I}\Delta_0$ proves that every odd prime has a quadratic nonresidue. An open problem;
$\mathsf{I}\Delta_0$ with the $\Delta_0$ pigeonhole principle adjoined proves it.
- [Smi93, §3]
- [MM89] -/
axiom provable_existsQuadraticNonresidue_ISigma0 : 𝗜𝚺₀ ⊢ existsQuadraticNonresidue

/-- `-1` has a `k`-th root modulo `m`: `xᵏ ≡ -1 (mod m)` has a solution.
- [Smi93, Lemma 3.2, Question 5.3] -/
def negOneHasRoot (k : ℕ) : ArithmeticSemisentence 1 :=
  let pow (t : ArithmeticSemiterm Empty 2) := (Semiterm.Operator.npow ℒₒᵣ k).operator ![t]
  “m. ∃ x, m ∣ !!(pow #0) + 1”

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
axiom provable_quadraticResidueNegOne_IE1 : 𝗜𝗘₁ ⊢ quadraticResidueNegOne

/-- $\mathsf{I}\Delta_0$ proves that $(-1/q) = 1$ for every prime $q \equiv 1 \pmod 4$. An open
problem; $\mathsf{I}\Delta_0 + \Delta_0\mathrm{EQ}$ and
$\mathsf{I}\Delta_0 + \mathrm{Count}_2(\Delta_0)$ prove it.
- [Smi93, Question 5.1]
- [BI91, Theorem 3.5]
- [Jer10, Theorem 5.7] -/
axiom provable_quadraticResidueNegOne_ISigma0 : 𝗜𝚺₀ ⊢ quadraticResidueNegOne

/-- The converse of [Smi93, Theorem 3.11] for the odd prime `p`: for every odd
prime $q \ne p$, $(p/q) = 1$ implies $(q/p) = 1$ unless $p \equiv q \equiv 3 \pmod 4$, in which
case $(p/q) = -1$ implies $(q/p) = 1$.
- [Smi93, Theorem 3.11, Question 5.2] -/
def quadraticReciprocityConverse (p : ℕ) : ArithmeticSentence :=
  “∀ q, !isPrime q → q ≠ 2 → q ≠ ↑p →
    ((∃ k, ↑p = 4 * k + 3) ∧ (∃ k, q = 4 * k + 3) →
      ¬!quadraticResidue ↑p q → !quadraticResidue q ↑p) ∧
    (¬((∃ k, ↑p = 4 * k + 3) ∧ (∃ k, q = 4 * k + 3)) →
      !quadraticResidue ↑p q → !quadraticResidue q ↑p)”

/-- $\mathsf{I}\mathsf{E}_1$ proves the converse of [Smi93, Theorem 3.11] for each standard odd
prime `p`. An open problem; it follows from quadratic reciprocity, and Jeřábek states that his
proof of quadratic reciprocity and its supplementary laws can be formalized in
$\mathsf{I}\mathsf{E}_1 + \mathrm{Count}_2(\nabla_1)$.
- [Smi93, Question 5.2]
- [Jer21, Chapter 0, §2.2] -/
axiom provable_quadraticReciprocityConverse_IE1 {p : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2) :
    𝗜𝗘₁ ⊢ quadraticReciprocityConverse p

/-- $\mathsf{I}\Delta_0$ proves the converse of [Smi93, Theorem 3.11] for each standard odd prime
`p`. An open problem; $\mathsf{I}\Delta_0 + \mathrm{Count}_2(\Delta_0)$ proves it.
- [Smi93, Question 5.2]
- [Jer10, Theorem 5.7] -/
axiom provable_quadraticReciprocityConverse_ISigma0 {p : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2) :
    𝗜𝚺₀ ⊢ quadraticReciprocityConverse p

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
axiom provable_quadraticReciprocity_IE1 : 𝗜𝗘₁ ⊢ quadraticReciprocity

/-- If $m - 1 = 2^r s$ with $s$ odd, then $-1$ has no $2^r$-th root modulo $m$. Smith prints the
hypothesis as $m = 2^r s$; the case $r = 2$ is $m \equiv 5 \pmod 8$, and the case $r = 1$ is
[Smi93, Lemma 3.2].
- [Smi93, Lemma 3.2, Question 5.3] -/
def noRootNegOne (r : ℕ) : ArithmeticSentence :=
  “∀ m, (∃ k, m = ↑(2 ^ (r + 1)) * k + ↑(2 ^ r + 1)) → ¬!(negOneHasRoot (2 ^ r)) m”

/-- $\mathsf{I}\mathsf{E}_1$ proves that $-1$ has no $2^r$-th root modulo any $m$ with
$m - 1 = 2^r s$, $s$ odd, for each standard $r \ge 2$. An open problem.
- [Smi93, Question 5.3] -/
axiom provable_noRootNegOne_IE1 {r : ℕ} (hr : 2 ≤ r) : 𝗜𝗘₁ ⊢ noRootNegOne r

/-- $\mathsf{I}\Delta_0$ proves that $-1$ has no $2^r$-th root modulo any $m$ with
$m - 1 = 2^r s$, $s$ odd, for each standard $r \ge 2$. An open problem.
- [Smi93, Question 5.3] -/
axiom provable_noRootNegOne_ISigma0 {r : ℕ} (hr : 2 ≤ r) : 𝗜𝚺₀ ⊢ noRootNegOne r

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
axiom provable_squareAddMulSquareIff_IE1 {n : ℕ} {S : Finset ℕ} (hn : 4 < n)
    (hS : ∀ r ∈ S, r < 4 * n)
    (hN : ∀ p : ℕ, p.Prime → ¬p ∣ 4 * n → ((∃ x y, p = x * x + n * y * y) ↔ p % (4 * n) ∈ S)) :
    𝗜𝗘₁ ⊢ squareAddMulSquareIff n S

end FFL.FirstOrder.Arithmetic
