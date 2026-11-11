module

public import Foundation.FirstOrder.Arithmetic.Schemata
public import AlphaCentauri.Schemata.BoundedInduction
public import AlphaCentauri.ToFoundation.FirstOrder.BinderNotation

/-!
# Regularity principle schemata

The regularity principle for $\varphi(x, y, u)$ says that if for every $w$ some $x > w$ and
$y \le u$ satisfy $\varphi$, then some $y \le u$ satisfies $\varphi(x, y, u)$ for unboundedly many
$x$. Its bounded form with exponent $m$ requires such $x \le r w^m$ for some $r > 1$ and every
$w > 1$. The third variable of $\varphi$ is the bound $u$ and the others are parameters.

- [Cor13, Definition 1.1, Definition 1.6]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- The regularity principle for `φ`.
- [Cor13, Definition 1.1] -/
def regularity (φ : ArithmeticSemiformula ℕ 3) : ArithmeticSentence :=
  .univCl “∀ u, (∀ w, ∃ x, w < x ∧ ∃ y ≤ u, !φ x y u) → ∃ y ≤ u, ∀ w, ∃ x, w < x ∧ !φ x y u”

/-- The regularity principle for the formulas satisfying `Γ`. -/
def regularityOn (Γ : ArithmeticSemiformula ℕ 3 → Prop) : Set ArithmeticSentence :=
  regularity '' {φ | Γ φ}

/-- The bounded regularity principle with exponent `m` for `φ`.
- [Cor13, Definition 1.6] -/
def boundedRegularity (m : ℕ) (φ : ArithmeticSemiformula ℕ 3) : ArithmeticSentence :=
  .univCl “∀ u, (∃ r, 1 < r ∧ ∀ w, 1 < w → ∃ x ≤ r * w ^' m, ∃ y ≤ u, w < x ∧ !φ x y u) →
    ∃ y ≤ u, ∀ w, ∃ x, w < x ∧ !φ x y u”

/-- The bounded regularity principle with exponent `m` for the formulas satisfying `Γ`. -/
def boundedRegularityOn (m : ℕ) (Γ : ArithmeticSemiformula ℕ 3 → Prop) :
    Set ArithmeticSentence :=
  boundedRegularity m '' {φ | Γ φ}

/-- $\mathsf{EA}$ proves the regularity principle for $E_1$ formulas. An open problem.
- [Cor13, Problem 1.5] -/
def RegularityBoundedExistentialWeakerThanElementaryArithmetic : Prop :=
  𝗣𝗔⁻ ∪ regularityOn (IsBoundedExistential 1) ⪯ 𝗘𝗔

/-- $\mathsf{EA}$ proves the bounded regularity principle with exponent $3$ for $E_1$ formulas.
An open problem.
- [Cor13, Problem 1.7] -/
def BoundedRegularityBoundedExistentialWeakerThanElementaryArithmetic : Prop :=
  𝗣𝗔⁻ ∪ boundedRegularityOn 3 (IsBoundedExistential 1) ⪯ 𝗘𝗔

end FFL.FirstOrder.Arithmetic
