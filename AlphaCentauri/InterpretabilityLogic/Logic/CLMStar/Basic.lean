module

public import AlphaCentauri.InterpretabilityLogic.Logic.CL.Basic

/-!
# The logic $\mathbf{CL} + \mathsf{M}^*$ and principles of $\Sigma_1$-conservativity

The extension of $\mathbf{CL}$ by the principle $\mathsf{M}^*$, and the principles of
$\Sigma_1$-conservativity of [Ign93, Theorem 12.2] in which the $\Sigma_2$-possibility
$\langle 1 \rangle A$ is replaced by $\theta(A) = \Diamond A \land (A \rhd (A \land \Diamond A))$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- $\theta(A) = \Diamond A \land (A \rhd (A \land \Diamond A))$, the formula equivalent to
$\langle 1 \rangle A$ under the arithmetical interpretation of $\rhd$ as $\Sigma_1$-conservativity.

- [Ign92, Theorem 8.1]
- [Ign93, Theorem 12.1]
-/
abbrev Formula.sigma1Possibility (A : Formula α) : Formula α := ◇A ⋏ (A ▷ (A ⋏ ◇A))

namespace Axioms

variable (A B C : Formula α)

/-- - [Ign91, §10]
- [Ign92, Theorem 8.2]
- [Ign93, Theorem 12.2]
-/
protected abbrev Mstar : Formula α := A ▷ B 🡒 (A ⋏ ◇C) ▷ (B ⋏ ◇C)

/-- The principle $\mathsf{A5}^*$ with $\theta(A)$ in place of $\langle 1 \rangle A$.

- [Ign92, Theorem 8.2]
- [Ign93, Theorem 12.2]
-/
protected abbrev J5star : Formula α := A.sigma1Possibility ▷ A

/-- The principle $\mathsf{P}^*$ with $\theta(A \rhd B)$ in place of $\langle 1 \rangle (A \rhd B)$.

- [Ign92, Theorem 8.2]
- [Ign93, Theorem 12.2]
-/
protected abbrev Pstar : Formula α := (A ▷ B).sigma1Possibility 🡒 A ▷ B

/-- The principle $\mathsf{A2}^*$ with $\theta$ in place of $\langle 1 \rangle$.

- [Ign92, Theorem 8.2]
- [Ign93, Theorem 12.2]
-/
protected abbrev J4star : Formula α := A ▷ B 🡒 A.sigma1Possibility 🡒 B.sigma1Possibility

/-- The principle $\mathsf{C}$ with $\theta(A)$ in place of $\langle 1 \rangle A$.

- [Ign92, Theorem 8.2]
- [Ign93, Theorem 12.2]
-/
protected abbrev C : Formula α := A.sigma1Possibility 🡒 ⊤ ▷ A

/-- The principle $\mathsf{D}$ with $\theta(B)$ in place of $\langle 1 \rangle B$.

- [Ign92, Theorem 8.2]
- [Ign93, Theorem 12.2]
-/
protected abbrev D : Formula α := A ▷ (B ⋏ ◇A) 🡒 ◇A 🡒 B.sigma1Possibility

end Axioms

/-- - [Ign91, §10] -/
abbrev Logic.CLMStar : Logic α := Logic.ofCLAxioms {Axioms.Mstar A B C | (A) (B) (C)}

notation "𝐂𝐋𝐌*" => Logic.CLMStar

end FFL.InterpretabilityLogic
