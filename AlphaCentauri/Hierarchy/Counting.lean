module

public import Foundation.FirstOrder.Arithmetic.Definability.PrenexDefinable
public import Mathlib.Data.Finset.Card

/-!
# $\Delta_0$ counting functions

Counting functions of $\Delta_0$-definable sets.

- [DAq05, Question 7.9]
- [HP98, Bibliographical Remarks to Chapter V]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- The counting function $x \mapsto |A \cap [0, x)|$ of a $\Delta_0$-definable set
$A \subseteq \mathbb{N}$ is $\Delta_0$-definable. An open problem.
- [DAq05, Question 7.9]
- [HP98, Bibliographical Remarks to Chapter V] -/
axiom definableFunction_card_of_definablePred {A : ℕ → Prop} [DecidablePred A]
    (hA : 𝚺ᴬ₀.DefinablePred A) :
    𝚺ᴬ₀.DefinableFunction₁ fun x ↦ ((Finset.range x).filter A).card

end FFL.FirstOrder.Arithmetic
