module

public import Foundation.FirstOrder.Arithmetic.Definability.PrenexDefinable
public import Mathlib.Data.Finset.Card

/-!
# $\Delta_0$ counting functions

Whether the counting function of a $\Delta_0$-definable set is $\Delta_0$-definable is open, a
question of Paris and Wilkie. By a result of Toda the answer is negative unless the polynomial
hierarchy collapses.

- [DAq05, Question 7.9]
- [HP98, Bibliographical Remarks to Chapter V]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- An open problem: the counting function $x \mapsto |A \cap [0, x)|$ of a $\Delta_0$-definable
set $A \subseteq \mathbb{N}$ is $\Delta_0$-definable.
- [DAq05, Question 7.9]
- [HP98, Bibliographical Remarks to Chapter V] -/
axiom definableFunction_card_of_definablePred {A : ℕ → Prop} [DecidablePred A]
    (hA : 𝚺ᴬ₀.DefinablePred A) :
    𝚺ᴬ₀.DefinableFunction₁ fun x ↦ ((Finset.range x).filter A).card

end FFL.FirstOrder.Arithmetic
