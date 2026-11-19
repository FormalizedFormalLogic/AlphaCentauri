module

public import Foundation.FirstOrder.Tarski.Basic

/-! # Types over a structure

A type over a structure `M` is a set of formulas in the free variables $\bar x$, with parameters
from `M`, that is finitely satisfied in `M`. The variables $\bar x$ are the bound variables of the
formulas, and the parameters are their free variables, read in `M` by a valuation.
-/

@[expose] public section

namespace FFL.FirstOrder

open Semiformula

variable {L : Language} {M : Type*} [Tarski.Structure L M] {ξ : Type*} {k : ℕ}
  {p q : Set (Semiformula L ξ k)} {b : ξ → M}

/-- The tuple `a` realizes `p` with the parameters read as `b`.
- [Kay91, §8.1] -/
def RealizedBy (p : Set (Semiformula L ξ k)) (b : ξ → M) (a : Fin k → M) : Prop :=
  ∀ φ ∈ p, φ.Eval a b

variable (M) in
/-- `p` is realized in `M` with the parameters read as `b`.
- [Kay91, §8.1] -/
def Realized (p : Set (Semiformula L ξ k)) (b : ξ → M) : Prop :=
  ∃ a : Fin k → M, RealizedBy p b a

variable (M) in
/-- Every finite subset of `p` is realized in `M` with the parameters read as `b`.
- [Kay91, §11.2] -/
def FinitelySatisfied (p : Set (Semiformula L ξ k)) (b : ξ → M) : Prop :=
  ∀ s : Finset (Semiformula L ξ k), ↑s ⊆ p → Realized M (↑s : Set (Semiformula L ξ k)) b

/-- `p` decides every formula in `M` with the parameters read as `b`: some finite subset of `p`
implies the formula or its negation.
- [Kay91, §11.2] -/
def IsCompleteType (p : Set (Semiformula L ξ k)) (b : ξ → M) : Prop :=
  ∀ φ : Semiformula L ξ k, ∃ s : Finset (Semiformula L ξ k), ↑s ⊆ p ∧
    ((∀ a, RealizedBy (↑s : Set (Semiformula L ξ k)) b a → φ.Eval a b) ∨
      ∀ a, RealizedBy (↑s : Set (Semiformula L ξ k)) b a → ¬φ.Eval a b)

lemma RealizedBy.mono {a : Fin k → M} (h : RealizedBy p b a) (hqp : q ⊆ p) : RealizedBy q b a :=
  fun φ hφ ↦ h φ (hqp hφ)

lemma Realized.mono (h : Realized M p b) (hqp : q ⊆ p) : Realized M q b := by
  obtain ⟨a, ha⟩ := h
  use a
  exact ha.mono hqp

lemma Realized.finitelySatisfied (h : Realized M p b) : FinitelySatisfied M p b := by
  intro s hs
  exact h.mono hs

end FFL.FirstOrder
