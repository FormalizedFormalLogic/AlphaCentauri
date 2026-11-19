module

public import AlphaCentauri.ToFoundation.FirstOrder.Type
public import Foundation.FirstOrder.Arithmetic.Basic
public import Foundation.Vorspiel.Computability

/-! # Recursive saturation

A set of arithmetic formulas is recursive when the set of its codes is. A model of arithmetic is
$\Sigma_n$-recursively saturated when it realizes every recursive $\Sigma_n$ type over it with
finitely many parameters, and recursively saturated when it realizes every recursive type over it
with finitely many parameters.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Bounding

/-- The set of codes of the formulas of `Φ` is recursive.
- [Kay91, §11.2] -/
def IsRecursive {ξ : Type*} [Encodable ξ] {k : ℕ} (Φ : Set (ArithmeticSemiformula ξ k)) : Prop :=
  ComputablePred (· ∈ Encodable.encode '' Φ)

/-- Every finitely satisfied recursive $\Sigma_n$ type over `M` with finitely many parameters is
realized in `M`.
- [Kay91, §11.2] -/
def SigmaRecursivelySaturated (n : ℕ) (M : Type*) [ORingStructure M] : Prop :=
  ∀ (k m : ℕ) (Φ : Set (ArithmeticSemiformula (Fin m) k)) (b : Fin m → M),
    (∀ φ ∈ Φ, ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 n φ) → IsRecursive Φ → FinitelySatisfied M Φ b →
      Realized M Φ b

/-- Every finitely satisfied recursive type over `M` with finitely many parameters is realized in
`M`.
- [Kay91, §11.2] -/
def RecursivelySaturated (M : Type*) [ORingStructure M] : Prop :=
  ∀ (k m : ℕ) (Φ : Set (ArithmeticSemiformula (Fin m) k)) (b : Fin m → M),
    IsRecursive Φ → FinitelySatisfied M Φ b → Realized M Φ b

lemma RecursivelySaturated.sigmaRecursivelySaturated {M : Type*} [ORingStructure M]
    (h : RecursivelySaturated M) (n : ℕ) : SigmaRecursivelySaturated n M := by
  intro k m Φ b _ hp hf
  exact h k m Φ b hp hf

end FFL.FirstOrder.Arithmetic
