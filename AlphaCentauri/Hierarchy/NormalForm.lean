module

public import AlphaCentauri.Hierarchy.Prenex
public import Foundation.FirstOrder.Arithmetic.Prenex

/-!
# Prenex normal form for the strict hierarchy

Prenex normal forms for formulas in the arithmetical hierarchy.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

variable {Γ : Polarity} {s n : ℕ}

section
variable {ξ : Type*}

/-- The formula a `Prenex Γ s` code denotes is a prenex `Γ`-formula of level `s`.

- [HP98, 0.30] -/
@[simp, grind .]
lemma Prenex.val_strictHierarchy {φ : Prenex Γ s ξ n} : StrictHierarchy Γ s φ.val :=
  StrictHierarchy.toPrenex_of_deltaZero φ.matrix.sigma_prop

end

/-- Over a theory extending `𝗜𝚺 s`, every `Hierarchy Γ s` formula is provably equivalent to a
prenex `Γ`-formula of level `s`.

- [HP98, 0.30]
- [HP98, Theorem I.2.5(3)]
- [HP98, Lemma I.2.9] -/
theorem exists_strictHierarchy_of_hierarchy (T : ArithmeticTheory) [𝗜𝚺 s ⪯ T]
    {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
    ∃ ψ : ArithmeticSemisentence n, StrictHierarchy Γ s ψ ∧ T ⊢ ∀¹* (φ 🡘 ψ) := by
  obtain ⟨φ', hφ'⟩ := exists_prenex_of_hierarchy T h
  exact ⟨φ'.val, Prenex.val_strictHierarchy, hφ'⟩

end LO.FirstOrder.Arithmetic
