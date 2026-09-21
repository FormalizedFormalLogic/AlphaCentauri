module

public import Foundation.FirstOrder.Arithmetic.Definability.Definable
public import AlphaCentauri.ToFoundation.Hierarchy

/-!
# Definable predicates and formulas evaluated at a fixed valuation

The translation from `HierarchySymbol.Definable` to the evaluation of a `Hierarchy Γ s` formula
with free variables in `ℕ`.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] {Γ : Polarity} {s k : ℕ}

/-- A `Γ-[s]`-definable predicate is the evaluation of a `Hierarchy Γ s` formula at a fixed
valuation. -/
lemma exists_hierarchy_eval_iff {P : (Fin k → V) → Prop} (hP : Γ-[s].Definable P) :
    ∃ (e : ℕ → V) (φ : ArithmeticSemiformula ℕ k), Hierarchy Γ s φ ∧ ∀ v, P v ↔ φ.Eval v e := by
  classical
  rcases hP with ⟨φ, hφ⟩
  have : Inhabited V := Classical.inhabited_of_nonempty'
  exact ⟨φ.val.enumerateFVar, Rew.rewriteMap φ.val.idxOfFVar ▹ φ.val, by simp,
    fun _ ↦ by simp [Semiformula.eval_rewriteMap, hφ.df.iff]⟩

end FFL.FirstOrder.Arithmetic
