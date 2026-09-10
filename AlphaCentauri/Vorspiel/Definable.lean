module

public import Foundation.FirstOrder.Arithmetic.Definability.Definable
public import AlphaCentauri.Vorspiel.Hierarchy

/-!
# Definable predicates and formulas evaluated at a fixed valuation

The translation between `HierarchySymbol.Definable` and the evaluation of a `Hierarchy Γ s`
formula with free variables in `ℕ`, together with the monotonicity of definability in the
hierarchy class.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

namespace HierarchySymbol.Definable

variable {V : Type*} [ORingStructure V] {k : ℕ} {P : (Fin k → V) → Prop}

/-- A predicate definable in a hierarchy class of rank below `s` is `Γ-[s]`-definable. -/
lemma of_lt {C : HierarchySymbol} {Γ : SigmaPiDelta} {s : ℕ} (hP : C.Definable P)
    (h : C.rank < s) : Γ-[s].Definable P := by
  rcases hP with ⟨φ, hφ⟩
  exact .of_sigma_of_pi
    (.mkPolarity (Γ := 𝚺) φ.val (φ.hierarchy_of_lt h) fun _ ↦ hφ.iff.symm)
    (.mkPolarity (Γ := 𝚷) φ.val (φ.hierarchy_of_lt h) fun _ ↦ hφ.iff.symm)

end HierarchySymbol.Definable

variable {V : Type*} [ORingStructure V] {Γ : Polarity} {s k : ℕ}

/-- The evaluation of a `Hierarchy Γ s` formula in two variables at a fixed valuation is a
`Γ-[s]`-definable relation. -/
lemma definableRel_of_hierarchy {φ : ArithmeticSemiformula ℕ 2} (hφ : Hierarchy Γ s φ)
    (e : ℕ → V) : Γ-[s].DefinableRel fun x y ↦ φ.Eval ![x, y] e :=
  (definable_of_hierarchy hφ e).of_iff fun v ↦ by
    have h : ![v 0, v 1] = v := (Matrix.fun_eq_vec_two v).symm
    simp [h]

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
