module

public import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-!
# Factorial

The factorial function, built by primitive recursion inside a model of $\mathsf{I}\Sigma_1$.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section factorial

def factorial.blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. y = 1”
  succ := .mkSigma “y ih n. y = ih * (n + 1)”

noncomputable def factorial.construction : PR.Construction V factorial.blueprint where
  zero := fun _ ↦ 1
  succ := fun _ n ih ↦ ih * (n + 1)
  zero_defined := .mk fun _ ↦ by simp [factorial.blueprint]
  succ_defined := .mk fun _ ↦ by simp [factorial.blueprint]

/-- - [HP98, Theorem I.1.58(1)] -/
noncomputable def factorial (x : V) : V := factorial.construction.result ![] x

@[simp] lemma factorial_zero : factorial (0 : V) = 1 := by simp [factorial, factorial.construction]

@[simp] lemma factorial_succ (x : V) : factorial (x + 1) = factorial x * (x + 1) := by
  simp [factorial, factorial.construction]

def _root_.FFL.FirstOrder.Arithmetic.factorialDef : 𝚺₁.Semisentence 2 :=
  factorial.blueprint.resultDef

instance factorial_defined : 𝚺₁-Function₁[V] factorial via factorialDef := .mk
  fun v ↦ by
    have : (fun _ : Fin 0 ↦ v 1) = ![] := Subsingleton.elim _ _
    simp [factorial.construction.result_defined_iff, factorialDef, factorial, this]

instance factorial_definable : 𝚺₁-Function₁[V] factorial := factorial_defined.to_definable

@[simp] lemma factorial_pos (x : V) : 0 < factorial x := by
  induction x using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ x ih =>
    rw [factorial_succ]
    exact mul_pos ih (lt_of_le_of_lt (Arithmetic.zero_le x) (lt_add_one x))

private lemma dvd_factorial_aux (x : V) : ∀ d ≤ x, 0 < d → d ∣ factorial x := by
  induction x using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => exact fun d h pos ↦ absurd h (not_le.mpr pos)
  | succ x ih =>
    intro d h pos
    rcases h.lt_or_eq with hlt | rfl
    · rw [factorial_succ]; exact (ih d (le_iff_lt_succ.mpr hlt) pos).mul_right _
    · rw [factorial_succ]; exact dvd_rfl.mul_left _

lemma dvd_factorial {d x : V} (pos : 0 < d) (h : d ≤ x) : d ∣ factorial x :=
  dvd_factorial_aux x d h pos

end factorial

end FFL.FirstOrder.Arithmetic
