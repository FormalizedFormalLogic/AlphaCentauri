module

public import Foundation.FirstOrder.Incompleteness.StandardProvability

/-!
# The standard provability predicate

The iterate `Pr_T^n(⊥)` of the standard provability predicate is $\Sigma_1$.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping

variable {T : ArithmeticTheory} [T.Δ₁]

lemma hierarchy_iterate_standardProvability_bot (n : ℕ) :
    Hierarchy 𝚺 1 (T.standardProvability^[n] ⊥) := by
  rcases n with _ | n <;> simp [Function.iterate_succ_apply', standardProvability_def]

end FFL.FirstOrder.Arithmetic
