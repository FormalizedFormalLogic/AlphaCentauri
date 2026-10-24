module

public import Foundation.Logic.Entailment
public import Foundation.Propositional.Entailment.Cl
public import Foundation.Meta.ClProver

/-!
# Consistency as a simp lemma, and conjunctions of vectors

`simp` cannot close a goal `Consistent 𝓢` on its own, even when an instance is available; this
records `Consistent 𝓢` as a simp lemma whenever such an instance can be synthesized.

Introduction and elimination of `Matrix.conj` in a minimal entailment system.
-/

@[expose] public section

namespace FFL.Entailment

variable {F : Type*} {S : Type*} [Entailment S F]

@[simp] lemma consistent_eq_true (𝓢 : S) [h : Consistent 𝓢] : Consistent 𝓢 = True :=
  eq_true h

section matrixConj

variable [LogicalConnective F] [LogicalNeutral F] {𝓢 : S}

lemma matrixConj_elim [Entailment.Minimal 𝓢] :
    ∀ {k : ℕ} (v : Fin k → F) (i : Fin k), 𝓢 ⊢ Matrix.conj v 🡒 v i
  | _ + 1, v, i => by
    cases i using Fin.cases with
    | zero => exact and₁
    | succ i => exact C_trans and₂ <| matrixConj_elim (Matrix.vecTail v) i

lemma matrixConj_intro [Entailment.Minimal 𝓢] {φ : F} :
    ∀ {k : ℕ} {v : Fin k → F}, (∀ i, 𝓢 ⊢ φ 🡒 v i) → 𝓢 ⊢ φ 🡒 Matrix.conj v
  | 0, _, _ => C_of_conseq verum
  | _ + 1, v, h => right_K_intro (h 0) <| matrixConj_intro (v := Matrix.vecTail v) fun i ↦ h i.succ

lemma matrixConj_imp_matrixConj [Entailment.Cl 𝓢] {φ : F} {k : ℕ} {v u : Fin k → F}
    (h : ∀ i, 𝓢 ⊢ φ 🡒 v i 🡒 u i) : 𝓢 ⊢ φ 🡒 Matrix.conj v 🡒 Matrix.conj u := by
  have : 𝓢 ⊢ φ ⋏ Matrix.conj v 🡒 Matrix.conj u := matrixConj_intro fun i ↦ by
    have := matrixConj_elim (𝓢 := 𝓢) v i
    cl_prover [this, h i]
  cl_prover [this]

end matrixConj

end FFL.Entailment
