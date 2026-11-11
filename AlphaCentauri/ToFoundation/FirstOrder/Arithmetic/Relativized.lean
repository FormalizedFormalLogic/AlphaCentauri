module

public import Foundation.FirstOrder.Arithmetic.Definability.BoundedDefinable

/-!
# The relativized class $\Sigma_0(\Sigma_n)$

`Sigma0Of n` is the class of predicates on a model of arithmetic generated from the
$\Sigma_n$-definable ones by the Boolean operations, bounded quantification and substitution of
$\Delta_0$-definable bounded functions. At `n = 0` it is the class of $\Delta_0$-definable
predicates.

- [HP98, I.2.2]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V]

/-- The predicates of the class $\Sigma_0(\Sigma_n)$: the $\Sigma_n$-definable predicates closed
under negation, conjunction, bounded universal quantification and substitution of
$\Delta_0$-definable bounded functions.
- [HP98, I.2.2] -/
inductive Sigma0Of (n : ℕ) : {k : ℕ} → ((Fin k → V) → Prop) → Prop
  | atom {k} {P : (Fin k → V) → Prop} : 𝚺ᴬ_[n].Definable P → Sigma0Of n P
  | not {k} {P : (Fin k → V) → Prop} : Sigma0Of n P → Sigma0Of n fun v ↦ ¬P v
  | and {k} {P Q : (Fin k → V) → Prop} :
      Sigma0Of n P → Sigma0Of n Q → Sigma0Of n fun v ↦ P v ∧ Q v
  | ball {k} {P : (Fin (k + 2) → V) → Prop} :
      Sigma0Of n P → Sigma0Of n fun v : Fin (k + 1) → V ↦ ∀ x < v 0, P (x :> v)
  | subst {k l} {P : (Fin k → V) → Prop} {f : Fin k → (Fin l → V) → V} :
      Sigma0Of n P → (∀ i, DefinableBoundedFunction (f i)) → Sigma0Of n fun v ↦ P (f · v)

namespace Sigma0Of

variable {n k l : ℕ} {P Q : (Fin k → V) → Prop}

lemma of_iff (hQ : Sigma0Of n Q) (h : ∀ v, P v ↔ Q v) : Sigma0Of n P := by
  rwa [show P = Q from funext fun v ↦ propext (h v)]

lemma of_Pi (hP : 𝚷ᴬ_[n].Definable P) : Sigma0Of n P :=
  (not <| atom hP.notPi).of_iff fun _ ↦ not_not.symm

lemma of_Sigma0 (hP : 𝚺ᴬ₀.Definable P) : Sigma0Of n P := atom hP.of_zero

lemma or (hP : Sigma0Of n P) (hQ : Sigma0Of n Q) : Sigma0Of n fun v ↦ P v ∨ Q v :=
  (hP.not.and hQ.not).not.of_iff fun _ ↦ by tauto

lemma imp (hP : Sigma0Of n P) (hQ : Sigma0Of n Q) : Sigma0Of n fun v ↦ P v → Q v :=
  (hP.not.or hQ).of_iff fun _ ↦ imp_iff_not_or

variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

lemma retraction (hP : Sigma0Of n P) (f : Fin k → Fin l) :
    Sigma0Of n fun v : Fin l → V ↦ P fun i ↦ v (f i) :=
  hP.subst fun i ↦ .var (f i)

lemma ball_blt {P : (Fin (k + 1) → V) → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction f) (hP : Sigma0Of n P) :
    Sigma0Of n fun v ↦ ∀ x < f v, P (x :> v) := by
  apply ((hP.retraction (0 :> fun i ↦ i.succ.succ)).ball.subst
    (f := f :> fun i v ↦ v i) fun i ↦ by cases i using Fin.cases <;> simp [hf]).of_iff
  intro v
  apply forall₂_congr
  intro x _
  apply iff_of_eq
  congr 1
  funext i
  cases i using Fin.cases <;> simp

lemma bexs_blt {P : (Fin (k + 1) → V) → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction f) (hP : Sigma0Of n P) :
    Sigma0Of n fun v ↦ ∃ x < f v, P (x :> v) :=
  (ball_blt hf hP.not).not.of_iff fun _ ↦ by simp

lemma zero_iff : Sigma0Of 0 P ↔ 𝚺ᴬ₀.Definable P := by
  constructor
  · intro h
    induction h with
    | atom h => exact h
    | not _ ih => exact ih.notSigma.of_zero
    | and _ _ ihP ihQ => exact ihP.and ihQ
    | ball _ ih => simpa using ih.arithmetic_ballCons #0
    | subst _ hf ih => exact ih.arithmetic_bounded_substitution hf
  · exact of_Sigma0

end Sigma0Of

end FFL.FirstOrder.Arithmetic
