module

public import AlphaCentauri.ToMathlib.OpenPredicate
public import AlphaCentauri.ToMathlib.OpenPredicate.Induction
public import Foundation.FirstOrder.Arithmetic.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.OpenPredicate

/-!
# The degree of an open formula

`Semiterm.degree` bounds the degree of a term in its bound variables, and `Semiformula.degree` that
of the terms of a formula. Over a commutative ordered ring, an open `ℒₒᵣ`-formula of degree at most
`N` in one bound variable defines a predicate determined by the signs of polynomials of degree at
most `N`.
-/

@[expose] public section

open FFL FirstOrder Semiterm Polynomial

namespace FFL.FirstOrder

variable {L : Language} {ξ : Type*}

/-- An upper bound on the degree of a term in its bound variables: a bound variable counts `1`, a
free variable `0`, and a function application the sum over its arguments. -/
def Semiterm.degree {n : ℕ} : Semiterm L ξ n → ℕ
  | #_ => 1
  | &_ => 0
  | func _ v => ∑ i, (v i).degree

/-- The largest `Semiterm.degree` of a term in the formula. -/
def Semiformula.degree {n : ℕ} : Semiformula L ξ n → ℕ
  | ⊤ => 0
  | ⊥ => 0
  | rel _ v => ∑ i, (v i).degree
  | nrel _ v => ∑ i, (v i).degree
  | φ ⋏ ψ => max φ.degree ψ.degree
  | φ ⋎ ψ => max φ.degree ψ.degree
  | ∀¹ φ => φ.degree
  | ∃¹ φ => φ.degree

end FFL.FirstOrder

namespace OpenPredicate

variable {R : Type*} [CommRing R] [LinearOrder R] {ξ : Type*} {n : ℕ}

variable (b : Fin n → R[X]) (hb : ∀ i, (b i).natDegree ≤ 1) (ε : ξ → R)
include hb

lemma exists_polynomial_val (t : ArithmeticSemiterm ξ n) :
    ∃ p : R[X], p.natDegree ≤ t.degree ∧ ∀ x, t.val (fun i ↦ (b i).eval x) ε = p.eval x := by
  induction t with
  | bvar i =>
    use b i
    simpa [Semiterm.degree] using hb i
  | fvar a =>
    use C (ε a)
    simp [Semiterm.degree]
  | func f v ih =>
    cases f
    · use 0
      simp only [Semiterm.degree, natDegree_zero, zero_le, eval_zero, true_and]
      intro x
      rfl
    · use 1
      simp only [Semiterm.degree, natDegree_one, zero_le, eval_one, true_and]
      intro x
      rfl
    · obtain ⟨p, hp, hpv⟩ := ih 0
      obtain ⟨q, hq, hqv⟩ := ih 1
      use p + q
      constructor
      · simp only [Semiterm.degree, Fin.sum_univ_two]
        exact (natDegree_add_le p q).trans (max_le (hp.trans le_self_add) (hq.trans le_add_self))
      · intro x
        simp only [eval_add, ← hpv, ← hqv]
        rfl
    · obtain ⟨p, hp, hpv⟩ := ih 0
      obtain ⟨q, hq, hqv⟩ := ih 1
      use p * q
      constructor
      · simp only [Semiterm.degree, Fin.sum_univ_two]
        exact natDegree_mul_le.trans (add_le_add hp hq)
      · intro x
        simp only [eval_mul, ← hpv, ← hqv]
        rfl

variable [IsStrictOrderedRing R] {N : ℕ}

lemma determinedBySigns_eval_comp {φ : ArithmeticSemiformula ξ n} (hφ : φ.Open)
    (hN : φ.degree ≤ N) : DeterminedBySigns N fun x ↦ φ.Eval (fun i ↦ (b i).eval x) ε := by
  induction φ using Semiformula.rec' with
  | hverum => exact (DeterminedBySigns.eq_zero (p := 0) (by simp)).of_iff fun _ ↦ by simp
  | hfalsum => exact (DeterminedBySigns.eq_zero (p := 0) (by simp)).not.of_iff fun _ ↦ by simp
  | hrel r v =>
    cases r <;>
    · obtain ⟨p, hp, hpv⟩ := exists_polynomial_val b hb ε (v 0)
      obtain ⟨q, hq, hqv⟩ := exists_polynomial_val b hb ε (v 1)
      simp only [Semiformula.degree, Fin.sum_univ_two] at hN
      have hp' := hp.trans (le_self_add.trans hN)
      have hq' := hq.trans (le_add_self.trans hN)
      first
      | exact (DeterminedBySigns.eq hp' hq').of_iff fun x ↦ by rw [← hpv, ← hqv]; rfl
      | exact (DeterminedBySigns.lt hp' hq').of_iff fun x ↦ by rw [← hpv, ← hqv]; rfl
  | hnrel r v =>
    cases r <;>
    · obtain ⟨p, hp, hpv⟩ := exists_polynomial_val b hb ε (v 0)
      obtain ⟨q, hq, hqv⟩ := exists_polynomial_val b hb ε (v 1)
      simp only [Semiformula.degree, Fin.sum_univ_two] at hN
      have hp' := hp.trans (le_self_add.trans hN)
      have hq' := hq.trans (le_add_self.trans hN)
      first
      | exact (DeterminedBySigns.eq hp' hq').not.of_iff fun x ↦ by rw [← hpv, ← hqv]; rfl
      | exact (DeterminedBySigns.lt hp' hq').not.of_iff fun x ↦ by rw [← hpv, ← hqv]; rfl
  | hand φ ψ ihφ ihψ =>
    simp only [Semiformula.degree, max_le_iff] at hN
    simp at hφ
    simpa using (ihφ b hb hφ.1 hN.1).and (ihψ b hb hφ.2 hN.2)
  | hor φ ψ ihφ ihψ =>
    simp only [Semiformula.degree, max_le_iff] at hN
    simp at hφ
    simpa using (ihφ b hb hφ.1 hN.1).or (ihψ b hb hφ.2 hN.2)
  | hall => simp at hφ
  | hexs => simp at hφ

omit hb in
/-- An open formula of degree at most `N` in one bound variable is determined by the signs of
polynomials of degree at most `N`. -/
lemma determinedBySigns_eval {φ : ArithmeticSemiformula ξ 1} (hφ : φ.Open) (hN : φ.degree ≤ N) :
    DeterminedBySigns N fun x ↦ φ.Eval ![x] ε := by
  have := determinedBySigns_eval_comp (fun _ ↦ X) (fun _ ↦ natDegree_X_le) ε hφ hN
  refine this.of_iff fun x ↦ ?_
  rw [show (fun _ : Fin 1 ↦ (X : R[X]).eval x) = ![x] from funext fun i ↦ by simp]


end OpenPredicate
