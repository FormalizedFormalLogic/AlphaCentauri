module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.LeastNumberPrinciple
public import AlphaCentauri.ToMathlib.AddMonoidHomToInt

/-!
# $\mathbb{Z}$ is not a direct summand of a nonstandard model of $\mathsf{I}\mathsf{E}_1$

For a nonstandard model $V$ of $\mathsf{I}\mathsf{E}_1$, every additive homomorphism from the ring
of differences of $V$ to $\mathbb{Z}$ is zero, so $\mathbb{Z}$ is not a direct summand of its
additive group. Carl proved this over $\mathsf{I}\mathsf{E}_2$ and asked whether
$\mathsf{I}\mathsf{E}_1$ suffices.

- [Car16, Theorem 4]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open RingOfDifferences OpenPredicate

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗘₁] (hV : ∃ x : V, ∀ n : ℕ, (n : V) < x)

include hV

/-- Every additive homomorphism from the ring of differences of a nonstandard model of
$\mathsf{I}\mathsf{E}_1$ to $\mathbb{Z}$ is zero.
- [Car16, Lemma 5] -/
lemma addMonoidHom_eq_zero_IE1 (f : RingOfDifferences V →+ ℤ) : f = 0 := by
  apply leastNumberPrinciple_of_models_induction.addMonoidHom_eq_zero
  obtain ⟨x, hx⟩ := hV
  use of x
  intro n
  simpa using of_lt_of.2 (hx n)

/-- $\mathbb{Z}$ is not a direct summand of the additive group of the ring of differences of a
nonstandard model of $\mathsf{I}\mathsf{E}_1$.
- [Car16, Theorem 4] -/
theorem not_int_directSummand_IE1 :
    ¬∃ (f : RingOfDifferences V →+ ℤ) (s : ℤ →+ RingOfDifferences V), f.comp s = .id ℤ := by
  rintro ⟨f, s, h⟩
  simpa [addMonoidHom_eq_zero_IE1 hV f] using DFunLike.congr_fun h 1

end FFL.FirstOrder.Arithmetic
