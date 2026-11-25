module

public import AlphaCentauri.Bootstrapping.Proof.InductionAxiom
public import AlphaCentauri.Bootstrapping.Proof.AxiomReplacement
public import AlphaCentauri.Bootstrapping.Proof.ReadableSoundness
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Provable
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions
public import Foundation.FirstOrder.Arithmetic.EA.Basic
public import Foundation.FirstOrder.Incompleteness.Consistency
public import Foundation.FirstOrder.Incompleteness.Definability

/-!
# Uniform reflection in a model of $\mathsf{I}\Sigma_{k+1}$

## References

- [HP98, Corollary I.4.34]
- [Bek05, Theorem 7]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic
namespace Bootstrapping

section LocalReflection

open Arithmetic (substNumerals)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {k n : ℕ} {T : ArithmeticTheory} [T.Δ₁]

/-- Below any code `d` there is a set of false blocks, closed under the shift, that contains the
negation of a replacement of each axiom of `T` below `d`. -/
private lemma exists_falseBlock_set (hT : AdmitsFalseBlockReplacement T V k) (d : V) :
    ∃ a : V, IsFormulaSet ℒₒᵣ a ∧ setShift ℒₒᵣ a = a ∧ (∀ e ∈ a, IsFalseBlock k 3 e) ∧
      ∀ p ≤ d, p ∈ T.Δ₁Class →
        ∃ q, neg ℒₒᵣ q ∈ a ∧ Derivable (∅ : Theory ℒₒᵣ) (insert (neg ℒₒᵣ q) ({p} : V)) := by
  obtain ⟨R, hRdef, hRex, hR⟩ := hT
  obtain ⟨s, hs, hsP⟩ := finset_comprehension₁ (Γ := 𝚺) (P := fun p : V ↦ p ∈ T.Δ₁Class)
    (by definability) (d + 1)
  have hsd : ∀ x ∈ s, x ≤ d ∧ x ∈ T.Δ₁Class := by
    intro x hx
    have hx' : x < d + 1 := exp_monotone.mp (lt_of_le_of_lt (exp_le_of_mem hx) hs)
    exact ⟨lt_succ_iff_le.mp hx', (hsP x hx').mp hx⟩
  obtain ⟨F, hF, rfl, hFR⟩ := sigmaOne_skolem
    (R := fun x y : V ↦ ∃ q, y = neg ℒₒᵣ q ∧ R x q) (by definability)
    (s := s) fun x hx ↦ by
      obtain ⟨q, hq⟩ := hRex x (hsd x hx).2
      exact ⟨_, q, rfl, hq⟩
  have hmem : ∀ e ∈ range F, IsFalseBlock k 3 e := by
    intro e he
    obtain ⟨x, hx⟩ := mem_range_iff.mp he
    obtain ⟨q, rfl, hq⟩ := hFR x e hx
    exact (hR x q hq).2
  use range F
  and_intros
  · intro e he
    exact (hmem e he).isFormula
  · apply mem_ext
    intro y
    rw [mem_setShift_iff]
    exact ⟨fun ⟨x, hx, hy⟩ ↦ by rwa [hy, (hmem x hx).isSentence.shift_eq], fun hy ↦
      ⟨y, hy, ((hmem y hy).isSentence.shift_eq).symm⟩⟩
  · exact hmem
  · intro p hp hpT
    obtain ⟨y, hy⟩ := mem_domain_iff.mp ((hsP p (lt_succ_iff_le.mpr hp)).mpr hpT)
    obtain ⟨q, rfl, hq⟩ := hFR p y hy
    use q
    exact ⟨mem_range_iff.mpr ⟨p, hy⟩, (hR p q hq).1⟩

/-- In a model of $\mathsf{I}\Sigma^+_{k+1}$, a prenex $\Pi_{k+3}$ formula holds of
`v` if the internal `T`, each of whose axioms has a replacement by a false block, proves its
instance by the numerals of `v`.
- [HP98, Corollary I.4.34]
- [Bek05, Theorem 7] -/
theorem models_of_provable_substNumerals [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺(k + 1)]
    (hT : AdmitsFalseBlockReplacement T V k) {m : ℕ}
    (φ : ℬ[<, ℒₒᵣ].Prenex 𝚷 (k + 3) Empty m) (v : Fin m → V)
    (h : Provable T (substNumerals (⌜φ.val⌝ : V) v)) : V ⊧/v φ.val := by
  by_contra hV
  let ρ := φ.piInv.sigmaInv
  rw [show φ.val = ∀¹ ∃¹ ρ.val by rw [φ.val_piInv, φ.piInv.val_sigmaInv]] at h hV
  rw [Semiformula.eval_all] at hV
  obtain ⟨a, ha⟩ := not_forall.mp hV
  rw [Semiformula.eval_ex, not_exists] at ha
  obtain ⟨d, hd⟩ := provable_substNumerals_of_provable_substNumerals_all (∃¹ ρ.val) h a
  obtain ⟨A, hA, hAs, hAfb, hAax⟩ := exists_falseBlock_set hT d
  refine not_derivable_of_isFalseBlock (E := fstIdx d ∪ A) (k := k) (D := 3) ?_
    (Derivation.derivable_union_of_replacement hA hAs hAax hd.2)
  intro e he
  rcases mem_cup_iff.mp he with he | he
  · rw [hd.1, mem_singleton_iff] at he
    exact he ▸ isFalseBlock_substNumerals_exs le_rfl ρ (a :> v) ha
  · exact hAfb e he

/-- In a model of $\mathsf{I}\Sigma^+_{k+1}$, the internal $\mathsf{I}\Sigma_n$ is consistent for
$n \le k$.
- [HP98, Corollary I.4.34] -/
lemma consistent_ISigma [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺(k + 1)] (hn : n ≤ k) :
    (𝗜𝚺 n).Consistent V := by
  intro h
  let π : ℬ[<, ℒₒᵣ].Prenex 𝚷 (k + 3) Empty 0 := .falsum
  have hπ : Provable 𝗜𝚺n (⌜π.val⌝ : V) := by
    apply Derivable.toProvable
    apply Derivable.cut (^⊥ : V)
    · apply Derivable.wk (s' := insert (^⊥ : V) ∅) (by simp [-Bounding.Prenex.val_piInv])
      · exact insert_subset_insert_of_subset _ (by simp)
      · have := h.toDerivable
        rwa [Sentence.quote_falsum] at this
    · exact Derivable.verum (by simp [-Bounding.Prenex.val_piInv]) (by simp)
  have := models_of_provable_substNumerals (admitsFalseBlockReplacement_ISigma hn) π
    (![] : Fin 0 → V) (by rwa [substNumerals_quote_of_isEmpty])
  simpa using (Bounding.Prenex.models_falsum ![]).mp this

end LocalReflection

end Bootstrapping
end FFL.FirstOrder.Arithmetic
