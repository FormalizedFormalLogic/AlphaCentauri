module

public import Foundation.FirstOrder.Arithmetic.Schema.DeltaInduction

/-!
# The `Δ` induction scheme over the broad hierarchy

`𝗜𝚫⁺ s` is the variant of Foundation's `𝗜𝚫 s` whose `Δ` induction scheme ranges over the broad
hierarchy `ℬ[<, ℒₒᵣ].Hierarchy 𝚺 s` instead of the prenex one.

- [Sla04, §1.2]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

/-- The `Δ` induction scheme for the broad hierarchy `ℬ[<, ℒₒᵣ].Hierarchy 𝚺 s`. -/
abbrev IDeltaOnBroadHierarchy (s : ℕ) : ArithmeticTheory :=
  𝗜𝚺₀ ∪ DeltaInductionScheme (ℬ[<, ℒₒᵣ].Hierarchy 𝚺 s)

prefix:max "𝗜𝚫⁺ " => IDeltaOnBroadHierarchy

lemma IDelta_subset_IDeltaOnBroadHierarchy (s : ℕ) : 𝗜𝚫 s ⊆ 𝗜𝚫⁺ s :=
  Set.union_subset_union_right _ (DeltaInductionScheme_subset (·.hierarchy))

instance IDelta_weakerThan_IDeltaOnBroadHierarchy (s : ℕ) : 𝗜𝚫 s ⪯ 𝗜𝚫⁺ s :=
  WeakerThan.ofSubset (IDelta_subset_IDeltaOnBroadHierarchy s)

instance models_IDeltaOnBroadHierarchy (s : ℕ) : ℕ↓[ℒₒᵣ] ⊧* 𝗜𝚫⁺ s := by
  refine Semantics.ModelsSet.union_iff.mpr ⟨inferInstance, Semantics.ModelsSet.setOf_iff.mpr ?_⟩
  rintro _ ⟨φ, ψ, -, -, rfl⟩
  apply models_deltaInd_iff _ _ |>.mpr
  intro f _ hzero hsucc x
  induction x with
  | zero => exact hzero
  | succ x ih => exact hsucc x ih

end FFL.FirstOrder.Arithmetic
