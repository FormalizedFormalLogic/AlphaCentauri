module

public import Foundation.FirstOrder.Arithmetic.BoundedCollection

/-!
# The collection scheme `𝗕𝚺`

- [HP98, §I.2(a)]
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

section axioms

variable {L : Language} [L.ORing] {ξ : Type*} [DecidableEq ξ]

/-- The collection axiom for `φ`: a witness for `φ` at every `x` below `a` can be bounded by a
single `b`.
- [HP98, §I.2(a)] -/
def collectionAxiom {ξ} (φ : Semiformula L ξ 2) : Formula L ξ :=
  “∀ a, (∀ x < a, ∃ y, !φ x y) → ∃ b, ∀ x < a, ∃ y < b, !φ x y”

/-- The collection scheme for the class `Γ` of `Semiformula ℒₒᵣ ℕ 2`.
- [HP98, §I.2(a)] -/
def CollectionScheme (Γ : ArithmeticSemiformula ℕ 2 → Prop) : ArithmeticTheory :=
  { ψ | ∃ φ : ArithmeticSemiformula ℕ 2, Γ φ ∧ ψ = .univCl (collectionAxiom φ) }

/-- `𝗕𝚺 n` is `𝗣𝗔⁻` together with the collection scheme for `Hierarchy 𝚺 n`.
- [HP98, §I.2(a)] -/
abbrev BSigma (n : ℕ) : ArithmeticTheory := 𝗣𝗔⁻ ∪ CollectionScheme (Arithmetic.Hierarchy 𝚺 n)

prefix:max "𝗕𝚺 " => BSigma

notation "𝗕𝚺₁" => BSigma 1

variable {C C' : ArithmeticSemiformula ℕ 2 → Prop}

lemma CollectionScheme_subset (h : ∀ {φ : ArithmeticSemiformula ℕ 2}, C φ → C' φ) :
    CollectionScheme C ⊆ CollectionScheme C' := by
  rintro _ ⟨φ, hφ, rfl⟩; exact ⟨φ, h hφ, rfl⟩

lemma mem_CollectionScheme_of_mem {φ : ArithmeticSemiformula ℕ 2} (hφ : C φ) :
    .univCl (collectionAxiom φ) ∈ CollectionScheme C := ⟨φ, hφ, rfl⟩

lemma BSigma_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : 𝗕𝚺 s₁ ⊆ 𝗕𝚺 s₂ :=
  Set.union_subset_union_right _ (CollectionScheme_subset (fun H ↦ H.mono h))

lemma BSigma_weakerThan_of_le {s₁ s₂} (h : s₁ ≤ s₂) : 𝗕𝚺 s₁ ⪯ 𝗕𝚺 s₂ :=
  Entailment.WeakerThan.ofSubset (BSigma_subset_mono h)

instance (n : ℕ) : 𝗣𝗔⁻ ⪯ 𝗕𝚺 n := Entailment.WeakerThan.ofSubset Set.subset_union_left

instance (n : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ 𝗕𝚺 n :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

end axioms

section models

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- The reading of the collection axiom in a model of `𝗣𝗔⁻`.
- [HP98, §I.2(a)] -/
lemma models_collectionAxiom_iff (φ : ArithmeticSemiformula ℕ 2) :
    V↓[ℒₒᵣ] ⊧ .univCl (collectionAxiom φ) ↔
      ∀ f : ℕ → V, ∀ a : V, (∀ x < a, ∃ y, φ.Eval ![x, y] f) →
        ∃ b, ∀ x < a, ∃ y < b, φ.Eval ![x, y] f := by
  simp [models_iff, Semiformula.eval_univCl, collectionAxiom, Semiformula.eval_ballLT,
    Semiformula.eval_bexsLT, Semiformula.eval_substs]

end models

end LO.FirstOrder.Arithmetic
