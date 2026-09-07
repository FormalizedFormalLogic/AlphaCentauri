module

public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# The least number schemes `𝗟𝚺` and `𝗟𝚷`

- [HP98, §I.2(a)]
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

open _root_.LO.Entailment

section axioms

/-- The least number scheme for the class `Γ` of `Semiformula ℒₒᵣ ℕ 1`.
- [HP98, §I.2(a)] -/
def LeastNumberScheme (Γ : ArithmeticSemiformula ℕ 1 → Prop) : ArithmeticTheory :=
  { ψ | ∃ φ : ArithmeticSemiformula ℕ 1, Γ φ ∧ ψ = .univCl (leastNumber φ) }

/-- `𝗟 Γ n` is `𝗣𝗔⁻` together with the least number scheme for `Hierarchy Γ n`.
- [HP98, I.2.3] -/
abbrev LeastNumberOnHierarchy (Γ : Polarity) (n : ℕ) : ArithmeticTheory :=
  𝗣𝗔⁻ ∪ LeastNumberScheme (Arithmetic.Hierarchy Γ n)

prefix:max "𝗟 " => LeastNumberOnHierarchy

/-- `𝗟𝚺 n` is `𝗣𝗔⁻` together with the least number scheme for `𝚺-[n]` formulas.
- [HP98, I.2.3] -/
abbrev LSigma (n : ℕ) : ArithmeticTheory := 𝗟 𝚺 n

prefix:max "𝗟𝚺" => LSigma

/-- `𝗟𝚷 n` is `𝗣𝗔⁻` together with the least number scheme for `𝚷-[n]` formulas.
- [HP98, I.2.3] -/
abbrev LPi (n : ℕ) : ArithmeticTheory := 𝗟 𝚷 n

prefix:max "𝗟𝚷" => LPi

variable {C C' : ArithmeticSemiformula ℕ 1 → Prop} {Γ : Polarity}

lemma LeastNumberScheme_subset (h : ∀ {φ : ArithmeticSemiformula ℕ 1}, C φ → C' φ) :
    LeastNumberScheme C ⊆ LeastNumberScheme C' := by
  rintro _ ⟨φ, hφ, rfl⟩; exact ⟨φ, h hφ, rfl⟩

lemma mem_LeastNumberScheme_of_mem {φ : ArithmeticSemiformula ℕ 1} (hφ : C φ) :
    .univCl (leastNumber φ) ∈ LeastNumberScheme C := ⟨φ, hφ, rfl⟩

lemma LeastNumberOnHierarchy_subset_mono {n₁ n₂} (h : n₁ ≤ n₂) : 𝗟 Γ n₁ ⊆ 𝗟 Γ n₂ :=
  Set.union_subset_union_right _ (LeastNumberScheme_subset (fun H ↦ H.mono h))

lemma LeastNumberOnHierarchy_weakerThan_of_le {n₁ n₂} (h : n₁ ≤ n₂) : 𝗟 Γ n₁ ⪯ 𝗟 Γ n₂ :=
  WeakerThan.ofSubset (LeastNumberOnHierarchy_subset_mono h)

instance (Γ : Polarity) (n : ℕ) : 𝗣𝗔⁻ ⪯ 𝗟 Γ n := WeakerThan.ofSubset Set.subset_union_left

instance (Γ : Polarity) (n : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ 𝗟 Γ n :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻ := inferInstance
  WeakerThan.trans this inferInstance

end axioms

end LO.FirstOrder.Arithmetic
