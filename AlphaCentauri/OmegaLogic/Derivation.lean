module

public import AlphaCentauri.OmegaLogic.Truth
public import Mathlib.Data.ENat.Lattice
public import Mathlib.SetTheory.Ordinal.Family

/-!
# Derivations in `Z_∞`

The infinitary Tait calculus `Z_∞` over `ℒₒᵣ`: its sequents, derivations, ordinal height and cut
rank, and soundness.

- [Tow20, Section 13]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic
namespace OmegaLogic

/-- A `Z_∞` sequent: a finite set of arithmetic formulas, read disjunctively.

- [Tow20, Section 13] -/
abbrev Sequent := Finset (ArithmeticFormula ℕ)
/-- Derivations in the one-sided Tait calculus `Z_∞` over `ℒₒᵣ`.

- [Tow20, Section 13] -/
inductive Derivation : Sequent → Type
  | axL {Γ k} (r : (ℒₒᵣ).Rel k) (v) (hp : Semiformula.rel r v ∈ Γ) (hn : Semiformula.nrel r v ∈ Γ) :
    Derivation Γ
  | axTrue {Γ k} (b : Bool) (r : (ℒₒᵣ).Rel k) (v)
    (ht : LitTrue (signedLit b r v)) (hmem : signedLit b r v ∈ Γ) : Derivation Γ
  | verumR {Γ} (h : ⊤ ∈ Γ) : Derivation Γ
  | weak {Δ Γ} (D : Derivation Δ) (h : Δ ⊆ Γ) : Derivation Γ
  | andI {Γ} (φ ψ) (D₁ : Derivation (insert φ Γ)) (D₂ : Derivation (insert ψ Γ)) :
    Derivation (insert (φ ⋏ ψ) Γ)
  | orI {Γ} (φ ψ) (D : Derivation (insert φ (insert ψ Γ))) : Derivation (insert (φ ⋎ ψ) Γ)
  | allω {Γ} (φₓ : ArithmeticSemiformula ℕ 1)
    (Dₓ : (n : ℕ) → Derivation (insert (φₓ/[(↑n : ArithmeticTerm ℕ)]) Γ)) :
    Derivation (insert (∀¹ φₓ) Γ)
  | exI {Γ} (φₓ : ArithmeticSemiformula ℕ 1) (n : ℕ)
    (D : Derivation (insert (φₓ/[(↑n : ArithmeticTerm ℕ)]) Γ)) : Derivation (insert (∃¹ φₓ) Γ)
  | cut {Γ} (φ) (D₁ : Derivation (insert φ Γ)) (D₂ : Derivation (insert (∼φ) Γ)) : Derivation Γ

namespace Derivation

/-- The ordinal height of a `Z_∞` derivation.

- [Tow20, Section 15] -/
noncomputable def ordinalBound : {Γ : Sequent} → Derivation Γ → Ordinal.{0}
  | _, axL _ _ _ _ => 0
  | _, axTrue _ _ _ _ _ => 0
  | _, verumR _ => 0
  | _, weak D _ => D.ordinalBound
  | _, andI _ _ D₁ D₂ => max D₁.ordinalBound D₂.ordinalBound + 1
  | _, orI _ _ D => D.ordinalBound + 1
  | _, allω _ Dₓ => (⨆ n, (Dₓ n).ordinalBound) + 1
  | _, exI _ _ D => D.ordinalBound + 1
  | _, cut _ D₁ D₂ => max D₁.ordinalBound D₂.ordinalBound + 1

/-- The supremum of the quantifier ranks of a derivation's cut formulas, plus one per cut.

- [Tow20, Section 18] -/
noncomputable def cutRank : {Γ : Sequent} → Derivation Γ → ℕ∞
  | _, axL _ _ _ _ => 0
  | _, axTrue _ _ _ _ _ => 0
  | _, verumR _ => 0
  | _, weak D _ => D.cutRank
  | _, andI _ _ D₁ D₂ => max D₁.cutRank D₂.cutRank
  | _, orI _ _ D => D.cutRank
  | _, allω _ Dₓ => ⨆ n, (Dₓ n).cutRank
  | _, exI _ _ D => D.cutRank
  | _, cut φ D₁ D₂ => max (φ.qr + 1) (max D₁.cutRank D₂.cutRank)

/-- The sequent of a `Z_∞` derivation contains a formula true in `ℕ`.

- [Tow20, Section 14] -/
theorem sound {Γ : Sequent} (D : Derivation Γ) : ∃ φ ∈ Γ, LitTrue φ := by
  induction D with
  | axL r v hp hn =>
    rcases litTrue_or_neg (Semiformula.rel r v) with h | h
    · exact ⟨_, hp, h⟩
    · exact ⟨_, hn, by simpa using h⟩
  | axTrue b r v ht hmem => exact ⟨_, hmem, ht⟩
  | verumR h => exact ⟨_, h, litTrue_verum⟩
  | weak D h ih => obtain ⟨φ, hφ, ht⟩ := ih; exact ⟨φ, h hφ, ht⟩
  | andI φ ψ D₁ D₂ ih₁ ih₂ =>
    obtain ⟨χ, hχ, ht⟩ := ih₁
    rcases Finset.mem_insert.mp hχ with rfl | hχ
    · obtain ⟨χ', hχ', ht'⟩ := ih₂
      rcases Finset.mem_insert.mp hχ' with rfl | hχ'
      · exact ⟨_, Finset.mem_insert_self _ _, by simp [ht, ht']⟩
      · exact ⟨_, Finset.mem_insert_of_mem hχ', ht'⟩
    · exact ⟨_, Finset.mem_insert_of_mem hχ, ht⟩
  | orI φ ψ D ih =>
    obtain ⟨χ, hχ, ht⟩ := ih
    rcases Finset.mem_insert.mp hχ with rfl | hχ
    · exact ⟨_, Finset.mem_insert_self _ _, by simp [ht]⟩
    · rcases Finset.mem_insert.mp hχ with rfl | hχ
      · exact ⟨_, Finset.mem_insert_self _ _, by simp [ht]⟩
      · exact ⟨_, Finset.mem_insert_of_mem hχ, ht⟩
  | @allω Γ' φₓ Dₓ ih =>
    by_cases h : ∃ χ ∈ Γ', LitTrue χ
    · obtain ⟨χ, hχ, ht⟩ := h
      exact ⟨χ, Finset.mem_insert_of_mem hχ, ht⟩
    · refine ⟨_, Finset.mem_insert_self _ _, litTrue_all.mpr ?_⟩
      intro n
      obtain ⟨χ, hχ, ht⟩ := ih n
      rcases Finset.mem_insert.mp hχ with rfl | hχ
      · exact ht
      · exact absurd ⟨χ, hχ, ht⟩ h
  | exI φₓ n D ih =>
    obtain ⟨χ, hχ, ht⟩ := ih
    rcases Finset.mem_insert.mp hχ with rfl | hχ
    · exact ⟨_, Finset.mem_insert_self _ _, litTrue_exs.mpr ⟨n, ht⟩⟩
    · exact ⟨_, Finset.mem_insert_of_mem hχ, ht⟩
  | cut φ D₁ D₂ ih₁ ih₂ =>
    rcases litTrue_or_neg φ with h | h
    · obtain ⟨χ, hχ, ht⟩ := ih₂
      rcases Finset.mem_insert.mp hχ with rfl | hχ
      · exact absurd h (litTrue_neg.mp ht)
      · exact ⟨χ, hχ, ht⟩
    · obtain ⟨χ, hχ, ht⟩ := ih₁
      rcases Finset.mem_insert.mp hχ with rfl | hχ
      · exact absurd ht (litTrue_neg.mp h)
      · exact ⟨χ, hχ, ht⟩

end Derivation

end OmegaLogic
end FFL.FirstOrder.Arithmetic
