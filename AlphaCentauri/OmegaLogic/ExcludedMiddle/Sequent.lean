module

public import AlphaCentauri.OmegaLogic.Provable

/-!
# Excluded middle for sequents in `Z_∞`

A sequent containing a formula and its negation is derivable cut-free.

- [Tow20, Section 14]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.OmegaLogic

namespace Provable

section ExcludedMiddle

section
variable {α : Ordinal.{0}} {Γ : Sequent}

private lemma em_binaryStep {A B C D : ArithmeticFormula ℕ} (hab : A ⋏ B ∈ Γ) (hcd : C ⋎ D ∈ Γ)
    (h₁ : Z∞ ⊢[α, 0] insert A (insert C (insert D Γ)))
    (h₂ : Z∞ ⊢[α, 0] insert B (insert C (insert D Γ))) : Z∞ ⊢[α + 1 + 1, 0] Γ := by
  have h := (andI h₁ h₂).insert_absorb (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hab))
  simpa using h.orI.insert_absorb hcd

private lemma em_quantStep {φₓ ψₓ : ArithmeticSemiformula ℕ 1} (hall : (∀¹ φₓ) ∈ Γ)
    (hexs : (∃¹ ψₓ) ∈ Γ)
    (fam : ∀ n : ℕ, Z∞ ⊢[α, 0]
      insert (ψₓ/[(↑n : ArithmeticTerm ℕ)]) (insert (φₓ/[(↑n : ArithmeticTerm ℕ)]) Γ)) :
    Z∞ ⊢[α + 1 + 1, 0] Γ := by
  have h : ∀ n : ℕ, Z∞ ⊢[α + 1, 0] insert (φₓ/[(↑n : ArithmeticTerm ℕ)]) Γ :=
    fun n => (exI n (fam n)).insert_absorb (Finset.mem_insert_of_mem hexs)
  exact ((allω h).insert_absorb hall).mono_ordinalBound
    (add_le_add_left (Ordinal.iSup_le fun _ => le_rfl) 1)

end

variable {k : ℕ} {φ : ArithmeticFormula ℕ} {Γ : Sequent}

private lemma lemAux (hk : φ.complexity ≤ k) (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    Z∞ ⊢[((2 * k : ℕ) : Ordinal.{0}), 0] Γ := by
  induction k generalizing φ Γ with
  | zero =>
    cases φ using Semiformula.cases' with
    | hverum => exact (verumR hp).mono_ordinalBound zero_le
    | hfalsum => exact (verumR (by simpa using hn)).mono_ordinalBound zero_le
    | hrel r v => exact (axL r v hp (by simpa using hn)).mono_ordinalBound zero_le
    | hnrel r v => exact (axL r v (by simpa using hn) hp).mono_ordinalBound zero_le
    | _ => simp at hk
  | succ k ih =>
    have hcast : ((2 * (k + 1) : ℕ) : Ordinal.{0}) = ((2 * k : ℕ) : Ordinal.{0}) + 1 + 1 := by
      have : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
      rw [this]; push_cast; rfl
    rw [hcast]
    cases φ using Semiformula.cases' with
    | hverum => exact (verumR hp).mono_ordinalBound zero_le
    | hfalsum => exact (verumR (by simpa using hn)).mono_ordinalBound zero_le
    | hrel r v => exact (axL r v hp (by simpa using hn)).mono_ordinalBound zero_le
    | hnrel r v => exact (axL r v (by simpa using hn) hp).mono_ordinalBound zero_le
    | hand φ ψ =>
      simp only [Semiformula.complexity_and] at hk
      have h₁ := ih (φ := φ) (Γ := insert φ (insert (∼φ) (insert (∼ψ) Γ))) (by omega) (by simp)
        (by simp)
      have h₂ := ih (φ := ψ) (Γ := insert ψ (insert (∼φ) (insert (∼ψ) Γ))) (by omega) (by simp)
        (by simp)
      exact em_binaryStep hp (show (∼φ ⋎ ∼ψ) ∈ Γ by simpa using hn) h₁ h₂
    | hor φ ψ =>
      simp only [Semiformula.complexity_or] at hk
      have h₁ := ih (φ := φ) (Γ := insert (∼φ) (insert φ (insert ψ Γ))) (by omega) (by simp)
        (by simp)
      have h₂ := ih (φ := ψ) (Γ := insert (∼ψ) (insert φ (insert ψ Γ))) (by omega) (by simp)
        (by simp)
      exact em_binaryStep (show (∼φ ⋏ ∼ψ) ∈ Γ by simpa using hn) hp h₁ h₂
    | hall ψ =>
      apply em_quantStep hp (show (∃¹ ∼ψ) ∈ Γ by simpa using hn)
      intro n
      have h := ih (φ := ψ/[(↑n : ArithmeticTerm ℕ)])
        (Γ := insert (∼(ψ/[(↑n : ArithmeticTerm ℕ)])) (insert (ψ/[(↑n : ArithmeticTerm ℕ)]) Γ))
        (by simpa using hk) (by simp) (by simp)
      simpa using h
    | hexs ψ =>
      apply em_quantStep (show (∀¹ ∼ψ) ∈ Γ by simpa using hn) hp
      intro n
      have h := ih (φ := ψ/[(↑n : ArithmeticTerm ℕ)])
        (Γ := insert (ψ/[(↑n : ArithmeticTerm ℕ)]) (insert (∼(ψ/[(↑n : ArithmeticTerm ℕ)])) Γ))
        (by simpa using hk) (by simp) (by simp)
      simpa using h

/-- A sequent containing a formula and its negation is derivable cut-free below twice its
complexity.

- [Tow20, Section 14] -/
theorem lem (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    Z∞ ⊢[((2 * φ.complexity : ℕ) : Ordinal.{0}), 0] Γ := lemAux le_rfl hp hn

end ExcludedMiddle

end Provable

end FFL.FirstOrder.Arithmetic.OmegaLogic
