module

public import AlphaCentauri.OmegaLogic.Provable

/-!
# Derivability of true formulas in `Z_∞`

A true formula in a sequent is derivable cut-free at height bounded by its complexity.

- [Tow20, Section 14]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic
namespace OmegaLogic

namespace Provable


variable {k : ℕ} {φ : ArithmeticFormula ℕ} {Γ : Sequent}

private lemma of_trueAux (hk : φ.complexity ≤ k) (ht : LitTrue φ) (hmem : φ ∈ Γ) :
    Z∞ ⊢[(k : Ordinal.{0}), 0] Γ := by
  induction k generalizing φ Γ with
  | zero =>
    cases φ using Semiformula.cases' with
    | hverum => exact (verumR hmem).mono_ordinalBound zero_le
    | hfalsum => simp at ht
    | hrel r v => exact (axTrue true r v ht hmem).mono_ordinalBound zero_le
    | hnrel r v => exact (axTrue false r v ht hmem).mono_ordinalBound zero_le
    | _ => simp at hk
  | succ k ih =>
    have hcast : ((k + 1 : ℕ) : Ordinal.{0}) = (k : Ordinal.{0}) + 1 := by push_cast; rfl
    cases φ using Semiformula.cases' with
    | hverum => exact (verumR hmem).mono_ordinalBound zero_le
    | hfalsum => simp at ht
    | hrel r v => exact (axTrue true r v ht hmem).mono_ordinalBound zero_le
    | hnrel r v => exact (axTrue false r v ht hmem).mono_ordinalBound zero_le
    | hand φ ψ =>
      simp only [Semiformula.complexity_and] at hk
      have h₁ := ih (φ := φ) (Γ := insert φ Γ) (by omega) (litTrue_and.mp ht).1 (by simp)
      have h₂ := ih (φ := ψ) (Γ := insert ψ Γ) (by omega) (litTrue_and.mp ht).2 (by simp)
      rw [hcast]
      simpa using (andI h₁ h₂).insert_absorb hmem
    | hor φ ψ =>
      rw [hcast]
      simp only [Semiformula.complexity_or] at hk
      rcases litTrue_or.mp ht with h | h
      · have h₁ := ih (φ := φ) (Γ := insert φ (insert ψ Γ)) (by omega) h (by simp)
        exact h₁.orI.insert_absorb hmem
      · have h₂ := ih (φ := ψ) (Γ := insert φ (insert ψ Γ)) (by omega) h (by simp)
        exact h₂.orI.insert_absorb hmem
    | hall ψ =>
      have h : ∀ n : ℕ, Z∞ ⊢[(k : Ordinal.{0}), 0]
          insert (ψ/[(↑n : ArithmeticTerm ℕ)]) Γ := fun n =>
        ih (by simpa using hk) (litTrue_all.mp ht n) (by simp)
      apply ((allω h).insert_absorb hmem).mono_ordinalBound
      rw [hcast]
      exact add_le_add_left (Ordinal.iSup_le fun _ => le_rfl) 1
    | hexs ψ =>
      obtain ⟨n, hn⟩ := litTrue_exs.mp ht
      have h := ih (φ := ψ/[(↑n : ArithmeticTerm ℕ)])
        (Γ := insert (ψ/[(↑n : ArithmeticTerm ℕ)]) Γ) (by simpa using hk) hn (by simp)
      rw [hcast]
      exact (exI n h).insert_absorb hmem

/-- A true formula in a sequent is derivable cut-free at height bounded by its complexity.

- [Tow20, Section 14] -/
theorem of_true (ht : LitTrue φ) (hmem : φ ∈ Γ) :
    Z∞ ⊢[(φ.complexity : Ordinal.{0}), 0] Γ := of_trueAux le_rfl ht hmem


end Provable

end OmegaLogic
end FFL.FirstOrder.Arithmetic
