module

public import AlphaCentauri.OmegaLogic.CutElimination.Reduction

/-!
# Cut elimination for `Z_∞`

One level of cut elimination lowers the cut rank by one and raises the height to `ω ^ α`.
Consequently a sequent derivable at height `α` and cut rank `c` is derivable cut-free at height
`ω_c(α)`.

- [Tow20, Section 19.7]
- [Tow20, Section 19.9]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic
namespace OmegaLogic

open scoped Ordinal

variable {θ α : Ordinal.{0}} {c : ℕ}

namespace Provable

variable {Γ : Sequent}

/-- A derivation of cut rank at most `c + 1` becomes one of cut rank at most `c`, at height
`ω ^ D.ordinalBound`.

- [Tow20, Theorem 19.7] -/
private lemma cut_elimination_stepAux (D : Derivation Γ) (hcr : D.cutRank ≤ ((c : ℕ∞) + 1)) :
    Z∞ ⊢[ω ^ D.ordinalBound, c] Γ := by
  induction D with
  | @axL Γ k r v hp hn => exact (axL r v hp hn).mono zero_le (Nat.zero_le c)
  | @axTrue Γ k b r v ht hm => exact (axTrue b r v ht hm).mono zero_le (Nat.zero_le c)
  | @verumR Γ h => exact (verumR h).mono zero_le (Nat.zero_le c)
  | @weak Δ Γ D' hsub ih => exact (ih hcr).weakening hsub
  | @andI Γ₁ χ₀ χ₁ D₀ D₁ ih₀ ih₁ =>
    exact (andI (ih₀ ((le_max_left _ _).trans hcr))
      (ih₁ ((le_max_right _ _).trans hcr))).mono_ordinalBound
      (Ordinal.max_opow_add_one_le D₀.ordinalBound D₁.ordinalBound)
  | @orI Γ₁ χ₀ χ₁ D' ih =>
    exact (orI (ih hcr)).mono_ordinalBound (Ordinal.opow_add_one_le_opow_succ D'.ordinalBound)
  | @allω Γ₁ χ Dₓ ih =>
    exact (allω fun n => ih n ((le_iSup (fun m => (Dₓ m).cutRank) n).trans hcr)).mono_ordinalBound
      (Ordinal.iSup_opow_add_one_le fun n => (Dₓ n).ordinalBound)
  | @exI Γ₁ χ n D' ih =>
    exact (exI n (ih hcr)).mono_ordinalBound (Ordinal.opow_add_one_le_opow_succ D'.ordinalBound)
  | @cut Γ₁ χ D₁ D₂ ih₁ ih₂ =>
    have hqr : χ.qr ≤ c := by
      have h : ((χ.qr : ℕ∞) + 1) ≤ ((c : ℕ∞) + 1) := (le_max_left _ _).trans hcr
      have : χ.qr + 1 ≤ c + 1 := by exact_mod_cast h
      omega
    have hlt : ∀ β : Ordinal.{0}, β ≤ max D₁.ordinalBound D₂.ordinalBound →
        ω ^ β < ω ^ (max D₁.ordinalBound D₂.ordinalBound + 1) := fun β hβ =>
      (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (hβ.trans_lt (lt_add_one _))
    obtain ⟨ε, hε, h⟩ := cut_elim_principal (θ := max D₁.ordinalBound D₂.ordinalBound + 1)
      (Ordinal.zero_lt_add_one _) hqr (hlt _ (le_max_left _ _)) (hlt _ (le_max_right _ _))
      (ih₁ ((le_max_left D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr)))
      (ih₂ ((le_max_right D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr)))
    exact h.mono_ordinalBound hε.le

/-- **One level of cut elimination**: lowering the cut rank by one raises the height to `ω ^ α`.

- [Tow20, Theorem 19.7] -/
lemma cut_elimination_step (h : Z∞ ⊢[α, c + 1] Γ) : Z∞ ⊢[ω ^ α, c] Γ := by
  obtain ⟨D, ho, hcr⟩ := h
  refine (cut_elimination_stepAux D ?_).mono_ordinalBound
    (Ordinal.opow_le_opow_right Ordinal.omega0_pos ho)
  refine hcr.trans (le_of_eq ?_)
  push_cast
  rfl

/-- **Cut elimination for `Z_∞`.** A sequent derivable at height `α` and cut rank `c` is derivable
cut-free at the `c`-fold `ω`-tower over `α`.

- [Tow20, Theorem 19.9] -/
theorem cut_elimination (h : Z∞ ⊢[α, c] Γ) : Z∞ ⊢[Ordinal.omegaTower c α, 0] Γ := by
  induction c generalizing α with
  | zero => simpa using h
  | succ c ih => exact ih (cut_elimination_step h)

end Provable

end OmegaLogic
end FFL.FirstOrder.Arithmetic
