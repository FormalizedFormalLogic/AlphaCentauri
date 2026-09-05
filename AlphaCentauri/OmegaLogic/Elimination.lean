module

public import AlphaCentauri.OmegaLogic.Reduction

/-!
# Cut elimination for `Z_∞`

Every cut is removable, at the price of an `ω`-tower over the height: a derivation of ordinal
height `α` and cut rank `c` becomes a cut-free one of height `Ordinal.omegaTower c α`.

The **quantifier** cut rank of `Derivation.cutRank` costs something here. Towsner ranks a cut
formula by `Semiformula.complexity`, and then a `∧`- or `∨`-cut reduces to cuts of *strictly*
smaller rank, which a rank induction absorbs. Counting quantifiers instead, `(φ ⋏ ψ).qr = max φ.qr
ψ.qr`, so the reduction of a `∧`-cut produces cuts of the *same* rank, and a rank induction on
quantifier rank alone would give nothing.

Neither [HP98] nor [Lin97] treats ω-logic; the presentation followed is [Tow20].
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.OmegaLogic

open scoped Ordinal

variable {θ α : Ordinal.{0}} {c : ℕ} {ξ : ArithmeticFormula ℕ} {Γ : Sequent}

namespace Provable

private lemma cutReducibleAux (hθ : 0 < θ) (m : ℕ) :
    ∀ ξ : ArithmeticFormula ℕ, ξ.complexity ≤ m → ξ.qr ≤ c → CutReducible θ c ξ := by
  induction m with
  | zero => exact fun ξ hm _ => cutReducible_of_complexity_zero hθ (Nat.le_zero.mp hm)
  | succ m ih =>
    intro ξ hm hqr
    cases ξ using Semiformula.cases' with
    | hverum => exact cutReducible_of_complexity_zero hθ (by simp)
    | hfalsum => exact cutReducible_of_complexity_zero hθ (by simp)
    | hrel r v => exact cutReducible_of_complexity_zero hθ (by simp)
    | hnrel r v => exact cutReducible_of_complexity_zero hθ (by simp)
    | hand φ ψ =>
      simp only [Semiformula.complexity_and, Semiformula.qr_and] at hm hqr
      exact cut_reduce_and (ih φ (by omega) (by omega)) (ih ψ (by omega) (by omega))
    | hor φ ψ =>
      simp only [Semiformula.complexity_or, Semiformula.qr_or] at hm hqr
      exact cut_reduce_or (ih φ (by omega) (by omega)) (ih ψ (by omega) (by omega))
    | hall φ =>
      simp only [Semiformula.qr_all] at hqr
      exact cut_reduce_all hθ (by omega)
    | hexs φ =>
      simp only [Semiformula.qr_exs] at hqr
      intro Δ γ δ hγ hδ h₁ h₂
      exact cut_reduce_all (φₓ := ∼φ) hθ (by simpa using Nat.lt_of_succ_le hqr) hδ hγ
        (by simpa using h₂) (by simpa using h₁)

/-- **Reducibility of every admissible cut formula.** At cut rank `c`, a cut on a formula of
quantifier rank at most `c` can be traded for a derivation that stays below `ω ^ θ`.

- [Tow20, Theorem 19.7] -/
lemma cut_elim_principal (hθ : 0 < θ) (hqr : ξ.qr ≤ c) : CutReducible θ c ξ :=
  cutReducibleAux hθ ξ.complexity ξ le_rfl hqr

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

end LO.FirstOrder.Arithmetic.OmegaLogic
