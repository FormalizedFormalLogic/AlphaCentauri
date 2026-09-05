module

public import AlphaCentauri.OmegaLogic.Basic
public import AlphaCentauri.Vorspiel.Semiformula

/-!
# Inversion for `Z_∞`

This file proves bound-preserving inversion for disjunctions, conjunctions, and universal formulas
in `Z_∞`.

Neither [HP98] nor [Lin97] treats ω-logic; the presentation followed is [Tow20].
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.OmegaLogic

variable {α : Ordinal.{0}} {c k : ℕ} {φ ψ : ArithmeticFormula ℕ}
  {φₓ : ArithmeticSemiformula ℕ 1} {Γ : Sequent}

section Frame

variable (b : ArithmeticFormula ℕ)

private lemma inv_push (a e : ArithmeticFormula ℕ) (s : Sequent) :
    insert b ((insert a s).erase e) ⊆ insert a (insert b (s.erase e)) := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  tauto

private lemma inv_pull {a e : ArithmeticFormula ℕ} (h : a ≠ e) (s : Sequent) :
    insert a (insert b (s.erase e)) ⊆ insert b ((insert a s).erase e) := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | hx <;> tauto

variable {b}

private lemma inv_push₂ (a : ArithmeticFormula ℕ) (s : Sequent) :
    insert φ (insert ψ ((insert a s).erase (φ ⋎ ψ)))
      ⊆ insert a (insert φ (insert ψ (s.erase (φ ⋎ ψ)))) :=
  (Finset.insert_subset_insert φ (inv_push ψ a (φ ⋎ ψ) s)).trans (Finset.insert_comm φ a _).subset

private lemma inv_pull₂ {a : ArithmeticFormula ℕ} (h : a ≠ (φ ⋎ ψ)) (s : Sequent) :
    insert a (insert φ (insert ψ (s.erase (φ ⋎ ψ))))
      ⊆ insert φ (insert ψ ((insert a s).erase (φ ⋎ ψ))) :=
  (Finset.insert_comm a φ _).subset.trans (Finset.insert_subset_insert φ (inv_pull ψ h s))

end Frame

lemma qr_lt_of_succ_le {χ : ArithmeticFormula ℕ} (h : ((χ.qr : ℕ∞) + 1) ≤ (c : ℕ∞)) :
    χ.qr < c := by exact_mod_cast h

namespace Provable

section InversionOr

/-- Replaces a disjunction in a derivation by its two disjuncts while preserving both bounds.

- [Tow20, Section 19.2] -/
private lemma orInvAux (D : Derivation Γ) (hcr : D.cutRank ≤ (c : ℕ∞)) (hmem : (φ ⋎ ψ) ∈ Γ) :
    Z∞ ⊢[D.ordinalBound, c] insert φ (insert ψ (Γ.erase (φ ⋎ ψ))) := by
  induction D with
  | @axL Γ k r v hp hn => exact (axL r v (by grind) (by grind)).mono_cutRank (Nat.zero_le c)
  | @axTrue Γ k b r v ht hm =>
    refine (axTrue b r v ht ?_).mono_cutRank (Nat.zero_le c)
    cases b <;> · simp only [signedLit] at hm ⊢; grind
  | @verumR Γ h => exact (verumR (by grind)).mono_cutRank (Nat.zero_le c)
  | @weak Δ Γ D' hsub ih =>
    by_cases hd : (φ ⋎ ψ) ∈ Δ
    · refine (ih hcr hd).weakening ?_
      intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind
    · refine (show Z∞ ⊢[D'.ordinalBound, c] Δ from ⟨D', le_rfl, hcr⟩).weakening ?_
      intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind
  | @andI Γ₀ φ' ψ' D₁ D₂ ih₁ ih₂ =>
    refine (andI ?_ ?_).weakening (inv_pull₂ (by grind) Γ₀)
    · exact (ih₁ ((le_max_left _ _).trans hcr) (by grind)).weakening (inv_push₂ φ' Γ₀)
    · exact (ih₂ ((le_max_right _ _).trans hcr) (by grind)).weakening (inv_push₂ ψ' Γ₀)
  | @orI Γ₀ φ' ψ' D' ih =>
    by_cases hhd : (φ' ⋎ ψ') = (φ ⋎ ψ)
    · obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp hhd.symm
      by_cases hd : (φ ⋎ ψ) ∈ Γ₀
      · refine ((ih hcr (by simp [hd])).weakening ?_).mono_ordinalBound (lt_add_one _).le
        intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind
      · refine ((show Z∞ ⊢[D'.ordinalBound, c] insert φ (insert ψ Γ₀) from
          ⟨D', le_rfl, hcr⟩).weakening ?_).mono_ordinalBound (lt_add_one _).le
        intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind
    · refine (orI ?_).weakening (inv_pull₂ hhd Γ₀)
      refine (ih hcr (by grind)).weakening ?_
      intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind
  | @allω Γ₀ χ Dₓ ih =>
    refine (allω ?_).weakening (inv_pull₂ (by grind) Γ₀)
    intro n
    exact (ih n ((le_iSup (fun m => (Dₓ m).cutRank) n).trans hcr) (by grind)).weakening
      (inv_push₂ _ Γ₀)
  | @exI Γ₀ χ n D' ih =>
    refine (exI n ?_).weakening (inv_pull₂ (by grind) Γ₀)
    exact (ih hcr (by grind)).weakening (inv_push₂ _ Γ₀)
  | @cut Γ₀ χ D₁ D₂ ih₁ ih₂ =>
    refine cut χ (qr_lt_of_succ_le ((le_max_left _ _).trans hcr)) ?_ ?_
    · exact (ih₁ ((le_max_left D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr))
        (by grind)).weakening (inv_push₂ χ Γ₀)
    · exact (ih₂ ((le_max_right D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr))
        (by grind)).weakening (inv_push₂ (∼χ) Γ₀)

/-- Replaces a disjunction by its two disjuncts while preserving both bounds.

- [Tow20, Section 19.2] -/
@[grind →]
lemma or_inv (hmem : (φ ⋎ ψ) ∈ Γ) (h : Z∞ ⊢[α, c] Γ) :
    Z∞ ⊢[α, c] insert φ (insert ψ (Γ.erase (φ ⋎ ψ))) := by
  obtain ⟨D, ho, hcr⟩ := h
  exact (orInvAux D hcr hmem).mono_ordinalBound ho

end InversionOr

section InversionAll

/-- Replaces a universal formula by a numeral instance while preserving both derivation bounds.

- [Tow20, Section 19.4] -/
private lemma allInvAux (n : ℕ) (D : Derivation Γ) (hcr : D.cutRank ≤ (c : ℕ∞))
    (hmem : (∀¹ φₓ) ∈ Γ) :
    Z∞ ⊢[D.ordinalBound, c] insert (φₓ/[(↑n : ArithmeticTerm ℕ)]) (Γ.erase (∀¹ φₓ)) := by
  induction D with
  | @axL Γ k r v hp hn => exact (axL r v (by grind) (by grind)).mono_cutRank (Nat.zero_le c)
  | @axTrue Γ k b r v ht hm =>
    refine (axTrue b r v ht ?_).mono_cutRank (Nat.zero_le c)
    cases b <;> · simp only [signedLit] at hm ⊢; grind
  | @verumR Γ h => exact (verumR (by grind)).mono_cutRank (Nat.zero_le c)
  | @weak Δ Γ D' hsub ih =>
    by_cases hd : (∀¹ φₓ) ∈ Δ
    · refine (ih hcr hd).weakening ?_
      intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind
    · refine (show Z∞ ⊢[D'.ordinalBound, c] Δ from ⟨D', le_rfl, hcr⟩).weakening ?_
      intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind
  | @andI Γ₀ φ' ψ' D₁ D₂ ih₁ ih₂ =>
    refine (andI ?_ ?_).weakening (inv_pull _ (by grind) Γ₀)
    · exact (ih₁ ((le_max_left _ _).trans hcr) (by grind)).weakening (inv_push _ φ' _ Γ₀)
    · exact (ih₂ ((le_max_right _ _).trans hcr) (by grind)).weakening (inv_push _ ψ' _ Γ₀)
  | @orI Γ₀ φ' ψ' D' ih =>
    refine (orI ?_).weakening (inv_pull _ (by grind) Γ₀)
    refine (ih hcr (by grind)).weakening ?_
    intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind
  | @allω Γ₀ χ Dₓ ih =>
    by_cases hhd : (∀¹ χ) = (∀¹ φₓ)
    · obtain rfl := (Semiformula.all_inj _ _).mp hhd
      have hcrn : (Dₓ n).cutRank ≤ (c : ℕ∞) := (le_iSup (fun m => (Dₓ m).cutRank) n).trans hcr
      have hb : (Dₓ n).ordinalBound ≤ (⨆ m, (Dₓ m).ordinalBound) + 1 :=
        (Ordinal.le_iSup (fun m => (Dₓ m).ordinalBound) n).trans (lt_add_one _).le
      by_cases hd : (∀¹ χ) ∈ Γ₀
      · refine ((ih n hcrn (by simp [hd])).weakening ?_).mono_ordinalBound hb
        intro x; simp only [Finset.mem_insert, Finset.mem_erase]; grind
      · refine ((show Z∞ ⊢[(Dₓ n).ordinalBound, c] insert (χ/[(↑n : ArithmeticTerm ℕ)]) Γ₀ from
          ⟨Dₓ n, le_rfl, hcrn⟩).weakening ?_).mono_ordinalBound hb
        intro x; simp only [Finset.mem_insert, Finset.mem_erase]; grind
    · refine (allω ?_).weakening (inv_pull _ hhd Γ₀)
      intro m
      exact (ih m ((le_iSup (fun j => (Dₓ j).cutRank) m).trans hcr) (by grind)).weakening
        (inv_push _ _ _ Γ₀)
  | @exI Γ₀ χ m D' ih =>
    refine (exI m ?_).weakening (inv_pull _ (by grind) Γ₀)
    exact (ih hcr (by grind)).weakening (inv_push _ _ _ Γ₀)
  | @cut Γ₀ χ D₁ D₂ ih₁ ih₂ =>
    refine cut χ (qr_lt_of_succ_le ((le_max_left _ _).trans hcr)) ?_ ?_
    · exact (ih₁ ((le_max_left D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr))
        (by grind)).weakening (inv_push _ χ _ Γ₀)
    · exact (ih₂ ((le_max_right D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr))
        (by grind)).weakening (inv_push _ (∼χ) _ Γ₀)

/-- Replaces a universal formula by a numeral instance while preserving both bounds.

- [Tow20, Section 19.4] -/
lemma all_inv (hmem : (∀¹ φₓ) ∈ Γ) (n : ℕ) (h : Z∞ ⊢[α, c] Γ) :
    Z∞ ⊢[α, c] insert (φₓ/[(↑n : ArithmeticTerm ℕ)]) (Γ.erase (∀¹ φₓ)) := by
  obtain ⟨D, ho, hcr⟩ := h
  exact (allInvAux n D hcr hmem).mono_ordinalBound ho

end InversionAll

section InversionAnd

/-- Replaces a conjunction by either conjunct while preserving both derivation bounds.

- [Tow20, Section 19.3] -/
private lemma andInvAux (D : Derivation Γ) (hcr : D.cutRank ≤ (c : ℕ∞)) (hmem : (φ ⋏ ψ) ∈ Γ) :
    (Z∞ ⊢[D.ordinalBound, c] insert φ (Γ.erase (φ ⋏ ψ))) ∧
      (Z∞ ⊢[D.ordinalBound, c] insert ψ (Γ.erase (φ ⋏ ψ))) := by
  induction D with
  | @axL Γ k r v hp hn =>
    exact ⟨(axL r v (by grind) (by grind)).mono_cutRank (Nat.zero_le c),
      (axL r v (by grind) (by grind)).mono_cutRank (Nat.zero_le c)⟩
  | @axTrue Γ k b r v ht hm =>
    have h : signedLit b r v ∈ Γ.erase (φ ⋏ ψ) := by
      cases b <;> · simp only [signedLit] at hm ⊢; grind
    exact ⟨(axTrue b r v ht (by simp [h])).mono_cutRank (Nat.zero_le c),
      (axTrue b r v ht (by simp [h])).mono_cutRank (Nat.zero_le c)⟩
  | @verumR Γ h =>
    exact ⟨(verumR (by grind)).mono_cutRank (Nat.zero_le c),
      (verumR (by grind)).mono_cutRank (Nat.zero_le c)⟩
  | @weak Δ Γ D' hsub ih =>
    by_cases hd : (φ ⋏ ψ) ∈ Δ
    · exact ⟨(ih hcr hd).1.weakening (by
        intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind),
        (ih hcr hd).2.weakening (by
        intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind)⟩
    · have h : Z∞ ⊢[D'.ordinalBound, c] Δ := ⟨D', le_rfl, hcr⟩
      exact ⟨h.weakening (by
        intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind),
        h.weakening (by
        intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind)⟩
  | @andI Γ₀ φ' ψ' D₁ D₂ ih₁ ih₂ =>
    have hcr₁ : D₁.cutRank ≤ (c : ℕ∞) := (le_max_left _ _).trans hcr
    have hcr₂ : D₂.cutRank ≤ (c : ℕ∞) := (le_max_right _ _).trans hcr
    by_cases hhd : (φ' ⋏ ψ') = (φ ⋏ ψ)
    · obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp hhd.symm
      constructor
      · have hb : D₁.ordinalBound ≤ max D₁.ordinalBound D₂.ordinalBound + 1 :=
          (le_max_left _ _).trans (lt_add_one _).le
        by_cases hd : (φ ⋏ ψ) ∈ Γ₀
        · refine ((ih₁ hcr₁ (by simp [hd])).1.weakening ?_).mono_ordinalBound hb
          intro x; simp only [Finset.mem_insert, Finset.mem_erase]; grind
        · refine ((show Z∞ ⊢[D₁.ordinalBound, c] insert φ Γ₀ from
            ⟨D₁, le_rfl, hcr₁⟩).weakening ?_).mono_ordinalBound hb
          intro x; simp only [Finset.mem_insert, Finset.mem_erase]; grind
      · have hb : D₂.ordinalBound ≤ max D₁.ordinalBound D₂.ordinalBound + 1 :=
          (le_max_right _ _).trans (lt_add_one _).le
        by_cases hd : (φ ⋏ ψ) ∈ Γ₀
        · refine ((ih₂ hcr₂ (by simp [hd])).2.weakening ?_).mono_ordinalBound hb
          intro x; simp only [Finset.mem_insert, Finset.mem_erase]; grind
        · refine ((show Z∞ ⊢[D₂.ordinalBound, c] insert ψ Γ₀ from
            ⟨D₂, le_rfl, hcr₂⟩).weakening ?_).mono_ordinalBound hb
          intro x; simp only [Finset.mem_insert, Finset.mem_erase]; grind
    · constructor
      · refine (andI ?_ ?_).weakening (inv_pull _ hhd Γ₀)
        · exact (ih₁ hcr₁ (by grind)).1.weakening (inv_push _ φ' _ Γ₀)
        · exact (ih₂ hcr₂ (by grind)).1.weakening (inv_push _ ψ' _ Γ₀)
      · refine (andI ?_ ?_).weakening (inv_pull _ hhd Γ₀)
        · exact (ih₁ hcr₁ (by grind)).2.weakening (inv_push _ φ' _ Γ₀)
        · exact (ih₂ hcr₂ (by grind)).2.weakening (inv_push _ ψ' _ Γ₀)
  | @orI Γ₀ φ' ψ' D' ih =>
    constructor
    · refine (orI ?_).weakening (inv_pull _ (by grind) Γ₀)
      refine (ih hcr (by grind)).1.weakening ?_
      intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind
    · refine (orI ?_).weakening (inv_pull _ (by grind) Γ₀)
      refine (ih hcr (by grind)).2.weakening ?_
      intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind
  | @allω Γ₀ χ Dₓ ih =>
    constructor
    · refine (allω ?_).weakening (inv_pull _ (by grind) Γ₀)
      intro m
      exact (ih m ((le_iSup (fun j => (Dₓ j).cutRank) m).trans hcr) (by grind)).1.weakening
        (inv_push _ _ _ Γ₀)
    · refine (allω ?_).weakening (inv_pull _ (by grind) Γ₀)
      intro m
      exact (ih m ((le_iSup (fun j => (Dₓ j).cutRank) m).trans hcr) (by grind)).2.weakening
        (inv_push _ _ _ Γ₀)
  | @exI Γ₀ χ m D' ih =>
    constructor
    · refine (exI m ?_).weakening (inv_pull _ (by grind) Γ₀)
      exact (ih hcr (by grind)).1.weakening (inv_push _ _ _ Γ₀)
    · refine (exI m ?_).weakening (inv_pull _ (by grind) Γ₀)
      exact (ih hcr (by grind)).2.weakening (inv_push _ _ _ Γ₀)
  | @cut Γ₀ χ D₁ D₂ ih₁ ih₂ =>
    have hc : χ.qr < c := qr_lt_of_succ_le ((le_max_left _ _).trans hcr)
    have hcr₁ : D₁.cutRank ≤ (c : ℕ∞) :=
      (le_max_left D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr)
    have hcr₂ : D₂.cutRank ≤ (c : ℕ∞) :=
      (le_max_right D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr)
    constructor
    · exact cut χ hc ((ih₁ hcr₁ (by grind)).1.weakening (inv_push _ χ _ Γ₀))
        ((ih₂ hcr₂ (by grind)).1.weakening (inv_push _ (∼χ) _ Γ₀))
    · exact cut χ hc ((ih₁ hcr₁ (by grind)).2.weakening (inv_push _ χ _ Γ₀))
        ((ih₂ hcr₂ (by grind)).2.weakening (inv_push _ (∼χ) _ Γ₀))

/-- Replaces a conjunction by its left conjunct while preserving both bounds.

- [Tow20, Section 19.3] -/
@[grind →]
lemma and_inv_left (hmem : (φ ⋏ ψ) ∈ Γ) (h : Z∞ ⊢[α, c] Γ) :
    Z∞ ⊢[α, c] insert φ (Γ.erase (φ ⋏ ψ)) := by
  obtain ⟨D, ho, hcr⟩ := h
  exact (andInvAux D hcr hmem).1.mono_ordinalBound ho

/-- Replaces a conjunction by its right conjunct while preserving both bounds.

- [Tow20, Section 19.3] -/
@[grind →]
lemma and_inv_right (hmem : (φ ⋏ ψ) ∈ Γ) (h : Z∞ ⊢[α, c] Γ) :
    Z∞ ⊢[α, c] insert ψ (Γ.erase (φ ⋏ ψ)) := by
  obtain ⟨D, ho, hcr⟩ := h
  exact (andInvAux D hcr hmem).2.mono_ordinalBound ho

end InversionAnd

end Provable

end LO.FirstOrder.Arithmetic.OmegaLogic
