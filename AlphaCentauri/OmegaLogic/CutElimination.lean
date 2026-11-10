module

public import AlphaCentauri.OmegaLogic.Basic
public import AlphaCentauri.ToFoundation.Semiformula
public import AlphaCentauri.ToMathlib.Ordinal.Bounds

/-!
# Cut elimination for `Z_∞`

This file proves bound-preserving inversion for disjunctions, conjunctions, and universal formulas
in `Z_∞`, defines cut reducibility below `ω ^ θ` and proves it for each form of cut formula. A
derivation of height `α` and cut rank `c` yields a cut-free derivation of height
`Ordinal.omegaTower c α`.

Neither [HP98] nor [Lin97] treats ω-logic; the presentation followed is [Tow20].
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.OmegaLogic

variable {α : Ordinal.{0}} {c : ℕ} {φ ψ : ArithmeticFormula ℕ}
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
      apply (ih hcr (by grind)).weakening
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
    apply (ih hcr (by grind)).weakening
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
      apply (ih hcr (by grind)).1.weakening
      intro χ; simp only [Finset.mem_insert, Finset.mem_erase]; grind
    · refine (orI ?_).weakening (inv_pull _ (by grind) Γ₀)
      apply (ih hcr (by grind)).2.weakening
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

open scoped Ordinal

variable {θ α β : Ordinal.{0}} {c k : ℕ} {φ ψ : ArithmeticFormula ℕ}
  {φₓ : ArithmeticSemiformula ℕ 1} {Γ : Sequent}

section Frame

/-! ### Moving an `insert` across an `erase`

Subset relations for moving insertion across erasure and union. -/

private lemma eraseIn (a e : ArithmeticFormula ℕ) (s : Sequent) :
    (insert a s).erase e ⊆ insert a (s.erase e) := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  tauto

private lemma eraseOut {a e : ArithmeticFormula ℕ} (h : a ≠ e) (s : Sequent) :
    insert a (s.erase e) ⊆ (insert a s).erase e := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | hx <;> tauto

private lemma frameIn (a e : ArithmeticFormula ℕ) (s t : Sequent) :
    (insert a s).erase e ∪ t ⊆ insert a (s.erase e ∪ t) := by
  grind

private lemma frameOut {a e : ArithmeticFormula ℕ} (h : a ≠ e) (s t : Sequent) :
    insert a (s.erase e ∪ t) ⊆ (insert a s).erase e ∪ t := by
  grind

end Frame

/-- A cut formula is reducible below `ω ^ θ` at rank `c` when cutting two bounded derivations on it
produces another derivation with the same bounds.

- [Tow20, Section 19.5] -/
def CutReducible (θ : Ordinal.{0}) (c : ℕ) (φ : ArithmeticFormula ℕ) : Prop :=
  ∀ {Γ : Sequent} {γ δ : Ordinal.{0}}, γ < ω ^ θ → δ < ω ^ θ →
    Z∞ ⊢[γ, c] insert φ Γ → Z∞ ⊢[δ, c] insert (∼φ) Γ → ∃ ε < ω ^ θ, Z∞ ⊢[ε, c] Γ

namespace CutReducible

lemma neg (h : CutReducible θ c φ) : CutReducible θ c (∼φ) := fun hγ hδ h₁ h₂ =>
  h hδ hγ (by simpa using h₂) h₁

end CutReducible

namespace Provable

/-- A formula of quantifier rank below `c` is cut-reducible at rank `c`.

- [Tow20, Section 19.5] -/
lemma cutReducible_of_qr_lt (hθ : 0 < θ) (h : φ.qr < c) : CutReducible θ c φ :=
  fun hγ hδ h₁ h₂ =>
    ⟨_, Ordinal.add_one_lt_omega0_opow hθ (max_lt hγ hδ), cut φ h h₁ h₂⟩

section Falsum

/-- Erases `⊥` from a cut-free derivation without increasing its height.

- [Tow20, Section 19.2] -/
private lemma remove_falsumAux (D : Derivation Γ) (hcr : D.cutRank ≤ (0 : ℕ∞)) (hmem : ⊥ ∈ Γ) :
    Z∞ ⊢[D.ordinalBound, 0] Γ.erase ⊥ := by
  induction D with
  | @axL Γ k r v hp hn => exact axL r v (by grind) (by grind)
  | @axTrue Γ k b r v ht hm =>
    apply axTrue b r v ht
    cases b <;> · simp only [signedLit] at hm ⊢; grind
  | @verumR Γ h => exact verumR (by grind)
  | @weak Δ Γ D' hsub ih =>
    by_cases hd : (⊥ : ArithmeticFormula ℕ) ∈ Δ
    · exact (ih hcr hd).weakening (Finset.erase_subset_erase _ hsub)
    · refine (show Z∞ ⊢[D'.ordinalBound, 0] Δ from ⟨D', le_rfl, hcr⟩).weakening ?_
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩
  | @andI Γ₁ χ₀ χ₁ D₀ D₁ ih₀ ih₁ =>
    have h₀ : Z∞ ⊢[D₀.ordinalBound, 0] insert χ₀ (Γ₁.erase ⊥) :=
      (ih₀ ((le_max_left _ _).trans hcr) (by grind)).weakening (eraseIn χ₀ ⊥ Γ₁)
    have h₁ : Z∞ ⊢[D₁.ordinalBound, 0] insert χ₁ (Γ₁.erase ⊥) :=
      (ih₁ ((le_max_right _ _).trans hcr) (by grind)).weakening (eraseIn χ₁ ⊥ Γ₁)
    exact (andI h₀ h₁).weakening (eraseOut (by grind) Γ₁)
  | @orI Γ₁ χ₀ χ₁ D' ih =>
    have h : Z∞ ⊢[D'.ordinalBound, 0] insert χ₀ (insert χ₁ (Γ₁.erase ⊥)) :=
      (ih hcr (by grind)).weakening
        ((eraseIn χ₀ ⊥ _).trans (Finset.insert_subset_insert χ₀ (eraseIn χ₁ ⊥ Γ₁)))
    exact (orI h).weakening (eraseOut (by grind) Γ₁)
  | @allω Γ₁ χ Dₓ ih =>
    have h : ∀ n : ℕ, Z∞ ⊢[(Dₓ n).ordinalBound, 0]
        insert (χ/[(↑n : ArithmeticTerm ℕ)]) (Γ₁.erase ⊥) := fun n =>
      (ih n ((le_iSup (fun m => (Dₓ m).cutRank) n).trans hcr) (by grind)).weakening
        (eraseIn _ ⊥ Γ₁)
    exact (allω h).weakening (eraseOut (by grind) Γ₁)
  | @exI Γ₁ χ n D' ih =>
    have h : Z∞ ⊢[D'.ordinalBound, 0] insert (χ/[(↑n : ArithmeticTerm ℕ)]) (Γ₁.erase ⊥) :=
      (ih hcr (by grind)).weakening (eraseIn _ ⊥ Γ₁)
    exact (exI n h).weakening (eraseOut (by grind) Γ₁)
  | @cut Γ₁ ξ D₁ D₂ ih₁ ih₂ => exact absurd ((le_max_left _ _).trans hcr) (by simp)

/-- Removes `⊥` from a cut-free sequent without increasing its height.

- [Tow20, Section 19.2] -/
lemma remove_falsum (h : Z∞ ⊢[α, 0] insert ⊥ Γ) : Z∞ ⊢[α, 0] Γ := by
  obtain ⟨D, ho, hcr⟩ := h
  refine ((remove_falsumAux D hcr (Finset.mem_insert_self _ _)).weakening ?_).mono_ordinalBound ho
  intro x hx
  simp only [Finset.mem_erase, Finset.mem_insert] at hx
  exact hx.2.resolve_left hx.1

lemma cutReducible_verum : CutReducible θ 0 (⊤ : ArithmeticFormula ℕ) :=
  fun _ hδ _ h₂ => ⟨_, hδ, remove_falsum (by simpa using h₂)⟩

lemma cutReducible_falsum : CutReducible θ 0 (⊥ : ArithmeticFormula ℕ) :=
  fun hγ _ h₁ _ => ⟨_, hγ, remove_falsum h₁⟩

end Falsum

section Atom

variable {k₀ : ℕ} {b₀ : Bool} {r₀ : (ℒₒᵣ).Rel k₀} {v₀ : Fin k₀ → ArithmeticTerm ℕ}

/-- Erases a false literal from a cut-free derivation without increasing its height.

- [Tow20, Section 19.2] -/
private lemma remove_false_litAux (hL : ¬LitTrue (signedLit b₀ r₀ v₀)) (D : Derivation Γ)
    (hcr : D.cutRank ≤ (0 : ℕ∞)) (hmem : signedLit b₀ r₀ v₀ ∈ Γ) :
    Z∞ ⊢[D.ordinalBound, 0] Γ.erase (signedLit b₀ r₀ v₀) := by
  have hne : ∀ χ : ArithmeticFormula ℕ, χ.complexity ≠ 0 → χ ≠ signedLit b₀ r₀ v₀ := fun χ h =>
    Semiformula.ne_of_ne_complexity (by cases b₀ <;> simp [signedLit, h])
  induction D with
  | @axL Γ k r v hp hn =>
    by_cases h₁ : signedLit b₀ r₀ v₀ = Semiformula.rel r v
    · refine axTrue false r v ?_ (Finset.mem_erase.mpr ⟨by rw [h₁]; simp [signedLit], hn⟩)
      change LitTrue (Semiformula.nrel r v)
      rw [← Semiformula.neg_rel, litTrue_neg]
      exact h₁ ▸ hL
    · by_cases h₂ : signedLit b₀ r₀ v₀ = Semiformula.nrel r v
      · refine axTrue true r v ?_ (Finset.mem_erase.mpr ⟨by rw [h₂]; simp [signedLit], hp⟩)
        change LitTrue (Semiformula.rel r v)
        by_contra hc
        exact (h₂ ▸ hL) (by rw [← Semiformula.neg_rel, litTrue_neg]; exact hc)
      · exact axL r v (Finset.mem_erase.mpr ⟨fun e => h₁ e.symm, hp⟩)
          (Finset.mem_erase.mpr ⟨fun e => h₂ e.symm, hn⟩)
  | @axTrue Γ k b r v ht hm =>
    exact axTrue b r v ht (Finset.mem_erase.mpr ⟨fun e => hL (e ▸ ht), hm⟩)
  | @verumR Γ h => exact verumR (Finset.mem_erase.mpr ⟨signedLit_ne_verum.symm, h⟩)
  | @weak Δ Γ D' hsub ih =>
    by_cases hd : signedLit b₀ r₀ v₀ ∈ Δ
    · exact (ih hcr hd).weakening (Finset.erase_subset_erase _ hsub)
    · refine (show Z∞ ⊢[D'.ordinalBound, 0] Δ from ⟨D', le_rfl, hcr⟩).weakening ?_
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩
  | @andI Γ₁ χ₀ χ₁ D₀ D₁ ih₀ ih₁ =>
    have hd : signedLit b₀ r₀ v₀ ∈ Γ₁ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hne _ (by simp) e.symm
    have h₀ := (ih₀ ((le_max_left _ _).trans hcr) (Finset.mem_insert_of_mem hd)).weakening
      (eraseIn χ₀ _ Γ₁)
    have h₁ := (ih₁ ((le_max_right _ _).trans hcr) (Finset.mem_insert_of_mem hd)).weakening
      (eraseIn χ₁ _ Γ₁)
    exact (andI h₀ h₁).weakening (eraseOut (hne _ (by simp)) Γ₁)
  | @orI Γ₁ χ₀ χ₁ D' ih =>
    have hd : signedLit b₀ r₀ v₀ ∈ Γ₁ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hne _ (by simp) e.symm
    have h := (ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hd))).weakening
      ((eraseIn χ₀ _ _).trans (Finset.insert_subset_insert χ₀ (eraseIn χ₁ _ Γ₁)))
    exact (orI h).weakening (eraseOut (hne _ (by simp)) Γ₁)
  | @allω Γ₁ χ Dₓ ih =>
    have hd : signedLit b₀ r₀ v₀ ∈ Γ₁ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hne _ (by simp) e.symm
    have h : ∀ n : ℕ, Z∞ ⊢[(Dₓ n).ordinalBound, 0]
        insert (χ/[(↑n : ArithmeticTerm ℕ)]) (Γ₁.erase (signedLit b₀ r₀ v₀)) := fun n =>
      (ih n ((le_iSup (fun m => (Dₓ m).cutRank) n).trans hcr)
        (Finset.mem_insert_of_mem hd)).weakening (eraseIn _ _ Γ₁)
    exact (allω h).weakening (eraseOut (hne _ (by simp)) Γ₁)
  | @exI Γ₁ χ n D' ih =>
    have hd : signedLit b₀ r₀ v₀ ∈ Γ₁ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hne _ (by simp) e.symm
    have h := (ih hcr (Finset.mem_insert_of_mem hd)).weakening (eraseIn _ _ Γ₁)
    exact (exI n h).weakening (eraseOut (hne _ (by simp)) Γ₁)
  | @cut Γ₁ ξ D₁ D₂ ih₁ ih₂ => exact absurd ((le_max_left _ _).trans hcr) (by simp)

/-- Removes a false literal from a cut-free sequent without increasing its height.

- [Tow20, Section 19.2] -/
lemma remove_false_lit (hL : ¬LitTrue (signedLit b₀ r₀ v₀))
    (h : Z∞ ⊢[α, 0] insert (signedLit b₀ r₀ v₀) Γ) : Z∞ ⊢[α, 0] Γ := by
  obtain ⟨D, ho, hcr⟩ := h
  refine ((remove_false_litAux hL D hcr
    (Finset.mem_insert_self _ _)).weakening ?_).mono_ordinalBound ho
  intro x hx
  simp only [Finset.mem_erase, Finset.mem_insert] at hx
  exact hx.2.resolve_left hx.1

variable {Δ : Sequent}

/-- Eliminates an atomic cut against a cut-free derivation with an explicit height bound.

- [Tow20, Section 19.2] -/
private lemma atom_cutAux (r : (ℒₒᵣ).Rel k) (v) (hNC : Z∞ ⊢[β, 0] insert (Semiformula.nrel r v) Γ)
    (D : Derivation Δ) (hcr : D.cutRank ≤ (0 : ℕ∞)) (hmem : (Semiformula.rel r v) ∈ Δ) :
    Z∞ ⊢[β + D.ordinalBound + 1, 0] (Δ.erase (Semiformula.rel r v) ∪ Γ) := by
  induction D with
  | @axL Δ k' r' v' hp hn =>
    have hnn : (Semiformula.nrel r' v' : ArithmeticFormula ℕ) ∈ Δ.erase (Semiformula.rel r v) :=
      Finset.mem_erase.mpr ⟨by simp, hn⟩
    by_cases hrel : (Semiformula.rel r' v' : ArithmeticFormula ℕ) = Semiformula.rel r v
    · have hnrv : (Semiformula.nrel r' v' : ArithmeticFormula ℕ) = Semiformula.nrel r v := by
        rw [← Semiformula.neg_rel r' v', hrel, Semiformula.neg_rel]
      refine (hNC.weakening ?_).mono_ordinalBound (le_self_add.trans (lt_add_one _).le)
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_union_left _ (hnrv ▸ hnn)
      · exact Finset.mem_union_right _ hx
    · exact (axL r' v' (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hrel, hp⟩))
        (Finset.mem_union_left _ hnn)).mono_ordinalBound zero_le
  | @axTrue Δ k' b' r' v' ht hm =>
    by_cases heq : (signedLit b' r' v' : ArithmeticFormula ℕ) = Semiformula.rel r v
    · have hfalse : ¬LitTrue (signedLit false r v) := by
        have : LitTrue (Semiformula.rel r v) := heq ▸ ht
        simpa [signedLit, ← Semiformula.neg_rel] using this
      have hrm := remove_false_lit hfalse
        (show Z∞ ⊢[β, 0] insert (signedLit false r v) Γ by simpa [signedLit] using hNC)
      exact (hrm.weakening Finset.subset_union_right).mono_ordinalBound
        (le_self_add.trans (lt_add_one _).le)
    · exact (axTrue b' r' v' ht (Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨heq, hm⟩))).mono_ordinalBound zero_le
  | @verumR Δ h =>
    exact (verumR (Finset.mem_union_left _
      (Finset.mem_erase.mpr ⟨by simp, h⟩))).mono_ordinalBound zero_le
  | @weak Δ' Δ D' hsub ih =>
    by_cases hd : (Semiformula.rel r v) ∈ Δ'
    · refine (ih hcr hd).weakening ?_
      intro x; simp only [Finset.mem_union, Finset.mem_erase]; grind
    · refine ((show Z∞ ⊢[D'.ordinalBound, 0] Δ' from ⟨D', le_rfl, hcr⟩).weakening
        ?_).mono_ordinalBound (le_add_self.trans (lt_add_one _).le)
      intro x hx
      exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
  | @andI Γ₁ χ₀ χ₁ D₀ D₁ ih₀ ih₁ =>
    have h₀ := (ih₀ ((le_max_left _ _).trans hcr) (by grind)).weakening (frameIn χ₀ _ Γ₁ Γ)
    have h₁ := (ih₁ ((le_max_right _ _).trans hcr) (by grind)).weakening (frameIn χ₁ _ Γ₁ Γ)
    exact ((andI h₀ h₁).weakening (frameOut (by grind) Γ₁ Γ)).mono_ordinalBound
      (Ordinal.max_add_add_one_add_one_le β D₀.ordinalBound D₁.ordinalBound)
  | @orI Γ₁ χ₀ χ₁ D' ih =>
    have h := (ih hcr (by grind)).weakening
      ((frameIn χ₀ _ _ Γ).trans (Finset.insert_subset_insert χ₀ (frameIn χ₁ _ Γ₁ Γ)))
    exact ((orI h).weakening (frameOut (by grind) Γ₁ Γ)).mono_ordinalBound
      (Ordinal.add_add_one_add_one_le β D'.ordinalBound)
  | @allω Γ₁ χ Dₓ ih =>
    have h : ∀ n : ℕ, Z∞ ⊢[β + (Dₓ n).ordinalBound + 1, 0]
        insert (χ/[(↑n : ArithmeticTerm ℕ)]) (Γ₁.erase (Semiformula.rel r v) ∪ Γ) := fun n =>
      (ih n ((le_iSup (fun m => (Dₓ m).cutRank) n).trans hcr) (by grind)).weakening
        (frameIn _ _ Γ₁ Γ)
    exact ((allω h).weakening (frameOut (by grind) Γ₁ Γ)).mono_ordinalBound
      (Ordinal.iSup_add_add_one_add_one_le β fun n => (Dₓ n).ordinalBound)
  | @exI Γ₁ χ n D' ih =>
    have h := (ih hcr (by grind)).weakening (frameIn _ _ Γ₁ Γ)
    exact ((exI n h).weakening (frameOut (by grind) Γ₁ Γ)).mono_ordinalBound
      (Ordinal.add_add_one_add_one_le β D'.ordinalBound)
  | @cut Γ₁ ξ D₁ D₂ ih₁ ih₂ => exact absurd ((le_max_left _ _).trans hcr) (by simp)

/-- Eliminates a cut on an atomic formula between cut-free derivations.

- [Tow20, Section 19.2] -/
lemma atom_cut (r : (ℒₒᵣ).Rel k) (v) (hC : Z∞ ⊢[α, 0] insert (Semiformula.rel r v) Γ)
    (hNC : Z∞ ⊢[β, 0] insert (Semiformula.nrel r v) Γ) : Z∞ ⊢[β + α + 1, 0] Γ := by
  obtain ⟨D, ho, hcr⟩ := hC
  refine ((atom_cutAux r v hNC D hcr (Finset.mem_insert_self _ _)).weakening ?_).mono_ordinalBound
    (by gcongr)
  grind

/-- An atomic formula reduces at rank `0`.

- [Tow20, Section 19.2] -/
lemma cutReducible_rel (hθ : 0 < θ) (r : (ℒₒᵣ).Rel k) (v) :
    CutReducible θ 0 (Semiformula.rel r v) := fun hγ hδ h₁ h₂ =>
  ⟨_, Ordinal.add_one_lt_omega0_opow hθ (Ordinal.add_lt_omega0_opow hδ hγ),
    atom_cut r v h₁ (by simpa using h₂)⟩

/-- A negated atomic formula reduces at rank `0`.

- [Tow20, Section 19.2] -/
lemma cutReducible_nrel (hθ : 0 < θ) (r : (ℒₒᵣ).Rel k) (v) :
    CutReducible θ 0 (Semiformula.nrel r v) := fun hγ hδ h₁ h₂ =>
  ⟨_, Ordinal.add_one_lt_omega0_opow hθ (Ordinal.add_lt_omega0_opow hγ hδ),
    atom_cut r v (by simpa using h₂) h₁⟩

lemma cutReducible_of_complexity_zero (hθ : 0 < θ) (hc : φ.complexity = 0) :
    CutReducible θ c φ := by
  rcases Nat.eq_zero_or_pos c with rfl | hpos
  · cases φ using Semiformula.cases' with
    | hverum => exact cutReducible_verum
    | hfalsum => exact cutReducible_falsum
    | hrel r v => exact cutReducible_rel hθ r v
    | hnrel r v => exact cutReducible_nrel hθ r v
    | _ => simp at hc
  · refine cutReducible_of_qr_lt hθ ?_
    have : φ.qr = 0 := by cases φ using Semiformula.cases' <;> simp_all
    omega

end Atom

section Binary

/-- Reducibility of both conjuncts implies reducibility of their conjunction.

- [Tow20, Theorem 19.5] -/
lemma cut_reduce_and (hφ : CutReducible θ c φ) (hψ : CutReducible θ c ψ) :
    CutReducible θ c (φ ⋏ ψ) := by
  intro Γ γ δ hγ hδ hC hNC
  have hA : Z∞ ⊢[γ, c] insert φ Γ :=
    (hC.and_inv_left (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  have hB : Z∞ ⊢[γ, c] insert ψ Γ :=
    (hC.and_inv_right (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  have hNab : Z∞ ⊢[δ, c] insert (∼φ) (insert (∼ψ) Γ) :=
    ((show Z∞ ⊢[δ, c] insert (∼φ ⋎ ∼ψ) Γ by simpa using hNC).or_inv
      (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  obtain ⟨ε, hε, h⟩ := hφ hγ hδ (hA.weakening (by
    intro x hx; simp only [Finset.mem_insert] at hx ⊢; tauto)) hNab
  exact hψ hγ hε hB h

/-- Reducibility of both disjuncts implies reducibility of their disjunction.

- [Tow20, Theorem 19.5] -/
lemma cut_reduce_or (hφ : CutReducible θ c φ) (hψ : CutReducible θ c ψ) :
    CutReducible θ c (φ ⋎ ψ) := by
  intro Γ γ δ hγ hδ hC hNC
  exact cut_reduce_and hφ.neg hψ.neg hδ hγ (by simpa using hNC) (by simpa using hC)

end Binary

section Quantifier

variable {Δ : Sequent}

/-- Eliminates a universal cut against a bounded derivation with an explicit height bound.

- [Tow20, Theorem 19.6] -/
private lemma cut_reduce_allAux (hqr : φₓ.qr < c)
    (fam : ∀ n : ℕ, Z∞ ⊢[α, c] insert (φₓ/[(↑n : ArithmeticTerm ℕ)]) Γ)
    (D : Derivation Δ) (hcr : D.cutRank ≤ (c : ℕ∞)) (hmem : (∃¹ ∼φₓ) ∈ Δ) :
    Z∞ ⊢[α + D.ordinalBound + 1, c] (Δ.erase (∃¹ ∼φₓ) ∪ Γ) := by
  induction D with
  | @axL Δ k r v hp hn =>
    exact (axL r v (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by grind, hp⟩))
      (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by grind, hn⟩))).mono
      zero_le (Nat.zero_le c)
  | @axTrue Δ k b r v ht hm =>
    refine (axTrue b r v ht (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hm⟩))).mono
      zero_le (Nat.zero_le c)
    cases b <;> · simp only [signedLit]; grind
  | @verumR Δ h =>
    exact (verumR (Finset.mem_union_left _
      (Finset.mem_erase.mpr ⟨by grind, h⟩))).mono zero_le (Nat.zero_le c)
  | @weak Δ' Δ D' hsub ih =>
    by_cases hd : (∃¹ ∼φₓ) ∈ Δ'
    · refine (ih hcr hd).weakening ?_
      intro x; simp only [Finset.mem_union, Finset.mem_erase]; grind
    · refine ((show Z∞ ⊢[D'.ordinalBound, c] Δ' from ⟨D', le_rfl, hcr⟩).weakening
        ?_).mono_ordinalBound (le_add_self.trans (lt_add_one _).le)
      intro x hx
      exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
  | @andI Γ₁ χ₀ χ₁ D₀ D₁ ih₀ ih₁ =>
    have h₀ := (ih₀ ((le_max_left _ _).trans hcr) (by grind)).weakening (frameIn χ₀ _ Γ₁ Γ)
    have h₁ := (ih₁ ((le_max_right _ _).trans hcr) (by grind)).weakening (frameIn χ₁ _ Γ₁ Γ)
    exact ((andI h₀ h₁).weakening (frameOut (by grind) Γ₁ Γ)).mono_ordinalBound
      (Ordinal.max_add_add_one_add_one_le α D₀.ordinalBound D₁.ordinalBound)
  | @orI Γ₁ χ₀ χ₁ D' ih =>
    have h := (ih hcr (by grind)).weakening
      ((frameIn χ₀ _ _ Γ).trans (Finset.insert_subset_insert χ₀ (frameIn χ₁ _ Γ₁ Γ)))
    exact ((orI h).weakening (frameOut (by grind) Γ₁ Γ)).mono_ordinalBound
      (Ordinal.add_add_one_add_one_le α D'.ordinalBound)
  | @allω Γ₁ χ Dₓ ih =>
    have h : ∀ n : ℕ, Z∞ ⊢[α + (Dₓ n).ordinalBound + 1, c]
        insert (χ/[(↑n : ArithmeticTerm ℕ)]) (Γ₁.erase (∃¹ ∼φₓ) ∪ Γ) := fun n =>
      (ih n ((le_iSup (fun m => (Dₓ m).cutRank) n).trans hcr) (by grind)).weakening
        (frameIn _ _ Γ₁ Γ)
    exact ((allω h).weakening (frameOut (by grind) Γ₁ Γ)).mono_ordinalBound
      (Ordinal.iSup_add_add_one_add_one_le α fun n => (Dₓ n).ordinalBound)
  | @exI Γ₁ χ n D' ih =>
    by_cases hhd : (∃¹ χ) = (∃¹ ∼φₓ)
    · obtain rfl := (Semiformula.exs_inj _ _).mp hhd
      rw [Finset.erase_insert_eq_erase]
      have hcut : ((φₓ/[(↑n : ArithmeticTerm ℕ)]) : ArithmeticFormula ℕ).qr < c := by
        simpa using hqr
      have hfam := (fam n).weakening (show insert (φₓ/[(↑n : ArithmeticTerm ℕ)]) Γ
          ⊆ insert (φₓ/[(↑n : ArithmeticTerm ℕ)]) (Γ₁.erase (∃¹ ∼φₓ) ∪ Γ) from by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_union] at hx ⊢; tauto)
      by_cases hd : (∃¹ ∼φₓ) ∈ Γ₁
      · have hP : Z∞ ⊢[α + D'.ordinalBound + 1, c]
            insert (∼(φₓ/[(↑n : ArithmeticTerm ℕ)])) (Γ₁.erase (∃¹ ∼φₓ) ∪ Γ) := by
          apply (ih hcr (Finset.mem_insert_of_mem hd)).weakening
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
          rcases hx with ⟨hne, rfl | hx⟩ | hx
          · left; simp
          · exact Or.inr (Or.inl ⟨hne, hx⟩)
          · exact Or.inr (Or.inr hx)
        apply (cut _ hcut hfam hP).mono_ordinalBound
        gcongr
        exact max_le le_self_add (le_of_eq (add_assoc α D'.ordinalBound 1))
      · have hP : Z∞ ⊢[D'.ordinalBound, c]
            insert (∼(φₓ/[(↑n : ArithmeticTerm ℕ)])) (Γ₁.erase (∃¹ ∼φₓ) ∪ Γ) := by
          refine (show Z∞ ⊢[D'.ordinalBound, c] insert ((∼φₓ)/[(↑n : ArithmeticTerm ℕ)]) Γ₁ from
            ⟨D', le_rfl, hcr⟩).weakening ?_
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with rfl | hx
          · left; simp
          · exact Or.inr (Or.inl ⟨fun e => hd (e ▸ hx), hx⟩)
        apply (cut _ hcut hfam hP).mono_ordinalBound
        gcongr
        exact max_le le_self_add ((lt_add_one _).le.trans le_add_self)
    · have h := (ih hcr (by grind)).weakening (frameIn _ _ Γ₁ Γ)
      exact ((exI n h).weakening (frameOut hhd Γ₁ Γ)).mono_ordinalBound
        (Ordinal.add_add_one_add_one_le α D'.ordinalBound)
  | @cut Γ₁ ξ D₁ D₂ ih₁ ih₂ =>
    have hcξ : ξ.qr < c := qr_lt_of_succ_le ((le_max_left _ _).trans hcr)
    have h₁ := (ih₁ ((le_max_left D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr))
      (Finset.mem_insert_of_mem hmem)).weakening (frameIn ξ _ Γ₁ Γ)
    have h₂ := (ih₂ ((le_max_right D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr))
      (Finset.mem_insert_of_mem hmem)).weakening (frameIn (∼ξ) _ Γ₁ Γ)
    exact (cut ξ hcξ h₁ h₂).mono_ordinalBound
      (Ordinal.max_add_add_one_add_one_le α D₁.ordinalBound D₂.ordinalBound)

/-- A universal formula of quantifier rank below `c` is cut-reducible at rank `c`.

- [Tow20, Theorem 19.6] -/
lemma cut_reduce_all (hθ : 0 < θ) (hqr : φₓ.qr < c) : CutReducible θ c (∀¹ φₓ) := by
  intro Γ γ δ hγ hδ hC hNC
  have fam : ∀ n : ℕ, Z∞ ⊢[γ, c] insert (φₓ/[(↑n : ArithmeticTerm ℕ)]) Γ := fun n =>
    (hC.all_inv (Finset.mem_insert_self _ _) n).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  obtain ⟨D, ho, hcr⟩ : Z∞ ⊢[δ, c] insert (∃¹ ∼φₓ) Γ := by simpa using hNC
  refine ⟨γ + δ + 1, Ordinal.add_one_lt_omega0_opow hθ (Ordinal.add_lt_omega0_opow hγ hδ), ?_⟩
  refine ((cut_reduce_allAux hqr fam D hcr
    (Finset.mem_insert_self _ _)).weakening ?_).mono_ordinalBound (by gcongr)
  grind

end Quantifier

end Provable

open scoped Ordinal

variable {θ α : Ordinal.{0}} {c : ℕ}

namespace Provable

section
variable {ξ : ArithmeticFormula ℕ}

private lemma cutReducibleAux (hθ : 0 < θ) (m : ℕ) :
    ∀ ξ : ArithmeticFormula ℕ, ξ.complexity ≤ m → ξ.qr ≤ c → CutReducible θ c ξ := by
  induction m with
  | zero =>
    intro ξ hm _
    exact cutReducible_of_complexity_zero hθ (Nat.le_zero.mp hm)
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

end

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

end FFL.FirstOrder.Arithmetic.OmegaLogic
