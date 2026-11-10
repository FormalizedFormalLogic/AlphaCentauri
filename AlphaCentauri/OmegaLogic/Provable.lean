module

public import AlphaCentauri.OmegaLogic.Derivation

/-!
# Bounded derivability in `Z_∞`

`Z∞ ⊢[α, c] Γ` for ordinal height at most `α` and cut rank at most `c`, with its structural rules,
logical rules, and soundness.

- [Tow20, Section 13]
- [Tow20, Section 14]
- [Tow20, Section 18]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.OmegaLogic

/-- `Z∞ ⊢[α, c] Γ` means that `Γ` has a derivation of height at most `α` and cut rank at most `c`.

- [Tow20, Section 18] -/
def Provable (α : Ordinal.{0}) (c : ℕ) (Γ : Sequent) : Prop :=
  ∃ D : Derivation Γ, D.ordinalBound ≤ α ∧ D.cutRank ≤ (c : ℕ∞)

@[inherit_doc] scoped notation:45 "Z∞" " ⊢[" α ", " c "] " Γ:46 => Provable α c Γ

namespace Provable

section

variable {α β : Ordinal.{0}} {c c' k : ℕ} {φ ψ : ArithmeticFormula ℕ}
  {φₓ : ArithmeticSemiformula ℕ 1} {Γ : Sequent}

/-- Both bounds may be relaxed.

- [Tow20, Section 18] -/
lemma mono (hα : α ≤ β) (hc : c ≤ c') : Z∞ ⊢[α, c] Γ → Z∞ ⊢[β, c'] Γ := by
  rintro ⟨D, ho, hcr⟩
  exact ⟨D, ho.trans hα, hcr.trans (by exact_mod_cast hc)⟩

lemma mono_ordinalBound (h : α ≤ β) : Z∞ ⊢[α, c] Γ → Z∞ ⊢[β, c] Γ := mono h le_rfl

lemma mono_cutRank (h : c ≤ c') : Z∞ ⊢[α, c] Γ → Z∞ ⊢[α, c'] Γ := mono le_rfl h

section
variable {Δ : Sequent}

/-- Weakening preserves both derivation bounds.

- [Tow20, Section 14] -/
lemma weakening (h : Γ ⊆ Δ) : Z∞ ⊢[α, c] Γ → Z∞ ⊢[α, c] Δ := by
  rintro ⟨D, ho, hcr⟩
  exact ⟨D.weak h, by simpa [Derivation.ordinalBound] using ho,
    by simpa [Derivation.cutRank] using hcr⟩

end

lemma insert_absorb (h : Z∞ ⊢[α, c] insert φ Γ) (hmem : φ ∈ Γ) : Z∞ ⊢[α, c] Γ := by
  rwa [Finset.insert_eq_self.mpr hmem] at h

/-- The identity axiom.

- [Tow20, Section 13] -/
lemma axL (r : (ℒₒᵣ).Rel k) (v) (hp : Semiformula.rel r v ∈ Γ) (hn : Semiformula.nrel r v ∈ Γ) :
    Z∞ ⊢[0, 0] Γ :=
  ⟨Derivation.axL r v hp hn, by simp [Derivation.ordinalBound], by simp [Derivation.cutRank]⟩

/-- The ω-logic leaf: a true literal closes its sequent.

- [Tow20, Section 13] -/
lemma axTrue (b : Bool) (r : (ℒₒᵣ).Rel k) (v) (ht : LitTrue (signedLit b r v))
    (hmem : signedLit b r v ∈ Γ) : Z∞ ⊢[0, 0] Γ :=
  ⟨Derivation.axTrue b r v ht hmem, by simp [Derivation.ordinalBound], by simp [Derivation.cutRank]⟩

/-- `⊤` closes a sequent.

- [Tow20, Section 13] -/
lemma verumR (h : ⊤ ∈ Γ) : Z∞ ⊢[0, 0] Γ :=
  ⟨Derivation.verumR h, by simp [Derivation.ordinalBound], by simp [Derivation.cutRank]⟩

/-- The `∧`-rule.

- [Tow20, Section 13] -/
lemma andI (hφ : Z∞ ⊢[α, c] insert φ Γ) (hψ : Z∞ ⊢[β, c] insert ψ Γ) :
    Z∞ ⊢[max α β + 1, c] insert (φ ⋏ ψ) Γ := by
  obtain ⟨D₁, ho₁, hcr₁⟩ := hφ
  obtain ⟨D₂, ho₂, hcr₂⟩ := hψ
  refine ⟨Derivation.andI φ ψ D₁ D₂, ?_, ?_⟩
  · simpa [Derivation.ordinalBound] using add_le_add_left (max_le_max ho₁ ho₂) 1
  · simpa [Derivation.cutRank] using max_le hcr₁ hcr₂

/-- The bounded `∨`-rule.

- [Tow20, Section 13] -/
lemma orI (h : Z∞ ⊢[α, c] insert φ (insert ψ Γ)) :
    Z∞ ⊢[α + 1, c] insert (φ ⋎ ψ) Γ := by
  obtain ⟨D, ho, hcr⟩ := h
  exact ⟨Derivation.orI φ ψ D, by simpa [Derivation.ordinalBound] using add_le_add_left ho 1,
    by simpa [Derivation.cutRank] using hcr⟩

/-- The bounded `∃`-rule with a numeral witness.

- [Tow20, Section 13] -/
lemma exI (n : ℕ) (h : Z∞ ⊢[α, c] insert (φₓ/[(↑n : ArithmeticTerm ℕ)]) Γ) :
    Z∞ ⊢[α + 1, c] insert (∃¹ φₓ) Γ := by
  obtain ⟨D, ho, hcr⟩ := h
  exact ⟨Derivation.exI φₓ n D, by simpa [Derivation.ordinalBound] using add_le_add_left ho 1,
    by simpa [Derivation.cutRank] using hcr⟩

/-- The bounded ω-rule for universal formulas.

- [Tow20, Section 13] -/
lemma allω {βₓ : ℕ → Ordinal.{0}}
    (h : ∀ n, Z∞ ⊢[βₓ n, c] insert (φₓ/[(↑n : ArithmeticTerm ℕ)]) Γ) :
    Z∞ ⊢[(⨆ n, βₓ n) + 1, c] insert (∀¹ φₓ) Γ := by
  choose Dₓ ho hcr using h
  refine ⟨Derivation.allω φₓ Dₓ, ?_, by simpa [Derivation.cutRank] using iSup_le hcr⟩
  have : (⨆ n, (Dₓ n).ordinalBound) ≤ ⨆ n, βₓ n :=
    Ordinal.iSup_le fun n => (ho n).trans (Ordinal.le_iSup βₓ n)
  simpa [Derivation.ordinalBound] using add_le_add_left this 1

/-- The bounded cut rule for formulas of quantifier rank below `c`.

- [Tow20, Section 13] -/
lemma cut (χ : ArithmeticFormula ℕ) (hc : χ.qr < c) (h₁ : Z∞ ⊢[α, c] insert χ Γ)
    (h₂ : Z∞ ⊢[β, c] insert (∼χ) Γ) : Z∞ ⊢[max α β + 1, c] Γ := by
  obtain ⟨D₁, ho₁, hcr₁⟩ := h₁
  obtain ⟨D₂, ho₂, hcr₂⟩ := h₂
  refine ⟨Derivation.cut χ D₁ D₂, ?_, ?_⟩
  · simpa [Derivation.ordinalBound] using add_le_add_left (max_le_max ho₁ ho₂) 1
  · have : ((χ.qr : ℕ∞) + 1) ≤ (c : ℕ∞) := by exact_mod_cast Nat.succ_le_of_lt hc
    simpa [Derivation.cutRank] using max_le this (max_le hcr₁ hcr₂)

/-- A boundedly derivable sequent contains a formula true in `ℕ`.

- [Tow20, Section 14] -/
lemma sound (h : Z∞ ⊢[α, c] Γ) : ∃ φ ∈ Γ, LitTrue φ := h.choose.sound

lemma not_empty : ¬(Z∞ ⊢[α, c] ∅) := fun h => by simpa using h.sound

end

end Provable

end FFL.FirstOrder.Arithmetic.OmegaLogic
