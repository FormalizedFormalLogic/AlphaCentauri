module

public import Foundation.FirstOrder.Arithmetic.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.SetTheory.Ordinal.Family

/-!
# `Z_∞`, an ω-logic sequent calculus for arithmetic

This file defines the infinitary Tait calculus `Z_∞`, its ordinal height and cut rank, and bounded
derivability. It also proves soundness, excluded middle, and derivability of true formulas.

Neither [HP98] nor [Lin97] treats ω-logic, ordinal heights, or ordinal analysis; nothing in this
file is cited from them. The presentation followed is [Tow20].
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.OmegaLogic

/-- A `Z_∞` sequent: a finite set of arithmetic formulas, read disjunctively.

- [Tow20, Section 13] -/
abbrev Sequent := Finset (ArithmeticFormula ℕ)

section Truth

variable {k : ℕ} {b : Bool} {r : (ℒₒᵣ).Rel k} {v : Fin k → ArithmeticTerm ℕ}
  {φ ψ : ArithmeticFormula ℕ} {φₓ : ArithmeticSemiformula ℕ 1}

/-- Truth of an arithmetic formula in the standard model `ℕ`.

- [Tow20, Section 13] -/
def LitTrue (φ : ArithmeticFormula ℕ) : Prop := Semiformula.Evalf (M := ℕ) id φ

@[simp, grind =] lemma litTrue_neg : LitTrue (∼φ) ↔ ¬LitTrue φ := by simp [LitTrue]

@[simp] lemma litTrue_verum : LitTrue ⊤ := by simp [LitTrue]

@[simp] lemma litTrue_falsum : ¬LitTrue ⊥ := by simp [LitTrue]

@[simp, grind =] lemma litTrue_and : LitTrue (φ ⋏ ψ) ↔ LitTrue φ ∧ LitTrue ψ := by simp [LitTrue]

@[simp, grind =] lemma litTrue_or : LitTrue (φ ⋎ ψ) ↔ LitTrue φ ∨ LitTrue ψ := by simp [LitTrue]

lemma litTrue_or_neg (φ : ArithmeticFormula ℕ) : LitTrue φ ∨ LitTrue (∼φ) := by simp [LitTrue, em]

@[simp, grind =]
lemma litTrue_substs_numeral {n : ℕ} :
    LitTrue (φₓ/[(↑n : ArithmeticTerm ℕ)]) ↔ Semiformula.Eval ![n] id φₓ := by simp [LitTrue]

/-- A universal formula is true exactly when all its numeral instances are true.

- [Tow20, Section 13] -/
@[simp, grind =]
lemma litTrue_all : LitTrue (∀¹ φₓ) ↔ ∀ n : ℕ, LitTrue (φₓ/[(↑n : ArithmeticTerm ℕ)]) := by
  simp [LitTrue]

/-- An existential formula is true exactly when some numeral instance is true.

- [Tow20, Section 13] -/
@[simp, grind =]
lemma litTrue_exs : LitTrue (∃¹ φₓ) ↔ ∃ n : ℕ, LitTrue (φₓ/[(↑n : ArithmeticTerm ℕ)]) := by
  simp [LitTrue]

/-- The atomic literal with positive polarity for `true` and negative polarity for `false`.

- [Tow20, Section 13] -/
def signedLit : Bool → {k : ℕ} → (ℒₒᵣ).Rel k → (Fin k → ArithmeticTerm ℕ) → ArithmeticFormula ℕ
  |  true, _, r, v => Semiformula.rel r v
  | false, _, r, v => Semiformula.nrel r v

@[simp, grind =] lemma neg_signedLit : ∼(signedLit b r v) = signedLit (!b) r v := by
  cases b <;> simp [signedLit]

@[grind =] lemma litTrue_signedLit_not :
    LitTrue (signedLit (!b) r v) ↔ ¬LitTrue (signedLit b r v) := by simp [← neg_signedLit]

@[simp, grind .] lemma signedLit_ne_verum : signedLit b r v ≠ ⊤ := by cases b <;> simp [signedLit]

@[simp, grind .] lemma signedLit_ne_falsum : signedLit b r v ≠ ⊥ := by cases b <;> simp [signedLit]

end Truth

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

lemma ordinalBound_lt_allω {Γ : Sequent} {φₓ : ArithmeticSemiformula ℕ 1} {n : ℕ}
    {Dₓ : (n : ℕ) → Derivation (insert (φₓ/[(↑n : ArithmeticTerm ℕ)]) Γ)} :
    (Dₓ n).ordinalBound < (allω φₓ Dₓ).ordinalBound :=
  lt_of_le_of_lt (Ordinal.le_iSup _ n) (lt_add_of_pos_right _ one_pos)

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
    · refine ⟨_, Finset.mem_insert_self _ _, litTrue_all.mpr fun n => ?_⟩
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

/-- `Z∞ ⊢[α, c] Γ` means that `Γ` has a derivation of height at most `α` and cut rank at most `c`.

- [Tow20, Section 18] -/
def Provable (α : Ordinal.{0}) (c : ℕ) (Γ : Sequent) : Prop :=
  ∃ D : Derivation Γ, D.ordinalBound ≤ α ∧ D.cutRank ≤ (c : ℕ∞)

@[inherit_doc] scoped notation:45 "Z∞" " ⊢[" α ", " c "] " Γ:46 => Provable α c Γ

namespace Provable

section

variable {α β : Ordinal.{0}} {c c' k : ℕ} {φ ψ : ArithmeticFormula ℕ}
  {φₓ : ArithmeticSemiformula ℕ 1} {Γ Δ : Sequent}

/-- Both bounds may be relaxed.

- [Tow20, Section 18] -/
lemma mono (hα : α ≤ β) (hc : c ≤ c') : Z∞ ⊢[α, c] Γ → Z∞ ⊢[β, c'] Γ := by
  rintro ⟨D, ho, hcr⟩
  exact ⟨D, ho.trans hα, hcr.trans (by exact_mod_cast hc)⟩

lemma mono_ordinalBound (h : α ≤ β) : Z∞ ⊢[α, c] Γ → Z∞ ⊢[β, c] Γ := mono h le_rfl

lemma mono_cutRank (h : c ≤ c') : Z∞ ⊢[α, c] Γ → Z∞ ⊢[α, c'] Γ := mono le_rfl h

/-- Weakening preserves both derivation bounds.

- [Tow20, Section 14] -/
lemma weakening (h : Γ ⊆ Δ) : Z∞ ⊢[α, c] Γ → Z∞ ⊢[α, c] Δ := by
  rintro ⟨D, ho, hcr⟩
  exact ⟨D.weak h, by simpa [Derivation.ordinalBound] using ho,
    by simpa [Derivation.cutRank] using hcr⟩

lemma insert_absorb (h : Z∞ ⊢[α, c] insert φ Γ) (hmem : φ ∈ Γ) : Z∞ ⊢[α, c] Γ := by
  rwa [Finset.insert_eq_self.mpr hmem] at h

lemma contr (h : Z∞ ⊢[α, c] insert φ (insert φ Γ)) : Z∞ ⊢[α, c] insert φ Γ := by
  simpa using h

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
  refine ⟨Derivation.orI φ ψ D, ?_, ?_⟩
  · simpa [Derivation.ordinalBound] using add_le_add_left ho 1
  · simpa [Derivation.cutRank] using hcr

/-- The bounded `∃`-rule with a numeral witness.

- [Tow20, Section 13] -/
lemma exI (n : ℕ) (h : Z∞ ⊢[α, c] insert (φₓ/[(↑n : ArithmeticTerm ℕ)]) Γ) :
    Z∞ ⊢[α + 1, c] insert (∃¹ φₓ) Γ := by
  obtain ⟨D, ho, hcr⟩ := h
  refine ⟨Derivation.exI φₓ n D, ?_, ?_⟩
  · simpa [Derivation.ordinalBound] using add_le_add_left ho 1
  · simpa [Derivation.cutRank] using hcr

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

section ExcludedMiddle

variable {α : Ordinal.{0}} {k : ℕ} {φ : ArithmeticFormula ℕ} {Γ : Sequent}

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
  refine ((allω h).insert_absorb hall).mono_ordinalBound ?_
  exact add_le_add_left (Ordinal.iSup_le fun _ => le_rfl) 1

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
      refine em_quantStep hp (show (∃¹ ∼ψ) ∈ Γ by simpa using hn) fun n => ?_
      have h := ih (φ := ψ/[(↑n : ArithmeticTerm ℕ)])
        (Γ := insert (∼(ψ/[(↑n : ArithmeticTerm ℕ)])) (insert (ψ/[(↑n : ArithmeticTerm ℕ)]) Γ))
        (by simpa using hk) (by simp) (by simp)
      simpa using h
    | hexs ψ =>
      refine em_quantStep (show (∀¹ ∼ψ) ∈ Γ by simpa using hn) hp fun n => ?_
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

section OmegaCompleteness

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
      refine ((allω h).insert_absorb hmem).mono_ordinalBound ?_
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

end OmegaCompleteness

end Provable

end LO.FirstOrder.Arithmetic.OmegaLogic
