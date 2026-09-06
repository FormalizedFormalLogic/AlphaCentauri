module

public import AlphaCentauri.Bootstrapping.PartialTruth.Snowing
public import AlphaCentauri.Reflection.StandardProvability

@[expose] public section
/-!
# The collapse formula for a `Δ₁` set of `Γ_{n + 1}` sentences

Given an arithmetic theory `T` and a `Δ₁`-presented set `U` of `Γ_{n + 1}` sentences, this module
constructs a single `Γ_{n + 1}` sentence `collapseSentence T U n Γ` whose extension of `T` proves
every member of `U` while staying consistent whenever `T ∪ U` is. Those two claims are proved
elsewhere; this module supplies only the sentence and its syntactic properties.

The sentence is the one-step unfolding of the fixed point of `collapseFormula T U n Γ`, a formula
built from `U`'s `Δ₁` presentation, a syntactic guard against junk codes, and the partial truth
predicates of `AlphaCentauri.Bootstrapping.PartialTruth.Snowing`.

- [Lin97, Theorem 4.3]
- [AB05, Theorem 23]
-/

namespace LO.FirstOrder.Arithmetic

open Bootstrapping

variable (T U : ArithmeticTheory) [T.Δ₁] [U.Δ₁] (n : ℕ)

/-- The formula, in one free variable `v` for the code of a sentence, whose fixed point collapses
a `Δ₁`-presented set `U` of `Γ_{n + 1}` sentences relative to `T`: at polarity `𝚷`, "every early
enough `T`-consistent member of `U` (checked against a code `v` of `∼collapseSentence T U n 𝚷`
through `negGraph`) is true"; at polarity `𝚺`, its dual, "some standard proof of `∼v` from `T`
exists at a stage by which every member of `U` still true is caught".

- [Lin97, Theorem 4.3]
- [AB05, Theorem 23]
- [AB05, Remark 24] -/
noncomputable def collapseFormula : Polarity → ArithmeticSemisentence 1
  | 𝚷 => “v. ∀ y, ((!U.Δ₁ch.sigma.val y ∧ !(isUFormula ℒₒᵣ).sigma.val y ∧
        !(isStrictPi (n + 1)).sigma.val y ∧
        ∀ u < y, ∃ w, !(negGraph ℒₒᵣ).val w v ∧ ¬!(proof T).pi.val u w)
      → !(satPi n).val y 0)”
  | 𝚺 => “v. ∃ y, ((∃ u < y, ∃ w, !(negGraph ℒₒᵣ).val w v ∧ !(proof T).sigma.val u w) ∧
      ∀ z < y, ((!U.Δ₁ch.pi.val z ∧ !(isUFormula ℒₒᵣ).pi.val z ∧
          !(isStrictSigma (n + 1)).pi.val z)
        → !(satSigma n).val z 0))”

/-- `collapseFormula` lies in `Γ_{n + 1}` of the arithmetical hierarchy, for either polarity `Γ`.

- [Lin97, Theorem 4.3]
- [AB05, Theorem 23]
- [AB05, Remark 24] -/
theorem hierarchy_collapseFormula (Γ : Polarity) :
    Hierarchy Γ (n + 1) (collapseFormula T U n Γ) := by
  cases Γ with
  | pi =>
    show Hierarchy 𝚷 (n + 1) (collapseFormula T U n 𝚷)
    have hξ : Hierarchy 𝚺 (n + 1) U.Δ₁ch.sigma.val :=
      U.Δ₁ch.sigma.sigma_prop.mono (Nat.le_add_left 1 n)
    have hU : Hierarchy 𝚺 (n + 1) (isUFormula ℒₒᵣ).sigma.val :=
      (isUFormula ℒₒᵣ).sigma.sigma_prop.mono (Nat.le_add_left 1 n)
    have hSP : Hierarchy 𝚺 (n + 1) (isStrictPi (n + 1)).sigma.val :=
      (isStrictPi (n + 1)).sigma.sigma_prop.mono (Nat.le_add_left 1 n)
    have hneg : Hierarchy 𝚺 (n + 1) (negGraph ℒₒᵣ).val :=
      (negGraph ℒₒᵣ).sigma_prop.mono (Nat.le_add_left 1 n)
    have hproof : Hierarchy 𝚷 (n + 1) (proof T).pi.val :=
      (proof T).pi.pi_prop.mono (Nat.le_add_left 1 n)
    have hTr : Hierarchy 𝚷 (n + 1) (satPi n).val := (satPi n).pi_prop
    simp [collapseFormula, hξ, hU, hSP, hneg, hproof, hTr]
  | sigma =>
    show Hierarchy 𝚺 (n + 1) (collapseFormula T U n 𝚺)
    have hneg : Hierarchy 𝚺 (n + 1) (negGraph ℒₒᵣ).val :=
      (negGraph ℒₒᵣ).sigma_prop.mono (Nat.le_add_left 1 n)
    have hproof : Hierarchy 𝚺 (n + 1) (proof T).sigma.val :=
      (proof T).sigma.sigma_prop.mono (Nat.le_add_left 1 n)
    have hξ : Hierarchy 𝚷 (n + 1) U.Δ₁ch.pi.val :=
      U.Δ₁ch.pi.pi_prop.mono (Nat.le_add_left 1 n)
    have hU : Hierarchy 𝚷 (n + 1) (isUFormula ℒₒᵣ).pi.val :=
      (isUFormula ℒₒᵣ).pi.pi_prop.mono (Nat.le_add_left 1 n)
    have hSS : Hierarchy 𝚷 (n + 1) (isStrictSigma (n + 1)).pi.val :=
      (isStrictSigma (n + 1)).pi.pi_prop.mono (Nat.le_add_left 1 n)
    have hTr : Hierarchy 𝚺 (n + 1) (satSigma n).val := (satSigma n).sigma_prop
    simp [collapseFormula, hneg, hproof, hξ, hU, hSS, hTr]

/-- The one-step unfolding of the fixed point of `collapseFormula`, at the code of that very fixed
point: the sentence collapsing `U` relative to `T`.

- [Lin97, Theorem 4.3]
- [AB05, Theorem 23]
- [AB05, Remark 24] -/
noncomputable def collapseSentence (Γ : Polarity) : ArithmeticSentence :=
  (collapseFormula T U n Γ)/[⌜fixedpoint (collapseFormula T U n Γ)⌝]

/-- `collapseSentence` lies in `Γ_{n + 1}` of the arithmetical hierarchy.

- [Lin97, Theorem 4.3]
- [AB05, Theorem 23]
- [AB05, Remark 24] -/
theorem hierarchy_collapseSentence (Γ : Polarity) :
    Hierarchy Γ (n + 1) (collapseSentence T U n Γ) := by
  simpa [collapseSentence] using hierarchy_collapseFormula T U n Γ

/-- `collapseSentence` is, over `𝗜𝚺₁`, equivalent to the fixed point of `collapseFormula`.

- [Lin97, Theorem 4.3]
- [AB05, Theorem 23] -/
theorem provable_fixedpoint_collapseFormula_iff (Γ : Polarity) :
    𝗜𝚺₁ ⊢ fixedpoint (collapseFormula T U n Γ) 🡘 collapseSentence T U n Γ :=
  diagonal (collapseFormula T U n Γ)

end LO.FirstOrder.Arithmetic
