module

public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Basic

@[expose] public section
/-!
# Local reflection principles for the provability abstraction

Local reflection schemas for an abstract provability predicate and their relation to consistency.

- [Lin97, §4.1, p. 52]
- [AB05, §4]
-/

namespace LO.FirstOrder.ProvabilityAbstraction.Provability

variable {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T)

/-- The local reflection schema of `𝔅`, restricted to sentences satisfying `Γ`:
`Rfn_Γ(𝔅) = { 𝔅 σ 🡒 σ | Γ σ }`.
- [Lin97, §4.1, p. 52]
- [AB05, §4] -/
def localReflectionOn (Γ : Sentence L → Prop) : Theory L :=
  (fun σ ↦ 𝔅 σ 🡒 σ) '' {σ | Γ σ}

/-- The full local reflection schema of `𝔅`: `Rfn(𝔅) = { 𝔅 σ 🡒 σ | σ }`.
- [Lin97, §4.1, p. 52]
- [AB05, §4] -/
abbrev localReflection : Theory L := 𝔅.localReflectionOn fun _ ↦ True

variable {Γ Γ' : Sentence L → Prop}

@[simp]
lemma mem_localReflectionOn_iff {ψ : Sentence L} :
    ψ ∈ 𝔅.localReflectionOn Γ ↔ ∃ σ, Γ σ ∧ ψ = 𝔅 σ 🡒 σ := by
  simp [localReflectionOn, eq_comm]

/-- Local reflection is monotone in the sentence class.
- [Lin97, §4.1, p. 52]
- [AB05, §4] -/
lemma localReflectionOn_mono (h : ∀ σ, Γ σ → Γ' σ) :
    𝔅.localReflectionOn Γ ⊆ 𝔅.localReflectionOn Γ' :=
  Set.image_mono fun σ hσ ↦ h σ hσ

variable [L.DecidableEq]

/-- `T ∪ Rfn_Γ(𝔅) ⊢ Con(𝔅)` whenever `⊥` is among the reflected sentences.
- [Lin97, §4.1, p. 52]
- [AB05, §4] -/
axiom con_of_localReflection (h : Γ ⊥) : T ∪ 𝔅.localReflectionOn Γ ⊢ 𝔅.con

variable {σ : Sentence L}

/-- `Con(𝔅)` implies `𝔅 σ 🡒 σ` when `𝔅` is formally complete for `∼σ`.
- [Lin97, Exercise 4.1(b)(ii)]
- [AB05, Lemma 22(i)] -/
axiom localReflection_of_con [𝔅.HBL2] [𝔅.FormalizedCompleteOn (∼σ)] :
    T₀ ⊢ 𝔅.con 🡒 (𝔅 σ 🡒 σ)

variable {π : Sentence L}

/-- If `T ∪ {π}` proves the reflection instance for `∼π`, then `T ∪ {π}` is inconsistent.
- [AB05, Theorem 23, finite case]
- [Lin97, Theorem 4.1] -/
axiom inconsistent_of_localReflection_provable
    (h : insert π T ⊢ 𝔅 (∼π) 🡒 ∼π) : Entailment.Inconsistent (insert π T)

end LO.FirstOrder.ProvabilityAbstraction.Provability
