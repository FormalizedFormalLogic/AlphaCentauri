module

public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Basic

@[expose] public section
/-!
# Local reflection principles for the provability abstraction

The local reflection schema `Rfn_Γ(𝔅) = { 𝔅 σ 🡒 σ | Γ σ }` of a provability predicate `𝔅`,
restricted to sentences satisfying a class `Γ`, together with its membership API and the two
basic facts relating it to `𝔅.con`: reflecting `⊥` already yields consistency, and, in the other
direction, consistency yields every single reflection instance for sentences to which `𝔅` is
formally complete.

This mirrors Foundation's split between the abstract `ProvabilityAbstraction.Basic`
(`Löb.lean`, `Second.lean`) and its arithmetic instantiation: the definitions and lemmas here
depend only on the derivability conditions `D1`–`D3`, so they are stated for an arbitrary
`Provability` instance and are specialized to the standard provability predicate in
`AlphaCentauri.Reflection.StandardProvability`.

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

/-- Membership form of `localReflectionOn`; no separate counterpart in the literature. -/
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

/-- `Con(𝔅)` implies the single reflection instance `𝔅 σ 🡒 σ`, provided `𝔅` is formally complete
for `∼σ`. The hypotheses are the abstract derivability conditions `HBL2` and
`FormalizedCompleteOn`, so the statement is not tied to the standard provability predicate.
- [Lin97, Exercise 4.1(b)(ii)]
- [AB05, Lemma 22(i)] -/
axiom localReflection_of_con [𝔅.HBL2] [𝔅.FormalizedCompleteOn (∼σ)] :
    T₀ ⊢ 𝔅.con 🡒 (𝔅 σ 🡒 σ)

variable {π : Sentence L}

/-- A single reflection instance for `∼π`, already provable from `T ∪ {π}`, makes `T ∪ {π}`
inconsistent. This is the finite case of the unboundedness of the local reflection schema: no
consistent extension of `T` by finitely many sentences proves even one reflection instance for
its own negation.
- [AB05, Theorem 23, finite case]
- [Lin97, Theorem 4.1] -/
axiom inconsistent_of_localReflection_provable
    (h : insert π T ⊢ 𝔅 (∼π) 🡒 ∼π) : Entailment.Inconsistent (insert π T)

end LO.FirstOrder.ProvabilityAbstraction.Provability
