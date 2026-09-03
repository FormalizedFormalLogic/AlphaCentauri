module

public import Foundation.FirstOrder.Arithmetic.Basic.Hierarchy

/-! # Prenex arithmetical classes

The strict hierarchy records the prenex alternation pattern separately from the cumulative
arithmetical hierarchy. Its levels alternate the polarity of the leading unbounded quantifier
block, while bounded quantifiers remain available at every level.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

variable {L : Language} [L.LT] {ξ : Type*}

/-- `StrictHierarchy Γ s φ`: `φ` is a prenex `Γ`-formula of level `s`: a block of
quantifiers of the kind `Γ`, followed by a prenex formula of the dual kind one level down,
with a `Δ₀` matrix at the bottom. Unlike `Hierarchy`, the classes are prenex: level `s + 1`
is `Q*(level s of the dual kind)`, nothing else.

- [HP98, 0.30]
- [HP98, Lemma I.1.69] -/
inductive StrictHierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop
  | zero {Γ n} {φ : Semiformula L ξ n} : Hierarchy 𝚺 0 φ → StrictHierarchy Γ 0 φ
  | ofAlt {Γ s n} {φ : Semiformula L ξ n} : StrictHierarchy Γ.alt s φ → StrictHierarchy Γ (s + 1) φ
  | exs {s n} {φ : Semiformula L ξ (n + 1)} :
      StrictHierarchy 𝚺 (s + 1) φ → StrictHierarchy 𝚺 (s + 1) (∃¹ φ)
  | all {s n} {φ : Semiformula L ξ (n + 1)} :
      StrictHierarchy 𝚷 (s + 1) φ → StrictHierarchy 𝚷 (s + 1) (∀¹ φ)

namespace StrictHierarchy

-- NOTE (from Foundation PR 849): recursive lemmas over `StrictHierarchy` must bind
-- `Γ s n φ` in their own signature, not via `variable`, or the equation compiler cannot
-- generalize them.

/-- A strict hierarchy class is contained in the ordinary cumulative hierarchy.

- [HP98, 0.30] -/
lemma hierarchy {Γ s n} {φ : Semiformula L ξ n} : StrictHierarchy Γ s φ → Hierarchy Γ s φ
  | zero h => h.of_zero
  | ofAlt h => (hierarchy h).accum _
  | exs h => (hierarchy h).exs
  | all h => (hierarchy h).all

/-- Negation exchanges the polarity of a strict hierarchy class.

- [HP98, 0.30] -/
lemma neg {Γ s n} {φ : Semiformula L ξ n} : StrictHierarchy Γ s φ → StrictHierarchy Γ.alt s (∼φ)
  | zero h => zero (by exact (Hierarchy.neg h).of_zero)
  | ofAlt h => ofAlt (by simpa using neg h)
  | exs h => by simpa using (neg h).all
  | all h => by simpa using (neg h).exs

/-- Strict hierarchy classes are preserved by syntactic rewriting.

- [HP98, 0.30] -/
lemma rew {Γ s n₁ n₂} {ξ₁ ξ₂ : Type*} {φ : Semiformula L ξ₁ n₁} (ω : Rew L ξ₁ n₁ ξ₂ n₂) :
    StrictHierarchy Γ s φ → StrictHierarchy Γ s (ω ▹ φ)
  | zero h => zero (Hierarchy.rew ω h)
  | ofAlt h => ofAlt (rew ω h)
  | exs h => by simpa using (rew ω.q h).exs
  | all h => by simpa using (rew ω.q h).all

/-- Strict hierarchy classes are monotone in their level.

- [HP98, 0.30] -/
lemma mono {Γ s s' n} {φ : Semiformula L ξ n} (h : StrictHierarchy Γ s φ) (hs : s ≤ s') :
    StrictHierarchy Γ s' φ := sorry

end StrictHierarchy

end LO.FirstOrder.Arithmetic
