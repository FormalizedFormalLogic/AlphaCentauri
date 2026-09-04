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

/-- Prefixing `s` alternating quantifiers, the outermost one of the kind `Γ`, raises a strict
class by `s` levels.

- [HP98, 0.30] -/
lemma toPrenex {Γ j s n} {φ : Semiformula L ξ (n + s)} (h : StrictHierarchy (Γ.altItr s) j φ) :
    StrictHierarchy Γ (j + s) (φ.toPrenex Γ s) := by
  induction s generalizing n j with
  | zero => simpa using h
  | succ s ih =>
    rw [Polarity.altItr_succ] at h
    show StrictHierarchy Γ (j + (s + 1)) (Polarity.quantItr Γ (s + 1) φ)
    rw [Polarity.quantItr_succ', show j + (s + 1) = j + 1 + s by omega]
    rcases hΓ : Γ.altItr s with _ | _
    · apply ih
      rw [hΓ] at h ⊢
      exact (ofAlt h).exs
    · apply ih
      rw [hΓ] at h ⊢
      exact (ofAlt h).all

/-- A `Δ₀` matrix under `s` alternating quantifiers, the outermost one of the kind `Γ`, is a
strict `Γ`-formula of level `s`.

- [HP98, 0.30] -/
lemma toPrenex_of_deltaZero {Γ s n} {φ : Semiformula L ξ (n + s)} (h : Hierarchy 𝚺 0 φ) :
    StrictHierarchy Γ s (φ.toPrenex Γ s) := by simpa using toPrenex (Γ := Γ) (zero h)

/-- Strict hierarchy classes are monotone in their level.

- [HP98, 0.30] -/
lemma mono {Γ s s' n} {φ : Semiformula L ξ n} (h : StrictHierarchy Γ s φ) (hs : s ≤ s') :
    StrictHierarchy Γ s' φ := by
  induction h generalizing s' with
  | @zero Γ₀ n₀ φ₀ h =>
    have key : ∀ t Γ', StrictHierarchy Γ' t φ₀ := by
      intro t
      induction t with
      | zero => intro Γ'; exact zero h
      | succ t ih => intro Γ'; exact ofAlt (ih Γ'.alt)
    exact key s' Γ₀
  | @ofAlt Γ₀ s₀ n₀ φ₀ h ih =>
    obtain ⟨t, rfl⟩ : ∃ t, s' = t + 1 := ⟨s' - 1, by omega⟩
    exact ofAlt (ih (s' := t) (by omega))
  | @exs s₀ n₀ φ₀ h ih =>
    obtain ⟨t, rfl⟩ : ∃ t, s' = t + 1 := ⟨s' - 1, by omega⟩
    exact exs (ih (s' := t + 1) (by omega))
  | @all s₀ n₀ φ₀ h ih =>
    obtain ⟨t, rfl⟩ : ∃ t, s' = t + 1 := ⟨s' - 1, by omega⟩
    exact all (ih (s' := t + 1) (by omega))

end StrictHierarchy

end LO.FirstOrder.Arithmetic
