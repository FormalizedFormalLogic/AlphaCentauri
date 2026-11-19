module

public import AlphaCentauri.Model.ElementarySubstructure
public import Mathlib.Order.DirectedInverseSystem

/-! # Countable elementary chains

A countable elementary chain is a sequence of `ℒₒᵣ`-structures `M 0 ≼ₑ M 1 ≼ₑ M 2 ≼ₑ ⋯`, each an
elementary substructure of the next. Composing the steps gives an elementary substructure
`M m ≼ₑ M n` for every `m ≤ n`, and these form a directed system.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

universe u

/-- A countable elementary chain: a sequence of `ℒₒᵣ`-structures `M 0 ≼ₑ M 1 ≼ₑ M 2 ≼ₑ ⋯`.
- [Kay91, Lemma 0.6] -/
structure ElementaryChain (M : ℕ → Type u) [∀ n, ORingStructure (M n)] where
  step : ∀ n, M n ≼ₑ M (n + 1)

namespace ElementaryChain

variable {M : ℕ → Type u} [∀ n, ORingStructure (M n)] (c : ElementaryChain M) {l m n : ℕ}

/-- The elementary substructure `M m ≼ₑ M n` composed of the steps from `m` to `n`. -/
def map (h : m ≤ n) : M m ≼ₑ M n := Nat.leRecOn h (fun e ↦ e.trans (c.step _)) (.refl _ _)

@[simp] lemma map_self (x : M m) : c.map le_rfl x = x := by
  simp [map, Nat.leRecOn_self]

lemma map_succ (h : m ≤ n) (x : M m) : c.map (h.trans n.le_succ) x = c.step n (c.map h x) := by
  simp [map, Nat.leRecOn_succ h]

@[simp] lemma map_map (h₁ : l ≤ m) (h₂ : m ≤ n) (x : M l) :
    c.map h₂ (c.map h₁ x) = c.map (h₁.trans h₂) x := by
  induction n, h₂ using Nat.le_induction with
  | base => simp
  | succ n h ih => rw [map_succ c h, ih, ← map_succ]

instance : DirectedSystem M fun _ _ h ↦ (c.map h).emb where
  map_self _ := c.map_self
  map_map _ _ _ := c.map_map

end ElementaryChain

end FFL.FirstOrder.Arithmetic
