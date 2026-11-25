module

public import AlphaCentauri.Init
public import Foundation.Vorspiel.Matrix

/-!
# The elementary closure of a family of functions

The closure of a family of functions under composition and bounded primitive recursion.

- [Bek99, §6]
-/

@[expose] public section

namespace Nat

variable (K : ∀ k, Set ((Fin k → ℕ) → ℕ))

/-- `ElementaryClosure K f` holds when `f` is built from `K` and the basic functions `0`,
successor, projections, addition, truncated subtraction, multiplication, and `2 ^ ·`, by
composition and bounded primitive recursion.
- [Bek99, §6] -/
inductive ElementaryClosure : ∀ {k}, ((Fin k → ℕ) → ℕ) → Prop
  | base {k} {f : (Fin k → ℕ) → ℕ} (hf : f ∈ K k) : ElementaryClosure f
  | zero : ElementaryClosure (fun _ : Fin 0 → ℕ ↦ 0)
  | succ : ElementaryClosure (fun v : Fin 1 → ℕ ↦ v 0 + 1)
  | proj {k} (i : Fin k) : ElementaryClosure (fun v : Fin k → ℕ ↦ v i)
  | add : ElementaryClosure (fun v : Fin 2 → ℕ ↦ v 0 + v 1)
  | sub : ElementaryClosure (fun v : Fin 2 → ℕ ↦ v 0 - v 1)
  | mul : ElementaryClosure (fun v : Fin 2 → ℕ ↦ v 0 * v 1)
  | exp : ElementaryClosure (fun v : Fin 1 → ℕ ↦ 2 ^ v 0)
  | comp {k l} {g : (Fin l → ℕ) → ℕ} {h : Fin l → (Fin k → ℕ) → ℕ}
      (hg : ElementaryClosure g) (hh : ∀ i, ElementaryClosure (h i)) :
      ElementaryClosure (fun v : Fin k → ℕ ↦ g fun i ↦ h i v)
  | boundedRec {n} {f : (Fin n → ℕ) → ℕ} {g : (Fin (n + 2) → ℕ) → ℕ} {b : (Fin (n + 1) → ℕ) → ℕ}
      (hf : ElementaryClosure f) (hg : ElementaryClosure g) (hb : ElementaryClosure b)
      (hbound : ∀ v : Fin (n + 1) → ℕ,
        (v 0).rec (f (v ·.succ)) (fun y ih ↦ g (y :> ih :> (v ·.succ))) ≤ b v) :
      ElementaryClosure
        (fun v : Fin (n + 1) → ℕ ↦ (v 0).rec (f (v ·.succ)) (fun y ih ↦ g (y :> ih :> (v ·.succ))))

/-- The elementary closure of `K`: the family of function classes, one per arity, of the
functions reachable from `K` by `Nat.ElementaryClosure`.
- [Bek99, §6] -/
def elementaryClosure (k : ℕ) : Set ((Fin k → ℕ) → ℕ) :=
  {f | ElementaryClosure K f}

variable {K} {K' : ∀ k, Set ((Fin k → ℕ) → ℕ)}

lemma ElementaryClosure.mono (h : ∀ k, K k ⊆ K' k) {k : ℕ}
    {f : (Fin k → ℕ) → ℕ} (hf : ElementaryClosure K f) : ElementaryClosure K' f := by
  induction hf with
  | base hf => exact .base (h _ hf)
  | zero => exact .zero
  | succ => exact .succ
  | proj i => exact .proj i
  | add => exact .add
  | sub => exact .sub
  | mul => exact .mul
  | exp => exact .exp
  | comp _ _ ihg ihh => exact .comp ihg ihh
  | boundedRec _ _ _ hbound ihf ihg ihb => exact .boundedRec ihf ihg ihb hbound


lemma elementaryClosure_mono (h : ∀ k, K k ⊆ K' k) (k : ℕ) :
    elementaryClosure K k ⊆ elementaryClosure K' k := fun _ hf ↦ hf.mono h

end Nat
