module

public import Foundation.Vorspiel.Matrix

/-!
# Elementary closure

`Nat.ElementaryClosure K f` holds when `f` is reachable from a family `K` of functions,
indexed by arity, together with the basic functions `0`, successor, projections, addition,
truncated subtraction, multiplication, and `2 ^ ·`, by composition and bounded primitive
recursion. `Nat.elementaryClosure K` is the resulting family of function classes, one per arity.

[Bek99, §6] takes the elementary closure of `K` to be the closure of `K` and all elementary
functions under composition and bounded recursion, leaving the elementary functions themselves to
[Ros84]. The basic functions above, closed under the same two operations with no base family, are
exactly those — Grzegorczyk's `E³` — so the two readings agree.
-/

@[expose] public section

namespace Nat

/-- `ElementaryClosure K f` holds when `f` is built from `K` and the basic functions `0`,
successor, projections, addition, truncated subtraction, multiplication, and `2 ^ ·`, by
composition and bounded primitive recursion.
- [Bek99, §6] -/
inductive ElementaryClosure (K : ∀ k, Set ((Fin k → ℕ) → ℕ)) : ∀ {k}, ((Fin k → ℕ) → ℕ) → Prop
  | base {k} {f : (Fin k → ℕ) → ℕ} (hf : f ∈ K k) : ElementaryClosure K f
  | zero : ElementaryClosure K (fun _ : Fin 0 → ℕ ↦ 0)
  | succ : ElementaryClosure K (fun v : Fin 1 → ℕ ↦ v 0 + 1)
  | proj {k} (i : Fin k) : ElementaryClosure K (fun v : Fin k → ℕ ↦ v i)
  | add : ElementaryClosure K (fun v : Fin 2 → ℕ ↦ v 0 + v 1)
  | sub : ElementaryClosure K (fun v : Fin 2 → ℕ ↦ v 0 - v 1)
  | mul : ElementaryClosure K (fun v : Fin 2 → ℕ ↦ v 0 * v 1)
  | exp : ElementaryClosure K (fun v : Fin 1 → ℕ ↦ 2 ^ v 0)
  | comp {k l} {g : (Fin l → ℕ) → ℕ} {h : Fin l → (Fin k → ℕ) → ℕ}
      (hg : ElementaryClosure K g) (hh : ∀ i, ElementaryClosure K (h i)) :
      ElementaryClosure K (fun v : Fin k → ℕ ↦ g fun i ↦ h i v)
  | boundedRec {n} {f : (Fin n → ℕ) → ℕ} {g : (Fin (n + 2) → ℕ) → ℕ} {b : (Fin (n + 1) → ℕ) → ℕ}
      (hf : ElementaryClosure K f) (hg : ElementaryClosure K g) (hb : ElementaryClosure K b)
      (hbound : ∀ v : Fin (n + 1) → ℕ,
        (v 0).rec (f (v ·.succ)) (fun y ih ↦ g (y :> ih :> (v ·.succ))) ≤ b v) :
      ElementaryClosure K
        (fun v : Fin (n + 1) → ℕ ↦ (v 0).rec (f (v ·.succ)) (fun y ih ↦ g (y :> ih :> (v ·.succ))))

/-- The elementary closure of `K`: the family of function classes, one per arity, of the
functions reachable from `K` by `Nat.ElementaryClosure`.
- [Bek99, §6] -/
def elementaryClosure (K : ∀ k, Set ((Fin k → ℕ) → ℕ)) (k : ℕ) : Set ((Fin k → ℕ) → ℕ) :=
  {f | ElementaryClosure K f}

@[simp] lemma mem_elementaryClosure {K : ∀ k, Set ((Fin k → ℕ) → ℕ)} {k : ℕ}
    {f : (Fin k → ℕ) → ℕ} : f ∈ elementaryClosure K k ↔ ElementaryClosure K f := .rfl

namespace ElementaryClosure

lemma mono {K K' : ∀ k, Set ((Fin k → ℕ) → ℕ)} (h : ∀ k, K k ⊆ K' k) {k : ℕ}
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

lemma of_mem {K : ∀ k, Set ((Fin k → ℕ) → ℕ)} {k : ℕ} {f : (Fin k → ℕ) → ℕ} (hf : f ∈ K k) :
    ElementaryClosure K f := .base hf

end ElementaryClosure

lemma elementaryClosure_mono {K K' : ∀ k, Set ((Fin k → ℕ) → ℕ)} (h : ∀ k, K k ⊆ K' k) (k : ℕ) :
    elementaryClosure K k ⊆ elementaryClosure K' k := fun _ hf ↦ hf.mono h

lemma subset_elementaryClosure (K : ∀ k, Set ((Fin k → ℕ) → ℕ)) (k : ℕ) :
    K k ⊆ elementaryClosure K k := fun _ hf ↦ .of_mem hf

end Nat
