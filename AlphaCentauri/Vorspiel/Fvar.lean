module

public import Foundation.FirstOrder.Basic.Semantics.Semantics

/-!
# Free variables of a formula as bound variables of a semisentence

`Semiformula.toSemisentence` turns a formula with `ℕ`-indexed free variables into a semisentence
whose extra bound variables are those free variables, with the original bound variables placed by
a caller-supplied substitution `b`.
-/

@[expose] public section

namespace FFL.FirstOrder.Semiformula

variable {L : Language} {k : ℕ}

/-- The substitution sending the bound variables of `φ` to `b` and the free variables below
`φ.fvSup` to the remaining bound variables. -/
noncomputable def paramSubst [NeZero k] (φ : Semiformula L ℕ k)
    (b : Fin k → Semiterm L Empty (φ.fvSup + k)) : Rew L ℕ k Empty (φ.fvSup + k) :=
  haveI : NeZero (φ.fvSup + k) := ⟨by have := Nat.pos_of_ne_zero (NeZero.ne k); omega⟩
  Rew.bind b fun x ↦ if h : x < φ.fvSup then #⟨x + k, by omega⟩ else #0

/-- `φ`, viewed as a semisentence whose extra bound variables are its free variables, with its
own bound variables placed by `b`. -/
noncomputable def toSemisentence [NeZero k] (φ : Semiformula L ℕ k)
    (b : Fin k → Semiterm L Empty (φ.fvSup + k)) : Semisentence L (φ.fvSup + k) :=
  paramSubst φ b ▹ φ

variable {M : Type*} [Structure L M]

lemma eval_toSemisentence [NeZero k] {φ : Semiformula L ℕ k}
    (b : Fin k → Semiterm L Empty (φ.fvSup + k)) {v : Fin (φ.fvSup + k) → M} {w : Fin k → M}
    {f : ℕ → M} (hb : ∀ i, Semiterm.val v Empty.elim (b i) = w i)
    (hv : ∀ y : Fin φ.fvSup, v ⟨y + k, by omega⟩ = f y) :
    M ⊧/v (φ.toSemisentence b) ↔ φ.Eval w f := by
  rw [toSemisentence, Semiformula.eval_rew]
  have hbv : (Semiterm.val v Empty.elim ∘ φ.paramSubst b ∘ Semiterm.bvar) = w := funext hb
  rw [hbv]
  refine Semiformula.eval_iff_of_funEqOn φ fun y hy ↦ ?_
  have hlt : y < φ.fvSup := Semiformula.lt_fvSup_of_fvar? hy
  simp [paramSubst, hlt, hv ⟨y, hlt⟩]

/-- `eval_toSemisentence` at `k = 1`, with `b` placing the bound variable at `#0`. -/
lemma eval_toSemisentence_one (φ : Semiformula L ℕ 1) (x : M)
    (f : ℕ → M) :
    M ⊧/(x :> fun i : Fin φ.fvSup ↦ f i) (φ.toSemisentence ![#0]) ↔ φ.Eval ![x] f :=
  eval_toSemisentence ![#0]
    (fun i ↦ by induction i using Fin.cases with | zero => simp | succ i => exact i.elim0)
    (fun _ ↦ by simp)

/-- `eval_toSemisentence` at `k = 2`, with `b` placing the two bound variables at `#1`, `#0` (the
witness-then-bound order). -/
lemma eval_toSemisentence_two (φ : Semiformula L ℕ 2) (x y : M)
    (f : ℕ → M) :
    M ⊧/(y :> x :> fun i : Fin φ.fvSup ↦ f i) (φ.toSemisentence ![#1, #0]) ↔ φ.Eval ![x, y] f :=
  eval_toSemisentence ![#1, #0]
    (fun i ↦ by
      induction i using Fin.cases with
      | zero => simp
      | succ i => induction i using Fin.cases with
        | zero => simp
        | succ i => exact i.elim0)
    (fun _ ↦ by simp)

end FFL.FirstOrder.Semiformula
