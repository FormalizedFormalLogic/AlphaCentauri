module

public import Foundation.FirstOrder.Tarski.Basic
public import Mathlib.Order.Filter.Finite

/-!
# Open formulas along eventually agreeing maps

Let `π i : M → N` be maps indexed along a filter, which eventually commute with each function
symbol and eventually preserve and reflect each relation symbol. Then every open formula
eventually has the same truth value in `M` as its image under `π i` in `N`. Along a proper filter,
every universal sentence true in `N` is therefore true in `M`.
-/

@[expose] public section

open Filter

namespace FFL.FirstOrder

variable {L : Language} {M N : Type*} [Tarski.Structure L M] [Tarski.Structure L N] {ι : Type*}
  {l : Filter ι} {π : ι → M → N}
  (hfunc : ∀ {k} (f : L.Func k) (v : Fin k → M),
    ∀ᶠ i in l, π i (Tarski.Structure.func f v) = Tarski.Structure.func f (π i ∘ v))
  (hrel : ∀ {k} (r : L.Rel k) (v : Fin k → M),
    ∀ᶠ i in l, (Tarski.Structure.rel r v ↔ Tarski.Structure.rel r (π i ∘ v)))

include hfunc in
lemma Semiterm.eventually_val {ξ : Type*} {n : ℕ} (t : Semiterm L ξ n) (b : Fin n → M)
    (f : ξ → M) : ∀ᶠ i in l, π i (t.val b f) = t.val (π i ∘ b) (π i ∘ f) := by
  induction t with
  | bvar x => simp
  | fvar x => simp
  | func F v ih =>
    filter_upwards [hfunc F (fun j ↦ (v j).val b f), eventually_all.mpr ih] with i h₁ h₂
    simp only [Semiterm.val_func', h₁]
    exact congrArg _ (funext h₂)

include hfunc hrel in
lemma Semiformula.eventually_eval_iff_of_open {ξ : Type*} {n : ℕ} {φ : Semiformula L ξ n}
    (hφ : φ.Open) (b : Fin n → M) (f : ξ → M) :
    ∀ᶠ i in l, (φ.Eval b f ↔ φ.Eval (π i ∘ b) (π i ∘ f)) :=
  match φ with
  | ⊤ | ⊥ => by simp
  | .rel r v | .nrel r v => by
    filter_upwards [hrel r (fun j ↦ (v j).val b f),
      eventually_all.mpr fun j ↦ Semiterm.eventually_val hfunc (v j) b f] with i h₁ h₂
    simp only [Semiformula.eval_rel', Semiformula.eval_nrel', h₁]
    rw [show (π i ∘ fun j ↦ (v j).val b f) = fun j ↦ (v j).val (π i ∘ b) (π i ∘ f) from
      funext h₂]
  | φ ⋏ ψ | φ ⋎ ψ => by
    simp only [Semiformula.open_and, Semiformula.open_or] at hφ
    filter_upwards [eventually_eval_iff_of_open hφ.1 b f,
      eventually_eval_iff_of_open hφ.2 b f] with i h₁ h₂
    simp [h₁, h₂]

include hfunc hrel in
/-- Along a proper filter, the universal closure of an open formula true in `N` is true in `M`. -/
lemma models_univCl_of_open [l.NeBot] [Nonempty M] [Nonempty N] {φ : Semiformula L ℕ 0}
    (hφ : φ.Open) (h : N↓[L] ⊧ φ.univCl) : M↓[L] ⊧ φ.univCl := by
  rw [models_iff_proposition] at h ⊢
  intro f
  obtain ⟨i, hi⟩ := (Semiformula.eventually_eval_iff_of_open hfunc hrel hφ ![] f).exists
  rw [hi, Matrix.empty_eq (π i ∘ ![])]
  exact h _

end FFL.FirstOrder
