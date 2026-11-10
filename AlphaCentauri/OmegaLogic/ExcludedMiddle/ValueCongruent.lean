module

public import AlphaCentauri.ToFoundation.FirstOrder.Rew
public import AlphaCentauri.OmegaLogic.Provable
public import AlphaCentauri.ToFoundation.FirstOrder.Semiformula
public import Foundation.FirstOrder.Arithmetic.Schemata
public import Foundation.FirstOrder.LK.Simplified

/-!
# Value-congruent excluded middle in `Z_∞`

Equal-valued closed substitutions into a formula and its negation are derivable cut-free.

- [Tow20, Section 16]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.OmegaLogic

variable {n : ℕ} {Γ : Sequent}

section ExcludedMiddle

/-! ### Value-congruent excluded middle

Cut-free excluded middle for substitutions by closed terms of the same standard value. -/

variable {k : ℕ} {w w' : Fin n → ArithmeticTerm ℕ}

private lemma litTrue_subst_congr
    (h : ∀ i, Semiterm.val (M := ℕ) ![] id (w i) = Semiterm.val (M := ℕ) ![] id (w' i))
    (b : Bool) (r : (ℒₒᵣ).Rel k) (v : Fin k → Semiterm ℒₒᵣ ℕ n) :
    LitTrue (signedLit b r fun i => Rew.subst w (v i))
      ↔ LitTrue (signedLit b r fun i => Rew.subst w' (v i)) := by
  have hv : (fun i => Semiterm.val (M := ℕ) ![] id (Rew.subst w (v i)))
      = fun i => Semiterm.val (M := ℕ) ![] id (Rew.subst w' (v i)) :=
    funext fun i => Rew.val_subst_congr h (v i)
  cases b <;>
    simp only [signedLit, LitTrue, Semiformula.Evalf, Semiformula.eval_rel, Semiformula.eval_nrel,
      hv, Function.comp_def]

namespace Provable

private lemma em_binary {A B C D : ArithmeticFormula ℕ} (hab : A ⋏ B ∈ Γ) (hcd : C ⋎ D ∈ Γ)
    (h₁ : ∃ α, Z∞ ⊢[α, 0] insert A (insert C (insert D Γ)))
    (h₂ : ∃ α, Z∞ ⊢[α, 0] insert B (insert C (insert D Γ))) : ∃ α, Z∞ ⊢[α, 0] Γ := by
  obtain ⟨α₁, h₁⟩ := h₁
  obtain ⟨α₂, h₂⟩ := h₂
  have h := (andI h₁ h₂).insert_absorb
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hab))
  exact ⟨_, h.orI.insert_absorb hcd⟩

private lemma em_quant {φₓ ψₓ : ArithmeticSemiformula ℕ 1} (hall : (∀¹ φₓ) ∈ Γ)
    (hexs : (∃¹ ψₓ) ∈ Γ)
    (fam : ∀ m : ℕ, ∃ α, Z∞ ⊢[α, 0] insert (ψₓ/[(↑m : ArithmeticTerm ℕ)])
      (insert (φₓ/[(↑m : ArithmeticTerm ℕ)]) Γ)) : ∃ α, Z∞ ⊢[α, 0] Γ := by
  choose βₓ hβ using fam
  have h : ∀ m : ℕ, Z∞ ⊢[βₓ m + 1, 0] insert (φₓ/[(↑m : ArithmeticTerm ℕ)]) Γ := fun m =>
    (exI m (hβ m)).insert_absorb (Finset.mem_insert_of_mem hexs)
  exact ⟨_, (allω h).insert_absorb hall⟩

private lemma em_atomic
    (h : ∀ i, Semiterm.val (M := ℕ) ![] id (w i) = Semiterm.val (M := ℕ) ![] id (w' i))
    (b : Bool) (r : (ℒₒᵣ).Rel k) (v : Fin k → Semiterm ℒₒᵣ ℕ n)
    (hp : signedLit b r (fun i => Rew.subst w (v i)) ∈ Γ)
    (hn : signedLit (!b) r (fun i => Rew.subst w' (v i)) ∈ Γ) : ∃ α, Z∞ ⊢[α, 0] Γ := by
  rcases litTrue_or_neg (signedLit b r fun i => Rew.subst w (v i)) with ht | ht
  · exact ⟨0, axTrue b r _ ht hp⟩
  · rw [neg_signedLit] at ht
    exact ⟨0, axTrue (!b) r _ ((litTrue_subst_congr h (!b) r v).mp ht) hn⟩

private lemma em_congAux : ∀ (k : ℕ) {n : ℕ} (w w' : Fin n → ArithmeticTerm ℕ)
    (ψ : ArithmeticSemiformula ℕ n), ψ.complexity ≤ k →
    (∀ i, Semiterm.val (M := ℕ) ![] id (w i) = Semiterm.val (M := ℕ) ![] id (w' i)) →
    ∀ {Γ : Sequent}, (Rew.subst w ▹ ψ) ∈ Γ → (∼(Rew.subst w' ▹ ψ)) ∈ Γ →
      ∃ α, Z∞ ⊢[α, 0] Γ := by
  intro k
  induction k with
  | zero =>
    intro n w w' ψ hk h Γ hp hn
    cases ψ using Semiformula.cases' with
    | hverum => exact ⟨0, verumR (by simpa using hp)⟩
    | hfalsum => exact ⟨0, verumR (by simpa using hn)⟩
    | hrel r v =>
      exact em_atomic h true r v (by simpa [signedLit, Function.comp_def] using hp)
        (by simpa [signedLit, Function.comp_def] using hn)
    | hnrel r v =>
      exact em_atomic h false r v (by simpa [signedLit, Function.comp_def] using hp)
        (by simpa [signedLit, Function.comp_def] using hn)
    | _ => simp at hk
  | succ k ih =>
    intro n w w' ψ hk h Γ hp hn
    cases ψ using Semiformula.cases' with
    | hverum => exact ⟨0, verumR (by simpa using hp)⟩
    | hfalsum => exact ⟨0, verumR (by simpa using hn)⟩
    | hrel r v =>
      exact em_atomic h true r v (by simpa [signedLit, Function.comp_def] using hp)
        (by simpa [signedLit, Function.comp_def] using hn)
    | hnrel r v =>
      exact em_atomic h false r v (by simpa [signedLit, Function.comp_def] using hp)
        (by simpa [signedLit, Function.comp_def] using hn)
    | hand a b =>
      simp only [Semiformula.complexity_and] at hk
      refine em_binary (show ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b)) ∈ Γ by simpa using hp)
        (show (∼(Rew.subst w' ▹ a) ⋎ ∼(Rew.subst w' ▹ b)) ∈ Γ by simpa using hn)
        (ih w w' a (by omega) h (by simp) (by simp))
        (ih w w' b (by omega) h (by simp) (by simp))
    | hor a b =>
      simp only [Semiformula.complexity_or] at hk
      refine em_binary (show (∼(Rew.subst w' ▹ a) ⋏ ∼(Rew.subst w' ▹ b)) ∈ Γ by simpa using hn)
        (show ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) ∈ Γ by simpa using hp)
        (ih w w' a (by omega) h (by simp) (by simp))
        (ih w w' b (by omega) h (by simp) (by simp))
    | hall a =>
      simp only [Semiformula.complexity_all] at hk
      refine em_quant (show (∀¹ ((Rew.subst w).q ▹ a)) ∈ Γ by simpa using hp)
        (show (∃¹ ((Rew.subst w').q ▹ ∼a)) ∈ Γ by simpa using hn) fun m => ?_
      have hx := ih ((↑m : ArithmeticTerm ℕ) :> w) ((↑m : ArithmeticTerm ℕ) :> w') a (by omega)
        (cons_val_congr h m)
        (Γ := insert (((Rew.subst w).q ▹ a)/[(↑m : ArithmeticTerm ℕ)])
          (insert (∼(((Rew.subst w').q ▹ a)/[(↑m : ArithmeticTerm ℕ)])) Γ))
        (by rw [← Rew.subst_q_app]; simp) (by rw [← Rew.subst_q_app]; simp)
      rw [show (((Rew.subst w').q ▹ ∼a)/[(↑m : ArithmeticTerm ℕ)])
        = ∼(((Rew.subst w').q ▹ a)/[(↑m : ArithmeticTerm ℕ)]) by simp, Finset.insert_comm]
      exact hx
    | hexs a =>
      simp only [Semiformula.complexity_exs] at hk
      refine em_quant (show (∀¹ ((Rew.subst w').q ▹ ∼a)) ∈ Γ by simpa using hn)
        (show (∃¹ ((Rew.subst w).q ▹ a)) ∈ Γ by simpa using hp) fun m => ?_
      have hx := ih ((↑m : ArithmeticTerm ℕ) :> w) ((↑m : ArithmeticTerm ℕ) :> w') a (by omega)
        (cons_val_congr h m)
        (Γ := insert (((Rew.subst w).q ▹ a)/[(↑m : ArithmeticTerm ℕ)])
          (insert (∼(((Rew.subst w').q ▹ a)/[(↑m : ArithmeticTerm ℕ)])) Γ))
        (by rw [← Rew.subst_q_app]; simp) (by rw [← Rew.subst_q_app]; simp)
      rwa [show (((Rew.subst w').q ▹ ∼a)/[(↑m : ArithmeticTerm ℕ)])
        = ∼(((Rew.subst w').q ▹ a)/[(↑m : ArithmeticTerm ℕ)]) by simp]
where
  cons_val_congr {n} {w w' : Fin n → ArithmeticTerm ℕ}
      (h : ∀ i, Semiterm.val (M := ℕ) ![] id (w i) = Semiterm.val (M := ℕ) ![] id (w' i))
      (m : ℕ) : ∀ i, Semiterm.val (M := ℕ) ![] id (((↑m : ArithmeticTerm ℕ) :> w) i)
        = Semiterm.val (M := ℕ) ![] id (((↑m : ArithmeticTerm ℕ) :> w') i) := by
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => simpa using h j

/-- Equal-valued closed substitutions into a formula and its negation are derivable cut-free.

- [Tow20, Section 16] -/
lemma em_cong (s s' : ArithmeticTerm ℕ)
    (h : Semiterm.val (M := ℕ) ![] id s = Semiterm.val (M := ℕ) ![] id s')
    (ψ : ArithmeticSemiformula ℕ 1) (hp : (ψ/[s]) ∈ Γ) (hn : (∼(ψ/[s'])) ∈ Γ) :
    ∃ α, Z∞ ⊢[α, 0] Γ := by
  refine em_congAux ψ.complexity ![s] ![s'] ψ le_rfl ?_ hp hn
  intro i
  cases i using Fin.cases with
  | zero => simpa using h
  | succ j => exact j.elim0

end Provable

end ExcludedMiddle

end FFL.FirstOrder.Arithmetic.OmegaLogic
