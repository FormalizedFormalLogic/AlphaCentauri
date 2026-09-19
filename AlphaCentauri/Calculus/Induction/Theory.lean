module

public import AlphaCentauri.Calculus.Induction.Basic
public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# What `LKI[C]` proves

The induction rule derives the induction axiom for every formula of `C` — which is what its side
formulas are for — so the whole `C`-induction scheme is derivable. A theory whose axioms are all
`LKI[C]`-derivable proves only `LKI[C]`-derivable sentences, and the `bounded` leaf is already
complete for the sequents of strict $\Pi_1$ formulas true in `ℕ`.

- [Bus98A, Section 1.4.2]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.LKI

open Rewriting LawfulSyntacticRewriting

variable {C : ArithmeticSemiformula ℕ 1 → Prop} {ξ : ArithmeticSemiformula ℕ 1}

namespace Derivable

variable {Γ : LK.Sequent ℒₒᵣ}

/-- Cutting a multiset of derivable formulas off a derivation. -/
lemma cutAll : ∀ Δ : LK.Sequent ℒₒᵣ, (∀ δ ∈ Δ, ⊢ᴸᴷᴵ[C] ⦃δ⦄) → ⊢ᴸᴷᴵ[C] Γ + ∼Δ → ⊢ᴸᴷᴵ[C] Γ := by
  intro Δ
  induction Δ using Multiset.induction_on with
  | empty => intro _ h; simpa using h
  | cons δ Δ ih =>
    intro hΔ h
    refine ih (fun d hd ↦ hΔ d (by simp [hd])) ?_
    have h₁ : ⊢ᴸᴷᴵ[C] (0 : LK.Sequent ℒₒᵣ) + ⦃δ⦄ := (hΔ δ (by simp)).cast (by simp)
    have h₂ : ⊢ᴸᴷᴵ[C] (Γ + ∼Δ) + ⦃∼δ⦄ :=
      h.cast (by simp [Multiset.tilde_def, Multiset.add_atom_eq_cons])
    exact (h₁.cut h₂).cast (by simp)

lemma allOne (h : ⊢ᴸᴷᴵ[C] ⦃free ξ⦄) : ⊢ᴸᴷᴵ[C] ⦃∀¹ ξ⦄ :=
  (Derivable.all (Γ := 0) (ξ := ξ) (h.cast (by simp [Rewriting.shifts]))).cast (by simp)

lemma allClosure_fixitr {φ : ArithmeticProposition} (h : ⊢ᴸᴷᴵ[C] ⦃φ⦄) :
    ∀ m : ℕ, ⊢ᴸᴷᴵ[C] ⦃∀¹* (Rew.fixitr 0 m ▹ φ)⦄
  | 0 => by simpa using h
  | m + 1 => by
    simp only [LawfulSyntacticRewriting.allClosure_fixitr]
    apply allOne
    simpa using allClosure_fixitr h m

/-- The universal closure of a derivable formula is derivable. -/
lemma univCl' {φ : ArithmeticProposition} (h : ⊢ᴸᴷᴵ[C] ⦃φ⦄) : ⊢ᴸᴷᴵ[C] ⦃φ.univCl'⦄ :=
  allClosure_fixitr h _

end Derivable

/-! ## Completeness for the true strict `$\Pi_1$` sequents -/

private lemma bounded_of_complexity_zero {φ : ArithmeticProposition} (h : φ.complexity = 0) :
    Semiformula.Bounded φ := by
  match φ with
  | .rel _ _ | .nrel _ _ | ⊤ | ⊥ => simp
  | _ ⋏ _ | _ ⋎ _ | ∀¹ _ | ∃¹ _ => simp at h

private lemma exists_all_of_strictPi1 {φ : ArithmeticProposition} (h : StrictHierarchy 𝚷 1 φ)
    (hb : ¬Semiformula.Bounded φ) : ∃ ξ, φ = ∀¹ ξ ∧ StrictHierarchy 𝚷 1 ξ := by
  rcases h with _ | h | _ | ⟨hξ⟩
  · rcases h with h | _ | _ | _
    · exact absurd h hb
  · exact ⟨_, rfl, hξ⟩

private lemma vecCons_head_tail (ε : ℕ → ℕ) : ε 0 :>ₙ (fun x ↦ ε (x + 1)) = ε := by
  funext x; cases x <;> rfl

/-- A sequent of strict $\Pi_1$ formulas true in `ℕ` under every assignment is derivable: on this
fragment the `bounded` leaf and the universal rule are already complete. -/
theorem derivable_of_valid : ∀ (n : ℕ) (Γ : LK.Sequent ℒₒᵣ),
    (Γ.map Semiformula.complexity).sum ≤ n → (∀ φ ∈ Γ, StrictHierarchy 𝚷 1 φ) →
    (∀ ε : ℕ → ℕ, ∃ φ ∈ Γ, φ.Evalf ε) → ⊢ᴸᴷᴵ[C] Γ := by
  intro n
  induction n with
  | zero =>
    intro Γ hsum hΓ hval
    refine Derivable.bounded Γ (fun φ hφ ↦ bounded_of_complexity_zero (Nat.le_zero.mp ?_)) hval
    exact le_trans (Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hφ)) hsum
  | succ n ih =>
    intro Γ hsum hΓ hval
    by_cases hb : ∀ φ ∈ Γ, Semiformula.Bounded φ
    · exact Derivable.bounded Γ hb hval
    · push Not at hb
      obtain ⟨φ, hφΓ, hφb⟩ := hb
      obtain ⟨ξ, rfl, hξ⟩ := exists_all_of_strictPi1 (hΓ φ hφΓ) hφb
      obtain ⟨Γ', rfl⟩ : ∃ Γ', Γ = Γ' + ⦃∀¹ ξ⦄ := by
        obtain ⟨Γ', rfl⟩ := Multiset.exists_cons_of_mem hφΓ
        exact ⟨Γ', by simp [Multiset.add_atom_eq_cons]⟩
      have hshift : (Γ'⁺).map Semiformula.complexity = Γ'.map Semiformula.complexity := by
        simp [Rewriting.shifts, Multiset.map_map]
      apply Derivable.all
      apply ih
      · simp only [Multiset.map_add, Multiset.sum_add, hshift] at hsum ⊢
        simp [Multiset.atom_eq_singleton] at hsum ⊢
        omega
      · intro ψ hψ
        rcases Multiset.mem_add.mp hψ with h | h
        · obtain ⟨χ, hχ, rfl⟩ := Multiset.mem_map.mp (by simpa [Rewriting.shifts] using h)
          exact StrictHierarchy.rew _ (hΓ χ (by simp [hχ]))
        · have e : ψ = free ξ := by simpa using h
          exact e ▸ StrictHierarchy.rew _ hξ
      · intro ε
        obtain ⟨ψ, hψ, hv⟩ := hval fun x ↦ ε (x + 1)
        rcases Multiset.mem_add.mp hψ with h | h
        · refine ⟨shift ψ, by simpa [Rewriting.shifts] using Or.inl ⟨ψ, h, rfl⟩, ?_⟩
          rw [← vecCons_head_tail ε]
          simpa using hv
        · have e : ψ = ∀¹ ξ := by simpa using h
          subst e
          refine ⟨free ξ, by simp, ?_⟩
          rw [← vecCons_head_tail ε]
          have : ∀ a : ℕ, Semiformula.Eval ![a] (fun x ↦ ε (x + 1)) ξ := by simpa using hv
          simpa using this (ε 0)

variable {T : ArithmeticTheory} {σ : ArithmeticSentence}

/-- A theory whose axioms are all derivable in `LKI[C]` proves only `LKI[C]`-derivable sentences. -/
theorem derivable_of_provable (hT : ∀ σ ∈ T, ⊢ᴸᴷᴵ[C] ⦃σ⦄) (h : T ⊢ σ) : ⊢ᴸᴷᴵ[C] ⦃σ⦄ := by
  obtain ⟨Δ, hΔ, hd⟩ := Theory.Proof.provable_iff.mp h
  refine Derivable.cutAll _ ?_ (Derivable.ofLK hd)
  · rintro δ hδ
    obtain ⟨ψ, hψ, rfl⟩ := Multiset.mem_map.mp (by simpa [LK.Sequent.embed] using hδ)
    exact hT ψ (hΔ ψ hψ)

variable [RewriteClosed C]

/-- The induction axiom for a formula of `C` is derivable: the induction rule, with its side
formulas, is as strong as the induction scheme for `C`.

- [Bus98A, Section 1.4.2] -/
theorem derivable_succInd (hξ : C ξ) : ⊢ᴸᴷᴵ[C] ⦃succInd ξ⦄ := by
  have step : ∀ η : ArithmeticSemiformula ℕ 1,
      ⊢ᴸᴷᴵ[C] ⦃∼(η/[(&0 : ArithmeticTerm ℕ)]), η/[‘(&0 + 1)’]⦄
        + ⦃(∃¹ (η ⋏ ∼(η/[‘(#0 + 1)’])) : ArithmeticProposition)⦄ := by
    intro η
    apply Derivable.exs (&0 : ArithmeticTerm ℕ)
    rw [show (η ⋏ ∼(η/[‘(#0 + 1)’]))/[(&0 : ArithmeticTerm ℕ)]
        = η/[(&0 : ArithmeticTerm ℕ)] ⋏ ∼(η/[‘(&0 + 1)’]) from by simp [Rew.subst_subst_eq]]
    apply Derivable.and
    · exact (Derivable.weakening (η/[‘(&0 + 1)’])
        (Derivable.lem (η/[(&0 : ArithmeticTerm ℕ)]))).cast (by abel)
    · exact (Derivable.weakening (∼(η/[(&0 : ArithmeticTerm ℕ)]))
        (Derivable.lem (η/[‘(&0 + 1)’]))).cast (by abel)
  have key : ⊢ᴸᴷᴵ[C]
      ⦃∼(ξ/[‘0’]), (∃¹ (ξ ⋏ ∼(ξ/[‘(#0 + 1)’])) : ArithmeticProposition), ∀¹ ξ⦄ := by
    apply Derivable.all
    have h := Derivable.ind' (C := C) (ξ := shift ξ) (RewriteClosed.shift hξ) (&0)
      (Γ := ⦃shift (∃¹ (ξ ⋏ ∼(ξ/[‘(#0 + 1)’])) : ArithmeticProposition)⦄)
      ((step (shift (shift ξ))).cast (by simp [Rewriting.shifts, Rew.shift_subst_eq]; try abel))
    exact h.cast (by simp [Rewriting.shifts, Rew.shift_subst_eq]; try abel)
  rw [show (succInd ξ : ArithmeticProposition)
      = ∼(ξ/[‘0’]) ⋎ ((∃¹ (ξ ⋏ ∼(ξ/[‘(#0 + 1)’]))) ⋎ (∀¹ ξ))
      from by simp [succInd, Semiformula.imp_eq]]
  have h₁ : ⊢ᴸᴷᴵ[C] ⦃∼(ξ/[‘0’])⦄
      + ⦃(∃¹ (ξ ⋏ ∼(ξ/[‘(#0 + 1)’])) : ArithmeticProposition), ∀¹ ξ⦄ := key.cast (by abel)
  have h₂ : ⊢ᴸᴷᴵ[C] (0 : LK.Sequent ℒₒᵣ)
      + ⦃∼(ξ/[‘0’]), (∃¹ (ξ ⋏ ∼(ξ/[‘(#0 + 1)’]))) ⋎ (∀¹ ξ)⦄ := (Derivable.or h₁).cast (by abel)
  exact (Derivable.or h₂).cast (by simp)

/-- The induction axiom of the scheme, universally closed, is derivable. -/
theorem derivable_univCl_succInd (hξ : C ξ) : ⊢ᴸᴷᴵ[C] ⦃Semiformula.univCl (succInd ξ)⦄ := by
  simpa using (derivable_succInd hξ).univCl'

/-- Every axiom of the `C`-induction scheme is derivable. -/
theorem derivable_of_mem_inductionScheme (h : σ ∈ InductionScheme ℒₒᵣ C) : ⊢ᴸᴷᴵ[C] ⦃σ⦄ := by
  obtain ⟨ξ, hξ, rfl⟩ := by simpa [InductionScheme] using h
  exact derivable_univCl_succInd hξ

end FFL.FirstOrder.Arithmetic.LKI

end
