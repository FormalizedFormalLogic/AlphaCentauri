module

public import AlphaCentauri.Calculus.Induction.Basic
public import AlphaCentauri.Schemata.Induction
public import AlphaCentauri.ToFoundation.Schemata

/-!
# What `LKI[C]` proves

The induction rule derives the induction axiom for every formula of `C` — which is what its side
formulas are for — so the whole `C`-induction scheme is derivable. A theory whose axioms are all
`LKI[C]`-derivable proves only `LKI[C]`-derivable sentences.

- [Bus98A, Section 1.4.2]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.LKI

open Rewriting LawfulSyntacticRewriting

variable {C : ArithmeticSemiformula ℕ 1 → Prop}
         {φ : ArithmeticProposition} {ξ : ArithmeticSemiformula ℕ 1}
         {T : ArithmeticTheory} {σ : ArithmeticSentence}
         {Γ Δ : LK.Sequent ℒₒᵣ}

/-- A theory whose axioms are all derivable in `LKI[C]` proves only `LKI[C]`-derivable sentences. -/
theorem derivable_of_provable (hT : ∀ σ ∈ T, ⊢ᴸᴷᴵ[C] ⦃σ⦄) (h : T ⊢ σ) : ⊢ᴸᴷᴵ[C] ⦃σ⦄ := by
  obtain ⟨Δ, hΔ, hd⟩ := Theory.Proof.provable_iff.mp h
  apply Derivable.cutAll ?_ (Derivable.ofLK hd)
  · rintro δ hδ;
    obtain ⟨ψ, hψ, rfl⟩ := Multiset.mem_map.mp (by simpa [LK.Sequent.embed] using hδ)
    exact hT ψ (hΔ ψ hψ)

/-- Every axiom of `𝗣𝗔⁻` has an anchored derivation: it is a leaf of the calculus. -/
theorem nonempty_anchored_of_mem_peanoMinus {D : ArithmeticProposition → Prop} (h : σ ∈ 𝗣𝗔⁻) :
    ⊢ᴸᴷᴵ[C, D] ⦃(σ : ArithmeticProposition)⦄ := ⟨⟨.axm h, by simp⟩⟩

/-- Every axiom of `𝗣𝗔⁻` is derivable. -/
theorem derivable_of_mem_peanoMinus (h : σ ∈ 𝗣𝗔⁻) : ⊢ᴸᴷᴵ[C] ⦃(σ : ArithmeticProposition)⦄ :=
  Nonempty.map Subtype.val
    (nonempty_anchored_of_mem_peanoMinus (C := C) (D := fun _ ↦ True) h)

variable [RewriteClosed C]

/-- The induction axiom for a formula of `C` is derivable: the induction rule, with its side
formulas, is as strong as the induction scheme for `C`.

- [Bus98A, Section 1.4.2] -/
theorem derivable_succInd (hξ : C ξ) : ⊢ᴸᴷᴵ[C] ⦃succInd ξ⦄ := by
  have step : ∀ η : ArithmeticSemiformula ℕ 1,
      ⊢ᴸᴷᴵ[C] ⦃∼(η/[&0]), η/[‘(&0 + 1)’]⦄ + ⦃∃¹ (η ⋏ ∼(η/[‘(#0 + 1)’]))⦄ := by
    intro η
    apply Derivable.exs &0
    rw [show (η ⋏ ∼(η/[‘(#0 + 1)’]))/[&0] = η/[&0] ⋏ ∼(η/[‘(&0 + 1)’])
        from by simp [Rew.subst_subst_eq]]
    apply Derivable.and
    · exact (Derivable.weakening (η/[‘(&0 + 1)’]) (Derivable.lem (η/[&0]))).cast (by abel)
    · exact (Derivable.weakening (∼(η/[&0])) (Derivable.lem (η/[‘(&0 + 1)’]))).cast (by abel)
  have key : ⊢ᴸᴷᴵ[C] ⦃∼(ξ/[‘0’]), ∃¹ (ξ ⋏ ∼(ξ/[‘(#0 + 1)’])), ∀¹ ξ⦄ := by
    apply Derivable.all
    have h := Derivable.ind' (ξ := shift ξ) (RewriteClosed.shift hξ) &0
      (Γ := ⦃shift (∃¹ (ξ ⋏ ∼(ξ/[‘(#0 + 1)’])))⦄)
      ((step (shift (shift ξ))).cast (by simp [Rewriting.shifts, Rew.shift_subst_eq]; try abel))
    exact h.cast (by simp [Rewriting.shifts, Rew.shift_subst_eq]; try abel)
  rw [show (succInd ξ : ArithmeticProposition)
      = ∼(ξ/[‘0’]) ⋎ ((∃¹ (ξ ⋏ ∼(ξ/[‘(#0 + 1)’]))) ⋎ (∀¹ ξ))
      from by simp [succInd, Semiformula.imp_eq]]
  have h₁ : ⊢ᴸᴷᴵ[C] ⦃∼(ξ/[‘0’])⦄ + ⦃∃¹ (ξ ⋏ ∼(ξ/[‘(#0 + 1)’])), ∀¹ ξ⦄ := key.cast (by abel)
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

/-- `LKI[C]` derives everything that `𝗣𝗔⁻` with `C`-induction proves.

- [Bus98A, Section 1.4.2] -/
theorem derivable_of_provable_induction (h : 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ C ⊢ σ) : ⊢ᴸᴷᴵ[C] ⦃σ⦄ := by
  refine derivable_of_provable ?_ h
  rintro α (hα | hα)
  · exact derivable_of_mem_peanoMinus hα
  · exact derivable_of_mem_inductionScheme hα

/-- `LKI` over the strict $\Sigma_1$ formulas derives everything `𝗜 𝚺 1` proves: the induction
scheme of `𝗜 𝚺 1` is the one its induction rule is as strong as.

- [Bus98A, Section 1.4.2] -/
theorem derivable_of_provable_inductionOnStrictHierarchy {b : Polarity} {s : ℕ}
    (h : 𝗜 b s ⊢ σ) : ⊢ᴸᴷᴵ[StrictHierarchy b s] ⦃σ⦄ := derivable_of_provable_induction h

end FFL.FirstOrder.Arithmetic.LKI

end
