module

public import AlphaCentauri.Calculus.Induction.Basic
public import AlphaCentauri.Hierarchy.Bound
public import AlphaCentauri.ToFoundation.Hierarchy

/-!
# Witnessing

From an anchored `LKI[C]` derivation of a sequent of strict $\Sigma_1$ and strict $\Pi_1$
formulas one reads a primitive recursive bound on the witnesses: if every non-$\Sigma_1$ formula
of the sequent is refuted below `b`, then some $\Sigma_1$ formula of the sequent holds below
`h l b`. The induction rule contributes the primitive recursion, every other rule a `max`.

- [Bus98A, Section 3.1.3]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.LKI

open Rewriting LawfulSyntacticRewriting

variable {Γ Δ : LK.Sequent ℒₒᵣ} {φ ψ : ArithmeticProposition} {h h' : List ℕ → ℕ → ℕ}

/-- `Witnesses Γ h` says that `h` bounds the witnesses of the $\Sigma_1$ formulas of `Γ`: if every
non-$\Sigma_1$ formula of `Γ` is refuted below `b` under `l`, then some $\Sigma_1$ formula of `Γ`
holds below `h l b`.

- [Bus98A, Section 3.1.3] -/
def Witnesses (Γ : LK.Sequent ℒₒᵣ) (h : List ℕ → ℕ → ℕ) : Prop :=
  ∀ (l : List ℕ) (b : ℕ), (∀ ψ ∈ Γ, ¬StrictHierarchy 𝚺 1 ψ → Bnd (∼ψ) b (l.getD · 0)) →
    ∃ φ ∈ Γ, StrictHierarchy 𝚺 1 φ ∧ Bnd φ (h l b) (l.getD · 0)

namespace Witnesses

lemma mono (H : Witnesses Γ h) (hle : ∀ l b, h l b ≤ h' l b) : Witnesses Γ h' := by
  intro l b hb
  obtain ⟨φ, hφ, hσ, hbnd⟩ := H l b hb
  exact ⟨φ, hφ, hσ, bnd_mono (hle l b) hbnd⟩

/-- A sequent whose formulas are those of a witnessed one is witnessed by the same bound. -/
lemma ofSubset (H : Witnesses Γ h) (hs : Γ ⊆ Δ) : Witnesses Δ h := by
  intro l b hb
  obtain ⟨φ, hφ, hσ, hbnd⟩ := H l b fun ψ hψ ↦ hb ψ (hs hψ)
  exact ⟨φ, hs hφ, hσ, hbnd⟩

/-- Sequents with the same formulas are witnessed alike. -/
lemma cast (H : Witnesses Γ h) (e : Γ = Δ) : Witnesses Δ h := e ▸ H

end Witnesses

/-! ## The leaves -/

lemma witnesses_verum : Witnesses ⦃(⊤ : ArithmeticProposition)⦄ fun _ _ ↦ 0 := by
  intro l b _
  exact ⟨⊤, by simp, StrictHierarchy.of_bounded (Hierarchy.verum _ _ _), by simp⟩

lemma witnesses_identity {k} (R : (ℒₒᵣ).Rel k) (v) :
    Witnesses ⦃Semiformula.rel R v, Semiformula.nrel R v⦄ fun _ _ ↦ 0 := by
  intro l b _
  by_cases hv : Semiformula.Eval ![] (l.getD · 0) (Semiformula.rel R v)
  · exact ⟨Semiformula.rel R v, by simp, StrictHierarchy.of_bounded (Hierarchy.rel _ _ R v),
      by simpa using hv⟩
  · exact ⟨Semiformula.nrel R v, by simp, StrictHierarchy.of_bounded (Hierarchy.nrel _ _ R v),
      by simpa using hv⟩

lemma exists_witnesses_axm {σ : ArithmeticSentence} (hσ : σ ∈ 𝗣𝗔⁻) :
    ∃ c, Witnesses ⦃(Rewriting.emb σ : ArithmeticProposition)⦄ fun _ _ ↦ c := by
  have htrue : ∀ ε : ℕ → ℕ, (Rewriting.emb σ : ArithmeticProposition).Evalf ε := by
    intro ε
    simpa [models_iff] using Theory.models (M := ℕ) _ hσ
  by_cases hs : StrictHierarchy 𝚺 1 (Rewriting.emb σ : ArithmeticProposition)
  · obtain ⟨c, hc⟩ := exists_bnd_of_closed hs (by simp [Semiformula.FVar?]) htrue
    exact ⟨c, fun l _ _ ↦ ⟨_, by simp, hs, hc _⟩⟩
  · refine ⟨0, fun l b hb ↦ absurd (htrue (l.getD · 0)) ?_⟩
    simpa using evalf_of_bnd (hb _ (by simp) hs)

/-! ## The propositional rules -/

lemma witnesses_weakening (H : Witnesses Γ h) : Witnesses (Γ + ⦃φ⦄) h :=
  H.ofSubset (Multiset.subset_of_le (Multiset.le_add_right _ _))

lemma witnesses_contraction (H : Witnesses (Γ + ⦃φ, φ⦄) h) : Witnesses (Γ + ⦃φ⦄) h :=
  H.ofSubset fun χ hχ ↦ by
    rcases Multiset.mem_add.mp hχ with hχ | hχ
    · simp [hχ]
    · simp_all

lemma witnesses_or (hd : (φ ⋎ ψ).Bounded) (H : Witnesses (Γ + ⦃φ, ψ⦄) h) :
    Witnesses (Γ + ⦃φ ⋎ ψ⦄) h := by
  obtain ⟨hφ, hψ⟩ := Hierarchy.or_iff.mp hd
  intro l b hb
  obtain ⟨χ, hχ, hσ, hbnd⟩ := H l b fun χ hχ hnσ ↦ by
    rcases Multiset.mem_add.mp hχ with hχ | hχ
    · exact hb χ (by simp [hχ]) hnσ
    · rcases show χ = φ ∨ χ = ψ by simpa using hχ with rfl | rfl
      · exact absurd (StrictHierarchy.of_bounded hφ) hnσ
      · exact absurd (StrictHierarchy.of_bounded hψ) hnσ
  rcases Multiset.mem_add.mp hχ with hχ | hχ
  · exact ⟨χ, by simp [hχ], hσ, hbnd⟩
  · refine ⟨φ ⋎ ψ, by simp, StrictHierarchy.of_bounded hd, ?_⟩
    rcases show χ = φ ∨ χ = ψ by simpa using hχ with rfl | rfl
    · simpa using Or.inl (eval_of_evalBound hbnd)
    · simpa using Or.inr (eval_of_evalBound hbnd)

lemma witnesses_and (hd : (φ ⋏ ψ).Bounded) (H₁ : Witnesses (Γ + ⦃φ⦄) h)
    (H₂ : Witnesses (Γ + ⦃ψ⦄) h') : Witnesses (Γ + ⦃φ ⋏ ψ⦄) fun l b ↦ max (h l b) (h' l b) := by
  obtain ⟨hφ, hψ⟩ := Hierarchy.and_iff.mp hd
  intro l b hb
  have hb₁ : ∀ χ ∈ Γ + ⦃φ⦄, ¬StrictHierarchy 𝚺 1 χ → Bnd (∼χ) b (l.getD · 0) := fun χ hχ hnσ ↦ by
    rcases Multiset.mem_add.mp hχ with hχ | hχ
    · exact hb χ (by simp [hχ]) hnσ
    · rcases show χ = φ by simpa using hχ
      exact absurd (StrictHierarchy.of_bounded hφ) hnσ
  have hb₂ : ∀ χ ∈ Γ + ⦃ψ⦄, ¬StrictHierarchy 𝚺 1 χ → Bnd (∼χ) b (l.getD · 0) := fun χ hχ hnσ ↦ by
    rcases Multiset.mem_add.mp hχ with hχ | hχ
    · exact hb χ (by simp [hχ]) hnσ
    · rcases show χ = ψ by simpa using hχ
      exact absurd (StrictHierarchy.of_bounded hψ) hnσ
  obtain ⟨χ₁, hχ₁, hσ₁, hbnd₁⟩ := H₁ l b hb₁
  obtain ⟨χ₂, hχ₂, hσ₂, hbnd₂⟩ := H₂ l b hb₂
  rcases Multiset.mem_add.mp hχ₁ with hm₁ | hm₁
  · exact ⟨χ₁, by simp [hm₁], hσ₁, bnd_mono (le_max_left _ _) hbnd₁⟩
  rcases Multiset.mem_add.mp hχ₂ with hm₂ | hm₂
  · exact ⟨χ₂, by simp [hm₂], hσ₂, bnd_mono (le_max_right _ _) hbnd₂⟩
  rcases show χ₁ = φ by simpa using hm₁
  rcases show χ₂ = ψ by simpa using hm₂
  exact ⟨φ ⋏ ψ, by simp, StrictHierarchy.of_bounded hd,
    by simpa using ⟨eval_of_evalBound hbnd₁, eval_of_evalBound hbnd₂⟩⟩

/-! ## The existential rule -/

lemma witnesses_exs {ξ : ArithmeticSemiformula ℕ 1} {t : ArithmeticTerm ℕ}
    (hσ : StrictHierarchy 𝚺 1 (∃¹ ξ)) (H : Witnesses (Γ + ⦃ξ/[t]⦄) h) :
    Witnesses (Γ + ⦃∃¹ ξ⦄) fun l b ↦ max (h l b) (Semiterm.val ![] (l.getD · 0) t + 1) := by
  have hsub : StrictHierarchy 𝚺 1 (ξ/[t]) := StrictHierarchy.rew _ (StrictHierarchy.of_exs hσ)
  intro l b hb
  obtain ⟨χ, hχ, hσχ, hbnd⟩ := H l b fun χ hχ hnσ ↦ by
    rcases Multiset.mem_add.mp hχ with hχ | hχ
    · exact hb χ (by simp [hχ]) hnσ
    · rcases show χ = ξ/[t] by simpa using hχ
      exact absurd hsub hnσ
  rcases Multiset.mem_add.mp hχ with hm | hm
  · exact ⟨χ, by simp [hm], hσχ, bnd_mono (le_max_left _ _) hbnd⟩
  rcases show χ = ξ/[t] by simpa using hm
  refine ⟨∃¹ ξ, by simp, hσ, Semiterm.val ![] (l.getD · 0) t,
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _), ?_⟩
  have h₁ := bnd_mono (le_max_left (h l b) (Semiterm.val ![] (l.getD · 0) t + 1)) hbnd
  rw [Bnd, Rewriting.subst, evalBound_rew] at h₁
  have e₁ : ((Semiterm.val ![] fun x ↦ l.getD x 0) ∘ ⇑(Rew.subst ![t]) ∘ Semiterm.bvar)
      = ![Semiterm.val ![] (fun x ↦ l.getD x 0) t] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ i => exact i.elim0
  have e₂ : ((Semiterm.val ![] fun x ↦ l.getD x 0) ∘ ⇑(Rew.subst ![t]) ∘ Semiterm.fvar)
      = fun x ↦ l.getD x 0 := by funext y; simp
  rw [e₁, e₂] at h₁
  exact h₁

end FFL.FirstOrder.Arithmetic.LKI

end
