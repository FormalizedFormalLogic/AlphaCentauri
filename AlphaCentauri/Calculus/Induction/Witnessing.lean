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

/-! ## The cut rule -/

private lemma witnesses_cut_sigma {χ : ArithmeticProposition} (hσ : StrictHierarchy 𝚺 1 χ)
    (H₁ : Witnesses (Γ + ⦃χ⦄) h) (H₂ : Witnesses (Δ + ⦃∼χ⦄) h') :
    Witnesses (Γ + Δ) fun l b ↦ max (h l b) (h' l (max b (h l b))) := by
  intro l b hb
  obtain ⟨χ₁, hχ₁, hσ₁, hbnd₁⟩ := H₁ l b fun ψ hψ hnσ ↦ by
    rcases Multiset.mem_add.mp hψ with hψ | hψ
    · exact hb ψ (by simp [hψ]) hnσ
    · rcases show ψ = χ by simpa using hψ
      exact absurd hσ hnσ
  rcases Multiset.mem_add.mp hχ₁ with hm | hm
  · exact ⟨χ₁, by simp [hm], hσ₁, bnd_mono (le_max_left _ _) hbnd₁⟩
  rcases show χ₁ = χ by simpa using hm
  obtain ⟨χ₂, hχ₂, hσ₂, hbnd₂⟩ := H₂ l (max b (h l b)) fun ψ hψ hnσ ↦ by
    rcases Multiset.mem_add.mp hψ with hψ | hψ
    · exact bnd_mono (le_max_left _ _) (hb ψ (by simp [hψ]) hnσ)
    · rcases show ψ = ∼χ by simpa using hψ
      simpa using bnd_mono (le_max_right _ _) hbnd₁
  rcases Multiset.mem_add.mp hχ₂ with hm₂ | hm₂
  · exact ⟨χ₂, by simp [hm₂], hσ₂, bnd_mono (le_max_right _ _) hbnd₂⟩
  rcases show χ₂ = ∼χ by simpa using hm₂
  exact absurd (eval_of_evalBound hbnd₁) (by simpa using eval_of_evalBound hbnd₂)

lemma witnesses_cut {χ : ArithmeticProposition}
    (hχ : StrictHierarchy 𝚺 1 χ ∨ StrictHierarchy 𝚷 1 χ)
    (H₁ : Witnesses (Γ + ⦃χ⦄) h) (H₂ : Witnesses (Δ + ⦃∼χ⦄) h') :
    Witnesses (Γ + Δ) fun l b ↦
      max (max (h l b) (h' l (max b (h l b)))) (max (h' l b) (h l (max b (h' l b)))) := by
  rcases hχ with hσ | hπ
  · exact (witnesses_cut_sigma hσ H₁ H₂).mono fun _ _ ↦ le_max_left _ _
  · have H₁' : Witnesses (Γ + ⦃∼∼χ⦄) h := by simpa using H₁
    exact ((witnesses_cut_sigma (StrictHierarchy.neg hπ) H₂ H₁').cast (by abel)).mono
      fun _ _ ↦ le_max_right _ _

/-! ## The universal rule -/

/-- The maximum of `f` below `n`. -/
def maxBelow (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => max (f n) (maxBelow f n)

lemma le_maxBelow (f : ℕ → ℕ) {x : ℕ} : {n : ℕ} → x < n → f x ≤ maxBelow f n
  | 0, h => absurd h (by simp)
  | n + 1, h => by
    rcases (Nat.lt_succ_iff.mp h).lt_or_eq with h' | rfl
    · exact le_trans (le_maxBelow f h') (le_max_right _ _)
    · exact le_max_left _ _

private lemma evalBound_shift {n : ℕ} {χ : ArithmeticSemiformula ℕ n} {e : Fin n → ℕ} {c x : ℕ}
    {l : List ℕ} :
    EvalBound e ((x :: l).getD · 0) c (Rewriting.shift χ) ↔ EvalBound e (l.getD · 0) c χ := by
  have e₁ : ((Semiterm.val e fun y ↦ (x :: l).getD y 0) ∘
      ⇑(Rew.shift : SyntacticRew ℒₒᵣ n n) ∘ Semiterm.bvar) = e := by funext i; simp
  have e₂ : ((Semiterm.val e fun y ↦ (x :: l).getD y 0) ∘
      ⇑(Rew.shift : SyntacticRew ℒₒᵣ n n) ∘ Semiterm.fvar) = fun y ↦ l.getD y 0 := by
    funext y; simp
  simp only [Rewriting.shift]
  rw [evalBound_rew, e₁, e₂]

private lemma bnd_shift {χ : ArithmeticProposition} {c x : ℕ} {l : List ℕ} :
    Bnd (Rewriting.shift χ) c ((x :: l).getD · 0) ↔ Bnd χ c (l.getD · 0) := evalBound_shift

private lemma bnd_subst {ξ : ArithmeticSemiformula ℕ 1} {s : ArithmeticTerm ℕ} {c : ℕ}
    {l : List ℕ} :
    Bnd (ξ/[s]) c (l.getD · 0) ↔
      EvalBound ![Semiterm.val ![] (l.getD · 0) s] (l.getD · 0) c ξ := by
  have e₁ : ((Semiterm.val ![] fun y ↦ l.getD y 0) ∘ ⇑(Rew.subst ![s]) ∘ Semiterm.bvar)
      = ![Semiterm.val ![] (fun y ↦ l.getD y 0) s] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ i => exact i.elim0
  have e₂ : ((Semiterm.val ![] fun y ↦ l.getD y 0) ∘ ⇑(Rew.subst ![s]) ∘ Semiterm.fvar)
      = fun y ↦ l.getD y 0 := by funext y; simp
  simp only [Bnd, Rewriting.subst]
  rw [evalBound_rew, e₁, e₂]

private lemma bnd_free {χ : ArithmeticSemiformula ℕ 1} {c x : ℕ} {l : List ℕ} :
    Bnd (Rewriting.free χ) c ((x :: l).getD · 0) ↔ EvalBound ![x] (l.getD · 0) c χ := by
  have e₁ : ((Semiterm.val ![] fun y ↦ (x :: l).getD y 0) ∘
      ⇑(Rew.free : SyntacticRew ℒₒᵣ 1 0) ∘ Semiterm.bvar) = ![x] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ i => exact i.elim0
  have e₂ : ((Semiterm.val ![] fun y ↦ (x :: l).getD y 0) ∘
      ⇑(Rew.free : SyntacticRew ℒₒᵣ 1 0) ∘ Semiterm.fvar) = fun y ↦ l.getD y 0 := by
    funext y; simp
  simp only [Bnd, Rewriting.free]
  rw [evalBound_rew, e₁, e₂]

/-- The universal rule when the principal formula is not $\Sigma_1$: the hypothesis refutes it
below `b`, which bounds the counterexample. -/
lemma witnesses_all_pi {ξ : ArithmeticSemiformula ℕ 1} (hnσ : ¬StrictHierarchy 𝚺 1 (∀¹ ξ))
    (H : Witnesses (Γ⁺ + ⦃Rewriting.free ξ⦄) h) :
    Witnesses (Γ + ⦃∀¹ ξ⦄) fun l b ↦ maxBelow (fun x ↦ h (x :: l) b) b := by
  intro l b hb
  obtain ⟨x₀, hx₀, hrefute⟩ : ∃ x < b, EvalBound ![x] (l.getD · 0) b (∼ξ) := by
    simpa using hb (∀¹ ξ) (by simp) hnσ
  obtain ⟨χ, hχ, hσχ, hbnd⟩ := H (x₀ :: l) b fun ψ hψ hnσψ ↦ by
    rcases Multiset.mem_add.mp hψ with hψ | hψ
    · obtain ⟨ψ', hψ', rfl⟩ := Multiset.mem_map.mp hψ
      have : ¬StrictHierarchy 𝚺 1 ψ' := by simpa [Rewriting.shift] using hnσψ
      simpa using bnd_shift.mpr (hb ψ' (by simp [hψ']) this)
    · rcases show ψ = Rewriting.free ξ by simpa using hψ
      simpa using bnd_free.mpr hrefute
  rcases Multiset.mem_add.mp hχ with hm | hm
  · obtain ⟨χ', hχ', rfl⟩ := Multiset.mem_map.mp hm
    exact ⟨χ', by simp [hχ'], by simpa [Rewriting.shift] using hσχ,
      bnd_mono (le_maxBelow _ hx₀) (bnd_shift.mp hbnd)⟩
  · rcases show χ = Rewriting.free ξ by simpa using hm
    exact absurd (eval_of_evalBound (bnd_free.mp hbnd))
      (by simpa using eval_of_evalBound hrefute)

/-- The universal rule when the principal formula is a bounded universal: the term bounds the
counterexample. -/
lemma witnesses_all_bounded {ψ : ArithmeticSemiformula ℕ 1} {t : ArithmeticTerm ℕ}
    (hψ : Hierarchy 𝚺 0 ψ)
    (H : Witnesses (Γ⁺ + ⦃Rewriting.free (“#0 < !!(Rew.bShift t)” 🡒 ψ)⦄) h) :
    Witnesses (Γ + ⦃∀¹[“#0 < !!(Rew.bShift t)”] ψ⦄)
      fun l b ↦ maxBelow (fun x ↦ h (x :: l) b) (Semiterm.val ![] (l.getD · 0) t) := by
  have hd : Hierarchy 𝚺 0 (∀¹[“#0 < !!(Rew.bShift t)”] ψ) :=
    Hierarchy.ball (Rew.positive_iff.mpr ⟨t, rfl⟩) hψ
  have hbody : Hierarchy 𝚺 0 (“#0 < !!(Rew.bShift t)” 🡒 ψ) := by
    simp [Semiformula.imp_eq, hψ]
  intro l b hb
  by_cases hex : ∃ x < Semiterm.val ![] (l.getD · 0) t,
      ∃ γ ∈ Γ, StrictHierarchy 𝚺 1 γ ∧ Bnd γ (h (x :: l) b) (l.getD · 0)
  · obtain ⟨x, hx, γ, hγ, hσγ, hbnd⟩ := hex
    exact ⟨γ, by simp [hγ], hσγ, bnd_mono (le_maxBelow _ hx) hbnd⟩
  push Not at hex
  refine ⟨∀¹[“#0 < !!(Rew.bShift t)”] ψ, by simp, StrictHierarchy.of_bounded hd, ?_⟩
  have hall : ∀ x < Semiterm.val ![] (l.getD · 0) t, Semiformula.Eval ![x] (l.getD · 0) ψ := by
    intro x hx
    obtain ⟨χ, hχ, hσχ, hbnd⟩ := H (x :: l) b fun ρ hρ hnσρ ↦ by
      rcases Multiset.mem_add.mp hρ with hρ | hρ
      · obtain ⟨ρ', hρ', rfl⟩ := Multiset.mem_map.mp hρ
        have : ¬StrictHierarchy 𝚺 1 ρ' := by simpa [Rewriting.shift] using hnσρ
        simpa using bnd_shift.mpr (hb ρ' (by simp [hρ']) this)
      · rcases show ρ = Rewriting.free (“#0 < !!(Rew.bShift t)” 🡒 ψ) by simpa using hρ
        exact absurd (StrictHierarchy.of_bounded (Hierarchy.rew _ hbody)) hnσρ
    rcases Multiset.mem_add.mp hχ with hm | hm
    · obtain ⟨χ', hχ', rfl⟩ := Multiset.mem_map.mp hm
      exact absurd (bnd_shift.mp hbnd)
        (hex x hx χ' (by simpa using hχ') (by simpa [Rewriting.shift] using hσχ))
    · rcases show χ = Rewriting.free (“#0 < !!(Rew.bShift t)” 🡒 ψ) by simpa using hm
      have h' : x < Semiterm.val ![] (l.getD · 0) t → Semiformula.Eval ![x] (l.getD · 0) ψ := by
        simpa using eval_of_evalBound (bnd_free.mp hbnd)
      exact h' hx
  simpa [FFL.FirstOrder.ball] using fun x hx ↦ hall x hx

/-! ## The induction rule -/

/-- The bounds the induction rule iterates: `b` at `0`, and at each step the larger of the
current bound and what the premise gives. -/
def indBound (h : List ℕ → ℕ → ℕ) (l : List ℕ) (b : ℕ) : ℕ → ℕ
  | 0 => b
  | n + 1 => max (indBound h l b n) (h (n :: l) (indBound h l b n))

lemma le_indBound (h : List ℕ → ℕ → ℕ) (l : List ℕ) (b : ℕ) : ∀ n, b ≤ indBound h l b n
  | 0 => le_rfl
  | n + 1 => le_trans (le_indBound h l b n) (le_max_left _ _)

/-- The induction rule: the bound is iterated along the term. `B` supplies the standard bound of
the induction formula, which is called for only when that formula is $\Delta_0$. -/
lemma witnesses_ind {ξ : ArithmeticSemiformula ℕ 1} {t : ArithmeticTerm ℕ} {B : List ℕ → ℕ}
    (hξ : StrictHierarchy 𝚺 1 ξ)
    (hB : Hierarchy 𝚺 0 ξ → ∀ (x : ℕ) (l : List ℕ),
      (Semiformula.Eval ![x] (l.getD · 0) ξ → EvalBound ![x] (l.getD · 0) (B l) ξ) ∧
        (Semiformula.Eval ![x] (l.getD · 0) (∼ξ) → EvalBound ![x] (l.getD · 0) (B l) (∼ξ)))
    (H : Witnesses (Γ⁺ + ⦃∼(Rewriting.free ξ), (Rewriting.shift ξ)/[‘&0 + 1’]⦄) h) :
    Witnesses (Γ + ⦃∼(ξ/[‘0’]), ξ/[t]⦄)
      fun l b ↦ indBound h l (max b (B l)) (Semiterm.val ![] (l.getD · 0) t) := by
  intro l b hb
  set c : ℕ → ℕ := indBound h l (max b (B l)) with hcdef
  have hbc : ∀ n, b ≤ c n := fun n ↦ le_trans (le_max_left _ _) (le_indBound _ _ _ n)
  have key : ∀ n : ℕ,
      (∃ φ ∈ Γ + ⦃∼(ξ/[(‘0’ : ArithmeticTerm ℕ)]), ξ/[t]⦄,
        StrictHierarchy 𝚺 1 φ ∧ Bnd φ (c n) (l.getD · 0)) ∨
      EvalBound ![n] (l.getD · 0) (c n) ξ := by
    intro n
    induction n with
    | zero =>
      by_cases hz : StrictHierarchy 𝚺 1 (∼(ξ/[(‘0’ : ArithmeticTerm ℕ)]) : ArithmeticProposition)
      · have hπξ : StrictHierarchy 𝚷 1 ξ := by
          have hπ : StrictHierarchy 𝚷 1 (ξ/[(‘0’ : ArithmeticTerm ℕ)]) := by simpa using hz
          simpa [Rewriting.subst] using hπ
        have hΔ : Hierarchy 𝚺 0 ξ := StrictHierarchy.bounded_of_sigmaOne_of_piOne hξ hπξ
        have hBc : B l ≤ c 0 := le_trans (le_max_right _ _) (le_indBound _ _ _ 0)
        by_cases hev : Semiformula.Eval ![0] (l.getD · 0) ξ
        · exact Or.inr (evalBound_mono hBc ((hB hΔ 0 l).1 hev))
        · refine Or.inl ⟨∼(ξ/[(‘0’ : ArithmeticTerm ℕ)]), by simp, hz, ?_⟩
          have hn : EvalBound ![0] (l.getD · 0) (c 0) (∼ξ) :=
            evalBound_mono hBc ((hB hΔ 0 l).2 (by simpa using hev))
          have hs : Bnd ((∼ξ)/[(‘0’ : ArithmeticTerm ℕ)]) (c 0) (l.getD · 0) :=
            bnd_subst.mpr (by simpa using hn)
          simpa using hs
      · refine Or.inr (evalBound_mono (hbc 0) ?_)
        have h₀ : Bnd (ξ/[(‘0’ : ArithmeticTerm ℕ)]) b (l.getD · 0) := by
          simpa using hb (∼(ξ/[(‘0’ : ArithmeticTerm ℕ)])) (by simp) hz
        simpa using bnd_subst.mp h₀
    | succ n ih =>
      rcases ih with ⟨φ, hφ, hσφ, hbnd⟩ | hinv
      · exact Or.inl ⟨φ, hφ, hσφ, bnd_mono (le_max_left _ _) hbnd⟩
      obtain ⟨χ, hχ, hσχ, hbndχ⟩ := H (n :: l) (c n) fun ρ hρ hnσρ ↦ by
        rcases Multiset.mem_add.mp hρ with hρ | hρ
        · obtain ⟨ρ', hρ', rfl⟩ := Multiset.mem_map.mp hρ
          have hnσ' : ¬StrictHierarchy 𝚺 1 ρ' := by simpa [Rewriting.shift] using hnσρ
          simpa using bnd_shift.mpr (bnd_mono (hbc n) (hb ρ' (by simp [hρ']) hnσ'))
        · rcases show ρ = ∼(Rewriting.free ξ) ∨ ρ = (Rewriting.shift ξ)/[‘&0 + 1’] by
            simpa using hρ with rfl | rfl
          · simpa using bnd_free.mpr hinv
          · exact absurd (StrictHierarchy.rew _ (StrictHierarchy.rew _ hξ)) hnσρ
      rcases Multiset.mem_add.mp hχ with hm | hm
      · obtain ⟨γ, hγ, rfl⟩ := Multiset.mem_map.mp hm
        exact Or.inl ⟨γ, by simp [hγ], by simpa [Rewriting.shift] using hσχ,
          bnd_mono (le_max_right _ _) (bnd_shift.mp hbndχ)⟩
      rcases show χ = ∼(Rewriting.free ξ) ∨ χ = (Rewriting.shift ξ)/[‘&0 + 1’] by
        simpa using hm with rfl | rfl
      · have hneg : EvalBound ![n] (l.getD · 0) (h (n :: l) (c n)) (∼ξ) :=
          bnd_free.mp (by simpa using hbndχ)
        exact absurd (eval_of_evalBound hinv) (by simpa using eval_of_evalBound hneg)
      · refine Or.inr (evalBound_mono (le_max_right _ _) ?_)
        have h₁ := bnd_subst.mp hbndχ
        simpa using evalBound_shift.mp (by simpa using h₁)
  rcases key (Semiterm.val ![] (l.getD · 0) t) with ⟨φ, hφ, hσφ, hbnd⟩ | hinv
  · exact ⟨φ, hφ, hσφ, hbnd⟩
  · exact ⟨ξ/[t], by simp, StrictHierarchy.rew _ hξ, bnd_subst.mpr hinv⟩

end FFL.FirstOrder.Arithmetic.LKI

end
