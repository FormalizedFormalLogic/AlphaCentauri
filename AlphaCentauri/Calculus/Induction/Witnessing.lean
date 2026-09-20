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

lemma maxBelow_eq_rec (f : ℕ → ℕ) : ∀ n : ℕ,
    maxBelow f n = n.rec (motive := fun _ ↦ ℕ) 0 fun x ih ↦ max (f x) ih
  | 0 => rfl
  | n + 1 => by simp [maxBelow, maxBelow_eq_rec f n]

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

lemma indBound_eq_rec (h : List ℕ → ℕ → ℕ) (l : List ℕ) (b : ℕ) : ∀ n : ℕ,
    indBound h l b n = n.rec (motive := fun _ ↦ ℕ) b fun x ih ↦ max ih (h (x :: l) ih)
  | 0 => rfl
  | n + 1 => by simp [indBound, indBound_eq_rec h l b n]

lemma le_indBound (h : List ℕ → ℕ → ℕ) (l : List ℕ) (b : ℕ) : ∀ n, b ≤ indBound h l b n
  | 0 => le_rfl
  | n + 1 => le_trans (le_indBound h l b n) (le_max_left _ _)

/-- The induction rule: the bound is iterated along the term. `B` supplies the standard bound of
the induction formula, which is called for only when that formula is $\Delta_0$. -/
lemma witnesses_ind {ξ : ArithmeticSemiformula ℕ 1} {t : ArithmeticTerm ℕ} {B : List ℕ → ℕ}
    (hξ : StrictHierarchy 𝚺 1 ξ)
    (hB : Hierarchy 𝚺 0 ξ → ∀ l : List ℕ,
      (Semiformula.Eval ![0] (l.getD · 0) ξ → EvalBound ![0] (l.getD · 0) (B l) ξ) ∧
        (Semiformula.Eval ![0] (l.getD · 0) (∼ξ) → EvalBound ![0] (l.getD · 0) (B l) (∼ξ)))
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
        · exact Or.inr (evalBound_mono hBc ((hB hΔ l).1 hev))
        · refine Or.inl ⟨∼(ξ/[(‘0’ : ArithmeticTerm ℕ)]), by simp, hz, ?_⟩
          have hn : EvalBound ![0] (l.getD · 0) (c 0) (∼ξ) :=
            evalBound_mono hBc ((hB hΔ l).2 (by simpa using hev))
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

/-! ## Primitive recursion of the bounds -/

lemma primrec_maxBelow {f : List ℕ × ℕ → ℕ → ℕ} (hf : Primrec₂ f) {B : List ℕ × ℕ → ℕ}
    (hB : Primrec B) : Primrec fun p : List ℕ × ℕ ↦ maxBelow (f p) (B p) := by
  have hstep : Primrec₂ fun (p : List ℕ × ℕ) (q : ℕ × ℕ) ↦ max (f p q.1) q.2 :=
    Primrec.to₂ (Primrec.nat_max.comp (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))
  have h : Primrec fun p : List ℕ × ℕ ↦
      (B p).rec (motive := fun _ ↦ ℕ) 0 fun x ih ↦ max (f p x) ih :=
    Primrec.nat_rec' hB (Primrec.const 0) hstep
  exact h.of_eq fun p ↦ (maxBelow_eq_rec _ _).symm

lemma primrec_indBound {h : List ℕ → ℕ → ℕ} (hh : Primrec₂ h) {b : List ℕ × ℕ → ℕ}
    (hb : Primrec b) {B : List ℕ × ℕ → ℕ} (hB : Primrec B) :
    Primrec fun p : List ℕ × ℕ ↦ indBound h p.1 (b p) (B p) := by
  have hstep : Primrec₂ fun (p : List ℕ × ℕ) (q : ℕ × ℕ) ↦ max q.2 (h (q.1 :: p.1) q.2) :=
    Primrec.to₂ (Primrec.nat_max.comp (Primrec.snd.comp Primrec.snd)
      (hh.comp
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd)))
  have h' : Primrec fun p : List ℕ × ℕ ↦
      (B p).rec (motive := fun _ ↦ ℕ) (b p) fun x ih ↦ max ih (h (x :: p.1) ih) :=
    Primrec.nat_rec' hB hb hstep
  exact h'.of_eq fun p ↦ (indBound_eq_rec _ _ _ _).symm

/-! ## The witnessing lemma -/

private lemma bounded_of_strictOne {b : Polarity} {φ : ArithmeticProposition}
    (h : StrictHierarchy b 1 φ) (hne : ∀ ψ, φ ≠ ∃¹ ψ) (hna : ∀ ψ, φ ≠ ∀¹ ψ) : φ.Bounded := by
  cases h with
  | ofAlt h => exact StrictHierarchy.bounded_of_zero h
  | exs => exact absurd rfl (hne _)
  | all => exact absurd rfl (hna _)

/-- Witnessing: from an anchored derivation of a sequent of strict $\Sigma_1$ and strict $\Pi_1$
formulas one reads a primitive recursive bound on the witnesses.

- [Bus98A, Section 3.1.3] -/
theorem exists_witnesses : {Γ : LK.Sequent ℒₒᵣ} → (d : ⊢ᴸᴷᴵ[StrictHierarchy 𝚺 1]! Γ) →
    Derivation.Anchored (fun φ ↦ StrictHierarchy 𝚺 1 φ ∨ StrictHierarchy 𝚷 1 φ) d →
    (∀ φ ∈ Γ, StrictHierarchy 𝚺 1 φ ∨ StrictHierarchy 𝚷 1 φ) →
    ∃ h : List ℕ → ℕ → ℕ, Primrec₂ h ∧ Witnesses Γ h
  | _, .axm hσ, _, _ => by
    obtain ⟨c, hc⟩ := exists_witnesses_axm hσ
    exact ⟨_, Primrec₂.const c, hc⟩
  | _, .verum, _, _ => ⟨_, Primrec₂.const 0, witnesses_verum⟩
  | _, .identity R v, _, _ => ⟨_, Primrec₂.const 0, witnesses_identity R v⟩
  | _, .weakening d, hd, hΓ => by
    obtain ⟨h, hp, H⟩ := exists_witnesses d hd fun φ hφ ↦ hΓ φ (by simp [hφ])
    exact ⟨h, hp, witnesses_weakening H⟩
  | _, .contraction d, hd, hΓ => by
    obtain ⟨h, hp, H⟩ := exists_witnesses d hd fun φ hφ ↦ by
      rcases Multiset.mem_add.mp hφ with hφ | hφ
      · exact hΓ φ (by simp [hφ])
      · exact hΓ φ (by simp_all)
    exact ⟨h, hp, witnesses_contraction H⟩
  | _, .or (φ := φ) (ψ := ψ) d, hd, hΓ => by
    have hd0 : (φ ⋎ ψ).Bounded := by
      rcases hΓ (φ ⋎ ψ) (by simp) with h | h <;>
        exact bounded_of_strictOne h (by simp) (by simp)
    obtain ⟨hφ, hψ⟩ := Hierarchy.or_iff.mp hd0
    obtain ⟨h, hp, H⟩ := exists_witnesses d hd fun χ hχ ↦ by
      rcases Multiset.mem_add.mp hχ with hχ | hχ
      · exact hΓ χ (by simp [hχ])
      · rcases show χ = φ ∨ χ = ψ by simpa using hχ with rfl | rfl
        · exact Or.inl (StrictHierarchy.of_bounded hφ)
        · exact Or.inl (StrictHierarchy.of_bounded hψ)
    exact ⟨h, hp, witnesses_or hd0 H⟩
  | _, .and (φ := φ) (ψ := ψ) d₁ d₂, hd, hΓ => by
    have hd0 : (φ ⋏ ψ).Bounded := by
      rcases hΓ (φ ⋏ ψ) (by simp) with h | h <;>
        exact bounded_of_strictOne h (by simp) (by simp)
    obtain ⟨hφ, hψ⟩ := Hierarchy.and_iff.mp hd0
    obtain ⟨h₁, hp₁, H₁⟩ := exists_witnesses d₁ hd.1 fun χ hχ ↦ by
      rcases Multiset.mem_add.mp hχ with hχ | hχ
      · exact hΓ χ (by simp [hχ])
      · rcases show χ = φ by simpa using hχ
        exact Or.inl (StrictHierarchy.of_bounded hφ)
    obtain ⟨h₂, hp₂, H₂⟩ := exists_witnesses d₂ hd.2 fun χ hχ ↦ by
      rcases Multiset.mem_add.mp hχ with hχ | hχ
      · exact hΓ χ (by simp [hχ])
      · rcases show χ = ψ by simpa using hχ
        exact Or.inl (StrictHierarchy.of_bounded hψ)
    exact ⟨_, Primrec.nat_max.comp hp₁ hp₂ |>.to₂, witnesses_and hd0 H₁ H₂⟩
  | _, .cut (φ := χ) d₁ d₂, hd, hΓ => by
    obtain ⟨h₁, hp₁, H₁⟩ := exists_witnesses d₁ hd.2.1 fun ρ hρ ↦ by
      rcases Multiset.mem_add.mp hρ with hρ | hρ
      · exact hΓ ρ (by simp [hρ])
      · rcases show ρ = χ by simpa using hρ
        exact hd.1
    obtain ⟨h₂, hp₂, H₂⟩ := exists_witnesses d₂ hd.2.2 fun ρ hρ ↦ by
      rcases Multiset.mem_add.mp hρ with hρ | hρ
      · exact hΓ ρ (by simp [hρ])
      · rcases show ρ = ∼χ by simpa using hρ
        rcases hd.1 with h | h
        · exact Or.inr (by simpa using StrictHierarchy.neg h)
        · exact Or.inl (by simpa using StrictHierarchy.neg h)
    refine ⟨_, ?_, witnesses_cut hd.1 H₁ H₂⟩
    have e₁ : Primrec fun p : List ℕ × ℕ ↦ h₁ p.1 p.2 := hp₁
    have e₂ : Primrec fun p : List ℕ × ℕ ↦ h₂ p.1 p.2 := hp₂
    exact Primrec.to₂ (Primrec.nat_max.comp
      (Primrec.nat_max.comp e₁
        (hp₂.comp Primrec.fst (Primrec.nat_max.comp Primrec.snd e₁)))
      (Primrec.nat_max.comp e₂
        (hp₁.comp Primrec.fst (Primrec.nat_max.comp Primrec.snd e₂))))
  | _, .exs (φ := ξ) (t := t) d, hd, hΓ => by
    have hσ : StrictHierarchy 𝚺 1 (∃¹ ξ) := by
      rcases hΓ (∃¹ ξ) (by simp) with h | h
      · exact h
      · cases h with
        | ofAlt h => exact StrictHierarchy.of_bounded (StrictHierarchy.bounded_of_zero h)
    obtain ⟨h, hp, H⟩ := exists_witnesses d hd fun χ hχ ↦ by
      rcases Multiset.mem_add.mp hχ with hχ | hχ
      · exact hΓ χ (by simp [hχ])
      · rcases show χ = ξ/[t] by simpa using hχ
        exact Or.inl (StrictHierarchy.rew _ (StrictHierarchy.of_exs hσ))
    refine ⟨_, ?_, witnesses_exs hσ H⟩
    exact Primrec.to₂ (Primrec.nat_max.comp hp
      (Primrec.succ.comp ((primrec_termVal t).comp Primrec.fst)))
  | _, .all (φ := ξ) d, hd, hΓ => by
    by_cases hσ : StrictHierarchy 𝚺 1 (∀¹ ξ)
    · have hd0 : (∀¹ ξ).Bounded := by
        cases hσ with | ofAlt h => exact StrictHierarchy.bounded_of_zero h
      obtain ⟨h, hp, H⟩ := exists_witnesses d hd fun χ hχ ↦ by
        rcases Multiset.mem_add.mp hχ with hχ | hχ
        · obtain ⟨χ', hχ', rfl⟩ := Multiset.mem_map.mp hχ
          rcases hΓ χ' (by simp [hχ']) with h | h
          · exact Or.inl (by simpa [Rewriting.shift] using h)
          · exact Or.inr (by simpa [Rewriting.shift] using h)
        · rcases show χ = Rewriting.free ξ by simpa using hχ
          exact Or.inl (StrictHierarchy.rew _ (StrictHierarchy.of_bounded
            (Hierarchy.of_bounded_all hd0)))
      obtain ⟨t, ρ, rfl, hρ⟩ := Hierarchy.exists_of_bounded_all hd0
      refine ⟨_, ?_, witnesses_all_bounded hρ H⟩
      exact Primrec.to₂ (primrec_maxBelow
        (Primrec.to₂ (hp.comp
          (Primrec.list_cons.comp Primrec.snd (Primrec.fst.comp (Primrec.fst (β := ℕ))))
          (Primrec.snd.comp (Primrec.fst (β := ℕ)))))
        ((primrec_termVal t).comp Primrec.fst))
    · obtain ⟨h, hp, H⟩ := exists_witnesses d hd fun χ hχ ↦ by
        rcases Multiset.mem_add.mp hχ with hχ | hχ
        · obtain ⟨χ', hχ', rfl⟩ := Multiset.mem_map.mp hχ
          rcases hΓ χ' (by simp [hχ']) with h | h
          · exact Or.inl (by simpa [Rewriting.shift] using h)
          · exact Or.inr (by simpa [Rewriting.shift] using h)
        · rcases show χ = Rewriting.free ξ by simpa using hχ
          rcases hΓ (∀¹ ξ) (by simp) with h | h
          · exact absurd h hσ
          · cases h with
            | ofAlt h =>
              exact Or.inl (StrictHierarchy.rew _ (StrictHierarchy.of_bounded
                (Hierarchy.of_bounded_all (StrictHierarchy.bounded_of_zero h))))
            | all h => exact Or.inr (StrictHierarchy.rew _ h)
      refine ⟨_, ?_, witnesses_all_pi hσ H⟩
      exact Primrec.to₂ (primrec_maxBelow
        (Primrec.to₂ (hp.comp
          (Primrec.list_cons.comp Primrec.snd (Primrec.fst.comp (Primrec.fst (β := ℕ))))
          (Primrec.snd.comp (Primrec.fst (β := ℕ)))))
        Primrec.snd)
  | _, .ind ξ hξ t d, hd, hΓ => by
    obtain ⟨h, hp, H⟩ := exists_witnesses d hd fun χ hχ ↦ by
      rcases Multiset.mem_add.mp hχ with hχ | hχ
      · obtain ⟨χ', hχ', rfl⟩ := Multiset.mem_map.mp hχ
        rcases hΓ χ' (by simp [hχ']) with h | h
        · exact Or.inl (by simpa [Rewriting.shift] using h)
        · exact Or.inr (by simpa [Rewriting.shift] using h)
      · rcases show χ = ∼(Rewriting.free ξ) ∨ χ = (Rewriting.shift ξ)/[‘&0 + 1’] by
          simpa using hχ with rfl | rfl
        · exact Or.inr (by simpa using hξ)
        · exact Or.inl (StrictHierarchy.rew _ (StrictHierarchy.rew _ hξ))
    by_cases hΔ : Hierarchy 𝚺 0 ξ
    · obtain ⟨s, hs⟩ := exists_term_evalBound_of_bounded hΔ
      have hΔ' : Hierarchy 𝚺 0 (∼ξ) := by simpa using hΔ.of_zero
      obtain ⟨s', hs'⟩ := exists_term_evalBound_of_bounded hΔ'
      have hB : Hierarchy 𝚺 0 ξ → ∀ l : List ℕ,
          (Semiformula.Eval ![0] (l.getD · 0) ξ →
            EvalBound ![0] (l.getD · 0)
              (max (Semiterm.val ![] (l.getD · 0) (Rew.subst ![(‘0’ : ArithmeticTerm ℕ)] s) + 1)
                (Semiterm.val ![] (l.getD · 0) (Rew.subst ![(‘0’ : ArithmeticTerm ℕ)] s') + 1)) ξ) ∧
          (Semiformula.Eval ![0] (l.getD · 0) (∼ξ) →
            EvalBound ![0] (l.getD · 0)
              (max (Semiterm.val ![] (l.getD · 0) (Rew.subst ![(‘0’ : ArithmeticTerm ℕ)] s) + 1)
                (Semiterm.val ![] (l.getD · 0) (Rew.subst ![(‘0’ : ArithmeticTerm ℕ)] s') + 1))
              (∼ξ)) := by
        intro _ l
        refine ⟨fun hev ↦ evalBound_mono (le_max_left _ _) ?_,
          fun hev ↦ evalBound_mono (le_max_right _ _) ?_⟩
        · simpa [Semiterm.val_substs, Matrix.constant_eq_singleton] using hs ![0] (l.getD · 0) hev
        · simpa [Semiterm.val_substs, Matrix.constant_eq_singleton] using
            hs' ![0] (l.getD · 0) hev
      refine ⟨_, ?_, witnesses_ind hξ hB H⟩
      exact Primrec.to₂ (primrec_indBound hp
        (Primrec.nat_max.comp Primrec.snd
          (Primrec.nat_max.comp
            (Primrec.succ.comp
              ((primrec_termVal (Rew.subst ![(‘0’ : ArithmeticTerm ℕ)] s)).comp Primrec.fst))
            (Primrec.succ.comp
              ((primrec_termVal (Rew.subst ![(‘0’ : ArithmeticTerm ℕ)] s')).comp Primrec.fst))))
        ((primrec_termVal t).comp Primrec.fst))
    · refine ⟨_, ?_, witnesses_ind (B := fun _ ↦ 0) hξ (fun hc ↦ absurd hc hΔ) H⟩
      exact Primrec.to₂ (primrec_indBound hp
        (Primrec.nat_max.comp Primrec.snd (Primrec.const 0))
        ((primrec_termVal t).comp Primrec.fst))

end FFL.FirstOrder.Arithmetic.LKI

end
