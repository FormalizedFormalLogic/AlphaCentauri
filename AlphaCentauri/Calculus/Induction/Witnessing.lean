module

public import AlphaCentauri.Calculus.Induction.Basic
public import AlphaCentauri.ToFoundation.Fvar
public import AlphaCentauri.ToFoundation.Hierarchy
public import AlphaCentauri.ToFoundation.Primrec
public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy
public import Foundation.FirstOrder.Tarski.Basic

/-!
# Bounded approximation and witnessing

`EvalBound e ε b φ` says that `φ` holds under `e` and `ε` with every leading existential
witnessed below `b`, which approximates a strict $\Sigma_1$ formula by a $\Delta_0$ one. The
approximation implies `φ`, it grows with the bound, and a true strict $\Sigma_1$ formula has one.

From an anchored `LKI[C]` derivation of a sequent of strict $\Sigma_1$ and strict $\Pi_1$
formulas one reads a primitive recursive bound on the witnesses: if every non-$\Sigma_1$ formula
of the sequent is refuted below `b`, then some $\Sigma_1$ formula of the sequent holds below
`h l b`. The induction rule contributes the primitive recursion, every other rule a `max`.

- [Bus98A, Section 3.1.2]
- [Bus98A, Section 3.1.3]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-! ## Bounded approximation of strict $\Sigma_1$ formulas -/

section
variable {ξ : Type*} {n : ℕ}

/-- `bound u φ` replaces the leading existential quantifiers of `φ` by quantifiers bounded
by `u`.

- [Bus98A, Section 3.1.2] -/
private def bound {n : ℕ} (u : ArithmeticSemiterm ξ n) :
    ArithmeticSemiformula ξ n → ArithmeticSemiformula ξ n
  | ∃¹ φ => ∃¹[“#0 < !!(Rew.bShift u)”] bound (Rew.bShift u) φ
  | φ => φ

@[simp, grind =] private lemma bound_exs (u : ArithmeticSemiterm ξ n)
    (φ : ArithmeticSemiformula ξ (n + 1)) :
    bound u (∃¹ φ) = ∃¹[“#0 < !!(Rew.bShift u)”] bound (Rew.bShift u) φ := rfl

/-- The approximation of a strict $\Sigma_1$ formula is $\Delta_0$. -/
private lemma bounded_bound {n : ℕ} {φ : ArithmeticSemiformula ξ n} (h : StrictHierarchy 𝚺 1 φ)
    (u : ArithmeticSemiterm ξ n) : (bound u φ).Bounded := by
  induction φ using Semiformula.rec' with
  | hexs φ ih => exact .bexs (Rew.positive_iff.mpr ⟨u, rfl⟩) (ih (StrictHierarchy.of_exs h) _)
  | _ => cases h with | ofAlt h => exact StrictHierarchy.bounded_of_zero h

/-! ## The approximation, read semantically -/

/-- `EvalBound e ε b φ` says that `φ` is true under `e` and `ε` with every leading existential
witnessed below `b`.

- [Bus98A, Section 3.1.2] -/
def EvalBound {n : ℕ} (e : Fin n → ℕ) (ε : ξ → ℕ) (b : ℕ) :
    ArithmeticSemiformula ξ n → Prop
  | ∃¹ φ => ∃ x < b, EvalBound (x :> e) ε b φ
  | φ => Semiformula.Eval e ε φ

@[simp, grind =] lemma evalBound_exs {e : Fin n → ℕ} {ε : ξ → ℕ} {b}
    {φ : ArithmeticSemiformula ξ (n + 1)} :
    EvalBound e ε b (∃¹ φ) ↔ ∃ x < b, EvalBound (x :> e) ε b φ := Iff.rfl

section

variable {e : Fin n → ℕ} {ε : ξ → ℕ} {b : ℕ} {k} {r : (ℒₒᵣ).Rel k}

@[simp, grind =] lemma evalBound_rel {v} :
    EvalBound e ε b (.rel r v) ↔ Semiformula.Eval e ε (.rel r v) := Iff.rfl

@[simp, grind =] lemma evalBound_nrel {v} :
    EvalBound e ε b (.nrel r v) ↔ Semiformula.Eval e ε (.nrel r v) := Iff.rfl

@[simp, grind ·] lemma evalBound_verum : EvalBound e ε b ⊤ := by tauto

@[simp, grind .] lemma evalBound_falsum : ¬EvalBound e ε b ⊥ := by tauto

@[simp, grind =] lemma evalBound_and {φ ψ : ArithmeticSemiformula ξ n} :
    EvalBound e ε b (φ ⋏ ψ) ↔ Semiformula.Eval e ε (φ ⋏ ψ) := Iff.rfl

@[simp, grind =] lemma evalBound_or {φ ψ : ArithmeticSemiformula ξ n} :
    EvalBound e ε b (φ ⋎ ψ) ↔ Semiformula.Eval e ε (φ ⋎ ψ) := Iff.rfl

@[simp, grind =] lemma evalBound_all {φ : ArithmeticSemiformula ξ (n + 1)} :
    EvalBound e ε b (∀¹ φ) ↔ Semiformula.Eval e ε (∀¹ φ) := Iff.rfl

end

variable {n n₁ n₂ : ℕ}

/-- The approximation is what the bounded formula says. -/
private lemma evalBound_iff_eval_bound {φ : ArithmeticSemiformula ξ n}
    {u : ArithmeticSemiterm ξ n}
    {e : Fin n → ℕ} {ε : ξ → ℕ} :
    EvalBound e ε (Semiterm.val e ε u) φ ↔ Semiformula.Eval e ε (bound u φ) := by
  induction φ using Semiformula.rec' with
  | hexs φ ih =>
    simp only [evalBound_exs, bound_exs, Semiformula.eval_bexs]
    constructor
    · rintro ⟨x, hx, h⟩
      exact ⟨x, by simpa using hx, ih.mp (by simpa using h)⟩
    · rintro ⟨x, hx, h⟩
      exact ⟨x, by simpa using hx, by simpa using ih.mpr h⟩
  | _ => exact Iff.rfl

/-- The approximation implies the formula. -/
lemma eval_of_evalBound {n : ℕ} {φ : ArithmeticSemiformula ξ n} {b : ℕ} {e : Fin n → ℕ}
    {ε : ξ → ℕ} (h : EvalBound e ε b φ) : Semiformula.Eval e ε φ := by
  induction φ using Semiformula.rec' with
  | hexs φ ih =>
    obtain ⟨x, _, hx⟩ := h
    exact ⟨x, ih hx⟩
  | _ => exact h

/-- The approximation grows with the bound. -/
lemma evalBound_mono {n : ℕ} {φ : ArithmeticSemiformula ξ n} {b b' : ℕ} (hb : b ≤ b')
    {e : Fin n → ℕ} {ε : ξ → ℕ} (h : EvalBound e ε b φ) : EvalBound e ε b' φ := by
  induction φ using Semiformula.rec' with
  | hexs φ ih => grind
  | _ => exact h

/-- A true strict $\Sigma_1$ formula has an approximation. -/
lemma exists_evalBound {φ : ArithmeticSemiformula ξ n} (hφ : StrictHierarchy 𝚺 1 φ)
    {e : Fin n → ℕ} {ε : ξ → ℕ} (h : Semiformula.Eval e ε φ) : ∃ b, EvalBound e ε b φ := by
  induction φ using Semiformula.rec' with
  | hexs φ ih =>
    obtain ⟨x, hx⟩ : ∃ x, Semiformula.Eval (x :> e) ε φ := by simpa using h
    obtain ⟨b, hb⟩ := ih (StrictHierarchy.of_exs hφ) hx
    exact ⟨max (x + 1) b, x, lt_of_lt_of_le (Nat.lt_succ_self x) (le_max_left _ _),
      evalBound_mono (le_max_right _ _) hb⟩
  | _ => exact ⟨0, h⟩

/-- The approximation commutes with rewriting. -/
lemma evalBound_rew {ξ₁ ξ₂ : Type*} (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂)
    (φ : ArithmeticSemiformula ξ₁ n₁) {e : Fin n₂ → ℕ} {ε : ξ₂ → ℕ} {b : ℕ} :
    EvalBound e ε b (ω ▹ φ) ↔
      EvalBound (Semiterm.val e ε ∘ ω ∘ Semiterm.bvar)
        (Semiterm.val e ε ∘ ω ∘ Semiterm.fvar) b φ := by
  induction φ using Semiformula.rec' generalizing n₂ ξ₂ e ε with
  | hexs φ ih =>
    have key : ∀ x : ℕ, EvalBound (x :> e) ε b (ω.q ▹ φ) ↔
        EvalBound (x :> (Semiterm.val e ε ∘ ⇑ω ∘ Semiterm.bvar))
          (Semiterm.val e ε ∘ ⇑ω ∘ Semiterm.fvar) b φ := by
      intro x
      have e₁ : (Semiterm.val (x :> e) ε ∘ ⇑ω.q ∘ Semiterm.bvar)
          = x :> (Semiterm.val e ε ∘ ⇑ω ∘ Semiterm.bvar) := by
        funext i; cases i using Fin.cases <;> simp
      have e₂ : (Semiterm.val (x :> e) ε ∘ ⇑ω.q ∘ Semiterm.fvar)
          = Semiterm.val e ε ∘ ⇑ω ∘ Semiterm.fvar := by funext y; simp
      rw [ih ω.q, e₁, e₂]
    simp only [Rewriting.app_exs, evalBound_exs]
    exact exists_congr fun x ↦ and_congr_right fun _ ↦ key x
  | _ => exact Semiformula.eval_rew ω _

/-- The approximation only looks at the free variables of the formula. -/
lemma evalBound_congr_fvar [DecidableEq ξ] {n : ℕ} {φ : ArithmeticSemiformula ξ n} {b : ℕ}
    {e : Fin n → ℕ} {ε ε' : ξ → ℕ} (h : Function.funEqOn φ.FVar? ε ε') :
    EvalBound e ε b φ ↔ EvalBound e ε' b φ := by
  induction φ using Semiformula.rec' with
  | hexs φ ih =>
    simp only [evalBound_exs]
    exact exists_congr fun x ↦ and_congr_right fun _ ↦
      ih (h.of_subset fun y hy ↦ by simpa using hy)
  | _ => exact Semiformula.eval_iff_of_funEqOn _ h

/-- A true $\Delta_0$ formula has an approximation bounded by a term of the formula: only its
leading bounded existential has to be witnessed. -/
lemma exists_term_evalBound_of_bounded {n : ℕ} {φ : ArithmeticSemiformula ξ n} (hφ : φ.Bounded) :
    ∃ s : ArithmeticSemiterm ξ n, ∀ (e : Fin n → ℕ) (ε : ξ → ℕ),
      Semiformula.Eval e ε φ → EvalBound e ε (Semiterm.val e ε s + 1) φ := by
  cases φ using Semiformula.cases' with
  | hexs ψ =>
    cases hφ with
    | bexs pt hρ =>
      rename_i ρ _
      obtain ⟨s, rfl⟩ := Rew.positive_iff.mp pt
      refine ⟨s, fun e ε h ↦ ?_⟩
      obtain ⟨x, hx, hρx⟩ : ∃ x, x < Semiterm.val e ε s ∧ Semiformula.Eval (x :> e) ε ρ := by
        simpa using h
      exact ⟨x, Nat.lt_succ_of_lt hx, by simpa using ⟨hx, hρx⟩⟩
  | _ => exact ⟨‘0’, fun _ _ h ↦ h⟩

end

/-! ## The approximation of a proposition -/

section
variable {φ : ArithmeticProposition} {b : ℕ} {ε : ℕ → ℕ}

/-- A true strict $\Sigma_1$ sentence has an approximation that does not depend on the
assignment. -/
lemma exists_evalBound_of_closed (hφ : StrictHierarchy 𝚺 1 φ) (hfv : ∀ x, ¬φ.FVar? x)
    (h : ∀ ε : ℕ → ℕ, φ.Evalf ε) : ∃ c, ∀ ε, EvalBound ![] ε c φ := by
  obtain ⟨c, hc⟩ := exists_evalBound hφ (h fun _ ↦ 0)
  exact ⟨c, fun ε ↦ (evalBound_congr_fvar fun x hx ↦ absurd hx (hfv x)).mp hc⟩

/-- The approximation of a proposition is the truth of a fixed $\Delta_0$ formula, with the bound
supplied by its bound variable. -/
private lemma evalBound_iff_eval_bound_bShift :
    EvalBound ![] ε b φ ↔ Semiformula.Eval ![b] ε (bound #0 (Rew.bShift ▹ φ)) := by
  have h := evalBound_iff_eval_bound (u := (#0 : ArithmeticSemiterm ℕ 1)) (e := ![b]) (ε := ε)
    (φ := Rew.bShift ▹ φ)
  simp only [Semiterm.val_bvar, Matrix.cons_val_zero] at h
  rw [← h, evalBound_rew]
  simp [Function.comp_def, Matrix.empty_eq]

/-- The approximation is a primitive recursive predicate of the bound and the assignment.

- [HP98, Theorem 0.35] -/
lemma primrecRel_evalBound (hφ : StrictHierarchy 𝚺 1 φ) :
    PrimrecRel fun (b : ℕ) (l : List ℕ) ↦ EvalBound ![] (l.getD · 0) b φ := by
  set ψ := bound #0 (Rew.bShift ▹ φ) with hψ
  have hb : ψ.Bounded := bounded_bound (StrictHierarchy.rew _ hφ) _
  have hσ : (ψ.toSemisentence ![#0]).Bounded := Semiformula.Bounded.rew _ hb
  have key : ∀ (b : ℕ) (l : List ℕ), EvalBound ![] (l.getD · 0) b φ ↔
      ℕ ⊧/(b :> fun i : Fin ψ.fvSup ↦ l.getD i 0) (ψ.toSemisentence ![#0]) := by
    intro b l
    rw [evalBound_iff_eval_bound_bShift]
    exact (Semiformula.eval_toSemisentence_one ψ b _).symm
  have hvec : Primrec₂ fun (b : ℕ) (l : List ℕ) ↦
      (b ::ᵥ List.Vector.ofFn fun i : Fin ψ.fvSup ↦ l.getD i 0) := by primrec
  have := (bounded_primrec_vec Empty.elim _ _ hσ).comp hvec
  refine this.of_eq fun p ↦ ?_
  have e : (List.Vector.ofFn fun i : Fin ψ.fvSup ↦ p.2.getD (i : ℕ) 0).get
      = fun i : Fin ψ.fvSup ↦ p.2.getD (i : ℕ) 0 := funext (List.Vector.get_ofFn _)
  simp only [List.Vector.cons_get, e]
  exact (key p.1 p.2).symm

/-- `primrecRel_evalBound` in the form the `primrec` tactic reads off a goal: the bound and the
assignment are themselves primitive recursive in a common argument. -/
@[primrec]
lemma primrecPred_evalBound {α : Type*} [Primcodable α] (hφ : StrictHierarchy 𝚺 1 φ)
    {b : α → ℕ} (hb : Primrec b) {l : α → List ℕ} (hl : Primrec l) :
    PrimrecPred fun a ↦ EvalBound ![] ((l a).getD · 0) (b a) φ :=
  PrimrecRel.comp (primrecRel_evalBound hφ) hb hl

end

namespace LKI

open Rewriting LawfulSyntacticRewriting

variable {Γ Δ : LK.Sequent ℒₒᵣ} {φ ψ : ArithmeticProposition} {f g : List ℕ → ℕ → ℕ}

/-! ## Witnessing -/

/-- `Witnesses Γ f` says that `f` bounds the witnesses of the $\Sigma_1$ formulas of `Γ`: if every
non-$\Sigma_1$ formula of `Γ` is refuted below `b` under `l`, then some $\Sigma_1$ formula of `Γ`
holds below `f l b`.

- [Bus98A, Section 3.1.3] -/
def Witnesses (Γ : LK.Sequent ℒₒᵣ) (f : List ℕ → ℕ → ℕ) : Prop :=
  ∀ (l : List ℕ) (b : ℕ),
      (∀ ψ ∈ Γ, ¬StrictHierarchy 𝚺 1 ψ → EvalBound ![] (l.getD · 0) b (∼ψ)) →
    ∃ φ ∈ Γ, StrictHierarchy 𝚺 1 φ ∧ EvalBound ![] (l.getD · 0) (f l b) φ

namespace Witnesses

lemma mono (H : Witnesses Γ f) (hle : ∀ l b, f l b ≤ g l b) : Witnesses Γ g := by
  intro l b hb
  obtain ⟨φ, hφ, hσ, hbnd⟩ := H l b hb
  exact ⟨φ, hφ, hσ, evalBound_mono (hle l b) hbnd⟩

/-- A sequent whose formulas are those of a witnessed one is witnessed by the same bound. -/
lemma ofSubset (H : Witnesses Γ f) (hs : Γ ⊆ Δ) : Witnesses Δ f := by
  intro l b hb
  obtain ⟨φ, hφ, hσ, hbnd⟩ := H l b fun ψ hψ ↦ hb ψ (hs hψ)
  exact ⟨φ, hs hφ, hσ, hbnd⟩

/-- Sequents with the same formulas are witnessed alike. -/
lemma cast (H : Witnesses Γ f) (e : Γ = Δ) : Witnesses Δ f := e ▸ H

end Witnesses

/-! ## The leaves -/

lemma witnesses_verum : Witnesses ⦃⊤⦄ fun _ _ ↦ 0 := by
  intro l b _
  exact ⟨⊤, by simp, by grind, by simp⟩

lemma witnesses_identity {k} (r : (ℒₒᵣ).Rel k) (v) :
    Witnesses ⦃.rel r v, .nrel r v⦄ fun _ _ ↦ 0 := by
  intro l b _
  by_cases hv : Semiformula.Eval ![] (l.getD · 0) (.rel r v)
  · exact ⟨.rel r v, by simp, by grind, by simpa using hv⟩
  · exact ⟨.nrel r v, by simp, by grind, by simpa using hv⟩

lemma exists_witnesses_axm {σ : ArithmeticSentence} (hσ : σ ∈ 𝗣𝗔⁻) :
    ∃ c, Witnesses ⦃σ⦄ fun _ _ ↦ c := by
  have htrue : ∀ ε : ℕ → ℕ, (Rewriting.emb σ).Evalf ε := by
    intro ε
    simpa [models_iff] using Theory.models (M := ℕ) _ hσ
  by_cases hs : StrictHierarchy 𝚺 1 (Rewriting.emb σ : ArithmeticProposition)
  · obtain ⟨c, hc⟩ := exists_evalBound_of_closed hs (by simp [Semiformula.FVar?]) htrue
    exact ⟨c, fun l _ _ ↦ ⟨_, by simp, hs, hc _⟩⟩
  · refine ⟨0, fun l b hb ↦ absurd (htrue (l.getD · 0)) ?_⟩
    simpa using eval_of_evalBound (hb _ (by simp) hs)

/-! ## The propositional rules -/

lemma witnesses_weakening (H : Witnesses Γ f) : Witnesses (Γ + ⦃φ⦄) f :=
  H.ofSubset (Multiset.subset_of_le (Multiset.le_add_right _ _))

lemma witnesses_contraction (H : Witnesses (Γ + ⦃φ, φ⦄) f) : Witnesses (Γ + ⦃φ⦄) f :=
  H.ofSubset fun χ hχ ↦ by
    rcases Multiset.mem_add.mp hχ with hχ | hχ
    · simp [hχ]
    · simp_all

lemma witnesses_or (hd : (φ ⋎ ψ).Bounded) (H : Witnesses (Γ + ⦃φ, ψ⦄) f) :
    Witnesses (Γ + ⦃φ ⋎ ψ⦄) f := by
  obtain ⟨hφ, hψ⟩ := Semiformula.Bounded.or_iff.mp hd
  intro l b hb
  obtain ⟨χ, hχ, hσ, hbnd⟩ := H l b fun χ hχ hnσ ↦ by
    rcases Multiset.mem_add.mp hχ with hχ | hχ
    · exact hb χ (by simp [hχ]) hnσ
    · rcases show χ = φ ∨ χ = ψ by simpa using hχ with rfl | rfl
      · grind
      · grind
  rcases Multiset.mem_add.mp hχ with hχ | hχ
  · exact ⟨χ, by simp [hχ], hσ, hbnd⟩
  · refine ⟨φ ⋎ ψ, by simp, by grind, ?_⟩
    rcases show χ = φ ∨ χ = ψ by simpa using hχ with rfl | rfl
    · simpa using Or.inl (eval_of_evalBound hbnd)
    · simpa using Or.inr (eval_of_evalBound hbnd)

lemma witnesses_and (hd : (φ ⋏ ψ).Bounded) (H₁ : Witnesses (Γ + ⦃φ⦄) f)
    (H₂ : Witnesses (Γ + ⦃ψ⦄) g) : Witnesses (Γ + ⦃φ ⋏ ψ⦄) fun l b ↦ max (f l b) (g l b) := by
  obtain ⟨hφ, hψ⟩ := Semiformula.Bounded.and_iff.mp hd
  intro l b hb
  have hb₁ : ∀ χ ∈ Γ + ⦃φ⦄, ¬StrictHierarchy 𝚺 1 χ →
      EvalBound ![] (l.getD · 0) b (∼χ) := fun χ hχ hnσ ↦ by
    rcases Multiset.mem_add.mp hχ with hχ | hχ
    · exact hb χ (by simp [hχ]) hnσ
    · rcases show χ = φ by simpa using hχ
      grind
  have hb₂ : ∀ χ ∈ Γ + ⦃ψ⦄, ¬StrictHierarchy 𝚺 1 χ →
      EvalBound ![] (l.getD · 0) b (∼χ) := fun χ hχ hnσ ↦ by
    rcases Multiset.mem_add.mp hχ with hχ | hχ
    · exact hb χ (by simp [hχ]) hnσ
    · rcases show χ = ψ by simpa using hχ
      grind
  obtain ⟨χ₁, hχ₁, hσ₁, hbnd₁⟩ := H₁ l b hb₁
  obtain ⟨χ₂, hχ₂, hσ₂, hbnd₂⟩ := H₂ l b hb₂
  rcases Multiset.mem_add.mp hχ₁ with hm₁ | hm₁
  · exact ⟨χ₁, by simp [hm₁], hσ₁, evalBound_mono (le_max_left _ _) hbnd₁⟩
  rcases Multiset.mem_add.mp hχ₂ with hm₂ | hm₂
  · exact ⟨χ₂, by simp [hm₂], hσ₂, evalBound_mono (le_max_right _ _) hbnd₂⟩
  rcases show χ₁ = φ by simpa using hm₁
  rcases show χ₂ = ψ by simpa using hm₂
  exact ⟨φ ⋏ ψ, by simp, by grind,
    by simpa using ⟨eval_of_evalBound hbnd₁, eval_of_evalBound hbnd₂⟩⟩

/-! ## The existential rule -/

lemma witnesses_exs {ξ : ArithmeticSemiformula ℕ 1} {t : ArithmeticTerm ℕ}
    (hσ : StrictHierarchy 𝚺 1 (∃¹ ξ)) (H : Witnesses (Γ + ⦃ξ/[t]⦄) f) :
    Witnesses (Γ + ⦃∃¹ ξ⦄) fun l b ↦ max (f l b) (Semiterm.val ![] (l.getD · 0) t + 1) := by
  have hsub : StrictHierarchy 𝚺 1 (ξ/[t]) := by grind
  intro l b hb
  obtain ⟨χ, hχ, hσχ, hbnd⟩ := H l b fun χ hχ hnσ ↦ by
    rcases Multiset.mem_add.mp hχ with hχ | hχ
    · exact hb χ (by simp [hχ]) hnσ
    · rcases show χ = ξ/[t] by simpa using hχ
      exact absurd hsub hnσ
  rcases Multiset.mem_add.mp hχ with hm | hm
  · exact ⟨χ, by simp [hm], hσχ, evalBound_mono (le_max_left _ _) hbnd⟩
  rcases show χ = ξ/[t] by simpa using hm
  refine ⟨∃¹ ξ, by simp, hσ, Semiterm.val ![] (l.getD · 0) t,
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _), ?_⟩
  have h₁ :=
    evalBound_mono (le_max_left (f l b) (Semiterm.val ![] (l.getD · 0) t + 1)) hbnd
  rw [Rewriting.subst, evalBound_rew] at h₁
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
    (H₁ : Witnesses (Γ + ⦃χ⦄) f) (H₂ : Witnesses (Δ + ⦃∼χ⦄) g) :
    Witnesses (Γ + Δ) fun l b ↦ max (f l b) (g l (max b (f l b))) := by
  intro l b hb
  obtain ⟨χ₁, hχ₁, hσ₁, hbnd₁⟩ := H₁ l b fun ψ hψ hnσ ↦ by
    rcases Multiset.mem_add.mp hψ with hψ | hψ
    · exact hb ψ (by simp [hψ]) hnσ
    · rcases show ψ = χ by simpa using hψ
      exact absurd hσ hnσ
  rcases Multiset.mem_add.mp hχ₁ with hm | hm
  · exact ⟨χ₁, by simp [hm], hσ₁, evalBound_mono (le_max_left _ _) hbnd₁⟩
  rcases show χ₁ = χ by simpa using hm
  obtain ⟨χ₂, hχ₂, hσ₂, hbnd₂⟩ := H₂ l (max b (f l b)) fun ψ hψ hnσ ↦ by
    rcases Multiset.mem_add.mp hψ with hψ | hψ
    · exact evalBound_mono (le_max_left _ _) (hb ψ (by simp [hψ]) hnσ)
    · rcases show ψ = ∼χ by simpa using hψ
      simpa using evalBound_mono (le_max_right _ _) hbnd₁
  rcases Multiset.mem_add.mp hχ₂ with hm₂ | hm₂
  · exact ⟨χ₂, by simp [hm₂], hσ₂, evalBound_mono (le_max_right _ _) hbnd₂⟩
  rcases show χ₂ = ∼χ by simpa using hm₂
  exact absurd (eval_of_evalBound hbnd₁) (by simpa using eval_of_evalBound hbnd₂)

lemma witnesses_cut {χ : ArithmeticProposition}
    (hχ : StrictHierarchy 𝚺 1 χ ∨ StrictHierarchy 𝚷 1 χ)
    (H₁ : Witnesses (Γ + ⦃χ⦄) f) (H₂ : Witnesses (Δ + ⦃∼χ⦄) g) :
    Witnesses (Γ + Δ) fun l b ↦
      max (max (f l b) (g l (max b (f l b)))) (max (g l b) (f l (max b (g l b)))) := by
  rcases hχ with hσ | hπ
  · exact (witnesses_cut_sigma hσ H₁ H₂).mono fun _ _ ↦ le_max_left _ _
  · have H₁' : Witnesses (Γ + ⦃∼∼χ⦄) f := by simpa using H₁
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

lemma maxBelow_le (f : ℕ → ℕ) {c : ℕ} : {n : ℕ} → (∀ x < n, f x ≤ c) → maxBelow f n ≤ c
  | 0, _ => by simp [maxBelow]
  | n + 1, h => by
    simp only [maxBelow, max_le_iff]
    exact ⟨h n (by simp), maxBelow_le f fun x hx ↦ h x (by omega)⟩

/-- A bounded search: the maximum below `n` of the partial identity on `p` is the unique element
of `p`, provided it lies below `n`. -/
lemma maxBelow_ite_eq {p : ℕ → Prop} [DecidablePred p] {c n : ℕ} (hc : p c) (hcn : c < n)
    (huniq : ∀ y, p y → y = c) : maxBelow (fun y ↦ if p y then y else 0) n = c :=
  le_antisymm (maxBelow_le _ fun x _ ↦ by grind)
    (by simpa [hc] using le_maxBelow (fun y ↦ if p y then y else 0) hcn)

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

private lemma evalBound_subst {ξ : ArithmeticSemiformula ℕ 1} {s : ArithmeticTerm ℕ} {c : ℕ}
    {l : List ℕ} :
    EvalBound ![] (l.getD · 0) c (ξ/[s]) ↔
      EvalBound ![Semiterm.val ![] (l.getD · 0) s] (l.getD · 0) c ξ := by
  have e₁ : ((Semiterm.val ![] fun y ↦ l.getD y 0) ∘ ⇑(Rew.subst ![s]) ∘ Semiterm.bvar)
      = ![Semiterm.val ![] (fun y ↦ l.getD y 0) s] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ i => exact i.elim0
  have e₂ : ((Semiterm.val ![] fun y ↦ l.getD y 0) ∘ ⇑(Rew.subst ![s]) ∘ Semiterm.fvar)
      = fun y ↦ l.getD y 0 := by funext y; simp
  simp only [Rewriting.subst]
  rw [evalBound_rew, e₁, e₂]

private lemma evalBound_free {χ : ArithmeticSemiformula ℕ 1} {c x : ℕ} {l : List ℕ} :
    EvalBound ![] ((x :: l).getD · 0) c (Rewriting.free χ) ↔ EvalBound ![x] (l.getD · 0) c χ := by
  have e₁ : ((Semiterm.val ![] fun y ↦ (x :: l).getD y 0) ∘
      ⇑(Rew.free : SyntacticRew ℒₒᵣ 1 0) ∘ Semiterm.bvar) = ![x] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ i => exact i.elim0
  have e₂ : ((Semiterm.val ![] fun y ↦ (x :: l).getD y 0) ∘
      ⇑(Rew.free : SyntacticRew ℒₒᵣ 1 0) ∘ Semiterm.fvar) = fun y ↦ l.getD y 0 := by
    funext y; simp
  simp only [Rewriting.free]
  rw [evalBound_rew, e₁, e₂]

/-- The universal rule when the principal formula is not $\Sigma_1$: the hypothesis refutes it
below `b`, which bounds the counterexample. -/
lemma witnesses_all_pi {ξ : ArithmeticSemiformula ℕ 1} (hnσ : ¬StrictHierarchy 𝚺 1 (∀¹ ξ))
    (H : Witnesses (Γ⁺ + ⦃Rewriting.free ξ⦄) f) :
    Witnesses (Γ + ⦃∀¹ ξ⦄) fun l b ↦ maxBelow (fun x ↦ f (x :: l) b) b := by
  intro l b hb
  obtain ⟨x₀, hx₀, hrefute⟩ : ∃ x < b, EvalBound ![x] (l.getD · 0) b (∼ξ) := by
    simpa using hb (∀¹ ξ) (by simp) hnσ
  obtain ⟨χ, hχ, hσχ, hbnd⟩ := H (x₀ :: l) b fun ψ hψ hnσψ ↦ by
    rcases Multiset.mem_add.mp hψ with hψ | hψ
    · obtain ⟨ψ', hψ', rfl⟩ := Multiset.mem_map.mp hψ
      have : ¬StrictHierarchy 𝚺 1 ψ' := by grind
      simpa using evalBound_shift.mpr (hb ψ' (by simp [hψ']) this)
    · rcases show ψ = Rewriting.free ξ by simpa using hψ
      simpa using evalBound_free.mpr hrefute
  rcases Multiset.mem_add.mp hχ with hm | hm
  · obtain ⟨χ', hχ', rfl⟩ := Multiset.mem_map.mp hm
    exact ⟨χ', by simp [hχ'], by grind,
      evalBound_mono (le_maxBelow _ hx₀) (evalBound_shift.mp hbnd)⟩
  · rcases show χ = Rewriting.free ξ by simpa using hm
    exact absurd (eval_of_evalBound (evalBound_free.mp hbnd))
      (by simpa using eval_of_evalBound hrefute)

/-- The universal rule when the principal formula is a bounded universal: the term bounds the
counterexample. -/
lemma witnesses_all_bounded {ψ : ArithmeticSemiformula ℕ 1} {t : ArithmeticTerm ℕ}
    (hψ : ψ.Bounded)
    (H : Witnesses (Γ⁺ + ⦃Rewriting.free (“#0 < !!(Rew.bShift t)” 🡒 ψ)⦄) f) :
    Witnesses (Γ + ⦃∀¹[“#0 < !!(Rew.bShift t)”] ψ⦄)
      fun l b ↦ maxBelow (fun x ↦ f (x :: l) b) (Semiterm.val ![] (l.getD · 0) t) := by
  have hd : (∀¹[“#0 < !!(Rew.bShift t)”] ψ).Bounded :=
    .ball (Rew.positive_iff.mpr ⟨t, rfl⟩) hψ
  have hbody : (“#0 < !!(Rew.bShift t)” 🡒 ψ).Bounded :=
    Semiformula.Bounded.imp_iff.mpr ⟨.rel _ _, hψ⟩
  intro l b hb
  by_cases hex : ∃ x < Semiterm.val ![] (l.getD · 0) t,
      ∃ γ ∈ Γ, StrictHierarchy 𝚺 1 γ ∧ EvalBound ![] (l.getD · 0) (f (x :: l) b) γ
  · obtain ⟨x, hx, γ, hγ, hσγ, hbnd⟩ := hex
    exact ⟨γ, by simp [hγ], hσγ, evalBound_mono (le_maxBelow _ hx) hbnd⟩
  push Not at hex
  refine ⟨∀¹[“#0 < !!(Rew.bShift t)”] ψ, by simp, by grind, ?_⟩
  have hall : ∀ x < Semiterm.val ![] (l.getD · 0) t, Semiformula.Eval ![x] (l.getD · 0) ψ := by
    intro x hx
    obtain ⟨χ, hχ, hσχ, hbnd⟩ := H (x :: l) b fun ρ hρ hnσρ ↦ by
      rcases Multiset.mem_add.mp hρ with hρ | hρ
      · obtain ⟨ρ', hρ', rfl⟩ := Multiset.mem_map.mp hρ
        have : ¬StrictHierarchy 𝚺 1 ρ' := by grind
        simpa using evalBound_shift.mpr (hb ρ' (by simp [hρ']) this)
      · rcases show ρ = Rewriting.free (“#0 < !!(Rew.bShift t)” 🡒 ψ) by simpa using hρ
        exact absurd (StrictHierarchy.of_bounded (Semiformula.Bounded.rew _ hbody)) hnσρ
    rcases Multiset.mem_add.mp hχ with hm | hm
    · obtain ⟨χ', hχ', rfl⟩ := Multiset.mem_map.mp hm
      exact absurd (evalBound_shift.mp hbnd)
        (hex x hx χ' (by simpa using hχ') (by grind))
    · rcases show χ = Rewriting.free (“#0 < !!(Rew.bShift t)” 🡒 ψ) by simpa using hm
      have h' : x < Semiterm.val ![] (l.getD · 0) t → Semiformula.Eval ![x] (l.getD · 0) ψ := by
        simpa using eval_of_evalBound (evalBound_free.mp hbnd)
      exact h' hx
  simpa [FFL.FirstOrder.ball] using fun x hx ↦ hall x hx

/-! ## The induction rule -/

/-- The bounds the induction rule iterates: `b` at `0`, and at each step the larger of the
current bound and what the premise gives. -/
def indBound (f : List ℕ → ℕ → ℕ) (l : List ℕ) (b : ℕ) : ℕ → ℕ
  | 0 => b
  | n + 1 => max (indBound f l b n) (f (n :: l) (indBound f l b n))

lemma indBound_eq_rec (f : List ℕ → ℕ → ℕ) (l : List ℕ) (b : ℕ) : ∀ n : ℕ,
    indBound f l b n = n.rec (motive := fun _ ↦ ℕ) b fun x ih ↦ max ih (f (x :: l) ih)
  | 0 => rfl
  | n + 1 => by simp [indBound, indBound_eq_rec f l b n]

lemma le_indBound (f : List ℕ → ℕ → ℕ) (l : List ℕ) (b : ℕ) : ∀ n, b ≤ indBound f l b n
  | 0 => le_rfl
  | n + 1 => le_trans (le_indBound f l b n) (le_max_left _ _)

/-- The induction rule: the bound is iterated along the term. `B` supplies the standard bound of
the induction formula, which is called for only when that formula is $\Delta_0$. -/
lemma witnesses_ind {ξ : ArithmeticSemiformula ℕ 1} {t : ArithmeticTerm ℕ} {B : List ℕ → ℕ}
    (hξ : StrictHierarchy 𝚺 1 ξ)
    (hB : ξ.Bounded → ∀ l : List ℕ,
      (Semiformula.Eval ![0] (l.getD · 0) ξ → EvalBound ![0] (l.getD · 0) (B l) ξ) ∧
        (Semiformula.Eval ![0] (l.getD · 0) (∼ξ) → EvalBound ![0] (l.getD · 0) (B l) (∼ξ)))
    (H : Witnesses (Γ⁺ + ⦃∼(.free ξ), (.shift ξ)/[‘&0 + 1’]⦄) f) :
    Witnesses (Γ + ⦃∼(ξ/[‘0’]), ξ/[t]⦄)
      fun l b ↦ indBound f l (max b (B l)) (Semiterm.val ![] (l.getD · 0) t) := by
  intro l b hb
  set c : ℕ → ℕ := indBound f l (max b (B l)) with hcdef
  have hbc : ∀ n, b ≤ c n := fun n ↦ le_trans (le_max_left _ _) (le_indBound _ _ _ n)
  have key : ∀ n : ℕ,
      (∃ φ ∈ Γ + ⦃∼(ξ/[‘0’]), ξ/[t]⦄,
        StrictHierarchy 𝚺 1 φ ∧ EvalBound ![] (l.getD · 0) (c n) φ) ∨
      EvalBound ![n] (l.getD · 0) (c n) ξ := by
    intro n
    induction n with
    | zero =>
      by_cases hz : StrictHierarchy 𝚺 1 (∼(ξ/[‘0’]) : ArithmeticProposition)
      · have hπξ : StrictHierarchy 𝚷 1 ξ := by simpa [Rewriting.subst] using hz
        have hΔ : ξ.Bounded := by grind
        have hBc : B l ≤ c 0 := le_trans (le_max_right _ _) (le_indBound _ _ _ 0)
        by_cases hev : Semiformula.Eval ![0] (l.getD · 0) ξ
        · exact Or.inr (evalBound_mono hBc ((hB hΔ l).1 hev))
        · refine Or.inl ⟨∼(ξ/[‘0’]), by simp, hz, ?_⟩
          have hn : EvalBound ![0] (l.getD · 0) (c 0) (∼ξ) :=
            evalBound_mono hBc ((hB hΔ l).2 (by simpa using hev))
          have hs : EvalBound ![] (l.getD · 0) (c 0) ((∼ξ)/[‘0’]) :=
            evalBound_subst.mpr (by simpa using hn)
          simpa using hs
      · refine Or.inr (evalBound_mono (hbc 0) ?_)
        have h₀ : EvalBound ![] (l.getD · 0) b (ξ/[‘0’]) := by
          simpa using hb (∼(ξ/[‘0’])) (by simp) hz
        simpa using evalBound_subst.mp h₀
    | succ n ih =>
      rcases ih with ⟨φ, hφ, hσφ, hbnd⟩ | hinv
      · exact Or.inl ⟨φ, hφ, hσφ, evalBound_mono (le_max_left _ _) hbnd⟩
      obtain ⟨χ, hχ, hσχ, hbndχ⟩ := H (n :: l) (c n) fun ρ hρ hnσρ ↦ by
        rcases Multiset.mem_add.mp hρ with hρ | hρ
        · obtain ⟨ρ', hρ', rfl⟩ := Multiset.mem_map.mp hρ
          have hnσ' : ¬StrictHierarchy 𝚺 1 ρ' := by grind
          simpa using evalBound_shift.mpr (evalBound_mono (hbc n) (hb ρ' (by simp [hρ']) hnσ'))
        · rcases show ρ = ∼(Rewriting.free ξ) ∨ ρ = (Rewriting.shift ξ)/[‘&0 + 1’] by
            simpa using hρ with rfl | rfl
          · simpa using evalBound_free.mpr hinv
          · grind
      rcases Multiset.mem_add.mp hχ with hm | hm
      · obtain ⟨γ, hγ, rfl⟩ := Multiset.mem_map.mp hm
        exact Or.inl ⟨γ, by simp [hγ], by grind,
          evalBound_mono (le_max_right _ _) (evalBound_shift.mp hbndχ)⟩
      rcases show χ = ∼(Rewriting.free ξ) ∨ χ = (Rewriting.shift ξ)/[‘&0 + 1’] by
        simpa using hm with rfl | rfl
      · have hneg : EvalBound ![n] (l.getD · 0) (f (n :: l) (c n)) (∼ξ) :=
          evalBound_free.mp (by simpa using hbndχ)
        exact absurd (eval_of_evalBound hinv) (by simpa using eval_of_evalBound hneg)
      · refine Or.inr (evalBound_mono (le_max_right _ _) ?_)
        have h₁ := evalBound_subst.mp hbndχ
        simpa using evalBound_shift.mp (by simpa using h₁)
  rcases key (Semiterm.val ![] (l.getD · 0) t) with ⟨φ, hφ, hσφ, hbnd⟩ | hinv
  · exact ⟨φ, hφ, hσφ, hbnd⟩
  · exact ⟨ξ/[t], by simp, by grind, evalBound_subst.mpr hinv⟩

/-! ## Primitive recursion of the bounds -/

@[primrec]
lemma primrec_maxBelow {α : Type*} [Primcodable α] {f : α → ℕ → ℕ} (hf : Primrec₂ f)
    {B : α → ℕ} (hB : Primrec B) : Primrec fun a ↦ maxBelow (f a) (B a) := by
  have hstep : Primrec₂ fun (a : α) (q : ℕ × ℕ) ↦ max (f a q.1) q.2 := by primrec
  have h : Primrec fun a : α ↦
      (B a).rec (motive := fun _ ↦ ℕ) 0 fun x ih ↦ max (f a x) ih :=
    Primrec.nat_rec' hB (Primrec.const 0) hstep
  exact h.of_eq fun a ↦ (maxBelow_eq_rec _ _).symm

@[primrec]
lemma primrec_indBound {α : Type*} [Primcodable α] {f : List ℕ → ℕ → ℕ} (hf : Primrec₂ f)
    {l : α → List ℕ} (hl : Primrec l) {b B : α → ℕ} (hb : Primrec b) (hB : Primrec B) :
    Primrec fun a ↦ indBound f (l a) (b a) (B a) := by
  have hstep : Primrec₂ fun (a : α) (q : ℕ × ℕ) ↦ max q.2 (f (q.1 :: l a) q.2) := by primrec
  have h' : Primrec fun a ↦
      (B a).rec (motive := fun _ ↦ ℕ) (b a) fun x ih ↦ max ih (f (x :: l a) ih) :=
    Primrec.nat_rec' hB hb hstep
  exact h'.of_eq fun a ↦ (indBound_eq_rec _ _ _ _).symm

/-! ## The witnessing lemma -/

private lemma bounded_of_strictOne {b : Polarity}
    (h : StrictHierarchy b 1 φ) (hne : ∀ ψ, φ ≠ ∃¹ ψ) (hna : ∀ ψ, φ ≠ ∀¹ ψ) : φ.Bounded := by
  cases h with
  | ofAlt h => grind
  | exs => exact absurd rfl (hne _)
  | all => exact absurd rfl (hna _)

/-- Witnessing: from an anchored derivation of a sequent of strict $\Sigma_1$ and strict $\Pi_1$
formulas one reads a primitive recursive bound on the witnesses.

- [Bus98A, Section 3.1.3] -/
theorem exists_witnesses (d : ⊢ᴸᴷᴵ[StrictHierarchy 𝚺 1]! Γ)
    (hd : Derivation.Anchored (fun φ ↦ StrictHierarchy 𝚺 1 φ ∨ StrictHierarchy 𝚷 1 φ) d)
    (hΓ : ∀ φ ∈ Γ, StrictHierarchy 𝚺 1 φ ∨ StrictHierarchy 𝚷 1 φ) :
    ∃ f : List ℕ → ℕ → ℕ, Primrec₂ f ∧ Witnesses Γ f := by
  induction d with
  | axm hσ =>
    obtain ⟨c, hc⟩ := exists_witnesses_axm hσ
    exact ⟨_, Primrec₂.const c, hc⟩
  | verum => exact ⟨_, Primrec₂.const 0, witnesses_verum⟩
  | identity R v => exact ⟨_, Primrec₂.const 0, witnesses_identity R v⟩
  | weakening d ih =>
    obtain ⟨f, hf, H⟩ := ih hd fun φ hφ ↦ hΓ φ (by simp [hφ])
    exact ⟨f, hf, witnesses_weakening H⟩
  | contraction d ih =>
    obtain ⟨f, hf, H⟩ := ih hd fun φ hφ ↦ by
      rcases Multiset.mem_add.mp hφ with hφ | hφ
      · exact hΓ φ (by simp [hφ])
      · exact hΓ φ (by simp_all)
    exact ⟨f, hf, witnesses_contraction H⟩
  | or d ih =>
    rename_i φ ψ
    have hd0 : (φ ⋎ ψ).Bounded := by
      rcases hΓ (φ ⋎ ψ) (by simp) with h | h <;>
        exact bounded_of_strictOne h (by simp) (by simp)
    obtain ⟨hφ, hψ⟩ := Semiformula.Bounded.or_iff.mp hd0
    obtain ⟨f, hf, H⟩ := ih hd fun χ hχ ↦ by
      rcases Multiset.mem_add.mp hχ with hχ | hχ
      · exact hΓ χ (by simp [hχ])
      · rcases show χ = φ ∨ χ = ψ by simpa using hχ with rfl | rfl <;> grind
    exact ⟨f, hf, witnesses_or hd0 H⟩
  | and d₁ d₂ ih₁ ih₂ =>
    rename_i φ ψ
    have hd0 : (φ ⋏ ψ).Bounded := by
      rcases hΓ (φ ⋏ ψ) (by simp) with h | h <;>
        exact bounded_of_strictOne h (by simp) (by simp)
    obtain ⟨hφ, hψ⟩ := Semiformula.Bounded.and_iff.mp hd0
    obtain ⟨f₁, hf₁, H₁⟩ := ih₁ hd.1 fun χ hχ ↦ by
      rcases Multiset.mem_add.mp hχ with hχ | hχ
      · exact hΓ χ (by simp [hχ])
      · rcases show χ = φ by simpa using hχ
        grind
    obtain ⟨f₂, hf₂, H₂⟩ := ih₂ hd.2 fun χ hχ ↦ by
      rcases Multiset.mem_add.mp hχ with hχ | hχ
      · exact hΓ χ (by simp [hχ])
      · rcases show χ = ψ by simpa using hχ
        grind
    exact ⟨_, by primrec, witnesses_and hd0 H₁ H₂⟩
  | cut d₁ d₂ ih₁ ih₂ =>
    rename_i χ
    obtain ⟨f₁, hf₁, H₁⟩ := ih₁ hd.2.1 fun ρ hρ ↦ by
      rcases Multiset.mem_add.mp hρ with hρ | hρ
      · exact hΓ ρ (by simp [hρ])
      · rcases show ρ = χ by simpa using hρ
        exact hd.1
    obtain ⟨f₂, hf₂, H₂⟩ := ih₂ hd.2.2 fun ρ hρ ↦ by
      rcases Multiset.mem_add.mp hρ with hρ | hρ
      · exact hΓ ρ (by simp [hρ])
      · rcases show ρ = ∼χ by simpa using hρ
        rcases hd.1 with h | h
        · exact Or.inr (StrictHierarchy.neg_iff.mpr h)
        · exact Or.inl (StrictHierarchy.neg_iff.mpr h)
    exact ⟨_, by primrec, witnesses_cut hd.1 H₁ H₂⟩
  | exs d ih =>
    rename_i ξ t
    have hσ : StrictHierarchy 𝚺 1 (∃¹ ξ) := by
      rcases hΓ (∃¹ ξ) (by simp) with h | h
      · exact h
      · cases h with
        | ofAlt h => grind
    obtain ⟨f, hf, H⟩ := ih hd fun χ hχ ↦ by
      rcases Multiset.mem_add.mp hχ with hχ | hχ
      · exact hΓ χ (by simp [hχ])
      · rcases show χ = ξ/[t] by simpa using hχ
        grind
    exact ⟨_, by primrec, witnesses_exs hσ H⟩
  | all d ih =>
    rename_i ξ
    by_cases hσ : StrictHierarchy 𝚺 1 (∀¹ ξ)
    · have hd0 : (∀¹ ξ).Bounded := by
        cases hσ with | ofAlt h => grind
      obtain ⟨f, hf, H⟩ := ih hd fun χ hχ ↦ by
        rcases Multiset.mem_add.mp hχ with hχ | hχ
        · obtain ⟨χ', hχ', rfl⟩ := Multiset.mem_map.mp hχ
          rcases hΓ χ' (by simp [hχ']) with h | h
          · grind
          · grind
        · rcases show χ = Rewriting.free ξ by simpa using hχ
          grind
      obtain ⟨t, ρ, rfl, hρ⟩ := Semiformula.Bounded.exists_of_all hd0
      exact ⟨_, by primrec, witnesses_all_bounded hρ H⟩
    · obtain ⟨f, hf, H⟩ := ih hd fun χ hχ ↦ by
        rcases Multiset.mem_add.mp hχ with hχ | hχ
        · obtain ⟨χ', hχ', rfl⟩ := Multiset.mem_map.mp hχ
          rcases hΓ χ' (by simp [hχ']) with h | h
          · grind
          · grind
        · rcases show χ = Rewriting.free ξ by simpa using hχ
          rcases hΓ (∀¹ ξ) (by simp) with h | h
          · exact absurd h hσ
          · cases h with
            | ofAlt h => grind
            | all h => exact Or.inr (StrictHierarchy.rew _ h)
      exact ⟨_, by primrec, witnesses_all_pi hσ H⟩
  | ind ξ hξ t d ih =>
    obtain ⟨f, hf, H⟩ := ih hd fun χ hχ ↦ by
      rcases Multiset.mem_add.mp hχ with hχ | hχ
      · obtain ⟨χ', hχ', rfl⟩ := Multiset.mem_map.mp hχ
        rcases hΓ χ' (by simp [hχ']) with h | h
        · grind
        · grind
      · rcases show χ = ∼(Rewriting.free ξ) ∨ χ = (Rewriting.shift ξ)/[‘&0 + 1’] by
          simpa using hχ with rfl | rfl
        · exact Or.inr (by simpa using hξ)
        · grind
    by_cases hΔ : ξ.Bounded
    · obtain ⟨s, hs⟩ := exists_term_evalBound_of_bounded hΔ
      have hΔ' : (∼ξ).Bounded := Semiformula.Bounded.neg_iff.mpr hΔ
      obtain ⟨s', hs'⟩ := exists_term_evalBound_of_bounded hΔ'
      have hB : ξ.Bounded → ∀ l : List ℕ,
          (Semiformula.Eval ![0] (l.getD · 0) ξ →
            EvalBound ![0] (l.getD · 0)
              (max (Semiterm.val ![] (l.getD · 0) (Rew.subst ![‘0’] s) + 1)
                (Semiterm.val ![] (l.getD · 0) (Rew.subst ![‘0’] s') + 1)) ξ) ∧
          (Semiformula.Eval ![0] (l.getD · 0) (∼ξ) →
            EvalBound ![0] (l.getD · 0)
              (max (Semiterm.val ![] (l.getD · 0) (Rew.subst ![‘0’] s) + 1)
                (Semiterm.val ![] (l.getD · 0) (Rew.subst ![‘0’] s') + 1))
              (∼ξ)) := by
        intro _ l
        refine ⟨fun hev ↦ evalBound_mono (le_max_left _ _) ?_,
          fun hev ↦ evalBound_mono (le_max_right _ _) ?_⟩
        · simpa [Semiterm.val_substs, Matrix.constant_eq_singleton] using hs ![0] (l.getD · 0) hev
        · simpa [Semiterm.val_substs, Matrix.constant_eq_singleton] using
            hs' ![0] (l.getD · 0) hev
      exact ⟨_, by primrec, witnesses_ind hξ hB H⟩
    · exact ⟨_, by primrec, witnesses_ind (B := fun _ ↦ 0) hξ (fun hc ↦ absurd hc hΔ) H⟩

end LKI

end FFL.FirstOrder.Arithmetic

end
