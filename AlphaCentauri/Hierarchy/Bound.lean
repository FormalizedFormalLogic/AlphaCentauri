module

public import AlphaCentauri.ToFoundation.Fvar
public import AlphaCentauri.ToFoundation.Primrec
public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy
public import Foundation.FirstOrder.Tarski.Basic

/-!
# Bounded approximation of $\Sigma_1$ formulas

`bound u φ` bounds the leading block of existential quantifiers of `φ` by `u`, so that the
approximation of a strict $\Sigma_1$ formula is $\Delta_0$. The approximation implies `φ`, it
grows with the bound, and a true strict $\Sigma_1$ formula has one.

- [Bus98A, Section 3.1.2]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {ξ : Type*} {n : ℕ}

/-- `bound u φ` replaces the leading existential quantifiers of `φ` by quantifiers bounded
by `u`.

- [Bus98A, Section 3.1.2] -/
def bound : {n : ℕ} → ArithmeticSemiterm ξ n → ArithmeticSemiformula ξ n →
    ArithmeticSemiformula ξ n
  | _, _, .rel R v => .rel R v
  | _, _, .nrel R v => .nrel R v
  | _, _, ⊤ => ⊤
  | _, _, ⊥ => ⊥
  | _, _, φ ⋏ ψ => φ ⋏ ψ
  | _, _, φ ⋎ ψ => φ ⋎ ψ
  | _, _, ∀¹ φ => ∀¹ φ
  | _, u, ∃¹ φ => ∃¹[“#0 < !!(Rew.bShift u)”] bound (Rew.bShift u) φ

@[simp] lemma bound_exs (u : ArithmeticSemiterm ξ n) (φ : ArithmeticSemiformula ξ (n + 1)) :
    bound u (∃¹ φ) = ∃¹[“#0 < !!(Rew.bShift u)”] bound (Rew.bShift u) φ := rfl

private lemma bounded_of_bounded_exs {φ : ArithmeticSemiformula ξ (n + 1)}
    (h : Semiformula.Bounded (∃¹ φ)) : φ.Bounded := by
  cases h with
  | bexs _ hφ => exact Hierarchy.and (Hierarchy.rel _ _ _ _) hφ

private lemma bounded_of_strictHierarchy_zero {b : Polarity} {φ : ArithmeticSemiformula ξ n}
    (h : StrictHierarchy b 0 φ) : φ.Bounded := by cases h with | zero h => exact h

private lemma strictSigmaOne_of_exs {φ : ArithmeticSemiformula ξ (n + 1)}
    (h : StrictHierarchy 𝚺 1 (∃¹ φ)) : StrictHierarchy 𝚺 1 φ := by
  cases h with
  | ofAlt h => exact .ofAlt (.zero (bounded_of_bounded_exs (bounded_of_strictHierarchy_zero h)))
  | exs h => exact h

/-- The approximation of a strict $\Sigma_1$ formula is $\Delta_0$. -/
lemma bounded_bound : {n : ℕ} → {φ : ArithmeticSemiformula ξ n} → StrictHierarchy 𝚺 1 φ →
    (u : ArithmeticSemiterm ξ n) → (bound u φ).Bounded
  | _, .rel _ _, _, _ => by simp [bound]
  | _, .nrel _ _, _, _ => by simp [bound]
  | _, ⊤, _, _ => by simp [bound]
  | _, ⊥, _, _ => by simp [bound]
  | _, _ ⋏ _, h, _ => by cases h with | ofAlt h => exact bounded_of_strictHierarchy_zero h
  | _, _ ⋎ _, h, _ => by cases h with | ofAlt h => exact bounded_of_strictHierarchy_zero h
  | _, ∀¹ _, h, _ => by cases h with | ofAlt h => exact bounded_of_strictHierarchy_zero h
  | _, ∃¹ φ, h, u => by
    refine Hierarchy.bexs (Rew.positive_iff.mpr ⟨u, rfl⟩) ?_
    exact bounded_bound (strictSigmaOne_of_exs h) _
  termination_by _ φ => φ.complexity

/-! ## The approximation, read semantically -/

/-- `EvalBound e ε b φ` says that `φ` is true under `e` and `ε` with every leading existential
witnessed below `b`.

- [Bus98A, Section 3.1.2] -/
def EvalBound : {n : ℕ} → (Fin n → ℕ) → (ξ → ℕ) → ℕ → ArithmeticSemiformula ξ n → Prop
  | _, e, ε, b, ∃¹ φ => ∃ x < b, EvalBound (x :> e) ε b φ
  | _, e, ε, _, φ => Semiformula.Eval e ε φ

@[simp] lemma evalBound_exs {e : Fin n → ℕ} {ε : ξ → ℕ} {b} {φ : ArithmeticSemiformula ξ (n + 1)} :
    EvalBound e ε b (∃¹ φ) ↔ ∃ x < b, EvalBound (x :> e) ε b φ := Iff.rfl

/-- The approximation is what the bounded formula says. -/
lemma evalBound_iff_eval_bound : {n : ℕ} → {φ : ArithmeticSemiformula ξ n} →
    {u : ArithmeticSemiterm ξ n} → {e : Fin n → ℕ} → {ε : ξ → ℕ} →
    (EvalBound e ε (Semiterm.val e ε u) φ ↔ Semiformula.Eval e ε (bound u φ))
  | _, .rel _ _, _, _, _ => Iff.rfl
  | _, .nrel _ _, _, _, _ => Iff.rfl
  | _, ⊤, _, _, _ => by simp [bound, EvalBound]
  | _, ⊥, _, _, _ => by simp [bound, EvalBound]
  | _, _ ⋏ _, _, _, _ => Iff.rfl
  | _, _ ⋎ _, _, _, _ => Iff.rfl
  | _, ∀¹ _, _, _, _ => Iff.rfl
  | _, ∃¹ φ, u, e, ε => by
    simp only [evalBound_exs, bound_exs, Semiformula.eval_bexs]
    constructor
    · rintro ⟨x, hx, h⟩
      refine ⟨x, by simpa using hx, ?_⟩
      exact evalBound_iff_eval_bound.mp (by simpa using h)
    · rintro ⟨x, hx, h⟩
      refine ⟨x, by simpa using hx, ?_⟩
      simpa using evalBound_iff_eval_bound.mpr h
  termination_by _ φ => φ.complexity

/-- The approximation implies the formula. -/
lemma eval_of_evalBound : {n : ℕ} → {φ : ArithmeticSemiformula ξ n} → {b : ℕ} →
    {e : Fin n → ℕ} → {ε : ξ → ℕ} → EvalBound e ε b φ → Semiformula.Eval e ε φ
  | _, .rel _ _, _, _, _, h => h
  | _, .nrel _ _, _, _, _, h => h
  | _, ⊤, _, _, _, h => h
  | _, ⊥, _, _, _, h => h
  | _, _ ⋏ _, _, _, _, h => h
  | _, _ ⋎ _, _, _, _, h => h
  | _, ∀¹ _, _, _, _, h => h
  | _, ∃¹ _, _, _, _, h => by
    obtain ⟨x, _, hx⟩ := h
    exact ⟨x, eval_of_evalBound hx⟩
  termination_by _ φ => φ.complexity

/-- The approximation grows with the bound. -/
lemma evalBound_mono : {n : ℕ} → {φ : ArithmeticSemiformula ξ n} → {b b' : ℕ} → b ≤ b' →
    {e : Fin n → ℕ} → {ε : ξ → ℕ} → EvalBound e ε b φ → EvalBound e ε b' φ
  | _, .rel _ _, _, _, _, _, _, h => h
  | _, .nrel _ _, _, _, _, _, _, h => h
  | _, ⊤, _, _, _, _, _, h => h
  | _, ⊥, _, _, _, _, _, h => h
  | _, _ ⋏ _, _, _, _, _, _, h => h
  | _, _ ⋎ _, _, _, _, _, _, h => h
  | _, ∀¹ _, _, _, _, _, _, h => h
  | _, ∃¹ _, _, _, hb, _, _, h => by
    obtain ⟨x, hx, hxb⟩ := h
    exact ⟨x, lt_of_lt_of_le hx hb, evalBound_mono hb hxb⟩
  termination_by _ φ => φ.complexity

/-- A true strict $\Sigma_1$ formula has an approximation. -/
lemma exists_evalBound : {n : ℕ} → {φ : ArithmeticSemiformula ξ n} → StrictHierarchy 𝚺 1 φ →
    {e : Fin n → ℕ} → {ε : ξ → ℕ} → Semiformula.Eval e ε φ → ∃ b, EvalBound e ε b φ
  | _, .rel _ _, _, _, _, h => ⟨0, h⟩
  | _, .nrel _ _, _, _, _, h => ⟨0, h⟩
  | _, ⊤, _, _, _, h => ⟨0, h⟩
  | _, ⊥, _, _, _, h => ⟨0, h⟩
  | _, _ ⋏ _, _, _, _, h => ⟨0, h⟩
  | _, _ ⋎ _, _, _, _, h => ⟨0, h⟩
  | _, ∀¹ _, _, _, _, h => ⟨0, h⟩
  | _, ∃¹ φ, hφ, e, ε, h => by
    obtain ⟨x, hx⟩ : ∃ x, Semiformula.Eval (x :> e) ε φ := by simpa using h
    obtain ⟨b, hb⟩ := exists_evalBound (strictSigmaOne_of_exs hφ) hx
    exact ⟨max (x + 1) b, x, lt_of_lt_of_le (Nat.lt_succ_self x) (le_max_left _ _),
      evalBound_mono (le_max_right _ _) hb⟩
  termination_by _ φ => φ.complexity

/-- The approximation commutes with rewriting. -/
lemma evalBound_rew : {n₁ n₂ : ℕ} → {ξ₁ ξ₂ : Type*} → (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) →
    (φ : ArithmeticSemiformula ξ₁ n₁) → {e : Fin n₂ → ℕ} → {ε : ξ₂ → ℕ} → {b : ℕ} →
    (EvalBound e ε b (ω ▹ φ) ↔
      EvalBound (Semiterm.val e ε ∘ ω ∘ Semiterm.bvar) (Semiterm.val e ε ∘ ω ∘ Semiterm.fvar) b φ)
  | _, _, _, _, ω, .rel _ _, _, _, _ => Semiformula.eval_rew ω _
  | _, _, _, _, ω, .nrel _ _, _, _, _ => Semiformula.eval_rew ω _
  | _, _, _, _, ω, ⊤, _, _, _ => Semiformula.eval_rew ω _
  | _, _, _, _, ω, ⊥, _, _, _ => Semiformula.eval_rew ω _
  | _, _, _, _, ω, _ ⋏ _, _, _, _ => Semiformula.eval_rew ω _
  | _, _, _, _, ω, _ ⋎ _, _, _, _ => Semiformula.eval_rew ω _
  | _, _, _, _, ω, ∀¹ _, _, _, _ => Semiformula.eval_rew ω _
  | _, _, _, _, ω, ∃¹ φ, e, ε, b => by
    have key : ∀ x : ℕ, EvalBound (x :> e) ε b (ω.q ▹ φ) ↔
        EvalBound (x :> (Semiterm.val e ε ∘ ⇑ω ∘ Semiterm.bvar))
          (Semiterm.val e ε ∘ ⇑ω ∘ Semiterm.fvar) b φ := by
      intro x
      have e₁ : (Semiterm.val (x :> e) ε ∘ ⇑ω.q ∘ Semiterm.bvar)
          = x :> (Semiterm.val e ε ∘ ⇑ω ∘ Semiterm.bvar) := by
        funext i; cases i using Fin.cases <;> simp
      have e₂ : (Semiterm.val (x :> e) ε ∘ ⇑ω.q ∘ Semiterm.fvar)
          = Semiterm.val e ε ∘ ⇑ω ∘ Semiterm.fvar := by funext y; simp
      rw [evalBound_rew ω.q φ, e₁, e₂]
    simp only [Rewriting.app_exs, evalBound_exs]
    exact exists_congr fun x ↦ and_congr_right fun _ ↦ key x
  termination_by _ _ _ _ _ φ => φ.complexity

/-! ## The approximation of a proposition -/

variable {φ : ArithmeticProposition} {b b' : ℕ} {ε : ℕ → ℕ}

/-- `Bnd φ b ε` says that `φ` is true under `ε` with every leading existential witnessed
below `b`.

- [Bus98A, Section 3.1.2] -/
abbrev Bnd (φ : ArithmeticProposition) (b : ℕ) (ε : ℕ → ℕ) : Prop := EvalBound ![] ε b φ

lemma evalf_of_bnd (h : Bnd φ b ε) : φ.Evalf ε := eval_of_evalBound h

lemma bnd_mono (hb : b ≤ b') (h : Bnd φ b ε) : Bnd φ b' ε := evalBound_mono hb h

lemma exists_bnd (hφ : StrictHierarchy 𝚺 1 φ) (h : φ.Evalf ε) : ∃ b, Bnd φ b ε :=
  exists_evalBound hφ h

/-- The approximation of a proposition is the truth of a fixed $\Delta_0$ formula, with the bound
supplied by its bound variable. -/
lemma bnd_iff_eval_bound_bShift :
    Bnd φ b ε ↔ Semiformula.Eval ![b] ε (bound #0 (Rew.bShift ▹ φ)) := by
  have h := evalBound_iff_eval_bound (u := (#0 : ArithmeticSemiterm ℕ 1)) (e := ![b]) (ε := ε)
    (φ := Rew.bShift ▹ φ)
  simp only [Semiterm.val_bvar, Matrix.cons_val_zero] at h
  rw [← h, evalBound_rew]
  simp [Function.comp_def, Matrix.empty_eq]

/-- The approximation is a primitive recursive predicate of the bound and the assignment.

- [HP98, Theorem 0.35] -/
lemma primrecRel_bnd (hφ : StrictHierarchy 𝚺 1 φ) :
    PrimrecRel fun (b : ℕ) (l : List ℕ) ↦ Bnd φ b (l.getD · 0) := by
  set ψ : ArithmeticSemiformula ℕ 1 := bound #0 (Rew.bShift ▹ φ) with hψ
  have hb : ψ.Bounded := bounded_bound (StrictHierarchy.rew _ hφ) _
  have hσ : (ψ.toSemisentence ![#0]).Bounded := Hierarchy.rew _ hb
  have key : ∀ (b : ℕ) (l : List ℕ), Bnd φ b (l.getD · 0) ↔
      ℕ ⊧/(b :> fun i : Fin ψ.fvSup ↦ l.getD i 0) (ψ.toSemisentence ![#0]) := by
    intro b l
    rw [bnd_iff_eval_bound_bShift]
    exact (Semiformula.eval_toSemisentence_one ψ b _).symm
  have hvec : Primrec₂ fun (b : ℕ) (l : List ℕ) ↦
      (b ::ᵥ List.Vector.ofFn fun i : Fin ψ.fvSup ↦ l.getD i 0) :=
    Primrec.vector_cons.comp₂ Primrec₂.left
      ((Primrec.vector_ofFn fun i ↦ (Primrec.list_getD 0).comp Primrec.id
        (Primrec.const (i : ℕ))).comp₂ Primrec₂.right)
  have := (bounded_primrec_vec Empty.elim _ _ hσ).comp hvec
  refine this.of_eq fun p ↦ ?_
  have e : (List.Vector.ofFn fun i : Fin ψ.fvSup ↦ p.2.getD (i : ℕ) 0).get
      = fun i : Fin ψ.fvSup ↦ p.2.getD (i : ℕ) 0 := funext (List.Vector.get_ofFn _)
  simp only [List.Vector.cons_get, e]
  exact (key p.1 p.2).symm

end FFL.FirstOrder.Arithmetic

end
