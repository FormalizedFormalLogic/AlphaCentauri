module

public import AlphaCentauri.ToFoundation.Rew
public import AlphaCentauri.Hierarchy.Bounded
public import Foundation.FirstOrder.Arithmetic.Basic
public import Foundation.FirstOrder.LK.Basic

/-!
# A one-sided sequent calculus with an induction rule

`LKI[C]` is Foundation's one-sided calculus `LK.Derivation` over `ℒₒᵣ` with two further rules: a
leaf `bounded` for a sequent of $\Delta_0$ formulas true in `ℕ` under every assignment, and an
induction rule for the formulas of a class `C`, carrying the side formulas that make it as strong
as the induction axioms for `C`. A derivation is `Anchored D` when every cut formula belongs
to `D`.

The induction class is a parameter: taking `C` to be the strict $\Sigma_1$ formulas and `D` the
strict $\Sigma_1$ and $\Pi_1$ ones gives the calculus for $\mathsf{I}\Sigma_1$, and the same
calculus serves the other induction schemes.

The leaf is semantic rather than the axioms of `𝗣𝗔⁻`, because `addEqOfLt` is $\Pi_2$ and would
break the invariant that every formula of a sequent is $\Sigma_1$ or $\Pi_1$.

- [Bus98A, Section 1.4.1]
- [Bus98A, Section 1.4.2]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Rewriting LawfulSyntacticRewriting

/-- Closure under substitution of terms for the free variables: what an induction class has to
satisfy for `LKI.Derivation.rewrite` to stay inside it. -/
class RewriteClosed {n : ℕ} (C : ArithmeticSemiformula ℕ n → Prop) : Prop where
  rewrite (f : ℕ → ArithmeticSemiterm ℕ n) {φ : ArithmeticSemiformula ℕ n} :
    C φ → C (Rew.rewrite f ▹ φ)

namespace RewriteClosed

variable {n s : ℕ} {b : Polarity} {C D : ArithmeticSemiformula ℕ n → Prop}

instance strictHierarchy : RewriteClosed (n := n) (StrictHierarchy b s) where
  rewrite f := StrictHierarchy.rew (Rew.rewrite f)

instance hierarchy : RewriteClosed (n := n) (Hierarchy b s) where
  rewrite f := Hierarchy.rew (Rew.rewrite f)

instance or [RewriteClosed C] [RewriteClosed D] : RewriteClosed fun φ ↦ C φ ∨ D φ where
  rewrite f := fun h ↦ h.imp (rewrite f) (rewrite f)

lemma shift [RewriteClosed C] {φ : ArithmeticSemiformula ℕ n} (h : C φ) :
    C (Rewriting.shift φ) := by
  have e : (Rew.shift : SyntacticRew ℒₒᵣ n n) = Rew.rewrite fun x ↦ &(x + 1) := by ext x <;> simp
  simpa [Rewriting.shift, e] using rewrite (C := C) (fun x ↦ &(x + 1)) h

end RewriteClosed

namespace LKI

/-- Derivations of `LKI[C]`: Foundation's one-sided calculus for `ℒₒᵣ`, together with a leaf for
the $\Delta_0$ sequents true in `ℕ` and an induction rule for the formulas of `C`.

The induction rule takes its base case as a premise of its own, where [Bus98A] keeps it as a side
formula of the conclusion. Buss's form is `Derivable.ind'`, derived from this one without a cut;
the converse needs a cut on the base case.

- [Bus98A, Section 1.4.1]
- [Bus98A, Section 1.4.2] -/
inductive Derivation (C : ArithmeticSemiformula ℕ 1 → Prop) : LK.Sequent ℒₒᵣ → Type
  | bounded (Γ) (hΓ : ∀ φ ∈ Γ, Semiformula.Bounded φ)
      (h : ∀ ε : ℕ → ℕ, ∃ φ ∈ Γ, φ.Evalf ε) : Derivation C Γ
  | ind {Γ} (φ) (hφ : C φ) (t) :
      Derivation C (Γ + ⦃φ/[‘0’]⦄) →
      Derivation C (Γ⁺ + ⦃∼(free φ), (shift φ)/[‘&0 + 1’]⦄) →
      Derivation C (Γ + ⦃φ/[t]⦄)
  | identity {k} (r : (ℒₒᵣ).Rel k) (v) : Derivation C ⦃Semiformula.rel r v, Semiformula.nrel r v⦄
  | cut {Γ Δ φ} : Derivation C (Γ + ⦃φ⦄) → Derivation C (Δ + ⦃∼φ⦄) → Derivation C (Γ + Δ)
  | contraction {Γ φ} : Derivation C (Γ + ⦃φ, φ⦄) → Derivation C (Γ + ⦃φ⦄)
  | weakening {Γ φ} : Derivation C Γ → Derivation C (Γ + ⦃φ⦄)
  | verum : Derivation C ⦃⊤⦄
  | or {Γ φ ψ} : Derivation C (Γ + ⦃φ, ψ⦄) → Derivation C (Γ + ⦃φ ⋎ ψ⦄)
  | and {Γ φ ψ} : Derivation C (Γ + ⦃φ⦄) → Derivation C (Γ + ⦃ψ⦄) → Derivation C (Γ + ⦃φ ⋏ ψ⦄)
  | all {Γ φ} : Derivation C (Γ⁺ + ⦃free φ⦄) → Derivation C (Γ + ⦃∀¹ φ⦄)
  | exs {Γ φ t} : Derivation C (Γ + ⦃φ/[t]⦄) → Derivation C (Γ + ⦃∃¹ φ⦄)

@[inherit_doc] notation:45 "⊢ᴸᴷᴵ[" C "]! " Γ:45 => Derivation C Γ

/-- `⊢ᴸᴷᴵ[C] Γ` says that the sequent `Γ` is derivable in `LKI[C]`.

- [Bus98A, Section 1.4.1] -/
def Derivable (C : ArithmeticSemiformula ℕ 1 → Prop) (Γ : LK.Sequent ℒₒᵣ) : Prop :=
  Nonempty (⊢ᴸᴷᴵ[C]! Γ)

@[inherit_doc] notation:45 "⊢ᴸᴷᴵ[" C "] " Γ:45 => Derivable C Γ

namespace Derivation

variable {C : ArithmeticSemiformula ℕ 1 → Prop}
  {D D' : ArithmeticProposition → Prop}
  {Γ Δ : LK.Sequent ℒₒᵣ} {φ ψ χ : ArithmeticProposition}
  {ξ : ArithmeticSemiformula ℕ 1} {t : ArithmeticTerm ℕ}

abbrev cast (d : ⊢ᴸᴷᴵ[C]! Δ) (e : Δ = Γ := by abel) : ⊢ᴸᴷᴵ[C]! Γ := e ▸ d

instance : Structural (Derivation C) where
  weakening d := d.weakening
  contraction d := d.contraction

/-! ## Excluded middle -/

/-- The law of excluded middle: the `identity` rule for an arbitrary formula, by recursion
on its construction.

- [Bus98A, Section 1.4.1] -/
def lem : (φ : ArithmeticProposition) → ⊢ᴸᴷᴵ[C]! ⦃φ, ∼φ⦄
  | .rel R v => identity R v
  | .nrel R v => (identity R v).cast (by simp [add_comm])
  | ⊤ => verum.weakening
  | ⊥ => (verum.weakening (φ := ⊥)).cast (by simp [add_comm])
  | φ ⋏ ψ =>
    or (Γ := ⦃φ ⋏ ψ⦄) (φ := ∼φ) (ψ := ∼ψ)
      (and (Γ := ⦃∼φ, ∼ψ⦄) (φ := φ) (ψ := ψ)
        ((lem φ).weakening (φ := ∼ψ) |>.cast)
        ((lem ψ).weakening (φ := ∼φ) |>.cast) |>.cast)
      |>.cast (by simp [add_comm])
  | φ ⋎ ψ =>
    and (Γ := ⦃φ ⋎ ψ⦄) (φ := ∼φ) (ψ := ∼ψ)
      (or (Γ := ⦃∼φ⦄) (φ := φ) (ψ := ψ) ((lem φ).weakening (φ := ψ) |>.cast) |>.cast)
      (or (Γ := ⦃∼ψ⦄) (φ := φ) (ψ := ψ) ((lem ψ).weakening (φ := φ) |>.cast) |>.cast)
      |>.cast (by simp)
  | ∀¹ φ =>
    all (Γ := ⦃∃¹ ∼φ⦄) (φ := φ)
      (exs (Γ := ⦃free φ⦄) (φ := ∼(shift φ)) (t := &0)
        ((lem (free φ)).cast (by simp)) |>.cast (by simp [add_comm]))
      |>.cast (by simp [add_comm])
  | ∃¹ φ =>
    all (Γ := ⦃∃¹ φ⦄) (φ := ∼φ)
      (exs (Γ := ⦃free (∼φ)⦄) (φ := shift φ) (t := &0)
        ((lem (free (∼φ))).cast (by simp [add_comm])) |>.cast (by simp [add_comm]))
      |>.cast (by simp)
  termination_by φ => φ.complexity

/-! ## Embedding `LK` -/

/-- Every `LK` derivation is an `LKI[C]` derivation. -/
def ofLK {Γ : LK.Sequent ℒₒᵣ} : (⊢ᴸᴷ¹ Γ) → ⊢ᴸᴷᴵ[C]! Γ
  | .identity R v => identity R v
  | .cut d₁ d₂ => (ofLK d₁).cut (ofLK d₂)
  | .contraction d => (ofLK d).contraction
  | .weakening d => (ofLK d).weakening
  | .verum => verum
  | .or d => (ofLK d).or
  | .and d₁ d₂ => (ofLK d₁).and (ofLK d₂)
  | .all d => (ofLK d).all
  | .exs d => (ofLK d).exs

/-! ## Soundness -/

/-- The sequent of an `LKI[C]` derivation contains a formula true in `ℕ` under every assignment.

- [Bus98A, Section 1.4.1] -/
theorem sound (ε : ℕ → ℕ) {Γ} : (⊢ᴸᴷᴵ[C]! Γ) → ∃ φ ∈ Γ, φ.Evalf ε
  | bounded _ _ h => h ε
  | ind (Γ := Γ) φ _ t d₀ d => by
    by_contra! hc;
    have hΓ : ∀ ψ ∈ Γ, ¬ψ.Evalf ε := fun ψ hψ ↦ hc ψ (by simp [hψ])
    have base : Semiformula.Eval ![0] ε φ := by
      have h : (∃ ψ ∈ Γ, ψ.Evalf ε) ∨ Semiformula.Eval ![0] ε φ := by simpa using sound ε d₀
      rcases h with (⟨ψ, hψ, h⟩ | h)
      · exact absurd h (hΓ ψ hψ)
      · exact h
    have top : ¬Semiformula.Eval ![Semiterm.val ![] ε t] ε φ := by simpa using hc (φ/[t]) (by simp)
    have step : ∀ a : ℕ, Semiformula.Eval ![a] ε φ → Semiformula.Eval ![a + 1] ε φ := by
      intro a ha
      have h : (∃ ψ ∈ Γ, ψ.Evalf ε) ∨
          ¬Semiformula.Eval ![a] ε φ ∨ Semiformula.Eval ![a + 1] ε φ := by
        simpa [Rewriting.shifts, or_and_right, exists_or] using sound (a :>ₙ ε) d
      rcases h with (⟨ψ, hψ, h⟩ | h | h)
      · exact absurd h (hΓ ψ hψ)
      · exact absurd ha h
      · exact h
    have : ∀ a : ℕ, Semiformula.Eval ![a] ε φ := by
      intro a
      induction a with
      | zero => exact base
      | succ b ih => exact step b ih
    exact top (this _)
  | identity r v => by
    by_cases h : (Semiformula.rel r v).Evalf ε
    · exact ⟨Semiformula.rel r v, by simp, h⟩
    · exact ⟨Semiformula.nrel r v, by simp, by simpa using h⟩
  | verum => ⟨⊤, by simp, by simp⟩
  | cut (Γ := Γ) (Δ := Δ) (φ := φ) d dn => by
    have h : (∃ ψ ∈ Γ, ψ.Evalf ε) ∨ φ.Evalf ε := by simpa using sound ε d
    have hn : (∃ ψ ∈ Δ, ψ.Evalf ε) ∨ ¬φ.Evalf ε := by simpa using sound ε dn
    rcases h with (⟨ψ, h, hψ⟩ | h)
    · exact ⟨ψ, by simp [h], hψ⟩
    · rcases hn with (⟨ψ, hn, hψ⟩ | hn)
      · exact ⟨ψ, by simp [hn], hψ⟩
      · exact absurd h hn
  | contraction d => by simpa using sound ε d
  | weakening d => by
    obtain ⟨φ, hφ, h⟩ := sound ε d
    exact ⟨φ, by simp [hφ], h⟩
  | or (Γ := Γ) (φ := φ) (ψ := ψ) d => by
    have : (∃ χ ∈ Γ, χ.Evalf ε) ∨ φ.Evalf ε ∨ ψ.Evalf ε := by
      simpa [or_and_right, exists_or] using sound ε d
    rcases this with (⟨χ, hχ, h⟩ | h | h)
    · exact ⟨χ, by simp [hχ], h⟩
    · exact ⟨φ ⋎ ψ, by simp, by simp [h]⟩
    · exact ⟨φ ⋎ ψ, by simp, by simp [h]⟩
  | and (Γ := Γ) (φ := φ) (ψ := ψ) dφ dψ => by
    have hφ : (∃ χ ∈ Γ, χ.Evalf ε) ∨ φ.Evalf ε := by simpa using sound ε dφ;
    have hψ : (∃ χ ∈ Γ, χ.Evalf ε) ∨ ψ.Evalf ε := by simpa using sound ε dψ;
    rcases hφ with (⟨χ, hχ, h⟩ | hφ) <;>
    rcases hψ with (⟨χ, hχ, h⟩ | hψ);
    case inr.inr => exact ⟨φ ⋏ ψ, by simp_all⟩
    all_goals exact ⟨χ, by simp_all⟩;
  | all (Γ := Γ) (φ := φ) d => by
    have : (∃ ψ ∈ Γ, ψ.Evalf ε) ∨ ∀ a : ℕ, Semiformula.Eval ![a] ε φ := by
      simpa [Rewriting.shifts, forall_or_left] using fun a : ℕ ↦ sound (a :>ₙ ε) d
    rcases this with (⟨ψ, hψ, h⟩ | h)
    · exact ⟨ψ, by simp [hψ], h⟩
    · exact ⟨∀¹ φ, by simp, h⟩
  | exs (Γ := Γ) (φ := φ) (t := t) d => by
    have : (∃ ψ ∈ Γ, ψ.Evalf ε) ∨ Semiformula.Eval ![Semiterm.val ![] ε t] ε φ := by
      simpa using sound ε d
    rcases this with (⟨ψ, hψ, h⟩ | h)
    · exact ⟨ψ, by simp [hψ], h⟩
    · exact ⟨∃¹ φ, by simp, Semiterm.val ![] ε t, h⟩

/-- Weakening by a whole sequent, along a traversal of it. -/
abbrev weakeningMany (t : Δ.Traversal) (d : ⊢ᴸᴷᴵ[C]! Γ) : ⊢ᴸᴷᴵ[C]! Γ + Δ :=
  Structural.weakenMany t d

/-- The induction rule in the form that leaves the base case as a side formula of the conclusion.

- [Bus98A, Section 1.4.2] -/
def ind' (hξ : C ξ) (t) (tΓ : Γ.Traversal)
    (d : ⊢ᴸᴷᴵ[C]! Γ⁺ + ⦃∼(free ξ), (shift ξ)/[‘&0 + 1’]⦄) :
    ⊢ᴸᴷᴵ[C]! Γ + ⦃∼(ξ/[‘0’]), ξ/[t]⦄ :=
  ind (Γ := Γ + ⦃∼(ξ/[‘0’])⦄) ξ hξ t
      (cast (weakeningMany tΓ (lem (ξ/[‘0’]))))
      (cast (d.weakening (φ := ∼((shift ξ)/[‘0’])))
        (by simp [Rewriting.shifts, Rew.shift_subst_eq]; abel))
    |>.cast

/-! ## Anchored derivations -/

/-- A derivation is `Anchored D` when every one of its cut formulas belongs to `D`.

- [Bus98A, Section 1.4.2] -/
def Anchored (D : ArithmeticProposition → Prop) {Γ} : (⊢ᴸᴷᴵ[C]! Γ) → Prop
  | bounded _ _ _ => True
  | ind _ _ _ d₀ d => Anchored D d₀ ∧ Anchored D d
  | identity _ _ => True
  | cut (φ := χ) dp dn => D χ ∧ Anchored D dp ∧ Anchored D dn
  | contraction d => Anchored D d
  | weakening d => Anchored D d
  | verum => True
  | or d => Anchored D d
  | and dp dq => Anchored D dp ∧ Anchored D dq
  | all d => Anchored D d
  | exs d => Anchored D d

@[simp] lemma anchored_bounded {hΓ h} : Anchored D (bounded (C := C) Γ hΓ h) := trivial

@[simp] lemma anchored_ind_iff {hξ} {d₀ : ⊢ᴸᴷᴵ[C]! Γ + ⦃ξ/[‘0’]⦄}
    {d : ⊢ᴸᴷᴵ[C]! Γ⁺ + ⦃∼(free ξ), (shift ξ)/[‘&0 + 1’]⦄} :
    Anchored D (ind ξ hξ t d₀ d) ↔ Anchored D d₀ ∧ Anchored D d := Iff.rfl

@[simp] lemma anchored_identity {k} {r : (ℒₒᵣ).Rel k} {v} :
    Anchored D (identity (C := C) r v) := trivial

@[simp] lemma anchored_cut_iff {dp : ⊢ᴸᴷᴵ[C]! Γ + ⦃χ⦄} {dn : ⊢ᴸᴷᴵ[C]! Δ + ⦃∼χ⦄} :
    Anchored D (dp.cut dn) ↔ D χ ∧ Anchored D dp ∧ Anchored D dn := Iff.rfl

@[simp] lemma anchored_contraction_iff {d : ⊢ᴸᴷᴵ[C]! Γ + ⦃φ, φ⦄} :
    Anchored D d.contraction ↔ Anchored D d := Iff.rfl

@[simp] lemma anchored_weakening_iff {d : ⊢ᴸᴷᴵ[C]! Γ} :
    Anchored D (d.weakening (φ := φ)) ↔ Anchored D d := Iff.rfl

@[simp] lemma anchored_verum : Anchored D (verum (C := C)) := trivial

@[simp] lemma anchored_or_iff {d : ⊢ᴸᴷᴵ[C]! Γ + ⦃φ, ψ⦄} :
    Anchored D d.or ↔ Anchored D d := Iff.rfl

@[simp] lemma anchored_and_iff {dp : ⊢ᴸᴷᴵ[C]! Γ + ⦃φ⦄} {dq : ⊢ᴸᴷᴵ[C]! Γ + ⦃ψ⦄} :
    Anchored D (dp.and dq) ↔ Anchored D dp ∧ Anchored D dq := Iff.rfl

@[simp] lemma anchored_all_iff {d : ⊢ᴸᴷᴵ[C]! Γ⁺ + ⦃free ξ⦄} :
    Anchored D d.all ↔ Anchored D d := Iff.rfl

@[simp] lemma anchored_exs_iff {d : ⊢ᴸᴷᴵ[C]! Γ + ⦃ξ/[t]⦄} :
    Anchored D d.exs ↔ Anchored D d := Iff.rfl

@[simp] lemma anchored_cast_iff {d : ⊢ᴸᴷᴵ[C]! Δ} {e : Δ = Γ} :
    Anchored D (cast d e) ↔ Anchored D d := by rcases e; rfl

@[simp] lemma anchored_structural_cast_iff {d : ⊢ᴸᴷᴵ[C]! Γ} {e : Γ = Δ} :
    Anchored D (Structural.cast (𝔇 := Derivation C) d e) ↔ Anchored D d := by rcases e; rfl

@[simp] lemma anchored_weakeningMany_iff {t : Δ.Traversal} {d : ⊢ᴸᴷᴵ[C]! Γ} :
    Anchored D (weakeningMany t d) ↔ Anchored D d := by
  induction t with
  | zero => simp [weakeningMany, Structural.weakenMany]
  | succ φ t ih => simpa [weakeningMany, Structural.weakenMany, Structural.weakening] using ih

/-- The excluded middle is derived without a cut, so its derivation is anchored in every class. -/
@[simp] lemma anchored_lem : ∀ φ : ArithmeticProposition, Anchored D (lem (C := C) φ)
  | .rel _ _ => by unfold lem; trivial
  | .nrel _ _ => by unfold lem; exact anchored_cast_iff.mpr trivial
  | ⊤ => by unfold lem; simp
  | ⊥ => by unfold lem; simp
  | φ ⋏ ψ => by unfold lem; simp [anchored_lem φ, anchored_lem ψ]
  | φ ⋎ ψ => by unfold lem; simp [anchored_lem φ, anchored_lem ψ]
  | ∀¹ φ => by
    unfold lem
    exact anchored_cast_iff.mpr <| anchored_cast_iff.mpr <| anchored_cast_iff.mpr <|
      anchored_lem (free φ)
  | ∃¹ φ => by
    unfold lem
    exact anchored_cast_iff.mpr <| anchored_cast_iff.mpr <| anchored_cast_iff.mpr <|
      anchored_lem (free (∼φ))
  termination_by φ => φ.complexity

@[simp] lemma anchored_ind'_iff {hξ : C ξ} {tΓ : Γ.Traversal}
    {d : ⊢ᴸᴷᴵ[C]! Γ⁺ + ⦃∼(free ξ), (shift ξ)/[‘&0 + 1’]⦄} :
    Anchored D (ind' hξ t tΓ d) ↔ Anchored D d := by simp [ind']

lemma Anchored.mono (h : ∀ φ, D φ → D' φ) {Γ} : {d : ⊢ᴸᴷᴵ[C]! Γ} → Anchored D d → Anchored D' d
  | bounded _ _ _, _ => trivial
  | ind _ _ _ _ _, hd => ⟨.mono h hd.1, .mono h hd.2⟩
  | identity _ _, _ => trivial
  | cut _ _, hd => ⟨h _ hd.1, .mono h hd.2.1, .mono h hd.2.2⟩
  | contraction d, hd => .mono h (d := d) hd
  | weakening d, hd => .mono h (d := d) hd
  | verum, _ => trivial
  | or d, hd => .mono h (d := d) hd
  | and _ _, hd => ⟨Anchored.mono h hd.1, .mono h hd.2⟩
  | all d, hd => .mono h (d := d) hd
  | exs d, hd => .mono h (d := d) hd

/-! ## Rewriting -/

section rewrite

variable [RewriteClosed C]

def rewrite {Γ} (f : ℕ → ArithmeticTerm ℕ) : (⊢ᴸᴷᴵ[C]! Γ) → ⊢ᴸᴷᴵ[C]! Γ.map (Rew.rewrite f ▹ ·)
  | bounded Γ hΓ h =>
    bounded _
      (by
        intro φ hφ
        rcases Multiset.mem_map.mp hφ with ⟨ψ, hψ, rfl⟩
        exact (hΓ ψ hψ).rew _)
      (by
        intro ε
        obtain ⟨ψ, hψ, hv⟩ := h fun x ↦ Semiterm.val ![] ε (f x)
        exact ⟨Rew.rewrite f ▹ ψ, Multiset.mem_map_of_mem _ hψ,
          by simpa [Semiformula.eval_rewrite] using hv⟩)
  | ind (Γ := Γ) φ hφ t d₀ d =>
    let g : ℕ → ArithmeticTerm ℕ := &0 :>ₙ fun x ↦ Rew.shift (f x)
    have h₀ := d₀.rewrite f
    have h := d.rewrite g
    ind (Γ := Γ.map (Rew.rewrite f ▹ ·)) (Rew.rewrite (Rew.bShift ∘ f) ▹ φ)
      (RewriteClosed.rewrite _ hφ) (Rew.rewrite f t)
      (cast h₀ (by simp [rewrite_subst_eq]))
      (cast h (by
        simp [g, free_rewrite_eq, Rewriting.shifts, shift_rewrite_eq, Function.comp_def,
          Rew.rewrite_subst_shift_eq]))
      |>.cast (by simp [rewrite_subst_eq])
  | identity R v => identity R (Rew.rewrite f ∘ v)
  | cut (Γ := Γ) (Δ := Δ) (φ := φ) d₁ d₂ => cut
      (Γ := Γ.map (Rew.rewrite f ▹ ·)) (Δ := Δ.map (Rew.rewrite f ▹ ·))
      (φ := Rew.rewrite f ▹ φ)
      ((d₁.rewrite f).cast (by simp)) ((d₂.rewrite f).cast (by simp))
      |>.cast (by simp)
  | contraction (Γ := Γ) (φ := φ) d =>
    (contraction (Γ := Γ.map (Rew.rewrite f ▹ ·)) (φ := Rew.rewrite f ▹ φ)
      ((d.rewrite f).cast (by simp))).cast (by simp)
  | weakening (Γ := Γ) (φ := φ) d => weakening
      (φ := Rew.rewrite f ▹ φ)
      (d.rewrite f)
      |>.cast (by simp)
  | verum => cast verum (by simp)
  | or (Γ := Γ) (φ := φ) (ψ := ψ) d => or
      (Γ := Γ.map (Rew.rewrite f ▹ ·))
      (φ := Rew.rewrite f ▹ φ)
      (ψ := Rew.rewrite f ▹ ψ)
      ((d.rewrite f).cast (by simp))
      |>.cast (by simp)
  | and (Γ := Γ) (φ := φ) (ψ := ψ) d₁ d₂ => and
      (Γ := Γ.map (Rew.rewrite f ▹ ·))
      (φ := Rew.rewrite f ▹ φ)
      (ψ := Rew.rewrite f ▹ ψ)
      ((d₁.rewrite f).cast (by simp)) ((d₂.rewrite f).cast (by simp))
      |>.cast (by simp)
  | all (Γ := Γ) (φ := φ) d =>
    let g : ℕ → ArithmeticTerm ℕ := &0 :>ₙ fun x ↦ Rew.shift (f x)
    have h := d.rewrite g
    (all (Γ := Γ.map (Rew.rewrite f ▹ ·)) (φ := Rew.rewrite (Rew.bShift ∘ f) ▹ φ)
      (cast h (by
        simp [g, free_rewrite_eq, Rewriting.shifts, shift_rewrite_eq,
          Function.comp_def]))).cast (by simp [Rew.q_rewrite])
  | exs (Γ := Γ) (φ := φ) (t := t) d =>
    have h := d.rewrite f
    (exs (Γ := Γ.map (Rew.rewrite f ▹ ·)) (φ := Rew.rewrite (Rew.bShift ∘ f) ▹ φ)
      (t := Rew.rewrite f t) (cast h (by simp [rewrite_subst_eq]))).cast (by simp [Rew.q_rewrite])

protected def map (d : ⊢ᴸᴷᴵ[C]! Γ) (f : ℕ → ℕ) : ⊢ᴸᴷᴵ[C]! Γ.map (Rew.rewriteMap f ▹ ·) :=
  d.rewrite fun x ↦ &(f x)

protected def shift (d : ⊢ᴸᴷᴵ[C]! Γ) : ⊢ᴸᴷᴵ[C]! Γ⁺ := cast (Derivation.map d Nat.succ) (by rfl)

/-- The induction rule with the step case taken at a variable that occurs in no formula of the
conclusion, in place of the shifted sequent the rule itself asks for. -/
def indByNewVar {m} (hξ : C ξ) (t) (hξm : ¬ξ.FVar? m) (hΓ : ∀ ψ ∈ Γ, ¬ψ.FVar? m)
    (d₀ : ⊢ᴸᴷᴵ[C]! Γ + ⦃ξ/[‘0’]⦄) (d : ⊢ᴸᴷᴵ[C]! Γ + ⦃∼(ξ/[&m]), ξ/[‘&m + 1’]⦄) :
    ⊢ᴸᴷᴵ[C]! Γ + ⦃ξ/[t]⦄ :=
  ind ξ hξ t d₀ <| cast (Derivation.map d fun x ↦ if x = m then 0 else x + 1) (by
    simp [Semiformula.map_rewriteMap_eq_shifts Γ hΓ, Semiformula.rewriteMap_subst_eq_free ξ hξm,
      Rew.app_substs, Semiformula.rewriteMap_eq_shift ξ hξm])

/-- Generalization on a variable that occurs in no formula of the conclusion. -/
def generalizeByNewVar {m} (hξ : ¬ξ.FVar? m) (hΓ : ∀ ψ ∈ Γ, ¬ψ.FVar? m)
    (d : ⊢ᴸᴷᴵ[C]! Γ + ⦃ξ/[&m]⦄) : ⊢ᴸᴷᴵ[C]! Γ + ⦃∀¹ ξ⦄ :=
  all <| cast (Derivation.map d fun x ↦ if x = m then 0 else x + 1)
    (by simp [Semiformula.rewriteMap_subst_eq_free ξ hξ, Semiformula.map_rewriteMap_eq_shifts Γ hΓ])

variable [RewriteClosed D] {Γ : LK.Sequent ℒₒᵣ}

lemma anchored_rewrite {Γ} : ∀ (d : ⊢ᴸᴷᴵ[C]! Γ) (f), Anchored D d → Anchored D (d.rewrite f)
  | bounded _ _ _, _, _ => trivial
  | ind _ _ _ d₀ d, _, h => by
    simpa [rewrite] using ⟨anchored_rewrite d₀ _ h.1, anchored_rewrite d _ h.2⟩
  | identity _ _, _, _ => trivial
  | cut dp dn, f, h => by
    simp only [rewrite, anchored_cast_iff, anchored_cut_iff]
    exact ⟨RewriteClosed.rewrite f h.1, anchored_rewrite dp f h.2.1, anchored_rewrite dn f h.2.2⟩
  | contraction d, f, h => by simpa [rewrite] using anchored_rewrite d f h
  | weakening d, f, h => by simpa [rewrite] using anchored_rewrite d f h
  | verum, _, _ => trivial
  | or d, f, h => by simpa [rewrite] using anchored_rewrite d f h
  | and dp dq, f, h => by
    simpa [rewrite] using ⟨anchored_rewrite dp f h.1, anchored_rewrite dq f h.2⟩
  | all d, _, h => by simpa [rewrite] using anchored_rewrite d _ h
  | exs d, f, h => by simpa [rewrite] using anchored_rewrite d f h

lemma anchored_map (d : ⊢ᴸᴷᴵ[C]! Γ) (f) (h : Anchored D d) : Anchored D (Derivation.map d f) :=
  anchored_rewrite d _ h

lemma anchored_shift (d : ⊢ᴸᴷᴵ[C]! Γ) (h : Anchored D d) : Anchored D d.shift :=
  anchored_map d Nat.succ h

lemma anchored_indByNewVar {m} {hξ : C ξ} {hξm : ¬ξ.FVar? m} {hΓ : ∀ ψ ∈ Γ, ¬ψ.FVar? m}
    {d₀ : ⊢ᴸᴷᴵ[C]! Γ + ⦃ξ/[‘0’]⦄} {d : ⊢ᴸᴷᴵ[C]! Γ + ⦃∼(ξ/[&m]), ξ/[‘&m + 1’]⦄}
    (h₀ : Anchored D d₀) (h : Anchored D d) : Anchored D (indByNewVar hξ t hξm hΓ d₀ d) := by
  simpa [indByNewVar] using And.intro h₀ (anchored_map d _ h)

lemma anchored_generalizeByNewVar {m} {hξ : ¬ξ.FVar? m} {hΓ : ∀ ψ ∈ Γ, ¬ψ.FVar? m}
    {d : ⊢ᴸᴷᴵ[C]! Γ + ⦃ξ/[&m]⦄} (h : Anchored D d) :
    Anchored D (generalizeByNewVar hξ hΓ d) := by
  simpa [generalizeByNewVar] using anchored_map d _ h

end rewrite

end Derivation

/-- The `D`-anchored derivations of `Γ` in `LKI[C]`. -/
abbrev AnchoredDerivation (C : ArithmeticSemiformula ℕ 1 → Prop) (D : ArithmeticProposition → Prop)
    (Γ : LK.Sequent ℒₒᵣ) := {d : ⊢ᴸᴷᴵ[C]! Γ // Derivation.Anchored D d}

@[inherit_doc] notation:45 "⊢ᴸᴷᴵ[" C ", " D "]! " Γ:45 => AnchoredDerivation C D Γ

namespace AnchoredDerivation

variable {C : ArithmeticSemiformula ℕ 1 → Prop} {D : ArithmeticProposition → Prop}
  {Γ Δ : LK.Sequent ℒₒᵣ}

def cast (d : ⊢ᴸᴷᴵ[C, D]! Γ) (e : Γ = Δ := by abel) : ⊢ᴸᴷᴵ[C, D]! Δ :=
  ⟨d.val.cast e, by simpa using d.prop⟩

end AnchoredDerivation

/-! ## Completeness for the true strict `$\Pi_1$` sequents -/

section valid

variable {C : ArithmeticSemiformula ℕ 1 → Prop} {D : ArithmeticProposition → Prop}
  {φ : ArithmeticProposition}

private lemma bounded_of_complexity_zero (h : φ.complexity = 0) : Semiformula.Bounded φ := by
  match φ with
  | .rel _ _ | .nrel _ _ | ⊤ | ⊥ => simp
  | _ ⋏ _ | _ ⋎ _ | ∀¹ _ | ∃¹ _ => simp at h

private lemma exists_all_of_strictPi1 (h : StrictHierarchy 𝚷 1 φ)
    (hb : ¬Semiformula.Bounded φ) : ∃ ξ, φ = ∀¹ ξ ∧ StrictHierarchy 𝚷 1 ξ := by
  rcases h with _ | h | _ | ⟨hξ⟩
  · rcases h with h | _ | _ | _
    · exact absurd h hb
  · exact ⟨_, rfl, hξ⟩

private lemma vecCons_head_tail (ε : ℕ → ℕ) : ε 0 :>ₙ (fun x ↦ ε (x + 1)) = ε := by
  funext x; cases x <;> rfl

/-- A sequent of strict $\Pi_1$ formulas true in `ℕ` under every assignment has an anchored
derivation: on this fragment the `bounded` leaf and the universal rule are already complete. -/
theorem nonempty_anchored_of_valid (n : ℕ) (Γ : LK.Sequent ℒₒᵣ)
    (hsum : (Γ.map Semiformula.complexity).sum ≤ n)
    (hΓ : ∀ φ ∈ Γ, StrictHierarchy 𝚷 1 φ)
    (hval : ∀ ε : ℕ → ℕ, ∃ φ ∈ Γ, φ.Evalf ε) : Nonempty (⊢ᴸᴷᴵ[C, D]! Γ) := by
  induction n generalizing Γ with
  | zero =>
    refine ⟨⟨.bounded Γ (fun φ hφ ↦ bounded_of_complexity_zero (Nat.le_zero.mp ?_)) hval, by simp⟩⟩
    exact le_trans (Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hφ)) hsum
  | succ n ih =>
    by_cases hb : ∀ φ ∈ Γ, Semiformula.Bounded φ
    · exact ⟨⟨.bounded Γ hb hval, by simp⟩⟩
    · push Not at hb;
      obtain ⟨φ, hφΓ, hφb⟩ := hb
      obtain ⟨ξ, rfl, hξ⟩ := exists_all_of_strictPi1 (hΓ φ hφΓ) hφb
      obtain ⟨Γ', rfl⟩ : ∃ Γ', Γ = Γ' + ⦃∀¹ ξ⦄ := by
        obtain ⟨Γ', rfl⟩ := Multiset.exists_cons_of_mem hφΓ
        exact ⟨Γ', by simp [Multiset.add_atom_eq_cons]⟩
      have hshift : (Γ'⁺).map Semiformula.complexity = Γ'.map Semiformula.complexity := by
        simp [Rewriting.shifts, Multiset.map_map]
      have h : Nonempty (⊢ᴸᴷᴵ[C, D]! Γ'⁺ + ⦃free ξ⦄) := by
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
      exact h.map fun d ↦ ⟨d.val.all, by simpa using d.prop⟩

/-- A sequent of strict $\Pi_1$ formulas true in `ℕ` under every assignment is derivable. -/
theorem derivable_of_valid (n : ℕ) (Γ : LK.Sequent ℒₒᵣ)
    (hsum : (Γ.map Semiformula.complexity).sum ≤ n)
    (hΓ : ∀ φ ∈ Γ, StrictHierarchy 𝚷 1 φ)
    (hval : ∀ ε : ℕ → ℕ, ∃ φ ∈ Γ, φ.Evalf ε) : ⊢ᴸᴷᴵ[C] Γ :=
  Nonempty.map Subtype.val
    (nonempty_anchored_of_valid (C := C) (D := fun _ ↦ True) n Γ hsum hΓ hval)

end valid

namespace Derivable

variable {C : ArithmeticSemiformula ℕ 1 → Prop} {Γ Δ : LK.Sequent ℒₒᵣ}
  {φ ψ : ArithmeticProposition} {ξ : ArithmeticSemiformula ℕ 1} {t : ArithmeticTerm ℕ}

/-! ### The rules, read as closure properties of derivability -/

lemma bounded (Γ) (hΓ : ∀ φ ∈ Γ, Semiformula.Bounded φ)
    (h : ∀ ε : ℕ → ℕ, ∃ φ ∈ Γ, φ.Evalf ε) : ⊢ᴸᴷᴵ[C] Γ := ⟨.bounded Γ hΓ h⟩

lemma ind (hξ : C ξ) (t) (h₀ : ⊢ᴸᴷᴵ[C] Γ + ⦃ξ/[‘0’]⦄)
    (h : ⊢ᴸᴷᴵ[C] Γ⁺ + ⦃∼(free ξ), (shift ξ)/[‘&0 + 1’]⦄) : ⊢ᴸᴷᴵ[C] Γ + ⦃ξ/[t]⦄ :=
  Nonempty.map2 (Derivation.ind ξ hξ t) h₀ h

lemma lem (φ : ArithmeticProposition) : ⊢ᴸᴷᴵ[C] ⦃φ, ∼φ⦄ := ⟨.lem φ⟩

lemma cut (h₁ : ⊢ᴸᴷᴵ[C] Γ + ⦃φ⦄) (h₂ : ⊢ᴸᴷᴵ[C] Δ + ⦃∼φ⦄) : ⊢ᴸᴷᴵ[C] Γ + Δ :=
  Nonempty.map2 Derivation.cut h₁ h₂

lemma contraction (h : ⊢ᴸᴷᴵ[C] Γ + ⦃φ, φ⦄) : ⊢ᴸᴷᴵ[C] Γ + ⦃φ⦄ :=
  Nonempty.map Derivation.contraction h

lemma weakening (φ) (h : ⊢ᴸᴷᴵ[C] Γ) : ⊢ᴸᴷᴵ[C] Γ + ⦃φ⦄ :=
  Nonempty.map (Derivation.weakening (φ := φ)) h

lemma verum : ⊢ᴸᴷᴵ[C] ⦃(⊤ : ArithmeticProposition)⦄ := ⟨.verum⟩

lemma or (h : ⊢ᴸᴷᴵ[C] Γ + ⦃φ, ψ⦄) : ⊢ᴸᴷᴵ[C] Γ + ⦃φ ⋎ ψ⦄ := Nonempty.map Derivation.or h

lemma and (h₁ : ⊢ᴸᴷᴵ[C] Γ + ⦃φ⦄) (h₂ : ⊢ᴸᴷᴵ[C] Γ + ⦃ψ⦄) : ⊢ᴸᴷᴵ[C] Γ + ⦃φ ⋏ ψ⦄ :=
  Nonempty.map2 Derivation.and h₁ h₂

lemma all (h : ⊢ᴸᴷᴵ[C] Γ⁺ + ⦃free ξ⦄) : ⊢ᴸᴷᴵ[C] Γ + ⦃∀¹ ξ⦄ := Nonempty.map Derivation.all h

lemma exs (t) (h : ⊢ᴸᴷᴵ[C] Γ + ⦃ξ/[t]⦄) : ⊢ᴸᴷᴵ[C] Γ + ⦃∃¹ ξ⦄ :=
  Nonempty.map (Derivation.exs (t := t)) h

lemma cast (h : ⊢ᴸᴷᴵ[C] Δ) (e : Δ = Γ := by abel) : ⊢ᴸᴷᴵ[C] Γ := e ▸ h

lemma ofLK (h : Nonempty (⊢ᴸᴷ¹ Γ)) : ⊢ᴸᴷᴵ[C] Γ := Nonempty.map Derivation.ofLK h

lemma weakeningMany (Δ) (h : ⊢ᴸᴷᴵ[C] Γ) : ⊢ᴸᴷᴵ[C] Γ + Δ :=
  Nonempty.map (Derivation.weakeningMany default) h

@[inherit_doc Derivation.ind']
lemma ind' (hξ : C ξ) (t) (h : ⊢ᴸᴷᴵ[C] Γ⁺ + ⦃∼(free ξ), (shift ξ)/[‘&0 + 1’]⦄) :
    ⊢ᴸᴷᴵ[C] Γ + ⦃∼(ξ/[‘0’]), ξ/[t]⦄ :=
  Nonempty.map (Derivation.ind' hξ t default) h

/-! ### Derived closure properties -/

/-- Cutting a multiset of derivable formulas off a derivation. -/
lemma cutAll (hΔ : ∀ δ ∈ Δ, ⊢ᴸᴷᴵ[C] ⦃δ⦄) (h : ⊢ᴸᴷᴵ[C] Γ + ∼Δ) : ⊢ᴸᴷᴵ[C] Γ := by
  induction Δ using Multiset.induction_on with
  | empty => simpa using h
  | cons δ Δ ih =>
    apply ih (fun d hd ↦ hΔ d (by simp [hd]));
    have h₁ : ⊢ᴸᴷᴵ[C] 0 + ⦃δ⦄ := (hΔ δ (by simp)).cast (by simp)
    have h₂ : ⊢ᴸᴷᴵ[C] (Γ + ∼Δ) + ⦃∼δ⦄ :=
      h.cast (by simp [Multiset.tilde_def, Multiset.add_atom_eq_cons])
    exact (h₁.cut h₂).cast (by simp)

lemma allOne (h : ⊢ᴸᴷᴵ[C] ⦃free ξ⦄) : ⊢ᴸᴷᴵ[C] ⦃∀¹ ξ⦄ :=
  Derivable.all (Γ := 0) (ξ := ξ) (h.cast (by simp [Rewriting.shifts])) |>.cast (by simp)

lemma allClosure_fixitr (h : ⊢ᴸᴷᴵ[C] ⦃φ⦄) : ∀ m : ℕ, ⊢ᴸᴷᴵ[C] ⦃∀¹* (Rew.fixitr 0 m ▹ φ)⦄
  | 0 => by simpa using h
  | m + 1 => by
    simp only [LawfulSyntacticRewriting.allClosure_fixitr]
    apply allOne
    simpa using allClosure_fixitr h m

/-- The universal closure of a derivable formula is derivable. -/
lemma univCl' (h : ⊢ᴸᴷᴵ[C] ⦃φ⦄) : ⊢ᴸᴷᴵ[C] ⦃φ.univCl'⦄ := allClosure_fixitr h _

/-! ### Soundness -/

/-- A derivable sequent contains a formula true in `ℕ` under every assignment.

- [Bus98A, Section 1.4.1] -/
theorem sound (ε : ℕ → ℕ) (h : ⊢ᴸᴷᴵ[C] Γ) : ∃ φ ∈ Γ, φ.Evalf ε :=
  Nonempty.elim h (Derivation.sound ε)

variable [RewriteClosed C]

lemma rewrite (f : ℕ → ArithmeticTerm ℕ) (h : ⊢ᴸᴷᴵ[C] Γ) :
    ⊢ᴸᴷᴵ[C] Γ.map (Rew.rewrite f ▹ ·) := Nonempty.map (Derivation.rewrite f) h

lemma map (f : ℕ → ℕ) (h : ⊢ᴸᴷᴵ[C] Γ) : ⊢ᴸᴷᴵ[C] Γ.map (Rew.rewriteMap f ▹ ·) :=
  Nonempty.map (Derivation.map · f) h

lemma shift (h : ⊢ᴸᴷᴵ[C] Γ) : ⊢ᴸᴷᴵ[C] Γ⁺ := Nonempty.map Derivation.shift h

end Derivable

end LKI

end FFL.FirstOrder.Arithmetic

end
