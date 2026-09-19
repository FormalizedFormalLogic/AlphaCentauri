module

public import AlphaCentauri.ToFoundation.Rew
public import AlphaCentauri.Hierarchy.Bounded
public import Foundation.FirstOrder.Arithmetic.Basic
public import Foundation.FirstOrder.LK.Basic

/-!
# A one-sided sequent calculus with an induction rule

`LI[C]` is Foundation's one-sided calculus `LK.Derivation` over `ℒₒᵣ` with two further rules: a
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
satisfy for `LI.Derivation.rewrite` to stay inside it. -/
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

namespace LI

/-- Derivations of `LI[C]`: Foundation's one-sided calculus for `ℒₒᵣ`, together with a leaf for
the $\Delta_0$ sequents true in `ℕ` and an induction rule for the formulas of `C`.

- [Bus98A, Section 1.4.1]
- [Bus98A, Section 1.4.2] -/
inductive Derivation (C : ArithmeticSemiformula ℕ 1 → Prop) : LK.Sequent ℒₒᵣ → Type
  | bounded (Γ : LK.Sequent ℒₒᵣ) (hΓ : ∀ φ ∈ Γ, Semiformula.Bounded φ)
      (h : ∀ ε : ℕ → ℕ, ∃ φ ∈ Γ, φ.Evalf ε) : Derivation C Γ
  | ind {Γ} (φ) (hφ : C φ) (t) :
      Derivation C (Γ⁺ + ⦃∼(free φ), (shift φ)/[‘&0 + 1’]⦄) →
      Derivation C (Γ + ⦃∼(φ/[‘0’]), φ/[t]⦄)
  | identity {k} (r : (ℒₒᵣ).Rel k) (v) : Derivation C ⦃Semiformula.rel r v, Semiformula.nrel r v⦄
  | cut {Γ Δ φ} : Derivation C (Γ + ⦃φ⦄) → Derivation C (Δ + ⦃∼φ⦄) → Derivation C (Γ + Δ)
  | contraction {Γ φ} : Derivation C (Γ + ⦃φ, φ⦄) → Derivation C (Γ + ⦃φ⦄)
  | weakening {Γ φ} : Derivation C Γ → Derivation C (Γ + ⦃φ⦄)
  | verum : Derivation C ⦃⊤⦄
  | or {Γ φ ψ} : Derivation C (Γ + ⦃φ, ψ⦄) → Derivation C (Γ + ⦃φ ⋎ ψ⦄)
  | and {Γ φ ψ} : Derivation C (Γ + ⦃φ⦄) → Derivation C (Γ + ⦃ψ⦄) → Derivation C (Γ + ⦃φ ⋏ ψ⦄)
  | all {Γ φ} : Derivation C (Γ⁺ + ⦃free φ⦄) → Derivation C (Γ + ⦃∀¹ φ⦄)
  | exs {Γ φ t} : Derivation C (Γ + ⦃φ/[t]⦄) → Derivation C (Γ + ⦃∃¹ φ⦄)

@[inherit_doc] notation:45 "⊢ᴸᴵ[" C "]! " Γ:45 => Derivation C Γ

/-- `⊢ᴸᴵ[C] Γ` says that the sequent `Γ` is derivable in `LI[C]`.

- [Bus98A, Section 1.4.1] -/
def Derivable (C : ArithmeticSemiformula ℕ 1 → Prop) (Γ : LK.Sequent ℒₒᵣ) : Prop :=
  Nonempty (⊢ᴸᴵ[C]! Γ)

@[inherit_doc] notation:45 "⊢ᴸᴵ[" C "] " Γ:45 => Derivable C Γ

namespace Derivation

variable {C : ArithmeticSemiformula ℕ 1 → Prop}
  {D D' : Set ArithmeticProposition}
  {Γ Δ : LK.Sequent ℒₒᵣ} {φ ψ χ : ArithmeticProposition}
  {ξ : ArithmeticSemiformula ℕ 1} {t : ArithmeticTerm ℕ}

abbrev cast (d : ⊢ᴸᴵ[C]! Δ) (e : Δ = Γ := by abel) : ⊢ᴸᴵ[C]! Γ := e ▸ d

instance : Structural (Derivation C) where
  weakening d := d.weakening
  contraction d := d.contraction

/-! ## Identity -/

/-- `identity` for an arbitrary formula, by recursion on its construction.

- [Bus98A, Section 1.4.1] -/
def eta : (φ : ArithmeticProposition) → ⊢ᴸᴵ[C]! ⦃φ, ∼φ⦄
  | .rel R v => identity R v
  | .nrel R v => (identity R v).cast (by simp [add_comm])
  | ⊤ => verum.weakening
  | ⊥ => (verum.weakening (φ := ⊥)).cast (by simp [add_comm])
  | φ ⋏ ψ =>
    or (Γ := ⦃φ ⋏ ψ⦄) (φ := ∼φ) (ψ := ∼ψ)
      (and (Γ := ⦃∼φ, ∼ψ⦄) (φ := φ) (ψ := ψ)
        ((eta φ).weakening (φ := ∼ψ) |>.cast)
        ((eta ψ).weakening (φ := ∼φ) |>.cast) |>.cast)
      |>.cast (by simp [add_comm])
  | φ ⋎ ψ =>
    and (Γ := ⦃φ ⋎ ψ⦄) (φ := ∼φ) (ψ := ∼ψ)
      (or (Γ := ⦃∼φ⦄) (φ := φ) (ψ := ψ) ((eta φ).weakening (φ := ψ) |>.cast) |>.cast)
      (or (Γ := ⦃∼ψ⦄) (φ := φ) (ψ := ψ) ((eta ψ).weakening (φ := φ) |>.cast) |>.cast)
      |>.cast (by simp)
  | ∀¹ φ =>
    all (Γ := ⦃∃¹ ∼φ⦄) (φ := φ)
      (exs (Γ := ⦃free φ⦄) (φ := ∼(shift φ)) (t := &0)
        ((eta (free φ)).cast (by simp)) |>.cast (by simp [add_comm]))
      |>.cast (by simp [add_comm])
  | ∃¹ φ =>
    all (Γ := ⦃∃¹ φ⦄) (φ := ∼φ)
      (exs (Γ := ⦃free (∼φ)⦄) (φ := shift φ) (t := &0)
        ((eta (free (∼φ))).cast (by simp [add_comm])) |>.cast (by simp [add_comm]))
      |>.cast (by simp)
  termination_by φ => φ.complexity

/-! ## Embedding `LK` -/

/-- Every `LK` derivation is an `LI[C]` derivation. -/
def ofLK : {Γ : LK.Sequent ℒₒᵣ} → (⊢ᴸᴷ¹ Γ) → ⊢ᴸᴵ[C]! Γ
  | _, .identity R v => identity R v
  | _, .cut d₁ d₂ => (ofLK d₁).cut (ofLK d₂)
  | _, .contraction d => (ofLK d).contraction
  | _, .weakening d => (ofLK d).weakening
  | _, .verum => verum
  | _, .or d => (ofLK d).or
  | _, .and d₁ d₂ => (ofLK d₁).and (ofLK d₂)
  | _, .all d => (ofLK d).all
  | _, .exs d => (ofLK d).exs

/-! ## Soundness -/

/-- The sequent of an `LI[C]` derivation contains a formula true in `ℕ` under every assignment.

- [Bus98A, Section 1.4.1] -/
theorem sound (ε : ℕ → ℕ) {Γ} : (⊢ᴸᴵ[C]! Γ) → ∃ φ ∈ Γ, φ.Evalf ε
  | bounded _ _ h => h ε
  | ind (Γ := Γ) φ _ t d => by
    by_contra hc
    push Not at hc
    have hΓ : ∀ ψ ∈ Γ, ¬ψ.Evalf ε := fun ψ hψ ↦ hc ψ (by simp [hψ])
    have base : Semiformula.Eval ![0] ε φ := by simpa using hc (∼(φ/[‘0’])) (by simp)
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
    have hφ : (∃ χ ∈ Γ, χ.Evalf ε) ∨ φ.Evalf ε := by simpa using sound ε dφ
    rcases hφ with (⟨χ, hχ, h⟩ | hφ)
    · exact ⟨χ, by simp [hχ], h⟩
    · have hψ : (∃ χ ∈ Γ, χ.Evalf ε) ∨ ψ.Evalf ε := by simpa using sound ε dψ
      rcases hψ with (⟨χ, hχ, h⟩ | hψ)
      · exact ⟨χ, by simp [hχ], h⟩
      · exact ⟨φ ⋏ ψ, by simp, by simp [hφ, hψ]⟩
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

/-! ## Anchored derivations -/

/-- A derivation is `Anchored D` when every one of its cut formulas belongs to `D`.

- [Bus98A, Section 1.4.2] -/
def Anchored (D : Set ArithmeticProposition) {Γ} : (⊢ᴸᴵ[C]! Γ) → Prop
  | bounded _ _ _ => True
  | ind _ _ _ d => Anchored D d
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

@[simp] lemma anchored_ind_iff {hξ} {d : ⊢ᴸᴵ[C]! Γ⁺ + ⦃∼(free ξ), (shift ξ)/[‘&0 + 1’]⦄} :
    Anchored D (ind ξ hξ t d) ↔ Anchored D d := Iff.rfl

@[simp] lemma anchored_identity {k} {r : (ℒₒᵣ).Rel k} {v} :
    Anchored D (identity (C := C) r v) := trivial

@[simp] lemma anchored_cut_iff {dp : ⊢ᴸᴵ[C]! Γ + ⦃χ⦄} {dn : ⊢ᴸᴵ[C]! Δ + ⦃∼χ⦄} :
    Anchored D (dp.cut dn) ↔ D χ ∧ Anchored D dp ∧ Anchored D dn := Iff.rfl

@[simp] lemma anchored_contraction_iff {d : ⊢ᴸᴵ[C]! Γ + ⦃φ, φ⦄} :
    Anchored D d.contraction ↔ Anchored D d := Iff.rfl

@[simp] lemma anchored_weakening_iff {d : ⊢ᴸᴵ[C]! Γ} :
    Anchored D (d.weakening (φ := φ)) ↔ Anchored D d := Iff.rfl

@[simp] lemma anchored_verum : Anchored D (verum (C := C)) := trivial

@[simp] lemma anchored_or_iff {d : ⊢ᴸᴵ[C]! Γ + ⦃φ, ψ⦄} :
    Anchored D d.or ↔ Anchored D d := Iff.rfl

@[simp] lemma anchored_and_iff {dp : ⊢ᴸᴵ[C]! Γ + ⦃φ⦄} {dq : ⊢ᴸᴵ[C]! Γ + ⦃ψ⦄} :
    Anchored D (dp.and dq) ↔ Anchored D dp ∧ Anchored D dq := Iff.rfl

@[simp] lemma anchored_all_iff {d : ⊢ᴸᴵ[C]! Γ⁺ + ⦃free ξ⦄} :
    Anchored D d.all ↔ Anchored D d := Iff.rfl

@[simp] lemma anchored_exs_iff {d : ⊢ᴸᴵ[C]! Γ + ⦃ξ/[t]⦄} :
    Anchored D d.exs ↔ Anchored D d := Iff.rfl

@[simp] lemma anchored_cast_iff {d : ⊢ᴸᴵ[C]! Δ} {e : Δ = Γ} :
    Anchored D (cast d e) ↔ Anchored D d := by rcases e; rfl


lemma Anchored.mono (h : ∀ φ, D φ → D' φ) {Γ} : {d : ⊢ᴸᴵ[C]! Γ} → Anchored D d → Anchored D' d
  | bounded _ _ _, _ => trivial
  | ind _ _ _ d, hd => .mono h (d := d) hd
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

def rewrite {Γ} (f : ℕ → ArithmeticTerm ℕ) : (⊢ᴸᴵ[C]! Γ) → ⊢ᴸᴵ[C]! Γ.map (Rew.rewrite f ▹ ·)
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
  | ind (Γ := Γ) φ hφ t d =>
    let g : ℕ → ArithmeticTerm ℕ := &0 :>ₙ fun x ↦ Rew.shift (f x)
    have h := d.rewrite g
    (ind (Γ := Γ.map (Rew.rewrite f ▹ ·)) (Rew.rewrite (Rew.bShift ∘ f) ▹ φ)
      (RewriteClosed.rewrite _ hφ) (Rew.rewrite f t)
      (cast h (by
        simp [g, free_rewrite_eq, Rewriting.shifts, shift_rewrite_eq, Function.comp_def,
          Rew.rewrite_subst_shift_eq]))).cast (by simp [rewrite_subst_eq])
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

protected def map (d : ⊢ᴸᴵ[C]! Γ) (f : ℕ → ℕ) : ⊢ᴸᴵ[C]! Γ.map (Rew.rewriteMap f ▹ ·) :=
  d.rewrite fun x ↦ &(f x)

protected def shift (d : ⊢ᴸᴵ[C]! Γ) : ⊢ᴸᴵ[C]! Γ⁺ := cast (Derivation.map d Nat.succ) (by rfl)

variable [RewriteClosed D] {Γ : LK.Sequent ℒₒᵣ}

lemma anchored_rewrite {Γ} : ∀ (d : ⊢ᴸᴵ[C]! Γ) (f), Anchored D d → Anchored D (d.rewrite f)
  | bounded _ _ _, _, _ => trivial
  | ind _ _ _ d, _, h => by simpa [rewrite] using anchored_rewrite d _ h
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

lemma anchored_map (d : ⊢ᴸᴵ[C]! Γ) (f) (h : Anchored D d) : Anchored D (Derivation.map d f) :=
  anchored_rewrite d _ h

lemma anchored_shift (d : ⊢ᴸᴵ[C]! Γ) (h : Anchored D d) : Anchored D d.shift :=
  anchored_map d Nat.succ h

end rewrite

end Derivation

namespace Derivable

variable {C : ArithmeticSemiformula ℕ 1 → Prop} {Γ Δ : LK.Sequent ℒₒᵣ}
  {φ ψ : ArithmeticProposition} {ξ : ArithmeticSemiformula ℕ 1} {t : ArithmeticTerm ℕ}

/-! ### The rules, read as closure properties of derivability -/

lemma bounded (Γ) (hΓ : ∀ φ ∈ Γ, Semiformula.Bounded φ)
    (h : ∀ ε : ℕ → ℕ, ∃ φ ∈ Γ, φ.Evalf ε) : ⊢ᴸᴵ[C] Γ := ⟨.bounded Γ hΓ h⟩

lemma ind (hξ : C ξ) (t) (h : ⊢ᴸᴵ[C] Γ⁺ + ⦃∼(free ξ), (shift ξ)/[‘&0 + 1’]⦄) :
    ⊢ᴸᴵ[C] Γ + ⦃∼(ξ/[‘0’]), ξ/[t]⦄ := Nonempty.map (Derivation.ind ξ hξ t) h

lemma eta (φ : ArithmeticProposition) : ⊢ᴸᴵ[C] ⦃φ, ∼φ⦄ := ⟨.eta φ⟩

lemma cut (h₁ : ⊢ᴸᴵ[C] Γ + ⦃φ⦄) (h₂ : ⊢ᴸᴵ[C] Δ + ⦃∼φ⦄) : ⊢ᴸᴵ[C] Γ + Δ :=
  Nonempty.map2 Derivation.cut h₁ h₂

lemma contraction (h : ⊢ᴸᴵ[C] Γ + ⦃φ, φ⦄) : ⊢ᴸᴵ[C] Γ + ⦃φ⦄ :=
  Nonempty.map Derivation.contraction h

lemma weakening (φ) (h : ⊢ᴸᴵ[C] Γ) : ⊢ᴸᴵ[C] Γ + ⦃φ⦄ :=
  Nonempty.map (Derivation.weakening (φ := φ)) h

lemma verum : ⊢ᴸᴵ[C] ⦃(⊤ : ArithmeticProposition)⦄ := ⟨.verum⟩

lemma or (h : ⊢ᴸᴵ[C] Γ + ⦃φ, ψ⦄) : ⊢ᴸᴵ[C] Γ + ⦃φ ⋎ ψ⦄ := Nonempty.map Derivation.or h

lemma and (h₁ : ⊢ᴸᴵ[C] Γ + ⦃φ⦄) (h₂ : ⊢ᴸᴵ[C] Γ + ⦃ψ⦄) : ⊢ᴸᴵ[C] Γ + ⦃φ ⋏ ψ⦄ :=
  Nonempty.map2 Derivation.and h₁ h₂

lemma all (h : ⊢ᴸᴵ[C] Γ⁺ + ⦃free ξ⦄) : ⊢ᴸᴵ[C] Γ + ⦃∀¹ ξ⦄ := Nonempty.map Derivation.all h

lemma exs (t) (h : ⊢ᴸᴵ[C] Γ + ⦃ξ/[t]⦄) : ⊢ᴸᴵ[C] Γ + ⦃∃¹ ξ⦄ :=
  Nonempty.map (Derivation.exs (t := t)) h

lemma cast (h : ⊢ᴸᴵ[C] Δ) (e : Δ = Γ := by abel) : ⊢ᴸᴵ[C] Γ := e ▸ h

lemma ofLK (h : Nonempty (⊢ᴸᴷ¹ Γ)) : ⊢ᴸᴵ[C] Γ := Nonempty.map Derivation.ofLK h

/-! ### Soundness -/

/-- A derivable sequent contains a formula true in `ℕ` under every assignment.

- [Bus98A, Section 1.4.1] -/
theorem sound (ε : ℕ → ℕ) (h : ⊢ᴸᴵ[C] Γ) : ∃ φ ∈ Γ, φ.Evalf ε :=
  Nonempty.elim h (Derivation.sound ε)

variable [RewriteClosed C]

lemma rewrite (f : ℕ → ArithmeticTerm ℕ) (h : ⊢ᴸᴵ[C] Γ) :
    ⊢ᴸᴵ[C] Γ.map (Rew.rewrite f ▹ ·) := Nonempty.map (Derivation.rewrite f) h

lemma map (f : ℕ → ℕ) (h : ⊢ᴸᴵ[C] Γ) : ⊢ᴸᴵ[C] Γ.map (Rew.rewriteMap f ▹ ·) :=
  Nonempty.map (Derivation.map · f) h

lemma shift (h : ⊢ᴸᴵ[C] Γ) : ⊢ᴸᴵ[C] Γ⁺ := Nonempty.map Derivation.shift h

end Derivable

end LI

end Arithmetic

end FirstOrder

end FFL

end
