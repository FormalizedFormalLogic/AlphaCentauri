module

public import AlphaCentauri.ToFoundation.Rew
public import Foundation.FirstOrder.Arithmetic.Basic
public import Foundation.FirstOrder.LK.Basic

/-!
# A one-sided sequent calculus with an induction rule

`LI[C]` is Foundation's one-sided calculus `LK.Derivation` over `ℒₒᵣ` with two further rules: a
leaf `axΔ₀` for a sequent of $\Delta_0$ formulas true in `ℕ` under every assignment, and an
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

instance {n s : ℕ} {b : Polarity} :
    RewriteClosed (n := n) (StrictHierarchy (L := ℒₒᵣ) (ξ := ℕ) b s) where
  rewrite f := StrictHierarchy.rew (Rew.rewrite f)

instance {n s : ℕ} {b : Polarity} :
    RewriteClosed (n := n) (Hierarchy (L := ℒₒᵣ) (ξ := ℕ) b s) where
  rewrite f := Hierarchy.rew (Rew.rewrite f)

instance {n : ℕ} {C D : ArithmeticSemiformula ℕ n → Prop} [RewriteClosed C] [RewriteClosed D] :
    RewriteClosed fun φ ↦ C φ ∨ D φ where
  rewrite f := fun h ↦ h.imp (RewriteClosed.rewrite f) (RewriteClosed.rewrite f)

namespace LI

/-- Derivations of `LI[C]`: Foundation's one-sided calculus for `ℒₒᵣ`, together with a leaf for
the $\Delta_0$ sequents true in `ℕ` and an induction rule for the formulas of `C`.

- [Bus98A, Section 1.4.1]
- [Bus98A, Section 1.4.2] -/
inductive Derivation (C : ArithmeticSemiformula ℕ 1 → Prop) : LK.Sequent ℒₒᵣ → Type
  | axΔ₀ (Γ : LK.Sequent ℒₒᵣ) (hΓ : ∀ φ ∈ Γ, StrictHierarchy 𝚺 0 φ)
      (h : ∀ ε : ℕ → ℕ, ∃ φ ∈ Γ, Semiformula.Evalf (M := ℕ) ε φ) : Derivation C Γ
  | ind {Γ : LK.Sequent ℒₒᵣ} (φ : ArithmeticSemiformula ℕ 1) (hφ : C φ) (t : ArithmeticTerm ℕ) :
      Derivation C (Γ⁺ + ⦃∼(free φ), (shift φ)/[‘&0 + 1’]⦄) →
      Derivation C (Γ + ⦃∼(φ/[‘0’]), φ/[t]⦄)
  | identity {k : ℕ} (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticTerm ℕ) :
      Derivation C ⦃Semiformula.rel r v, Semiformula.nrel r v⦄
  | cut {Γ Δ : LK.Sequent ℒₒᵣ} {φ : ArithmeticProposition} :
      Derivation C (Γ + ⦃φ⦄) → Derivation C (Δ + ⦃∼φ⦄) → Derivation C (Γ + Δ)
  | contraction {Γ : LK.Sequent ℒₒᵣ} {φ : ArithmeticProposition} :
      Derivation C (Γ + ⦃φ, φ⦄) → Derivation C (Γ + ⦃φ⦄)
  | weakening {Γ : LK.Sequent ℒₒᵣ} {φ : ArithmeticProposition} :
      Derivation C Γ → Derivation C (Γ + ⦃φ⦄)
  | verum : Derivation C ⦃⊤⦄
  | or {Γ : LK.Sequent ℒₒᵣ} {φ ψ : ArithmeticProposition} :
      Derivation C (Γ + ⦃φ, ψ⦄) → Derivation C (Γ + ⦃φ ⋎ ψ⦄)
  | and {Γ : LK.Sequent ℒₒᵣ} {φ ψ : ArithmeticProposition} :
      Derivation C (Γ + ⦃φ⦄) → Derivation C (Γ + ⦃ψ⦄) → Derivation C (Γ + ⦃φ ⋏ ψ⦄)
  | all {Γ : LK.Sequent ℒₒᵣ} {φ : ArithmeticSemiproposition 1} :
      Derivation C (Γ⁺ + ⦃free φ⦄) → Derivation C (Γ + ⦃∀¹ φ⦄)
  | exs {Γ : LK.Sequent ℒₒᵣ} {φ : ArithmeticSemiproposition 1} {t : ArithmeticTerm ℕ} :
      Derivation C (Γ + ⦃φ/[t]⦄) → Derivation C (Γ + ⦃∃¹ φ⦄)

notation:45 "⊢ᴸᴵ[" C "] " Γ:45 => Derivation C Γ

namespace Derivation

variable {C : ArithmeticSemiformula ℕ 1 → Prop}

abbrev cast {Γ Δ : LK.Sequent ℒₒᵣ} (d : ⊢ᴸᴵ[C] Δ) (e : Δ = Γ := by abel) : ⊢ᴸᴵ[C] Γ := e ▸ d

instance : Structural (Derivation C) where
  weakening d := d.weakening
  contraction d := d.contraction

/-- The sequent of an `LI[C]` derivation contains a formula true in `ℕ` under every assignment.

- [Bus98A, Section 1.4.1] -/
theorem sound (ε : ℕ → ℕ) {Γ : LK.Sequent ℒₒᵣ} :
    ⊢ᴸᴵ[C] Γ → ∃ φ ∈ Γ, Semiformula.Evalf (M := ℕ) ε φ
  | axΔ₀ _ _ h => h ε
  | ind (Γ := Γ) φ _ t d => by
    by_contra hc
    push Not at hc
    have hΓ : ∀ ψ ∈ Γ, ¬Semiformula.Evalf (M := ℕ) ε ψ := fun ψ hψ ↦ hc ψ (by simp [hψ])
    have base : Semiformula.Eval ![0] ε φ := by simpa using hc (∼(φ/[‘0’])) (by simp)
    have top : ¬Semiformula.Eval ![Semiterm.val ![] ε t] ε φ := by
      simpa using hc (φ/[t]) (by simp)
    have step : ∀ a : ℕ, Semiformula.Eval ![a] ε φ → Semiformula.Eval ![a + 1] ε φ := by
      intro a ha
      have h : (∃ ψ ∈ Γ, Semiformula.Evalf (M := ℕ) ε ψ) ∨
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
    by_cases h : Semiformula.Evalf (M := ℕ) ε (Semiformula.rel r v)
    · exact ⟨Semiformula.rel r v, by simp, h⟩
    · exact ⟨Semiformula.nrel r v, by simp, by simpa using h⟩
  | verum => ⟨⊤, by simp, by simp⟩
  | cut (Γ := Γ) (Δ := Δ) (φ := φ) d dn => by
    have h : (∃ ψ ∈ Γ, Semiformula.Evalf (M := ℕ) ε ψ) ∨ Semiformula.Evalf (M := ℕ) ε φ := by
      simpa using sound ε d
    have hn : (∃ ψ ∈ Δ, Semiformula.Evalf (M := ℕ) ε ψ) ∨ ¬Semiformula.Evalf (M := ℕ) ε φ := by
      simpa using sound ε dn
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
    have : (∃ χ ∈ Γ, Semiformula.Evalf (M := ℕ) ε χ) ∨
        Semiformula.Evalf (M := ℕ) ε φ ∨ Semiformula.Evalf (M := ℕ) ε ψ := by
      simpa [or_and_right, exists_or] using sound ε d
    rcases this with (⟨χ, hχ, h⟩ | h | h)
    · exact ⟨χ, by simp [hχ], h⟩
    · exact ⟨φ ⋎ ψ, by simp, by simp [h]⟩
    · exact ⟨φ ⋎ ψ, by simp, by simp [h]⟩
  | and (Γ := Γ) (φ := φ) (ψ := ψ) dφ dψ => by
    have hφ : (∃ χ ∈ Γ, Semiformula.Evalf (M := ℕ) ε χ) ∨ Semiformula.Evalf (M := ℕ) ε φ := by
      simpa using sound ε dφ
    rcases hφ with (⟨χ, hχ, h⟩ | hφ)
    · exact ⟨χ, by simp [hχ], h⟩
    · have hψ : (∃ χ ∈ Γ, Semiformula.Evalf (M := ℕ) ε χ) ∨ Semiformula.Evalf (M := ℕ) ε ψ := by
        simpa using sound ε dψ
      rcases hψ with (⟨χ, hχ, h⟩ | hψ)
      · exact ⟨χ, by simp [hχ], h⟩
      · exact ⟨φ ⋏ ψ, by simp, by simp [hφ, hψ]⟩
  | all (Γ := Γ) (φ := φ) d => by
    have : (∃ ψ ∈ Γ, Semiformula.Evalf (M := ℕ) ε ψ) ∨ ∀ a : ℕ, Semiformula.Eval ![a] ε φ := by
      simpa [Rewriting.shifts, forall_or_left] using fun a : ℕ ↦ sound (a :>ₙ ε) d
    rcases this with (⟨ψ, hψ, h⟩ | h)
    · exact ⟨ψ, by simp [hψ], h⟩
    · exact ⟨∀¹ φ, by simp, h⟩
  | exs (Γ := Γ) (φ := φ) (t := t) d => by
    have : (∃ ψ ∈ Γ, Semiformula.Evalf (M := ℕ) ε ψ) ∨
        Semiformula.Eval ![Semiterm.val ![] ε t] ε φ := by simpa using sound ε d
    rcases this with (⟨ψ, hψ, h⟩ | h)
    · exact ⟨ψ, by simp [hψ], h⟩
    · exact ⟨∃¹ φ, by simp, Semiterm.val ![] ε t, h⟩

section anchored

variable (D : ArithmeticProposition → Prop)

/-- A derivation is `Anchored D` when every one of its cut formulas belongs to `D`.

- [Bus98A, Section 1.4.2] -/
def Anchored : {Γ : LK.Sequent ℒₒᵣ} → (⊢ᴸᴵ[C] Γ) → Prop
  | _, axΔ₀ _ _ _ => True
  | _, ind _ _ _ d => Anchored d
  | _, identity _ _ => True
  | _, cut (φ := χ) dp dn => D χ ∧ Anchored dp ∧ Anchored dn
  | _, contraction d => Anchored d
  | _, weakening d => Anchored d
  | _, verum => True
  | _, or d => Anchored d
  | _, and dp dq => Anchored dp ∧ Anchored dq
  | _, all d => Anchored d
  | _, exs d => Anchored d

variable {D} {Γ Δ : LK.Sequent ℒₒᵣ} {φ ψ χ : ArithmeticProposition}

@[simp] lemma anchored_axΔ₀ {hΓ h} : Anchored D (axΔ₀ (C := C) Γ hΓ h) := trivial

@[simp] lemma anchored_ind_iff {ξ : ArithmeticSemiformula ℕ 1} {hξ t}
    {d : ⊢ᴸᴵ[C] Γ⁺ + ⦃∼(free ξ), (shift ξ)/[‘&0 + 1’]⦄} :
    Anchored D (ind ξ hξ t d) ↔ Anchored D d := Iff.rfl

@[simp] lemma anchored_identity {k} {r : (ℒₒᵣ).Rel k} {v} :
    Anchored D (identity (C := C) r v) := trivial

@[simp] lemma anchored_cut_iff {dp : ⊢ᴸᴵ[C] Γ + ⦃χ⦄} {dn : ⊢ᴸᴵ[C] Δ + ⦃∼χ⦄} :
    Anchored D (dp.cut dn) ↔ D χ ∧ Anchored D dp ∧ Anchored D dn := Iff.rfl

@[simp] lemma anchored_contraction_iff {d : ⊢ᴸᴵ[C] Γ + ⦃φ, φ⦄} :
    Anchored D d.contraction ↔ Anchored D d := Iff.rfl

@[simp] lemma anchored_weakening_iff {d : ⊢ᴸᴵ[C] Γ} :
    Anchored D (d.weakening (φ := φ)) ↔ Anchored D d := Iff.rfl

@[simp] lemma anchored_verum : Anchored D (verum (C := C)) := trivial

@[simp] lemma anchored_or_iff {d : ⊢ᴸᴵ[C] Γ + ⦃φ, ψ⦄} :
    Anchored D d.or ↔ Anchored D d := Iff.rfl

@[simp] lemma anchored_and_iff {dp : ⊢ᴸᴵ[C] Γ + ⦃φ⦄} {dq : ⊢ᴸᴵ[C] Γ + ⦃ψ⦄} :
    Anchored D (dp.and dq) ↔ Anchored D dp ∧ Anchored D dq := Iff.rfl

@[simp] lemma anchored_all_iff {ξ : ArithmeticSemiproposition 1} {d : ⊢ᴸᴵ[C] Γ⁺ + ⦃free ξ⦄} :
    Anchored D d.all ↔ Anchored D d := Iff.rfl

@[simp] lemma anchored_exs_iff {ξ : ArithmeticSemiproposition 1} {t} {d : ⊢ᴸᴵ[C] Γ + ⦃ξ/[t]⦄} :
    Anchored D d.exs ↔ Anchored D d := Iff.rfl

@[simp] lemma anchored_cast_iff {d : ⊢ᴸᴵ[C] Δ} {e : Δ = Γ} :
    Anchored D (cast d e) ↔ Anchored D d := by rcases e; rfl

lemma Anchored.mono {D' : ArithmeticProposition → Prop} (h : ∀ φ, D φ → D' φ) :
    ∀ {Γ : LK.Sequent ℒₒᵣ} {d : ⊢ᴸᴵ[C] Γ}, Anchored D d → Anchored D' d
  | _, axΔ₀ _ _ _, _ => trivial
  | _, ind _ _ _ d, hd => Anchored.mono h (d := d) hd
  | _, identity _ _, _ => trivial
  | _, cut _ _, hd => ⟨h _ hd.1, Anchored.mono h hd.2.1, Anchored.mono h hd.2.2⟩
  | _, contraction d, hd => Anchored.mono h (d := d) hd
  | _, weakening d, hd => Anchored.mono h (d := d) hd
  | _, verum, _ => trivial
  | _, or d, hd => Anchored.mono h (d := d) hd
  | _, and _ _, hd => ⟨Anchored.mono h hd.1, Anchored.mono h hd.2⟩
  | _, all d, hd => Anchored.mono h (d := d) hd
  | _, exs d, hd => Anchored.mono h (d := d) hd

end anchored

section rewrite

variable [RewriteClosed C]

def rewrite {Γ : LK.Sequent ℒₒᵣ} (f : ℕ → ArithmeticTerm ℕ) :
    (⊢ᴸᴵ[C] Γ) → ⊢ᴸᴵ[C] Γ.map (Rew.rewrite f ▹ ·)
  | axΔ₀ Γ hΓ h =>
    axΔ₀ _
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
    have h : ⊢ᴸᴵ[C] (Γ⁺ + ⦃∼(free φ), (shift φ)/[‘&0 + 1’]⦄).map (Rew.rewrite g ▹ ·) :=
      d.rewrite g
    (ind (Γ := Γ.map (Rew.rewrite f ▹ ·)) (Rew.rewrite (Rew.bShift ∘ f) ▹ φ)
      (RewriteClosed.rewrite _ hφ) (Rew.rewrite f t)
      (cast h (by
        simp [g, free_rewrite_eq, Rewriting.shifts, shift_rewrite_eq, Function.comp_def,
          Rew.rewrite_subst_shift_eq]))).cast (by simp [rewrite_subst_eq])
  | identity R v => identity R (Rew.rewrite f ∘ v)
  | cut (Γ := Γ) (Δ := Δ) (φ := φ) d₁ d₂ =>
    (cut (Γ := Γ.map (Rew.rewrite f ▹ ·)) (Δ := Δ.map (Rew.rewrite f ▹ ·))
      (φ := Rew.rewrite f ▹ φ)
      ((d₁.rewrite f).cast (by simp)) ((d₂.rewrite f).cast (by simp))).cast (by simp)
  | contraction (Γ := Γ) (φ := φ) d =>
    (contraction (Γ := Γ.map (Rew.rewrite f ▹ ·)) (φ := Rew.rewrite f ▹ φ)
      ((d.rewrite f).cast (by simp))).cast (by simp)
  | weakening (Γ := Γ) (φ := φ) d =>
    (weakening (φ := Rew.rewrite f ▹ φ) (d.rewrite f)).cast (by simp)
  | verum => cast verum (by simp)
  | or (Γ := Γ) (φ := φ) (ψ := ψ) d =>
    (or (Γ := Γ.map (Rew.rewrite f ▹ ·)) (φ := Rew.rewrite f ▹ φ) (ψ := Rew.rewrite f ▹ ψ)
      ((d.rewrite f).cast (by simp))).cast (by simp)
  | and (Γ := Γ) (φ := φ) (ψ := ψ) d₁ d₂ =>
    (and (Γ := Γ.map (Rew.rewrite f ▹ ·)) (φ := Rew.rewrite f ▹ φ) (ψ := Rew.rewrite f ▹ ψ)
      ((d₁.rewrite f).cast (by simp)) ((d₂.rewrite f).cast (by simp))).cast (by simp)
  | all (Γ := Γ) (φ := φ) d =>
    let g : ℕ → ArithmeticTerm ℕ := &0 :>ₙ fun x ↦ Rew.shift (f x)
    have h : ⊢ᴸᴵ[C] (Γ⁺ + ⦃free φ⦄).map (Rew.rewrite g ▹ ·) := d.rewrite g
    (all (Γ := Γ.map (Rew.rewrite f ▹ ·)) (φ := Rew.rewrite (Rew.bShift ∘ f) ▹ φ)
      (cast h (by
        simp [g, free_rewrite_eq, Rewriting.shifts, shift_rewrite_eq,
          Function.comp_def]))).cast (by simp [Rew.q_rewrite])
  | exs (Γ := Γ) (φ := φ) (t := t) d =>
    have h : ⊢ᴸᴵ[C] (Γ + ⦃φ/[t]⦄).map (Rew.rewrite f ▹ ·) := d.rewrite f
    (exs (Γ := Γ.map (Rew.rewrite f ▹ ·)) (φ := Rew.rewrite (Rew.bShift ∘ f) ▹ φ)
      (t := Rew.rewrite f t) (cast h (by simp [rewrite_subst_eq]))).cast (by simp [Rew.q_rewrite])

protected def map {Γ : LK.Sequent ℒₒᵣ} (d : ⊢ᴸᴵ[C] Γ) (f : ℕ → ℕ) :
    ⊢ᴸᴵ[C] Γ.map (Rew.rewriteMap f ▹ ·) := d.rewrite fun x ↦ &(f x)

protected def shift {Γ : LK.Sequent ℒₒᵣ} (d : ⊢ᴸᴵ[C] Γ) : ⊢ᴸᴵ[C] Γ⁺ :=
  cast (Derivation.map d Nat.succ) (by rfl)

variable {D : ArithmeticProposition → Prop} [RewriteClosed D]

lemma anchored_rewrite :
    ∀ {Γ : LK.Sequent ℒₒᵣ} (d : ⊢ᴸᴵ[C] Γ) (f : ℕ → ArithmeticTerm ℕ),
      Anchored D d → Anchored D (d.rewrite f)
  | _, axΔ₀ _ _ _, _, _ => trivial
  | _, ind _ _ _ d, _, h => by simpa [rewrite] using anchored_rewrite d _ h
  | _, identity _ _, _, _ => trivial
  | _, cut dp dn, f, h => by
    simp only [rewrite, anchored_cast_iff, anchored_cut_iff]
    exact ⟨RewriteClosed.rewrite f h.1, anchored_rewrite dp f h.2.1, anchored_rewrite dn f h.2.2⟩
  | _, contraction d, f, h => by simpa [rewrite] using anchored_rewrite d f h
  | _, weakening d, f, h => by simpa [rewrite] using anchored_rewrite d f h
  | _, verum, _, _ => trivial
  | _, or d, f, h => by simpa [rewrite] using anchored_rewrite d f h
  | _, and dp dq, f, h => by
    simpa [rewrite] using ⟨anchored_rewrite dp f h.1, anchored_rewrite dq f h.2⟩
  | _, all d, _, h => by simpa [rewrite] using anchored_rewrite d _ h
  | _, exs d, f, h => by simpa [rewrite] using anchored_rewrite d f h

lemma anchored_map {Γ : LK.Sequent ℒₒᵣ} (d : ⊢ᴸᴵ[C] Γ) (f : ℕ → ℕ) (h : Anchored D d) :
    Anchored D (Derivation.map d f) := anchored_rewrite d _ h

lemma anchored_shift {Γ : LK.Sequent ℒₒᵣ} (d : ⊢ᴸᴵ[C] Γ) (h : Anchored D d) :
    Anchored D d.shift := anchored_map d Nat.succ h

end rewrite

end Derivation

end LI

end Arithmetic

end FirstOrder

end FFL

end
