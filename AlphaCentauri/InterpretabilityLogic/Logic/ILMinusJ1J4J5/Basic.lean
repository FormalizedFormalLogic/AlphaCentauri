module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinus
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinusModel
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinusJ1J4PlusJ5.Basic

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4}, \mathbf{J5})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Entailment Formula

variable {α : Type*}

/-- $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4}, \mathbf{J5})$.

- [KO21, §6]
-/
abbrev ILMinusJ1J4J5 : Logic α :=
  ofAxiomsMinus ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J4 A B | (A) (B)} ∪ {Axioms.J5 A | A})

end Logic

namespace Verbrugge.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILMinusJ1J4J5 : Prop extends M.IsILMinus, M.IsJ1, M.IsJ4, M.IsJ5

instance (priority := low) [M.IsILMinus] [M.IsJ1] [M.IsJ4] [M.IsJ5] : M.IsILMinusJ1J4J5 := {}

end Verbrugge.Model

namespace Logic

/-! ## Completeness for Verbrugge models -/


open Entailment Formula MaximalConsistentSet Verbrugge Verbrugge.Model Verbrugge.Model.World

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ1J4J5.semantics_TFAE : [
    ILMinusJ1J4J5 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ1J4J5] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ1J4J5] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h _ _ M _;
    apply ofAxiomsMinus.sound_verbrugge _ h;
    rintro _ ((⟨A, B, rfl⟩ | ⟨A, B, rfl⟩) | ⟨A, rfl⟩) x;
    · exact forces_axiomJ1;
    · exact forces_axiomJ4;
    · exact forces_axiomJ5;
  tfae_have 2 → 3 := by
    intro h _ _ _ M _;
    exact h M;
  tfae_have 3 → 1 := by
    intro h;
    classical
    by_contra hA;
    obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
    have : Nonempty (LabelledSet ILMinusJ1J4J5 (ilMinusAdequateClosure {A})) := ⟨⟨Γ, ⊥, .bot⟩⟩;
    exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
      (LabelledSet.truthlemma_condJ4J5 (x := ⟨Γ, ⊥, .bot⟩)
        (ilMinusAdequateClosure.subset (by simp))).mp <|
          h (LabelledSet.model LabelledSet.condJ4J5) ⟨Γ, ⊥, .bot⟩;
  tfae_finish;

theorem ILMinusJ1J4J5.iff_valid_verbrugge :
    ILMinusJ1J4J5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ1J4J5] → M ⊧ A :=
  ILMinusJ1J4J5.semantics_TFAE.out 1 2

theorem ILMinusJ1J4J5.sound_verbrugge {κ : Type} [Nonempty κ] {M : Verbrugge.Model κ α}
    [M.IsILMinusJ1J4J5] (h : ILMinusJ1J4J5 ⊢ A) : M ⊧ A :=
  ILMinusJ1J4J5.iff_valid_verbrugge.mp h M

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ1J4J5.iff_valid_finite_verbrugge :
    ILMinusJ1J4J5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinusJ1J4J5] → M ⊧ A :=
  ILMinusJ1J4J5.semantics_TFAE.out 1 3


/-! ## Incompleteness for Verbrugge models -/


open Entailment Verbrugge.Model Verbrugge.Model.World

variable {L : Logic ℕ}

/-- The $\mathbf{IL}^-_{\mathrm{set}}$-frame of [KO21, Proposition 6.3], with `0` for `x` and
`i + 1` for `yᵢ`. -/
private abbrev counterJ4Plus : Verbrugge.Model (Fin 4) ℕ where
  Rel' w u := w = 0 ∧ (u = 1 ∨ u = 2)
  S' w u V := w = 0 ∧ (u = 1 ∧ (1 ∈ V ∨ 2 ∈ V ∧ 3 ∈ V) ∨ u = 2 ∧ 2 ∈ V)
  Val' w a := a = 0 ∧ w = 1 ∨ a = 1 ∧ (w = 2 ∨ w = 3) ∨ a = 2 ∧ w = 2

private instance : counterJ4Plus.IsILMinus where
  trans := by
    rintro _ _ _ ⟨-, h₁⟩ ⟨h₂, -⟩;
    subst h₂;
    rcases h₁ with h | h <;> exact absurd h (by decide);
  cwf := by
    have : IsTrans (Fin 4) counterJ4Plus.Rel := by
      constructor;
      rintro _ _ _ ⟨-, h₁⟩ ⟨rfl, -⟩;
      rcases h₁ with h | h <;> exact absurd h (by decide);
    have : Std.Irrefl counterJ4Plus.Rel := by
      constructor;
      rintro _ ⟨rfl, h | h⟩ <;> exact absurd h (by decide);
    exact Finite.converseWellFounded_of_trans_of_irrefl
  rel_of_s := by
    rintro w u V ⟨rfl, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩;
    · exact ⟨rfl, .inl rfl⟩;
    · exact ⟨rfl, .inr rfl⟩;
  nonempty_of_s := by
    rintro w u V ⟨-, ⟨-, h | ⟨h, -⟩⟩ | ⟨-, h⟩⟩ <;> exact ⟨_, h⟩
  s_mono := by
    rintro w u V Z ⟨rfl, h⟩ hVZ;
    constructor;
    · rfl;
    · rcases h with ⟨h₁, h₂ | ⟨h₂, h₃⟩⟩ | ⟨h₁, h₂⟩;
      · exact .inl ⟨h₁, .inl (hVZ h₂)⟩;
      · exact .inl ⟨h₁, .inr ⟨hVZ h₂, hVZ h₃⟩⟩;
      · exact .inr ⟨h₁, hVZ h₂⟩;

private instance : counterJ4Plus.IsJ1 where
  s_refl := by
    rintro w u ⟨rfl, rfl | rfl⟩;
    · exact ⟨rfl, .inl ⟨rfl, .inl rfl⟩⟩;
    · exact ⟨rfl, .inr ⟨rfl, rfl⟩⟩;

private instance : counterJ4Plus.IsJ4 where
  exists_rel_of_s := by
    rintro w u V ⟨rfl, ⟨-, h | ⟨h, -⟩⟩ | ⟨-, h⟩⟩;
    · use 1
      exact ⟨h, rfl, .inl rfl⟩;
    · use 2
      exact ⟨h, rfl, .inr rfl⟩;
    · use 2
      exact ⟨h, rfl, .inr rfl⟩;

private instance : counterJ4Plus.IsJ5 where
  s_of_rel := by
    rintro _ _ _ ⟨-, h₁⟩ ⟨h₂, -⟩;
    subst h₂;
    rcases h₁ with h | h <;> exact absurd h (by decide);

lemma unprovable_J4Plus [L ⪯ ILMinusJ1J4J5] : L ⊬ Axioms.J4Plus (#1) (#2) (#0) := by
  intro h;
  replace h := WeakerThan.pbl (𝓣 := ILMinusJ1J4J5) h;
  have h₁ : (0 : Fin 4) ⊩[counterJ4Plus] □(#1 🡒 #2) := by
    rintro y ⟨-, rfl | rfl⟩ hy;
    · exact absurd hy (by change ¬(_ ∨ _ ∨ _); decide);
    · change _ ∨ _ ∨ _; decide;
  have h₂ : (0 : Fin 4) ⊩[counterJ4Plus] #0 ▷ #1 := by
    intro y _ hy;
    obtain rfl : y = 1 := by
      change _ ∨ _ ∨ _ at hy;
      simpa using hy;
    use {2, 3};
    constructor;
    · exact ⟨rfl, .inl ⟨rfl, .inr ⟨by simp, by simp⟩⟩⟩;
    · rintro z (rfl | rfl) <;> (change _ ∨ _ ∨ _; decide);
  obtain ⟨V, hV, hV'⟩ :=
    ILMinusJ1J4J5.sound_verbrugge (M := counterJ4Plus) h 0 h₁ h₂ 1 ⟨rfl, .inl rfl⟩
      (by change _ ∨ _ ∨ _; decide);
  rcases hV with ⟨-, ⟨-, h₃ | ⟨-, h₃⟩⟩ | ⟨h, -⟩⟩;
  · exact absurd (hV' 1 h₃) (by change ¬(_ ∨ _ ∨ _); decide);
  · exact absurd (hV' 3 h₃) (by change ¬(_ ∨ _ ∨ _); decide);
  · exact absurd h (by decide);

open Veltman.Model.World in
lemma valid_J4Plus {κ : Type*} [Nonempty κ] (M : Veltman.Model κ ℕ) [M.IsJ4] :
    M ⊧ Axioms.J4Plus (#1) (#2) (#0) := fun _ ↦ forces_axiomJ4Plus

/-- - [KO21, Corollary 6.4] -/
theorem ILMinusJ1J4J5.incomplete : ∃ A : Formula ℕ,
    (∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ ℕ),
      [M.IsILMinusJ1J4PlusJ5] → M ⊧ A) ∧ ILMinusJ1J4J5 ⊬ A := by
  use Axioms.J4Plus (#1) (#2) (#0);
  constructor;
  · intro κ _ M _;
    exact valid_J4Plus M;
  · exact unprovable_J4Plus;

end Logic


end FFL.InterpretabilityLogic

