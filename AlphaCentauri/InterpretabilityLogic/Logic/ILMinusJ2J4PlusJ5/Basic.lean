module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinus.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinus
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinusModel

/-!
# Soundness and completeness of $\mathbf{IL}^-(\mathbf{J2}, \mathbf{J4}^+, \mathbf{J5})$
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

section SoundnessVerbrugge

namespace Logic

open Verbrugge Verbrugge.Model Verbrugge.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILMinusJ2J4PlusJ5.sound_verbrugge [M.IsILMinus] [M.IsJ2] [M.IsJ4Plus] [M.IsJ5] :
    ILMinusJ2J4PlusJ5 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound_verbrugge <| by
    rintro _ ((⟨A, B, C, rfl⟩ | ⟨A, B, C, rfl⟩) | ⟨A, rfl⟩) x;
    · exact forces_axiomJ2;
    · exact forces_axiomJ4Plus;
    · exact forces_axiomJ5;

end Logic

end SoundnessVerbrugge

section CompletenessVerbrugge

namespace Logic

open Entailment Formula MaximalConsistentSet Verbrugge Verbrugge.Model

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 7.4] -/
theorem ILMinusJ2J4PlusJ5.iff_valid_finite_verbrugge :
    ILMinusJ2J4PlusJ5 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ4Plus] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ2J4PlusJ5.sound_verbrugge h;
  · intro h;
    classical
    by_contra hA;
    obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
    have : Nonempty (Veltman.IndexedSet ILMinusJ2J4PlusJ5 (ilMinusAdequateClosure {A})) :=
      ⟨⟨Γ, [], by simp, by simp⟩⟩;
    exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
      (IndexedModel.truthlemma_condJ2J4PlusJ5 (x := ⟨Γ, [], by simp, by simp⟩)
        (ilMinusAdequateClosure.subset (by simp))).mp <|
          h (IndexedModel.model IndexedModel.condJ2J4PlusJ5) ⟨Γ, [], by simp, by simp⟩

end Logic

end CompletenessVerbrugge




section IncompletenessVerbrugge

namespace Logic

open Entailment Verbrugge.Model Verbrugge.Model.World

variable {L : Logic ℕ}

/-- The $\mathbf{IL}^-_{\mathrm{set}}$-frame of [KO21, Proposition 6.1], with `0` for `x` and
`i + 1` for `yᵢ`, and `#i` true exactly at `i + 1`. -/
private abbrev counterJ2Plus : Verbrugge.Model (Fin 4) ℕ where
  Rel' w u := w = 0 ∧ u ≠ 0
  S' w u V := w = 0 ∧ (u = 1 ∧ 2 ∈ V ∧ 3 ∈ V ∨ u = 2 ∧ 3 ∈ V ∨ u = 3 ∧ 1 ∈ V ∧ 2 ∈ V ∧ 3 ∈ V)
  Val' w a := w.val = a + 1

private instance : counterJ2Plus.IsILMinus where
  trans := by
    intro _ _ _ h₁ h₂;
    exact absurd h₂.1 h₁.2;
  cwf := by
    have : IsTrans (Fin 4) counterJ2Plus.Rel := ⟨fun _ _ _ h₁ h₂ ↦ absurd h₂.1 h₁.2⟩;
    have : Std.Irrefl counterJ2Plus.Rel := ⟨fun _ h ↦ h.2 h.1⟩;
    exact Finite.converseWellFounded_of_trans_of_irrefl
  rel_of_s := by
    rintro w u V ⟨rfl, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ <;> decide
  nonempty_of_s := by
    rintro w u V ⟨-, ⟨-, h, -⟩ | ⟨-, h⟩ | ⟨-, h, -⟩⟩ <;> exact ⟨_, h⟩
  s_mono := by
    rintro w u V Z ⟨rfl, h⟩ hVZ;
    constructor;
    · rfl;
    · rcases h with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃, h₄⟩;
      · exact .inl ⟨h₁, hVZ h₂, hVZ h₃⟩;
      · exact .inr <| .inl ⟨h₁, hVZ h₂⟩;
      · exact .inr <| .inr ⟨h₁, hVZ h₂, hVZ h₃, hVZ h₄⟩;

private lemma counterJ2Plus.three_mem {w u : Fin 4} {V : Set (Fin 4)}
    (h : counterJ2Plus.S' w u V) : 3 ∈ V := by
  rcases h with ⟨-, ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, -, -, h⟩⟩ <;> exact h

private lemma counterJ2Plus.s_of_mem {u : Fin 4} {V : Set (Fin 4)} (hu : u ≠ 0) (h₁ : 1 ∈ V)
    (h₂ : 2 ∈ V) (h₃ : 3 ∈ V) : counterJ2Plus.S' 0 u V := by
  constructor;
  · rfl;
  · match u, hu with
    | 0, hu => exact absurd rfl hu
    | 1, _ => exact .inl ⟨rfl, h₂, h₃⟩
    | 2, _ => exact .inr <| .inl ⟨rfl, h₃⟩
    | 3, _ => exact .inr <| .inr ⟨rfl, h₁, h₂, h₃⟩

private instance : counterJ2Plus.IsJ4Plus where
  s_inter := by
    rintro w u V ⟨rfl, h⟩;
    constructor;
    · rfl;
    · simp only [Set.mem_ofPred_eq];
      rcases h with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃, h₄⟩;
      · exact .inl ⟨h₁, ⟨h₂, rfl, by decide⟩, ⟨h₃, rfl, by decide⟩⟩;
      · exact .inr <| .inl ⟨h₁, ⟨h₂, rfl, by decide⟩⟩;
      · exact .inr <| .inr ⟨h₁, ⟨h₂, rfl, by decide⟩, ⟨h₃, rfl, by decide⟩, ⟨h₄, rfl, by decide⟩⟩;

private instance : counterJ2Plus.IsJ2 where
  exists_rel_of_s h := ⟨3, counterJ2Plus.three_mem h, h.1, by decide⟩
  s_trans := by
    rintro w u V Z ⟨rfl, hu⟩ hZ;
    have h₃ : 3 ∈ V := counterJ2Plus.three_mem ⟨rfl, hu⟩;
    have hm {i : Fin 4} (hi : i ∈ Z 3) : i ∈ ⋃ v ∈ {v ∈ V | counterJ2Plus.Rel' 0 v}, Z v :=
      Set.mem_biUnion (x := 3) ⟨h₃, rfl, by decide⟩ hi;
    obtain ⟨-, ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h₁, h₂, h₃'⟩⟩ := hZ 3 h₃ ⟨rfl, by decide⟩;
    · exact absurd h (by decide);
    · exact absurd h (by decide);
    · apply counterJ2Plus.s_of_mem _ (hm h₁) (hm h₂) (hm h₃');
      rcases hu with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide

private instance : counterJ2Plus.IsJ5 := ⟨fun h₁ h₂ ↦ absurd h₂.1 h₁.2⟩

lemma unprovable_J2Plus [L ⪯ ILMinusJ2J4PlusJ5] : L ⊬ Axioms.J2Plus (#0) (#1) (#2) := by
  intro h;
  replace h := WeakerThan.pbl (𝓣 := ILMinusJ2J4PlusJ5) h;
  have h₁ : (0 : Fin 4) ⊩[counterJ2Plus] #0 ▷ (#1 ⋎ #2) ⋏ #1 ▷ #2 := by
    apply forces_and.mpr;
    constructor;
    · intro y _ hy;
      obtain rfl : y = 1 := Fin.ext hy;
      use {2, 3};
      constructor;
      · exact ⟨rfl, .inl ⟨rfl, by simp, by simp⟩⟩;
      · rintro z (rfl | rfl);
        · exact forces_or.mpr <| .inl rfl;
        · exact forces_or.mpr <| .inr rfl;
    · intro y _ hy;
      obtain rfl : y = 2 := Fin.ext hy;
      use {3};
      constructor;
      · exact ⟨rfl, .inr <| .inl ⟨rfl, rfl⟩⟩;
      · rintro z rfl;
        rfl;
  obtain ⟨V, hV, hV'⟩ :=
    ILMinusJ2J4PlusJ5.sound_verbrugge (M := counterJ2Plus) h 0 h₁ 1 ⟨rfl, by decide⟩ rfl;
  rcases hV with ⟨-, ⟨-, h₂, -⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩;
  · exact absurd (hV' 2 h₂) (by change ¬(_ = _); decide);
  · exact absurd h (by decide);
  · exact absurd h (by decide);

open Veltman.Model.World in
lemma valid_J2Plus {κ : Type*} [Nonempty κ] (M : Veltman.Model κ ℕ) [M.IsJ2] :
    M ⊧ Axioms.J2Plus (#0) (#1) (#2) := fun _ ↦ forces_axiomJ2Plus

/-- - [KO21, Corollary 6.2] -/
theorem ILMinusJ2J4PlusJ5.incomplete : ∃ A : Formula ℕ,
    (∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ ℕ),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ5] → M ⊧ A) ∧ ILMinusJ2J4PlusJ5 ⊬ A := by
  use Axioms.J2Plus (#0) (#1) (#2);
  constructor;
  · intro κ _ M _ _ _;
    exact valid_J2Plus M;
  · exact unprovable_J2Plus;

end Logic

end IncompletenessVerbrugge



end FFL.InterpretabilityLogic

