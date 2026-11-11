module

public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinus

/-!
# Countermodels for the incompleteness of $\mathbf{IL}^-$ extensions for Veltman models

Generalised Veltman models satisfying all the frame conditions of $\mathbf{IL}^-$ extensions
by $\mathbf{J1}$, $\mathbf{J2}$, $\mathbf{J4}$, $\mathbf{J4}^+$, $\mathbf{J5}$ that are
validated by a given extension, in which an instance of $\mathbf{J4}^+$ or $\mathbf{J2}^+$ fails.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

namespace Verbrugge

open Model Model.World

/-- The $\mathbf{IL}^-_{\mathrm{set}}$-frame of [KO21, Proposition 6.3], with `0` for `x` and
`i + 1` for `yᵢ`. -/
abbrev counterJ4Plus : Verbrugge.Model (Fin 4) ℕ where
  Rel' w u := w = 0 ∧ (u = 1 ∨ u = 2)
  S' w u V := w = 0 ∧ (u = 1 ∧ (1 ∈ V ∨ 2 ∈ V ∧ 3 ∈ V) ∨ u = 2 ∧ 2 ∈ V)
  Val' w a := a = 0 ∧ w = 1 ∨ a = 1 ∧ (w = 2 ∨ w = 3) ∨ a = 2 ∧ w = 2

instance : counterJ4Plus.IsILMinus where
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

instance : counterJ4Plus.IsJ1 where
  s_refl := by
    rintro w u ⟨rfl, rfl | rfl⟩;
    · exact ⟨rfl, .inl ⟨rfl, .inl rfl⟩⟩;
    · exact ⟨rfl, .inr ⟨rfl, rfl⟩⟩;

instance : counterJ4Plus.IsJ4 where
  exists_rel_of_s := by
    rintro w u V ⟨rfl, ⟨-, h | ⟨h, -⟩⟩ | ⟨-, h⟩⟩;
    · use 1
      exact ⟨h, rfl, .inl rfl⟩;
    · use 2
      exact ⟨h, rfl, .inr rfl⟩;
    · use 2
      exact ⟨h, rfl, .inr rfl⟩;

instance : counterJ4Plus.IsJ5 where
  s_of_rel := by
    rintro _ _ _ ⟨-, h₁⟩ ⟨h₂, -⟩;
    subst h₂;
    rcases h₁ with h | h <;> exact absurd h (by decide);

lemma counterJ4Plus.not_models_J4Plus : ¬counterJ4Plus ⊧ Axioms.J4Plus (#1) (#2) (#0) := by
  intro h
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
    h 0 h₁ h₂ 1 ⟨rfl, .inl rfl⟩
      (by change _ ∨ _ ∨ _; decide);
  rcases hV with ⟨-, ⟨-, h₃ | ⟨-, h₃⟩⟩ | ⟨h, -⟩⟩;
  · exact absurd (hV' 1 h₃) (by change ¬(_ ∨ _ ∨ _); decide);
  · exact absurd (hV' 3 h₃) (by change ¬(_ ∨ _ ∨ _); decide);
  · exact absurd h (by decide);


/-- The $\mathbf{IL}^-_{\mathrm{set}}$-frame of [KO21, Proposition 6.1], with `0` for `x` and
`i + 1` for `yᵢ`, and `#i` true exactly at `i + 1`. -/
abbrev counterJ2Plus : Verbrugge.Model (Fin 4) ℕ where
  Rel' w u := w = 0 ∧ u ≠ 0
  S' w u V := w = 0 ∧ (u = 1 ∧ 2 ∈ V ∧ 3 ∈ V ∨ u = 2 ∧ 3 ∈ V ∨ u = 3 ∧ 1 ∈ V ∧ 2 ∈ V ∧ 3 ∈ V)
  Val' w a := w.val = a + 1

instance : counterJ2Plus.IsILMinus where
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

instance : counterJ2Plus.IsJ4Plus where
  s_inter := by
    rintro w u V ⟨rfl, h⟩;
    constructor;
    · rfl;
    · simp only [Set.mem_ofPred_eq];
      rcases h with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃, h₄⟩;
      · exact .inl ⟨h₁, ⟨h₂, rfl, by decide⟩, ⟨h₃, rfl, by decide⟩⟩;
      · exact .inr <| .inl ⟨h₁, ⟨h₂, rfl, by decide⟩⟩;
      · exact .inr <| .inr ⟨h₁, ⟨h₂, rfl, by decide⟩, ⟨h₃, rfl, by decide⟩, ⟨h₄, rfl, by decide⟩⟩;

instance : counterJ2Plus.IsJ2 where
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

instance : counterJ2Plus.IsJ5 := ⟨fun h₁ h₂ ↦ absurd h₂.1 h₁.2⟩

lemma counterJ2Plus.not_models_J2Plus : ¬counterJ2Plus ⊧ Axioms.J2Plus (#0) (#1) (#2) := by
  intro h
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
    h 0 h₁ 1 ⟨rfl, by decide⟩ rfl;
  rcases hV with ⟨-, ⟨-, h₂, -⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩;
  · exact absurd (hV' 2 h₂) (by change ¬(_ = _); decide);
  · exact absurd h (by decide);
  · exact absurd h (by decide);


end Verbrugge

end FFL.InterpretabilityLogic

end
