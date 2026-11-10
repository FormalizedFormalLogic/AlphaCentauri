module

public import AlphaCentauri.InterpretabilityLogic.Veltman.ILMinus
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.Basic

/-!
# Generalised Veltman semantics of the sublogics of $\mathbf{IL}$

$\mathbf{IL}^-_{\mathrm{set}}$-frames, the frame conditions of $\mathbf{J1}$, $\mathbf{J2}$,
$\mathbf{J4}$, $\mathbf{J4}^+$ and $\mathbf{J5}$ on them, the soundness of the extensions of
$\mathbf{IL}^-$, and the incompleteness of eight of them with respect to $\mathbf{IL}^-$-frames.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Verbrugge.Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α}

/-- `≺` is transitive and conversely well-founded, and `u ≺[w] V` implies `w ≺ u`, that `V` is
nonempty, and `u ≺[w] Z` for every `Z ⊇ V`.

- [KO21, Definition 2.6]
-/
class IsILMinus (M : Model κ α) extends IsTrans _ M.Rel, IsConverseWellFounded _ M.Rel where
  rel_of_s {w u : M.World} {V : Set M.World} : u ≺[w] V → w ≺ u
  nonempty_of_s {w u : M.World} {V : Set M.World} : u ≺[w] V → V.Nonempty
  s_mono {w u : M.World} {V Z : Set M.World} : u ≺[w] V → V ⊆ Z → u ≺[w] Z

/-- - [KO21, Proposition 3.3] -/
class IsJ1 (M : Model κ α) : Prop where
  s_refl {w u : M.World} : w ≺ u → u ≺[w] {u}

/-- - [KO21, Proposition 3.9] -/
class IsJ4 (M : Model κ α) : Prop where
  exists_rel_of_s {w u : M.World} {V : Set M.World} : u ≺[w] V → ∃ v ∈ V, w ≺ v

/-- - [KO21, Proposition 3.10] -/
class IsJ4Plus (M : Model κ α) : Prop where
  s_inter {w u : M.World} {V : Set M.World} : u ≺[w] V → u ≺[w] {v ∈ V | w ≺ v}

/-- - [KO21, Proposition 3.16] -/
class IsJ2 (M : Model κ α) : Prop extends M.IsJ4 where
  s_trans {w u : M.World} {V : Set M.World} (Z : M.World → Set M.World) :
    u ≺[w] V → (∀ v ∈ V, w ≺ v → v ≺[w] Z v) → u ≺[w] ⋃ v ∈ {v ∈ V | w ≺ v}, Z v

/-- - [KO21, Proposition 3.19] -/
class IsJ5 (M : Model κ α) : Prop where
  s_of_rel {w u v : M.World} : w ≺ u → u ≺ v → u ≺[w] {v}

end Verbrugge.Model

namespace Verbrugge.Model.World

open Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {x : M.World} {A B C : Formula α}

lemma forces_axiomJ3 : x ⊩[M] Axioms.J3 A B C := by
  intro hx y Rxy hy;
  obtain ⟨hAC, hBC⟩ := forces_and.mp hx;
  rcases forces_or.mp hy with hy | hy;
  · exact hAC y Rxy hy;
  · exact hBC y Rxy hy;

lemma forces_axiomJ6 [M.IsILMinus] : x ⊩[M] Axioms.J6 A := by
  apply forces_iff.mpr;
  constructor;
  · intro hx y Rxy hy;
    exact absurd (hx y Rxy) hy;
  · intro hx y Rxy;
    by_contra hy;
    obtain ⟨V, hV, hV'⟩ := hx y Rxy hy;
    obtain ⟨z, hz⟩ := IsILMinus.nonempty_of_s hV;
    exact hV' z hz;

lemma forces_axiomJ1 [M.IsJ1] : x ⊩[M] Axioms.J1 A B := by
  intro hx y Rxy hy;
  use {y};
  and_intros;
  · exact IsJ1.s_refl Rxy;
  · simpa using hx y Rxy hy;

lemma forces_axiomJ4 [M.IsJ4] : x ⊩[M] Axioms.J4 A B := by
  intro hx hA;
  obtain ⟨y, Rxy, hy⟩ := forces_dia.mp hA;
  obtain ⟨V, hV, hV'⟩ := hx y Rxy hy;
  obtain ⟨z, hz, Rxz⟩ := IsJ4.exists_rel_of_s hV;
  exact forces_dia.mpr ⟨z, Rxz, hV' z hz⟩;

lemma forces_axiomJ4Plus [M.IsJ4Plus] : x ⊩[M] Axioms.J4Plus A B C := by
  intro hx hCA y Rxy hy;
  obtain ⟨V, hV, hV'⟩ := hCA y Rxy hy;
  use {v ∈ V | x ≺ v};
  and_intros;
  · exact IsJ4Plus.s_inter hV;
  · rintro z ⟨hz, Rxz⟩;
    exact hx z Rxz (hV' z hz);

lemma forces_axiomJ2 [M.IsJ2] : x ⊩[M] Axioms.J2 A B C := by
  intro hx y Rxy hy;
  obtain ⟨hAB, hBC⟩ := forces_and.mp hx;
  obtain ⟨V, hV, hV'⟩ := hAB y Rxy hy;
  have hZ (v : M.World) : ∃ Z, x ≺ v → v ∈ V → v ≺[x] Z ∧ ∀ z ∈ Z, z ⊩ C := by
    by_cases h : x ≺ v ∧ v ∈ V;
    · obtain ⟨Z, hZ, hZ'⟩ := hBC v h.1 (hV' v h.2);
      exact ⟨Z, fun _ _ ↦ ⟨hZ, hZ'⟩⟩;
    · exact ⟨∅, fun h₁ h₂ ↦ absurd ⟨h₁, h₂⟩ h⟩;
  choose Z hZ using hZ;
  use ⋃ v ∈ {v ∈ V | x ≺ v}, Z v;
  and_intros;
  · exact IsJ2.s_trans Z hV fun v hv Rxv ↦ (hZ v Rxv hv).1;
  · simp only [Set.mem_iUnion, Set.mem_ofPred_eq];
    rintro z ⟨v, ⟨hv, Rxv⟩, hz⟩;
    exact (hZ v Rxv hv).2 z hz;

lemma forces_axiomJ5 [M.IsJ5] : x ⊩[M] Axioms.J5 A := by
  intro y Rxy hy;
  obtain ⟨z, Ryz, hz⟩ := forces_dia.mp hy;
  use {z};
  and_intros;
  · exact IsJ5.s_of_rel Rxy Ryz;
  · simpa;

end Verbrugge.Model.World

/-! ### Soundness -/

namespace Logic.ofAxiomsMinus

open Verbrugge Verbrugge.Model Verbrugge.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {𝔸 : Set (Formula α)} {A : Formula α}

/-- - [KO21, Proposition 2.7] -/
theorem sound_verbrugge [M.IsILMinus] (h𝔸 : ∀ A ∈ 𝔸, M ⊧ A) (h : ofAxiomsMinus 𝔸 ⊢ A) :
    M ⊧ A := by
  intro x;
  induction h generalizing x with
  | axm hA => exact h𝔸 _ hA x;
  | mdp _ _ ih₁ ih₂ => exact ih₁ x (ih₂ x);
  | nec _ ih =>
    intro y _;
    exact ih y;
  | rule1 _ ih =>
    intro hx y Rxy hy;
    obtain ⟨V, hV, hV'⟩ := hx y Rxy hy;
    use V;
    and_intros;
    · exact hV;
    · intro z hz;
      exact ih z (hV' z hz);
  | rule2 _ ih =>
    intro hx y Rxy hy;
    exact hx y Rxy (ih y hy);
  | axiomL => exact forces_axiomL;
  | axiomJ3 => exact forces_axiomJ3;
  | axiomJ6 => exact forces_axiomJ6;
  | _ => grind;

end Logic.ofAxiomsMinus

namespace Logic

open Verbrugge Verbrugge.Model Verbrugge.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILMinusJ2.sound_verbrugge [M.IsILMinus] [M.IsJ2] : ILMinusJ2 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound_verbrugge <| by
    rintro _ ⟨A, B, C, rfl⟩ x;
    exact forces_axiomJ2

theorem ILMinusJ2J4Plus.sound_verbrugge [M.IsILMinus] [M.IsJ2] [M.IsJ4Plus] :
    ILMinusJ2J4Plus ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound_verbrugge <| by
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, C, rfl⟩) x;
    · exact forces_axiomJ2;
    · exact forces_axiomJ4Plus;

theorem ILMinusJ2J5.sound_verbrugge [M.IsILMinus] [M.IsJ2] [M.IsJ5] :
    ILMinusJ2J5 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound_verbrugge <| by
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, rfl⟩) x;
    · exact forces_axiomJ2;
    · exact forces_axiomJ5;

theorem ILMinusJ2J4PlusJ5.sound_verbrugge [M.IsILMinus] [M.IsJ2] [M.IsJ4Plus] [M.IsJ5] :
    ILMinusJ2J4PlusJ5 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound_verbrugge <| by
    rintro _ ((⟨A, B, C, rfl⟩ | ⟨A, B, C, rfl⟩) | ⟨A, rfl⟩) x;
    · exact forces_axiomJ2;
    · exact forces_axiomJ4Plus;
    · exact forces_axiomJ5;

theorem ILMinusJ4.sound_verbrugge [M.IsILMinus] [M.IsJ4] : ILMinusJ4 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound_verbrugge <| by
    rintro _ ⟨A, B, rfl⟩ x;
    exact forces_axiomJ4

theorem ILMinusJ4J5.sound_verbrugge [M.IsILMinus] [M.IsJ4] [M.IsJ5] :
    ILMinusJ4J5 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound_verbrugge <| by
    rintro _ (⟨A, B, rfl⟩ | ⟨A, rfl⟩) x;
    · exact forces_axiomJ4;
    · exact forces_axiomJ5;

theorem ILMinusJ1J4.sound_verbrugge [M.IsILMinus] [M.IsJ1] [M.IsJ4] :
    ILMinusJ1J4 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound_verbrugge <| by
    rintro _ (⟨A, B, rfl⟩ | ⟨A, B, rfl⟩) x;
    · exact forces_axiomJ1;
    · exact forces_axiomJ4;

theorem ILMinusJ1J4J5.sound_verbrugge [M.IsILMinus] [M.IsJ1] [M.IsJ4] [M.IsJ5] :
    ILMinusJ1J4J5 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound_verbrugge <| by
    rintro _ ((⟨A, B, rfl⟩ | ⟨A, B, rfl⟩) | ⟨A, rfl⟩) x;
    · exact forces_axiomJ1;
    · exact forces_axiomJ4;
    · exact forces_axiomJ5;

end Logic

/-! ### Incompleteness with respect to $\mathbf{IL}^-$-frames -/

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

private lemma unprovable_J2Plus [L ⪯ ILMinusJ2J4PlusJ5] : L ⊬ Axioms.J2Plus (#0) (#1) (#2) := by
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

private lemma unprovable_J4Plus [L ⪯ ILMinusJ1J4J5] : L ⊬ Axioms.J4Plus (#1) (#2) (#0) := by
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
private lemma valid_J2Plus {κ : Type*} [Nonempty κ] (M : Veltman.Model κ ℕ) [M.IsJ2] :
    M ⊧ Axioms.J2Plus (#0) (#1) (#2) := fun _ ↦ forces_axiomJ2Plus

open Veltman.Model.World in
private lemma valid_J4Plus {κ : Type*} [Nonempty κ] (M : Veltman.Model κ ℕ) [M.IsJ4] :
    M ⊧ Axioms.J4Plus (#1) (#2) (#0) := fun _ ↦ forces_axiomJ4Plus

/-- - [KO21, Corollary 6.2] -/
theorem ILMinusJ2.incomplete : ∃ A : Formula ℕ,
    (∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ ℕ), [M.IsILMinus] → [M.IsJ2] → M ⊧ A) ∧
      ILMinusJ2 ⊬ A := by
  use Axioms.J2Plus (#0) (#1) (#2);
  constructor;
  · intro κ _ M _ _;
    exact valid_J2Plus M;
  · exact unprovable_J2Plus;

/-- - [KO21, Corollary 6.2] -/
theorem ILMinusJ2J4Plus.incomplete : ∃ A : Formula ℕ,
    (∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ ℕ), [M.IsILMinus] → [M.IsJ2] → M ⊧ A) ∧
      ILMinusJ2J4Plus ⊬ A := by
  use Axioms.J2Plus (#0) (#1) (#2);
  constructor;
  · intro κ _ M _ _;
    exact valid_J2Plus M;
  · exact unprovable_J2Plus;

/-- - [KO21, Corollary 6.2] -/
theorem ILMinusJ2J5.incomplete : ∃ A : Formula ℕ,
    (∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ ℕ),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ5] → M ⊧ A) ∧ ILMinusJ2J5 ⊬ A := by
  use Axioms.J2Plus (#0) (#1) (#2);
  constructor;
  · intro κ _ M _ _ _;
    exact valid_J2Plus M;
  · exact unprovable_J2Plus;

/-- - [KO21, Corollary 6.2] -/
theorem ILMinusJ2J4PlusJ5.incomplete : ∃ A : Formula ℕ,
    (∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ ℕ),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ5] → M ⊧ A) ∧ ILMinusJ2J4PlusJ5 ⊬ A := by
  use Axioms.J2Plus (#0) (#1) (#2);
  constructor;
  · intro κ _ M _ _ _;
    exact valid_J2Plus M;
  · exact unprovable_J2Plus;

/-- - [KO21, Corollary 6.4] -/
theorem ILMinusJ4.incomplete : ∃ A : Formula ℕ,
    (∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ ℕ), [M.IsILMinus] → [M.IsJ4] → M ⊧ A) ∧
      ILMinusJ4 ⊬ A := by
  use Axioms.J4Plus (#1) (#2) (#0);
  constructor;
  · intro κ _ M _ _;
    exact valid_J4Plus M;
  · exact unprovable_J4Plus;

/-- - [KO21, Corollary 6.4] -/
theorem ILMinusJ4J5.incomplete : ∃ A : Formula ℕ,
    (∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ ℕ),
      [M.IsILMinus] → [M.IsJ4] → [M.IsJ5] → M ⊧ A) ∧ ILMinusJ4J5 ⊬ A := by
  use Axioms.J4Plus (#1) (#2) (#0);
  constructor;
  · intro κ _ M _ _ _;
    exact valid_J4Plus M;
  · exact unprovable_J4Plus;

/-- - [KO21, Corollary 6.4] -/
theorem ILMinusJ1J4.incomplete : ∃ A : Formula ℕ,
    (∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ ℕ),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ4] → M ⊧ A) ∧ ILMinusJ1J4 ⊬ A := by
  use Axioms.J4Plus (#1) (#2) (#0);
  constructor;
  · intro κ _ M _ _ _;
    exact valid_J4Plus M;
  · exact unprovable_J4Plus;

/-- - [KO21, Corollary 6.4] -/
theorem ILMinusJ1J4J5.incomplete : ∃ A : Formula ℕ,
    (∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ ℕ),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ4] → [M.IsJ5] → M ⊧ A) ∧ ILMinusJ1J4J5 ⊬ A := by
  use Axioms.J4Plus (#1) (#2) (#0);
  constructor;
  · intro κ _ M _ _ _ _;
    exact valid_J4Plus M;
  · exact unprovable_J4Plus;

end Logic

end FFL.InterpretabilityLogic

end
