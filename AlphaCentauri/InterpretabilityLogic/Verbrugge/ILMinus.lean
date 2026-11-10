module

public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.Basic

/-!
# Generalised Veltman semantics of $\mathbf{IL}^-$

$\mathbf{IL}^-_{\mathrm{set}}$-frames, the frame conditions of $\mathbf{J1}$, $\mathbf{J2}$,
$\mathbf{J4}$, $\mathbf{J4}^+$ and $\mathbf{J5}$ on them, and the soundness of $\mathbf{IL}^-$
with respect to them. The soundness and incompleteness of each extension are in its own module.
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

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {𝔸 : FormulaSet α} {A : Formula α}

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

end FFL.InterpretabilityLogic

end
