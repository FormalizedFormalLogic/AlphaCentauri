module

public import AlphaCentauri.ToFoundation.InterpretabilityLogic.ILMinus
public import AlphaCentauri.ToFoundation.InterpretabilityLogic.Veltman.Basic

/-!
# Veltman semantics of the sublogics of $\mathbf{IL}$

$\mathbf{IL}^-$-frames, the frame conditions of $\mathbf{J1}$, $\mathbf{J2}$, $\mathbf{J2}^+$,
$\mathbf{J4}$, $\mathbf{J4}^+$ and $\mathbf{J5}$, the soundness of the extensions of
$\mathbf{IL}^-$, and the strict inclusions between them.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Veltman.Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {V : M.World → α → Prop}

/-- `≺` is transitive and conversely well-founded, and `≺[w]` relates only `≺`-successors of `w`
on the left.

- [KO21, Definition 2.2]
-/
class IsILMinus (M : Model κ α) extends IsTrans _ M.Rel, IsConverseWellFounded _ M.Rel where
  rel_of_s_left {w x y : M.World} : x ≺[w] y → w ≺ x

/-- - [KO21, Proposition 3.2] -/
class IsJ1 (M : Model κ α) : Prop where
  s_refl {w x : M.World} : w ≺ x → x ≺[w] x

/-- - [KO21, Proposition 3.8] -/
class IsJ4 (M : Model κ α) : Prop where
  rel_of_s_right {w x y : M.World} : x ≺[w] y → w ≺ y

/-- - [KO21, Proposition 3.15] -/
class IsJ2 (M : Model κ α) : Prop extends M.IsJ4 where
  s_trans {w x y z : M.World} : x ≺[w] y → y ≺[w] z → x ≺[w] z

/-- - [KO21, Proposition 3.18] -/
class IsJ5 (M : Model κ α) : Prop where
  s_of_rel {w x y : M.World} : w ≺ x → x ≺ y → x ≺[w] y

instance [M.IsIL] : M.IsILMinus where
  rel_of_s_left := rel_of_s_left

instance [M.IsIL] : M.IsJ1 := ⟨s_refl⟩

instance [M.IsIL] : M.IsJ2 where
  rel_of_s_right := rel_of_s_right
  s_trans := s_trans

instance [M.IsIL] : M.IsJ5 := ⟨s_of_rel⟩

instance [M.IsILMinus] : (M.overwrite V).IsILMinus where
  toIsTrans := inferInstanceAs (IsTrans _ M.Rel)
  toIsConverseWellFounded := inferInstanceAs (IsConverseWellFounded _ M.Rel)
  rel_of_s_left := IsILMinus.rel_of_s_left (M := M)

instance [M.IsJ1] : (M.overwrite V).IsJ1 := ⟨IsJ1.s_refl (M := M)⟩

instance [M.IsJ4] : (M.overwrite V).IsJ4 := ⟨IsJ4.rel_of_s_right (M := M)⟩

instance [M.IsJ2] : (M.overwrite V).IsJ2 where
  rel_of_s_right := IsJ4.rel_of_s_right (M := M)
  s_trans := IsJ2.s_trans (M := M)

instance [M.IsJ5] : (M.overwrite V).IsJ5 := ⟨IsJ5.s_of_rel (M := M)⟩

end Veltman.Model

namespace Veltman.Model.World

open Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {x : M.World} {A B C : Formula α}

lemma forces_axiomJ3 : x ⊩ Axioms.J3 A B C := by
  intro hx y Rxy hy;
  obtain ⟨hAC, hBC⟩ := forces_and.mp hx;
  rcases forces_or.mp hy with hy | hy;
  · exact hAC y Rxy hy;
  · exact hBC y Rxy hy;

lemma forces_axiomJ6 : x ⊩ Axioms.J6 A := by
  apply forces_iff.mpr;
  constructor;
  · intro hx y Rxy hy;
    exact absurd (hx y Rxy) hy;
  · intro hx y Rxy;
    by_contra hy;
    obtain ⟨z, -, hz⟩ := hx y Rxy hy;
    exact hz;

lemma forces_axiomJ1 [M.IsJ1] : x ⊩ Axioms.J1 A B := by
  intro hx y Rxy hy;
  use y;
  and_intros;
  · exact IsJ1.s_refl Rxy;
  · exact hx y Rxy hy;

lemma forces_axiomJ4Plus [M.IsJ4] : x ⊩ Axioms.J4Plus A B C := by
  intro hx hCA y Rxy hy;
  obtain ⟨z, Sxyz, hz⟩ := hCA y Rxy hy;
  use z;
  and_intros;
  · exact Sxyz;
  · exact hx z (IsJ4.rel_of_s_right Sxyz) hz;

lemma forces_axiomJ4 [M.IsJ4] : x ⊩ Axioms.J4 A B := by
  intro hx hA;
  obtain ⟨y, Rxy, hy⟩ := forces_dia.mp hA;
  obtain ⟨z, Sxyz, hz⟩ := hx y Rxy hy;
  exact forces_dia.mpr ⟨z, IsJ4.rel_of_s_right Sxyz, hz⟩;

lemma forces_axiomJ2Plus [M.IsJ2] : x ⊩ Axioms.J2Plus A B C := by
  intro hx y Rxy hy;
  obtain ⟨hABC, hBC⟩ := forces_and.mp hx;
  obtain ⟨z, Sxyz, hz⟩ := hABC y Rxy hy;
  rcases forces_or.mp hz with hz | hz;
  · obtain ⟨u, Sxzu, hu⟩ := hBC z (IsJ4.rel_of_s_right Sxyz) hz;
    use u;
    and_intros;
    · exact IsJ2.s_trans Sxyz Sxzu;
    · exact hu;
  · use z;

lemma forces_axiomJ2 [M.IsJ2] : x ⊩ Axioms.J2 A B C := by
  intro hx y Rxy hy;
  obtain ⟨hAB, hBC⟩ := forces_and.mp hx;
  obtain ⟨z, Sxyz, hz⟩ := hAB y Rxy hy;
  obtain ⟨u, Sxzu, hu⟩ := hBC z (IsJ4.rel_of_s_right Sxyz) hz;
  use u;
  and_intros;
  · exact IsJ2.s_trans Sxyz Sxzu;
  · exact hu;

lemma forces_axiomJ5 [M.IsJ5] : x ⊩ Axioms.J5 A := by
  intro y Rxy hy;
  obtain ⟨z, Ryz, hz⟩ := forces_dia.mp hy;
  use z;
  and_intros;
  · exact IsJ5.s_of_rel Rxy Ryz;
  · exact hz;

end Veltman.Model.World

/-! ### Soundness -/

namespace Logic.ofAxiomsMinus

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {𝔸 : Set (Formula α)} {A : Formula α}

/-- - [KO21, Proposition 2.3] -/
theorem sound [M.IsILMinus] (h𝔸 : ∀ A ∈ 𝔸, M ⊧ A) (h : ofAxiomsMinus 𝔸 ⊢ A) : M ⊧ A := by
  intro x;
  induction h generalizing x with
  | axm hA => exact h𝔸 _ hA x;
  | mdp _ _ ih₁ ih₂ => exact ih₁ x (ih₂ x);
  | nec _ ih =>
    intro y _;
    exact ih y;
  | rule1 _ ih =>
    intro hx y Rxy hy;
    obtain ⟨z, Sxyz, hz⟩ := hx y Rxy hy;
    use z;
    and_intros;
    · exact Sxyz;
    · exact ih z hz;
  | rule2 _ ih =>
    intro hx y Rxy hy;
    exact hx y Rxy (ih y hy);
  | axiomL => exact forces_axiomL;
  | axiomJ3 => exact forces_axiomJ3;
  | axiomJ6 => exact forces_axiomJ6;
  | _ => grind;

end Logic.ofAxiomsMinus

namespace Logic

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

theorem ILMinus.sound [M.IsILMinus] : 𝐈𝐋⁻ ⊢ A → M ⊧ A := ofAxiomsMinus.sound (by simp)

theorem ILMinusJ1.sound [M.IsILMinus] [M.IsJ1] : ILMinusJ1 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ ⟨A, B, rfl⟩ x;
    exact forces_axiomJ1

theorem ILMinusJ2.sound [M.IsILMinus] [M.IsJ2] : ILMinusJ2 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ ⟨A, B, C, rfl⟩ x;
    exact forces_axiomJ2

theorem ILMinusJ2Plus.sound [M.IsILMinus] [M.IsJ2] : ILMinusJ2Plus ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ ⟨A, B, C, rfl⟩ x;
    exact forces_axiomJ2Plus

theorem ILMinusJ4.sound [M.IsILMinus] [M.IsJ4] : ILMinusJ4 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ ⟨A, B, rfl⟩ x;
    exact forces_axiomJ4

theorem ILMinusJ4Plus.sound [M.IsILMinus] [M.IsJ4] : ILMinusJ4Plus ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ ⟨A, B, C, rfl⟩ x;
    exact forces_axiomJ4Plus

theorem ILMinusJ5.sound [M.IsILMinus] [M.IsJ5] : ILMinusJ5 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ ⟨A, rfl⟩ x;
    exact forces_axiomJ5

theorem ILMinusJ1J5.sound [M.IsILMinus] [M.IsJ1] [M.IsJ5] : ILMinusJ1J5 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ (⟨A, B, rfl⟩ | ⟨A, rfl⟩) x;
    · exact forces_axiomJ1;
    · exact forces_axiomJ5;

theorem ILMinusJ4PlusJ5.sound [M.IsILMinus] [M.IsJ4] [M.IsJ5] : ILMinusJ4PlusJ5 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, rfl⟩) x;
    · exact forces_axiomJ4Plus;
    · exact forces_axiomJ5;

theorem ILMinusJ1J4Plus.sound [M.IsILMinus] [M.IsJ1] [M.IsJ4] : ILMinusJ1J4Plus ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ (⟨A, B, rfl⟩ | ⟨A, B, C, rfl⟩) x;
    · exact forces_axiomJ1;
    · exact forces_axiomJ4Plus;

theorem ILMinusJ1J4PlusJ5.sound [M.IsILMinus] [M.IsJ1] [M.IsJ4] [M.IsJ5] :
    ILMinusJ1J4PlusJ5 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ ((⟨A, B, rfl⟩ | ⟨A, B, C, rfl⟩) | ⟨A, rfl⟩) x;
    · exact forces_axiomJ1;
    · exact forces_axiomJ4Plus;
    · exact forces_axiomJ5;

theorem ILMinusJ2PlusJ5.sound [M.IsILMinus] [M.IsJ2] [M.IsJ5] : ILMinusJ2PlusJ5 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, rfl⟩) x;
    · exact forces_axiomJ2Plus;
    · exact forces_axiomJ5;

theorem CL.sound [M.IsILMinus] [M.IsJ1] [M.IsJ2] : 𝐂𝐋 ⊢ A → M ⊧ A :=
  ofAxiomsMinus.sound <| by
    rintro _ (⟨A, B, rfl⟩ | ⟨A, B, C, rfl⟩) x;
    · exact forces_axiomJ1;
    · exact forces_axiomJ2;

end Logic

section Consistency

open Veltman.Model Logic

variable {α : Type*}

instance : Entailment.Consistent (𝐈𝐋⁻ : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinus.sound (M := pointModel fun _ ↦ False) h 0

instance : Entailment.Consistent (ILMinusJ1 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ1.sound (M := pointModel fun _ ↦ False) h 0

instance : Entailment.Consistent (ILMinusJ2 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ2.sound (M := pointModel fun _ ↦ False) h 0

instance : Entailment.Consistent (ILMinusJ2Plus : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ2Plus.sound (M := pointModel fun _ ↦ False) h 0

instance : Entailment.Consistent (ILMinusJ4 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ4.sound (M := pointModel fun _ ↦ False) h 0

instance : Entailment.Consistent (ILMinusJ4Plus : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ4Plus.sound (M := pointModel fun _ ↦ False) h 0

instance : Entailment.Consistent (ILMinusJ5 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ5.sound (M := pointModel fun _ ↦ False) h 0

instance : Entailment.Consistent (ILMinusJ1J5 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ1J5.sound (M := pointModel fun _ ↦ False) h 0

instance : Entailment.Consistent (ILMinusJ4PlusJ5 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ4PlusJ5.sound (M := pointModel fun _ ↦ False) h 0

instance : Entailment.Consistent (ILMinusJ1J4Plus : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ1J4Plus.sound (M := pointModel fun _ ↦ False) h 0

instance : Entailment.Consistent (ILMinusJ1J4PlusJ5 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ1J4PlusJ5.sound (M := pointModel fun _ ↦ False) h 0

instance : Entailment.Consistent (ILMinusJ2PlusJ5 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ ILMinusJ2PlusJ5.sound (M := pointModel fun _ ↦ False) h 0

instance : Entailment.Consistent (𝐂𝐋 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ CL.sound (M := pointModel fun _ ↦ False) h 0

end Consistency

end FFL.InterpretabilityLogic

end
