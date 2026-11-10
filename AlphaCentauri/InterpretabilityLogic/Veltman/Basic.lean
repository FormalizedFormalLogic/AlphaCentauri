module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import Foundation.Logic.Semantics
public import Foundation.Vorspiel.Rel.CWF
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinus.Basic

/-!
# Veltman semantics

Veltman models, forcing, the frame conditions of $\mathbf{J1}$, $\mathbf{J2}$, $\mathbf{J2}^+$,
$\mathbf{J4}$, $\mathbf{J4}^+$ and $\mathbf{J5}$ on $\mathbf{IL}^-$-frames, and the soundness of
$\mathbf{IL}^-$ with respect to them.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Veltman

/-- A model with an accessibility relation `≺` and, for every world `w`, a relation `≺[w]`. -/
structure Model (κ : Type*) [Nonempty κ] (α : Type*) where
  Rel' : κ → κ → Prop
  S' : κ → κ → κ → Prop
  Val' : κ → α → Prop

namespace Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α}

abbrev World (_ : Model κ α) := κ

abbrev Rel {M : Model κ α} : M.World → M.World → Prop := M.Rel'
scoped infix:60 " ≺ " => Rel

abbrev S {M : Model κ α} (w : M.World) : M.World → M.World → Prop := M.S' w
scoped notation:60 x:61 " ≺[" w "] " y:61 => S w x y

abbrev Val {M : Model κ α} : M.World → α → Prop := M.Val'

instance : CoeFun (Model κ α) (fun M ↦ M.World → α → Prop) := ⟨fun M ↦ M.Val⟩

/-- `≺` is transitive and conversely well-founded, and each `≺[w]` is a reflexive and transitive
relation on the `≺`-successors of `w` containing `≺` between them.

- [KO21, §1]
-/
class IsIL (M : Model κ α) extends IsTrans _ M.Rel, IsConverseWellFounded _ M.Rel where
  rel_of_s_left {w x y : M.World} : x ≺[w] y → w ≺ x
  rel_of_s_right {w x y : M.World} : x ≺[w] y → w ≺ y
  s_refl {w x : M.World} : w ≺ x → x ≺[w] x
  s_trans {w x y z : M.World} : x ≺[w] y → y ≺[w] z → x ≺[w] z
  s_of_rel {w x y : M.World} : w ≺ x → x ≺ y → x ≺[w] y

export IsIL (rel_of_s_left rel_of_s_right s_refl s_trans s_of_rel)

noncomputable def terminalOf (M : Model κ α) [IsConverseWellFounded _ M.Rel] (X : Set M.World)
    (hX : X.Nonempty) : { t // t ∈ X ∧ ∀ x ∈ X, ¬t ≺ x } :=
  have h := ConverseWellFounded.iff_has_max.mp IsConverseWellFounded.cwf X hX;
  ⟨h.choose, h.choose_spec⟩

abbrev pointModel (v : α → Prop) : Model (Fin 1) α where
  Rel' _ _ := False
  S' _ _ _ := False
  Val' _ := v

instance (v : α → Prop) : (pointModel v).IsIL where
  trans := by tauto;
  cwf := ⟨fun x ↦ ⟨x, fun _ h ↦ h.elim⟩⟩
  rel_of_s_left := by tauto;
  rel_of_s_right := by tauto;
  s_refl := by tauto;
  s_trans := by tauto;
  s_of_rel := by tauto;

end Model

namespace Model.World

open Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {x : M.World} {A B : Formula α}

@[grind]
def Forces (M : Model κ α) (x : M.World) : Formula α → Prop
  | #a    => M x a
  | ⊥     => False
  | A 🡒 B => Forces M x A → Forces M x B
  | □A    => ∀ y, x ≺ y → Forces M y A
  | A ▷ B => ∀ y, x ≺ y → Forces M y A → ∃ z, y ≺[x] z ∧ Forces M z B

scoped notation:55 x:56 " ⊩[" M "] " A:56 => Forces M x A

scoped notation:55 x:56 " ⊮[" M "] " A:56 => ¬Forces M x A

scoped notation:55 x:56 " ⊩ " A:56 => Forces _ x A

scoped notation:55 x:56 " ⊮ " A:56 => ¬Forces _ x A

@[simp, grind =] lemma forces_atom {a : α} : x ⊩ #a ↔ M x a := Iff.rfl
@[simp, grind .] lemma not_forces_bot : x ⊮ ⊥ := id
@[simp, grind .] lemma forces_top : x ⊩ ⊤ := id
@[grind =] lemma forces_imp : x ⊩ A 🡒 B ↔ x ⊮ A ∨ x ⊩ B := imp_iff_not_or
@[grind =] lemma forces_and : x ⊩ A ⋏ B ↔ x ⊩ A ∧ x ⊩ B := by
  change ((_ → _ → False) → False) ↔ _; tauto;
@[grind =] lemma forces_or : x ⊩ A ⋎ B ↔ x ⊩ A ∨ x ⊩ B := by
  change ((_ → False) → _) ↔ _; tauto;
@[grind =] lemma forces_neg : x ⊩ ∼A ↔ x ⊮ A := Iff.rfl
@[grind =] lemma forces_iff : x ⊩ A 🡘 B ↔ (x ⊩ A ↔ x ⊩ B) := by
  simp only [LogicalConnective.iff, forces_and]; grind;
@[grind =] lemma forces_box : x ⊩ □A ↔ ∀ y, x ≺ y → y ⊩ A := Iff.rfl
@[grind =] lemma forces_dia : x ⊩ ◇A ↔ ∃ y, x ≺ y ∧ y ⊩ A := by
  change ((∀ y, x ≺ y → y ⊩ A → False) → False) ↔ _; grind;
@[grind =] lemma forces_rhd : x ⊩ A ▷ B ↔ ∀ y, x ≺ y → y ⊩ A → ∃ z, y ≺[x] z ∧ z ⊩ B := Iff.rfl

@[grind =] lemma not_forces_imp : x ⊮ A 🡒 B ↔ x ⊩ A ∧ x ⊮ B := by grind;
@[grind =] lemma not_forces_box : x ⊮ □A ↔ ∃ y, x ≺ y ∧ y ⊮ A := by grind;
@[grind =] lemma not_forces_rhd : x ⊮ A ▷ B ↔ ∃ y, x ≺ y ∧ y ⊩ A ∧ ∀ z, y ≺[x] z → z ⊮ B := by
  grind;

lemma forces_axiomL [IsTrans _ M.Rel] [IsConverseWellFounded _ M.Rel] :
    x ⊩ □(□A 🡒 A) 🡒 □A := by
  intro hx;
  by_contra hA;
  obtain ⟨y, Rxy, hy⟩ := not_forces_box.mp hA;
  obtain ⟨t, ⟨Rxt, ht⟩, tmax⟩ := M.terminalOf {y | x ≺ y ∧ y ⊮ A} ⟨y, Rxy, hy⟩;
  apply ht;
  apply hx t Rxt;
  intro z Rtz;
  by_contra hz;
  exact tmax z ⟨IsTrans.trans _ _ _ Rxt Rtz, hz⟩ Rtz;

end Model.World

namespace Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α}

instance : Semantics (Model κ α) (Formula α) := ⟨fun M A ↦ ∀ x : M.World, World.Forces M x A⟩


/-- `≺` is transitive and conversely well-founded, and `x ≺[w] y` implies `w ≺ x`.

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

lemma IsIL.of_isILMinus [M.IsILMinus] [M.IsJ1] [M.IsJ2] [M.IsJ5] : M.IsIL where
  rel_of_s_left := IsILMinus.rel_of_s_left
  rel_of_s_right := IsJ4.rel_of_s_right
  s_refl := IsJ1.s_refl
  s_trans := IsJ2.s_trans
  s_of_rel := IsJ5.s_of_rel

end Model

namespace Model.World

open Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {x : M.World} {A B C : Formula α}

lemma forces_axiomJ3 : x ⊩ Axioms.J3 A B C := by
  intro hx y Rxy hy
  grind

lemma forces_axiomJ6 : x ⊩ Axioms.J6 A := by
  apply forces_iff.mpr
  constructor
  · intro hx y Rxy hy
    exact absurd (hx y Rxy) hy
  · intro hx y Rxy
    by_contra hy
    obtain ⟨z, -, hz⟩ := hx y Rxy hy
    exact hz

lemma forces_axiomJ1 [M.IsJ1] : x ⊩ Axioms.J1 A B := by
  intro hx y Rxy hy
  exact ⟨y, IsJ1.s_refl Rxy, hx y Rxy hy⟩

lemma forces_axiomJ4Plus [M.IsJ4] : x ⊩ Axioms.J4Plus A B C := by
  intro hx hCA y Rxy hy
  obtain ⟨z, Sxyz, hz⟩ := hCA y Rxy hy
  exact ⟨z, Sxyz, hx z (IsJ4.rel_of_s_right Sxyz) hz⟩

lemma forces_axiomJ4 [M.IsJ4] : x ⊩ Axioms.J4 A B := by
  intro hx hA
  obtain ⟨y, Rxy, hy⟩ := forces_dia.mp hA
  obtain ⟨z, Sxyz, hz⟩ := hx y Rxy hy
  exact forces_dia.mpr ⟨z, IsJ4.rel_of_s_right Sxyz, hz⟩

lemma forces_axiomJ2Plus [M.IsJ2] : x ⊩ Axioms.J2Plus A B C := by
  intro hx y Rxy hy
  obtain ⟨hABC, hBC⟩ := forces_and.mp hx
  obtain ⟨z, Sxyz, hz⟩ := hABC y Rxy hy
  rcases forces_or.mp hz with hz | hz
  · obtain ⟨u, Sxzu, hu⟩ := hBC z (IsJ4.rel_of_s_right Sxyz) hz
    exact ⟨u, IsJ2.s_trans Sxyz Sxzu, hu⟩
  · exact ⟨z, Sxyz, hz⟩

lemma forces_axiomJ2 [M.IsJ2] : x ⊩ Axioms.J2 A B C := by
  intro hx y Rxy hy
  obtain ⟨hAB, hBC⟩ := forces_and.mp hx
  obtain ⟨z, Sxyz, hz⟩ := hAB y Rxy hy
  obtain ⟨u, Sxzu, hu⟩ := hBC z (IsJ4.rel_of_s_right Sxyz) hz
  exact ⟨u, IsJ2.s_trans Sxyz Sxzu, hu⟩

lemma forces_axiomJ5 [M.IsJ5] : x ⊩ Axioms.J5 A := by
  intro y Rxy hy
  obtain ⟨z, Ryz, hz⟩ := forces_dia.mp hy
  exact ⟨z, IsJ5.s_of_rel Rxy Ryz, hz⟩

end Model.World

end Veltman

/-! ### Soundness of the sublogics of $\mathbf{IL}$ -/

namespace Logic.ofAxiomsMinus

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {𝔸 : FormulaSet α} {A : Formula α}

/-- - [KO21, Proposition 2.3] -/
theorem sound [M.IsILMinus] (h𝔸 : ∀ A ∈ 𝔸, M ⊧ A) (h : ofAxiomsMinus 𝔸 ⊢ A) : M ⊧ A := by
  intro x
  induction h generalizing x with
  | axm hA => exact h𝔸 _ hA x
  | mdp _ _ ih₁ ih₂ => exact ih₁ x (ih₂ x)
  | nec _ ih =>
    intro y _
    exact ih y
  | rule1 _ ih =>
    intro hx y Rxy hy
    obtain ⟨z, Sxyz, hz⟩ := hx y Rxy hy
    exact ⟨z, Sxyz, ih z hz⟩
  | rule2 _ ih =>
    intro hx y Rxy hy
    exact hx y Rxy (ih y hy)
  | axiomL => exact forces_axiomL
  | axiomJ3 => exact forces_axiomJ3
  | axiomJ6 => exact forces_axiomJ6
  | _ => grind

end Logic.ofAxiomsMinus


end FFL.InterpretabilityLogic

end
