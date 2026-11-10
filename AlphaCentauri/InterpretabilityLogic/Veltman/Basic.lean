module

public import AlphaCentauri.InterpretabilityLogic.Logic
public import Foundation.Logic.Semantics
public import Foundation.Vorspiel.Rel.CWF

/-!
# Veltman semantics

Veltman models, forcing, and the soundness of extensions of $\mathbf{IL}$ with respect to Veltman
models validating their axioms.
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

/-- The model on the frame of `M` with valuation `V`. -/
def overwrite (M : Model κ α) (V : M.World → α → Prop) : Model κ α := ⟨M.Rel', M.S', V⟩

instance {V : M.World → α → Prop} [M.IsIL] : (M.overwrite V).IsIL where
  toIsTrans := inferInstanceAs (IsTrans _ M.Rel)
  toIsConverseWellFounded := inferInstanceAs (IsConverseWellFounded _ M.Rel)
  rel_of_s_left := rel_of_s_left (M := M)
  rel_of_s_right := rel_of_s_right (M := M)
  s_refl := s_refl (M := M)
  s_trans := s_trans (M := M)
  s_of_rel := s_of_rel (M := M)

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

variable {κ α : Type*} [Nonempty κ]

instance : Semantics (Model κ α) (Formula α) := ⟨fun M A ↦ ∀ x : M.World, World.Forces M x A⟩

lemma models_iff {M : Model κ α} {A : Formula α} : M ⊧ A ↔ ∀ x : M.World, World.Forces M x A :=
  Iff.rfl

end Model

end Veltman

/-! ### Soundness -/

namespace Logic.ofAxioms

open Veltman Veltman.Model Veltman.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {𝔸 : Set (Formula α)} {A : Formula α}

theorem sound [M.IsIL] (h𝔸 : ∀ A ∈ 𝔸, M ⊧ A) (h : ofAxioms 𝔸 ⊢ A) : M ⊧ A := by
  intro x;
  induction h generalizing x with
  | axm hA => exact h𝔸 _ hA x;
  | mdp _ _ ih₁ ih₂ => exact ih₁ x (ih₂ x);
  | nec _ ih => exact fun y _ ↦ ih y;
  | axiomL => exact forces_axiomL;
  | axiomJ1 =>
    intro hx y Rxy hy;
    use y;
    and_intros;
    · exact s_refl Rxy;
    · exact hx y Rxy hy;
  | axiomJ2 =>
    intro hx y Rxy hy;
    obtain ⟨hAB, hBC⟩ := forces_and.mp hx;
    obtain ⟨z, Sxyz, hz⟩ := hAB y Rxy hy;
    obtain ⟨u, Sxzu, hu⟩ := hBC z (rel_of_s_right Sxyz) hz;
    use u;
    and_intros;
    · exact s_trans Sxyz Sxzu;
    · exact hu;
  | axiomJ3 =>
    intro hx y Rxy hy;
    obtain ⟨hAC, hBC⟩ := forces_and.mp hx;
    rcases forces_or.mp hy with hy | hy;
    · exact hAC y Rxy hy;
    · exact hBC y Rxy hy;
  | axiomJ4 =>
    intro hx hA;
    obtain ⟨y, Rxy, hy⟩ := forces_dia.mp hA;
    obtain ⟨z, Sxyz, hz⟩ := hx y Rxy hy;
    exact forces_dia.mpr ⟨z, rel_of_s_right Sxyz, hz⟩;
  | axiomJ5 =>
    intro y Rxy hy;
    obtain ⟨z, Ryz, hz⟩ := forces_dia.mp hy;
    use z;
    and_intros;
    · exact s_of_rel Rxy Ryz;
    · exact hz;
  | _ => grind;

end Logic.ofAxioms

instance {α : Type*} : Entailment.Consistent (𝐈𝐋 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦
    Logic.ofAxioms.sound (M := Veltman.Model.pointModel fun _ ↦ False) (by simp) h 0

end FFL.InterpretabilityLogic

end
