module

public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic

/-!
# Generalised Veltman semantics

Generalised Veltman models (Verbrugge semantics), in which each `≺[w]` relates a world to a set of
worlds, forcing, the soundness of extensions of $\mathbf{IL}$ with respect to generalised Veltman
models validating their axioms, and the generalised Veltman model of a Veltman model.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Verbrugge

/-- A model with an accessibility relation `≺` and, for every world `w`, a relation `≺[w]` between
worlds and sets of worlds. -/
structure Model (κ : Type*) [Nonempty κ] (α : Type*) where
  Rel' : κ → κ → Prop
  S' : κ → κ → Set κ → Prop
  Val' : κ → α → Prop

namespace Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α}

abbrev World (_ : Model κ α) := κ

abbrev Rel {M : Model κ α} : M.World → M.World → Prop := M.Rel'
scoped infix:60 " ≺ " => Rel

abbrev S {M : Model κ α} (w : M.World) : M.World → Set M.World → Prop := M.S' w
scoped notation:60 x:61 " ≺[" w "] " V:61 => S w x V

abbrev Val {M : Model κ α} : M.World → α → Prop := M.Val'

instance : CoeFun (Model κ α) (fun M ↦ M.World → α → Prop) := ⟨fun M ↦ M.Val⟩

/-- `≺` is transitive and conversely well-founded, and each `≺[w]` relates `≺`-successors of `w`
to nonempty sets of `≺`-successors of `w`, is quasi-reflexive and quasi-transitive, contains
$u \mathrel{≺[w]} \{v\}$ whenever $w ≺ u ≺ v$, and is monotone.

- [JMMV20, Definition 3.1]
- [Ver92]
- [Mas20, §6.2]
-/
class IsIL (M : Model κ α) extends IsTrans _ M.Rel, IsConverseWellFounded _ M.Rel where
  rel_of_s {w u : M.World} {V : Set M.World} : u ≺[w] V → w ≺ u
  rel_of_mem_of_s {w u v : M.World} {V : Set M.World} : u ≺[w] V → v ∈ V → w ≺ v
  nonempty_of_s {w u : M.World} {V : Set M.World} : u ≺[w] V → V.Nonempty
  s_refl {w u : M.World} : w ≺ u → u ≺[w] {u}
  s_trans {w u : M.World} {V : Set M.World} (Z : M.World → Set M.World) :
    u ≺[w] V → (∀ v ∈ V, v ≺[w] Z v) → u ≺[w] ⋃ v ∈ V, Z v
  s_of_rel {w u v : M.World} : w ≺ u → u ≺ v → u ≺[w] {v}
  s_mono {w u : M.World} {V Z : Set M.World} : u ≺[w] V → V ⊆ Z → (∀ z ∈ Z, w ≺ z) → u ≺[w] Z

export IsIL (rel_of_s rel_of_mem_of_s nonempty_of_s s_refl s_trans s_of_rel s_mono)

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
  | A ▷ B => ∀ y, x ≺ y → Forces M y A → ∃ V, y ≺[x] V ∧ ∀ z ∈ V, Forces M z B

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
@[grind =] lemma forces_rhd :
    x ⊩ A ▷ B ↔ ∀ y, x ≺ y → y ⊩ A → ∃ V, y ≺[x] V ∧ ∀ z ∈ V, z ⊩ B := Iff.rfl

@[grind =] lemma not_forces_imp : x ⊮ A 🡒 B ↔ x ⊩ A ∧ x ⊮ B := by grind;
@[grind =] lemma not_forces_box : x ⊮ □A ↔ ∃ y, x ≺ y ∧ y ⊮ A := by grind;
@[grind =] lemma not_forces_rhd :
    x ⊮ A ▷ B ↔ ∃ y, x ≺ y ∧ y ⊩ A ∧ ∀ V, y ≺[x] V → ∃ z ∈ V, z ⊮ B := by
  grind;

lemma forces_axiomL [IsTrans _ M.Rel] [IsConverseWellFounded _ M.Rel] :
    x ⊩ □(□A 🡒 A) 🡒 □A := by
  intro hx;
  by_contra hA;
  obtain ⟨y, Rxy, hy⟩ := not_forces_box.mp hA;
  obtain ⟨t, ⟨Rxt, ht⟩, tmax⟩ :=
    ConverseWellFounded.iff_has_max.mp (IsConverseWellFounded.cwf (rel := M.Rel))
      {y | x ≺ y ∧ y ⊮ A} ⟨y, Rxy, hy⟩;
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

end Verbrugge

/-! ### Soundness -/

namespace Logic.ofAxioms

open Verbrugge Verbrugge.Model Verbrugge.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {𝔸 : Set (Formula α)} {A : Formula α}

/-- - [JMMV20, Theorem 3.2]
- [Mas20, §6.2]
-/
theorem sound_verbrugge [M.IsIL] (h𝔸 : ∀ A ∈ 𝔸, M ⊧ A) (h : ofAxioms 𝔸 ⊢ A) : M ⊧ A := by
  intro x;
  induction h generalizing x with
  | axm hA => exact h𝔸 _ hA x;
  | mdp _ _ ih₁ ih₂ => exact ih₁ x (ih₂ x);
  | nec _ ih =>
    intro y _;
    exact ih y;
  | axiomL => exact forces_axiomL;
  | axiomJ1 =>
    intro hx y Rxy hy;
    use {y};
    and_intros;
    · exact s_refl Rxy;
    · simpa using hx y Rxy hy;
  | axiomJ2 =>
    intro hx y Rxy hy;
    obtain ⟨hAB, hBC⟩ := forces_and.mp hx;
    obtain ⟨V, SxyV, hV⟩ := hAB y Rxy hy;
    choose! Z SxZ hZ using fun v hv ↦ hBC v (rel_of_mem_of_s SxyV hv) (hV v hv);
    use ⋃ v ∈ V, Z v;
    and_intros;
    · exact s_trans Z SxyV SxZ;
    · simp only [Set.mem_iUnion];
      rintro z ⟨v, hv, hz⟩;
      exact hZ v hv z hz;
  | axiomJ3 =>
    intro hx y Rxy hy;
    obtain ⟨hAC, hBC⟩ := forces_and.mp hx;
    rcases forces_or.mp hy with hy | hy;
    · exact hAC y Rxy hy;
    · exact hBC y Rxy hy;
  | axiomJ4 =>
    intro hx hA;
    obtain ⟨y, Rxy, hy⟩ := forces_dia.mp hA;
    obtain ⟨V, SxyV, hV⟩ := hx y Rxy hy;
    obtain ⟨z, hz⟩ := nonempty_of_s SxyV;
    apply forces_dia.mpr;
    use z;
    and_intros;
    · exact rel_of_mem_of_s SxyV hz;
    · exact hV z hz;
  | axiomJ5 =>
    intro y Rxy hy;
    obtain ⟨z, Ryz, hz⟩ := forces_dia.mp hy;
    use {z};
    and_intros;
    · exact s_of_rel Rxy Ryz;
    · simpa;
  | _ => grind;

end Logic.ofAxioms

/-! ### Veltman models as generalised Veltman models -/

namespace Veltman.Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α}

/-- The generalised Veltman model on the frame of `M` in which $u \mathrel{≺[w]} V$ holds when
every element of $V$ is a `≺`-successor of `w` and $u \mathrel{≺[w]} v$ in `M` for some $v ∈ V$.

- [JMMV20, Theorem 3.2]
- [Mas20, §9]
-/
def toVerbrugge (M : Model κ α) : Verbrugge.Model κ α where
  Rel' := M.Rel'
  S' w u V := (∀ v ∈ V, M.Rel' w v) ∧ ∃ v ∈ V, M.S' w u v
  Val' := M.Val'

instance [M.IsIL] : M.toVerbrugge.IsIL where
  trans := IsTrans.trans (r := M.Rel)
  cwf := IsConverseWellFounded.cwf (rel := M.Rel)
  rel_of_s := by
    rintro w u V ⟨-, v, -, Suv⟩;
    exact rel_of_s_left Suv;
  rel_of_mem_of_s := by
    rintro w u v V ⟨hV, -⟩ hv;
    exact hV v hv;
  nonempty_of_s := by
    rintro w u V ⟨-, v, hv, -⟩;
    exact ⟨v, hv⟩;
  s_refl := by
    intro w u Rwu;
    constructor;
    · simpa;
    · simpa using s_refl Rwu;
  s_trans := by
    rintro w u V Z ⟨-, v, hv, Suv⟩ hZ;
    obtain ⟨hZv, z, hz, Svz⟩ := hZ v hv;
    constructor;
    · simp only [Set.mem_iUnion];
      rintro y ⟨v', hv', hy⟩;
      exact (hZ v' hv').1 y hy;
    · use z;
      and_intros;
      · simp only [Set.mem_iUnion];
        use v;
      · exact s_trans Suv Svz;
  s_of_rel := by
    intro w u v Rwu Ruv;
    constructor;
    · simpa using IsTrans.trans (r := M.Rel) _ _ _ Rwu Ruv;
    · simpa using s_of_rel Rwu Ruv;
  s_mono := by
    rintro w u V Z ⟨-, v, hv, Suv⟩ hVZ hZ;
    constructor;
    · exact hZ;
    · use v;
      and_intros;
      · exact hVZ hv;
      · exact Suv;

open Veltman.Model.World Verbrugge.Model.World in
/-- `M` and `M.toVerbrugge` force the same formulas.

- [JMMV20, Theorem 3.2]
- [Mas20, §9]
-/
lemma forces_toVerbrugge [M.IsIL] {x : M.World} {A : Formula α} :
    x ⊩[M.toVerbrugge] A ↔ x ⊩[M] A := by
  induction A generalizing x with
  | atom a => rfl;
  | falsum => rfl;
  | imp A B ihA ihB => exact imp_congr ihA ihB;
  | box A ihA => exact forall_congr' fun y ↦ imp_congr_right fun _ ↦ ihA;
  | rhd A B ihA ihB =>
    constructor;
    · intro hx y Rxy hy;
      obtain ⟨V, ⟨-, z, hz, Syz⟩, hV⟩ := hx y Rxy (ihA.mpr hy);
      use z;
      and_intros;
      · exact Syz;
      · exact ihB.mp (hV z hz);
    · intro hx y Rxy hy;
      obtain ⟨z, Syz, hz⟩ := hx y Rxy (ihA.mp hy);
      use {z};
      and_intros;
      · simpa using rel_of_s_right Syz;
      · simpa;
      · simpa using ihB.mpr hz;

end Veltman.Model

end FFL.InterpretabilityLogic

end
