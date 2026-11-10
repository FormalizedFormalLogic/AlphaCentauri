module

public import AlphaCentauri.InterpretabilityLogic.ILMinus
public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic

/-!
# Veltman semantics of the sublogics of $\mathbf{IL}$

$\mathbf{IL}^-$-frames, the frame conditions of $\mathbf{J1}$, $\mathbf{J2}$, $\mathbf{J2}^+$,
$\mathbf{J4}$, $\mathbf{J4}^+$ and $\mathbf{J5}$, the soundness of the extensions of
$\mathbf{IL}^-$, and the strict inclusions between them.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Veltman.Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α}

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

/-! ### Strict inclusions -/

namespace Logic

open Veltman Veltman.Model Veltman.Model.World Entailment ofAxiomsMinus

variable {α : Type*} {L : Logic α}

private abbrev counterJ1 (α : Type*) : Model (Fin 2) α :=
  ⟨(· < ·), fun _ _ _ ↦ False, fun _ _ ↦ False⟩

private instance : (counterJ1 α).IsILMinus where
  trans := by omega
  cwf := Finite.converseWellFounded_of_trans_of_irrefl
  rel_of_s_left := by tauto

private instance : (counterJ1 α).IsJ2 where
  rel_of_s_right := by tauto
  s_trans := by tauto

private instance : (counterJ1 α).IsJ5 := ⟨by omega⟩

private lemma unprovable_J1 [L ⪯ ILMinusJ2PlusJ5] : L ⊬ Axioms.J1 ⊤ ⊤ := by
  intro h;
  replace h := WeakerThan.pbl (𝓣 := ILMinusJ2PlusJ5) h;
  obtain ⟨z, h, -⟩ :=
    ILMinusJ2PlusJ5.sound (M := counterJ1 α) h 0 (fun _ _ ↦ id) 1 (by omega) forces_top;
  exact h;

private abbrev counterJ5 (α : Type*) : Model (Fin 3) α :=
  ⟨(· < ·), fun w x y ↦ w < x ∧ x = y, fun _ _ ↦ False⟩

private instance : (counterJ5 α).IsILMinus where
  trans := by omega
  cwf := Finite.converseWellFounded_of_trans_of_irrefl
  rel_of_s_left := by tauto

private instance : (counterJ5 α).IsJ1 := ⟨by tauto⟩

private instance : (counterJ5 α).IsJ2 where
  rel_of_s_right := by omega
  s_trans := by omega

private lemma unprovable_J5 [L ⪯ 𝐂𝐋] : L ⊬ Axioms.J5 (□⊥) := by
  intro h;
  replace h := WeakerThan.pbl (𝓣 := 𝐂𝐋) h;
  have h₁ : (1 : Fin 3) ⊩[counterJ5 α] ◇□⊥ := by
    apply forces_dia.mpr;
    use 2;
    and_intros;
    · omega;
    · intro y hy;
      omega;
  obtain ⟨z, ⟨-, rfl⟩, hz⟩ := CL.sound (M := counterJ5 α) h 0 1 (by omega) h₁;
  exact hz 2 (by omega);

private abbrev counterJ4 (α : Type*) : Model (Fin 3) α :=
  ⟨(· < ·), fun w x _ ↦ w < x, fun _ _ ↦ False⟩

private instance : (counterJ4 α).IsILMinus where
  trans := by omega
  cwf := Finite.converseWellFounded_of_trans_of_irrefl
  rel_of_s_left := by tauto

private instance : (counterJ4 α).IsJ1 := ⟨by tauto⟩

private instance : (counterJ4 α).IsJ5 := ⟨by tauto⟩

private lemma unprovable_J4Plus [L ⪯ ILMinusJ1J5] : L ⊬ Axioms.J4Plus (◇⊤) ⊥ ⊤ := by
  intro h;
  replace h := WeakerThan.pbl (𝓣 := ILMinusJ1J5) h;
  have h₁ : (1 : Fin 3) ⊩[counterJ4 α] □(◇⊤ 🡒 ⊥) := by
    intro y Rxy hy;
    obtain ⟨z, Ryz, -⟩ := forces_dia.mp hy;
    omega;
  have h₂ : (1 : Fin 3) ⊩[counterJ4 α] ⊤ ▷ ◇⊤ := by
    intro y Rxy _;
    use 0;
    and_intros;
    · exact Rxy;
    · exact forces_dia.mpr ⟨1, by omega, forces_top⟩;
  obtain ⟨z, -, hz⟩ := ILMinusJ1J5.sound (M := counterJ4 α) h 1 h₁ h₂ 2 (by omega) forces_top;
  exact hz;

private abbrev counterJ2 (α : Type*) : Model (Fin 4) α :=
  ⟨(· < ·), fun w x y ↦ w < x ∧ w < y ∧ (x ≤ y ∨ w = 0 ∧ (x = 3 ∧ y = 2 ∨ x = 2 ∧ y = 1)),
    fun _ _ ↦ False⟩

private instance : (counterJ2 α).IsILMinus where
  trans := by omega
  cwf := Finite.converseWellFounded_of_trans_of_irrefl
  rel_of_s_left := by tauto

private instance : (counterJ2 α).IsJ1 := ⟨by omega⟩

private instance : (counterJ2 α).IsJ4 := ⟨by omega⟩

private instance : (counterJ2 α).IsJ5 := ⟨by omega⟩

private lemma unprovable_J2 [L ⪯ ILMinusJ1J4PlusJ5] : L ⊬ Axioms.J2 (□⊥) (◇⊤ ⋏ □□⊥) (◇◇⊤) := by
  intro h;
  replace h := WeakerThan.pbl (𝓣 := ILMinusJ1J4PlusJ5) h;
  have h₁ : (0 : Fin 4) ⊩[counterJ2 α] □⊥ ▷ (◇⊤ ⋏ □□⊥) ⋏ (◇⊤ ⋏ □□⊥) ▷ ◇◇⊤ := by
    apply forces_and.mpr;
    constructor;
    · intro y _ hy;
      have : ¬y < 3 := hy 3;
      use 2;
      constructor;
      · omega;
      · apply forces_and.mpr;
        constructor;
        · exact forces_dia.mpr ⟨3, by omega, forces_top⟩;
        · intro z hz u hu;
          omega;
    · intro y _ hy;
      obtain ⟨hy₁, hy₂⟩ := forces_and.mp hy;
      obtain ⟨z, hz, -⟩ := forces_dia.mp hy₁;
      have : ¬y < 2 := by
        intro h;
        exact hy₂ 2 h 3 (by omega);
      use 1;
      constructor;
      · omega;
      · exact forces_dia.mpr ⟨2, by omega, forces_dia.mpr ⟨3, by omega, forces_top⟩⟩;
  have h₂ : (3 : Fin 4) ⊩[counterJ2 α] □⊥ := by
    intro y hy;
    omega;
  obtain ⟨z, hz, hz'⟩ := ILMinusJ1J4PlusJ5.sound (M := counterJ2 α) h 0 h₁ 3 (by omega) h₂;
  obtain ⟨u, hu, hu'⟩ := forces_dia.mp hz';
  obtain ⟨v, hv, -⟩ := forces_dia.mp hu';
  omega;

instance : (𝐈𝐋⁻ : Logic α) ⪱ ILMinusJ1 := .of_unprovable_provable unprovable_J1 (by simp)

instance : (ILMinusJ4Plus : Logic α) ⪱ ILMinusJ1J4Plus :=
  .of_unprovable_provable unprovable_J1 (axm (by simp))

instance : (ILMinusJ5 : Logic α) ⪱ ILMinusJ1J5 :=
  .of_unprovable_provable unprovable_J1 (axm (by simp))

instance : (ILMinusJ4PlusJ5 : Logic α) ⪱ ILMinusJ1J4PlusJ5 :=
  .of_unprovable_provable unprovable_J1 (axm (by simp))

instance : (ILMinusJ2Plus : Logic α) ⪱ 𝐂𝐋 := .of_unprovable_provable unprovable_J1 (by simp)

instance : (ILMinusJ2PlusJ5 : Logic α) ⪱ 𝐈𝐋 :=
  .of_unprovable_provable unprovable_J1 ofAxioms.axiomJ1

instance : (𝐈𝐋⁻ : Logic α) ⪱ ILMinusJ5 := .of_unprovable_provable unprovable_J5 (by simp)

instance : (ILMinusJ4Plus : Logic α) ⪱ ILMinusJ4PlusJ5 :=
  .of_unprovable_provable unprovable_J5 (axm (by simp))

instance : (ILMinusJ2Plus : Logic α) ⪱ ILMinusJ2PlusJ5 :=
  .of_unprovable_provable unprovable_J5 (axm (by simp))

instance : (ILMinusJ1 : Logic α) ⪱ ILMinusJ1J5 :=
  .of_unprovable_provable unprovable_J5 (axm (by simp))

instance : (ILMinusJ1J4Plus : Logic α) ⪱ ILMinusJ1J4PlusJ5 :=
  .of_unprovable_provable unprovable_J5 (axm (by simp))

instance : (𝐂𝐋 : Logic α) ⪱ 𝐈𝐋 := .of_unprovable_provable unprovable_J5 ofAxioms.axiomJ5

instance : (𝐈𝐋⁻ : Logic α) ⪱ ILMinusJ4Plus := .of_unprovable_provable unprovable_J4Plus (by simp)

instance : (ILMinusJ1 : Logic α) ⪱ ILMinusJ1J4Plus :=
  .of_unprovable_provable unprovable_J4Plus (axm (by simp))

instance : (ILMinusJ5 : Logic α) ⪱ ILMinusJ4PlusJ5 :=
  .of_unprovable_provable unprovable_J4Plus (axm (by simp))

instance : (ILMinusJ1J5 : Logic α) ⪱ ILMinusJ1J4PlusJ5 :=
  .of_unprovable_provable unprovable_J4Plus (axm (by simp))

instance : (ILMinusJ4Plus : Logic α) ⪱ ILMinusJ2Plus :=
  .of_unprovable_provable unprovable_J2 (by simp)

instance : (ILMinusJ1J4Plus : Logic α) ⪱ 𝐂𝐋 := .of_unprovable_provable unprovable_J2 (by simp)

instance : (ILMinusJ4PlusJ5 : Logic α) ⪱ ILMinusJ2PlusJ5 :=
  .of_unprovable_provable unprovable_J2 (WeakerThan.pbl (𝓢 := ILMinusJ2Plus) (by simp))

instance : (ILMinusJ1J4PlusJ5 : Logic α) ⪱ 𝐈𝐋 :=
  .of_unprovable_provable unprovable_J2 ofAxioms.axiomJ2

end Logic

end FFL.InterpretabilityLogic

end
