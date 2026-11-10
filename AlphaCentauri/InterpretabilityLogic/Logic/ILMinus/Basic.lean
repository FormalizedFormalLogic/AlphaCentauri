module

public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel
public import AlphaCentauri.InterpretabilityLogic.Veltman.IndexedSetModel
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinusModel

/-!
# Soundness and completeness of the sublogics of $\mathbf{IL}$

Each sublogic $\mathbf{IL}^-(\mathbf{J1}, \ldots)$ of $\mathbf{IL}$ other than $\mathbf{CL}$ proves
exactly the formulas valid in the finite Veltman models, or in the finite generalised Veltman
models, satisfying the frame conditions of its axioms. The sublogics complete with respect to
Veltman models and those complete with respect to generalised Veltman models are different ones.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

universe u

variable {α : Type u} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem ILMinus.iff_valid_finite :
    𝐈𝐋⁻ ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinus.sound h;
  · exact ILMinus.complete;

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1.iff_valid_finite :
    ILMinusJ1 ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ1.sound h;
  · exact ILMinusJ1.complete;

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ4Plus.iff_valid_finite :
    ILMinusJ4Plus ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ4] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ4Plus.sound h;
  · exact ILMinusJ4Plus.complete;

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J4Plus.iff_valid_finite :
    ILMinusJ1J4Plus ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ4] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ1J4Plus.sound h;
  · exact ILMinusJ1J4Plus.complete;

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ2Plus.iff_valid_finite :
    ILMinusJ2Plus ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ2Plus.sound h;
  · exact ILMinusJ2Plus.complete;

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ5.iff_valid_finite :
    ILMinusJ5 ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ5.sound h;
  · exact ILMinusJ5.complete;

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J5.iff_valid_finite :
    ILMinusJ1J5 ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ1J5.sound h;
  · exact ILMinusJ1J5.complete;

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ4PlusJ5.iff_valid_finite :
    ILMinusJ4PlusJ5 ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ4] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ4PlusJ5.sound h;
  · exact ILMinusJ4PlusJ5.complete;

/-- - [KO21, Theorem 5.1] -/
theorem ILMinusJ1J4PlusJ5.iff_valid_finite :
    ILMinusJ1J4PlusJ5 ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ4] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ1J4PlusJ5.sound h;
  · exact ILMinusJ1J4PlusJ5.complete;

/-- - [KO21, Theorem 5.4] -/
theorem ILMinusJ2PlusJ5.iff_valid_finite :
    ILMinusJ2PlusJ5 ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ2PlusJ5.sound h;
  · exact ILMinusJ2PlusJ5.complete;

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ4.iff_valid_finite_verbrugge :
    ILMinusJ4 ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ4] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ4.sound_verbrugge h;
  · exact ILMinusJ4.complete_verbrugge;

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ1J4.iff_valid_finite_verbrugge :
    ILMinusJ1J4 ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ4] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ1J4.sound_verbrugge h;
  · exact ILMinusJ1J4.complete_verbrugge;

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ4J5.iff_valid_finite_verbrugge :
    ILMinusJ4J5 ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ4] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ4J5.sound_verbrugge h;
  · exact ILMinusJ4J5.complete_verbrugge;

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ1J4J5.iff_valid_finite_verbrugge :
    ILMinusJ1J4J5 ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ4] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ1J4J5.sound_verbrugge h;
  · exact ILMinusJ1J4J5.complete_verbrugge;

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ2.iff_valid_finite_verbrugge :
    ILMinusJ2 ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ2.sound_verbrugge h;
  · exact ILMinusJ2.complete_verbrugge;

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ2J4Plus.iff_valid_finite_verbrugge :
    ILMinusJ2J4Plus ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ4Plus] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ2J4Plus.sound_verbrugge h;
  · exact ILMinusJ2J4Plus.complete_verbrugge;

/-- - [KO21, Theorem 7.4] -/
theorem ILMinusJ2J5.iff_valid_finite_verbrugge :
    ILMinusJ2J5 ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ2J5.sound_verbrugge h;
  · exact ILMinusJ2J5.complete_verbrugge;

/-- - [KO21, Theorem 7.4] -/
theorem ILMinusJ2J4PlusJ5.iff_valid_finite_verbrugge :
    ILMinusJ2J4PlusJ5 ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ4Plus] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILMinusJ2J4PlusJ5.sound_verbrugge h;
  · exact ILMinusJ2J4PlusJ5.complete_verbrugge;

end Logic

end FFL.InterpretabilityLogic

end
