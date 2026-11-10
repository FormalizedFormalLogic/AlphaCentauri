module

public import AlphaCentauri.InterpretabilityLogic.Gentzen.Veltman
public import AlphaCentauri.InterpretabilityLogic.Logic.IL.Basic

/-!
# The sequent calculus for $\mathbf{IL}$ and its Veltman semantics

The sequent calculus for $\mathbf{IL}$ is sound for Veltman models, is complete for finite Veltman
models, and agrees with $\mathbf{IL}$ on them.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

universe u

namespace IL

open Veltman Veltman.Model Veltman.Model.World
open SaturatedSequent

namespace Gentzen

variable {α : Type u} [DecidableEq α] {S : Sequent α}

theorem sound {κ : Type*} [Nonempty κ] (M : Veltman.Model κ α) [M.IsIL] (h : ⊢ᴳ[𝐈𝐋] S) :
    M.ValidatesSequent S := by
  intro x hx;
  exact forces_disj.mp <|
    Logic.ofAxioms.sound (by simp) (Logic.IL.of_gentzen h) x (forces_conj.mpr hx);

theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] (M : Veltman.Model κ α), [Finite κ] → [M.IsIL] →
      M.ValidatesSequent S) :
    ⊢ᴳ[𝐈𝐋] S := by
  by_contra hS;
  obtain ⟨x₀, hx₀⟩ := lindenbaum (BS := S) hS
    (fun _ hA ↦ subset_closure (Finset.mem_union_left _ hA))
    (fun _ hA ↦ subset_closure (Finset.mem_union_right _ hA));
  obtain ⟨B, hB, hw⟩ := h (countermodel x₀) (⟨[], trivial⟩ : Path x₀)
    (fun A hA ↦ countermodel.truthlemma.1 (hx₀.ant hA));
  exact countermodel.truthlemma.2 (hx₀.suc hB) hw;

end Gentzen

end IL

namespace Logic.IL


variable {α : Type u} [DecidableEq α] {A : Formula α}

/-- - [dJV90, Theorem 4.1] -/
theorem gentzen_TFAE : [
    𝐈𝐋 ⊢ A,
    ⊢ᴳ[𝐈𝐋] ∅ ⟹ {A},
    ∀ {κ : Type u} [Nonempty κ] (M : Veltman.Model κ α), [M.IsIL] → M ⊧ A,
    ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α), [M.IsIL] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 3 := by
    intro h _ _ M _;
    exact Logic.ofAxioms.sound (by simp) h;
  tfae_have 3 → 4 := by
    intro h _ _ _ M _;
    exact h M;
  tfae_have 4 → 2 := by
    intro h;
    apply IL.Gentzen.complete;
    intro _ _ M _ _ x _;
    use A;
    and_intros;
    · simp;
    · exact h M x;
  tfae_have 2 → 1 := by
    intro h;
    simpa using of_gentzen h ⨀ (by simp [Finset.conj]);
  tfae_finish;

end Logic.IL

end FFL.InterpretabilityLogic

end
