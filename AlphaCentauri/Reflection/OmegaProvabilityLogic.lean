module

public import AlphaCentauri.Reflection.IteratedConsistency
public import AlphaCentauri.Reflection.Unboundedness

@[expose] public section
/-!
# The provability logic of $T_\omega$

The provability logic of `T` relative to $T_\omega = T + \{\neg\Box_T^{n + 1}\bot\}_n$ is `𝐀`
whenever $T_\omega$ is consistent.

- [AB05, Example 59]
-/

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.Arithmetic

variable {α : Type*} {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- If $T_\omega$ is consistent, the provability logic of `T` relative to $T_\omega$ is `𝐀`.
- [AB05, Example 59] -/
theorem provabilityLogic_addAlpha_univ_eq_A [Consistent (T.addAlpha T Set.univ)] :
    T.provabilityLogicRelativeTo (T.addAlpha T Set.univ) (α := α) = 𝐀 := by
  have hT := trace_provabilityLogic_addAlpha_univ (T := T) (U := T) (α := α)
  apply Logic.weakerThan_antisymm _ (A_weakerThan_provabilityLogic hT)
  constructor
  intro A hA
  by_contra hAA
  have h : T.addAlpha T Set.univ ⊢* T.standardProvability.reflOn (Hierarchy 𝚺 1) :=
    provable_localReflectionOn_sigma1_of_mem_of_not_A hT (Logic.provable_iff_mem.mp hA) hAA
  obtain ⟨U, _, hU, e⟩ := exists_strictPi1_axiomatization_addAlpha (T := T)
  have h' : T.addAlpha T Set.univ ⊢* 𝗥𝗳𝗻[StrictHierarchy (Polarity.alt 𝚷) 1] T := fun hσ ↦
    h <| T.standardProvability.localReflectionOn_mono (fun _ hσ ↦ hσ.hierarchy) hσ
  exact (inconsistent_of_provable_localReflectionOn_union (n := 0) hU e h').not_con
    ‹Consistent (T.addAlpha T Set.univ)›

end FFL.ProvabilityLogic
