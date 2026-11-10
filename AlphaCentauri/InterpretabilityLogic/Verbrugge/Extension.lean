module

public import AlphaCentauri.InterpretabilityLogic.Verbrugge.Basic

/-!
# Generalised Veltman semantics of the extensions of $\mathbf{IL}$

Frame conditions on generalised Veltman models for the principles $\mathsf{R}$ and $\mathsf{W}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Verbrugge.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

/-- The family of sets $C \subseteq \mathrm{R}[x]$ meeting every $Z$ with $u \mathrel{≺[x]} Z$. -/
def choiceSets (x u : M.World) : Set (Set M.World) :=
  {C | (∀ y ∈ C, x ≺ y) ∧ ∀ Z, u ≺[x] Z → (Z ∩ C).Nonempty}

/-- If $w ≺ x ≺ u ≺[w] V$, then every choice set $C$ has $U \subseteq V$ with $x \mathrel{≺[w]} U$
and $\mathrm{R}[U] \subseteq C$.

- [MV20, Section 2.5]
- [JMMV20, Section 5.6.5]
-/
class HasR : Prop where
  exists_subset_of_rel_rel_s {w x u : M.World} {V : Set M.World} :
    w ≺ x → x ≺ u → u ≺[w] V → ∀ C ∈ M.choiceSets x u,
      ∃ U ⊆ V, x ≺[w] U ∧ ∀ y ∈ U, ∀ z, y ≺ z → z ∈ C

/-- If $u \mathrel{≺[w]} V$, then there is $V' \subseteq V$ with $u \mathrel{≺[w]} V'$ such that no
$≺$-successor of an element of $V'$ has $y \mathrel{≺[w]} V$.

- [MV20, Section 2.5]
- [JMMV20, Section 5.6.5]
-/
class HasW : Prop where
  exists_subset_of_s {w u : M.World} {V : Set M.World} :
    u ≺[w] V → ∃ V' ⊆ V, u ≺[w] V' ∧ ∀ x ∈ V', ∀ y, x ≺ y → ¬y ≺[w] V

end Verbrugge.Model

end FFL.InterpretabilityLogic

end
