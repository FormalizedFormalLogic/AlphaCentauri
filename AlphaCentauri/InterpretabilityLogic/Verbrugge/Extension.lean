module

public import AlphaCentauri.InterpretabilityLogic.Verbrugge.Basic

/-!
# Generalised Veltman semantics of the extensions of $\mathbf{IL}$

Frame conditions on generalised Veltman models for the principles $\mathsf{P}_0$, $\mathsf{R}$ and
$\mathsf{W}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Verbrugge.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

/-- If $w ≺ x ≺ u ≺[w] V$ and every element of $V$ has a `≺`-successor in $Z$, then
$u \mathrel{≺[x]} Z'$ for some $Z' \subseteq Z$.

- [MV20, §2.4]
-/
class HasP₀ : Prop where
  exists_subset_of_rel_rel_s {w x u : M.World} {V Z : Set M.World} :
    w ≺ x → x ≺ u → u ≺[w] V → (∀ v ∈ V, ∃ z ∈ Z, v ≺ z) → ∃ Z' ⊆ Z, u ≺[x] Z'

/-- The family of sets $C \subseteq \mathrm{R}[x]$ meeting every $Z$ with $u \mathrel{≺[x]} Z$. -/
def choiceSets (x u : M.World) : Set (Set M.World) :=
  {C | (∀ y ∈ C, x ≺ y) ∧ ∀ Z, u ≺[x] Z → (Z ∩ C).Nonempty}

/-- If $w ≺ x ≺ u ≺[w] V$, then every choice set $C$ has $U \subseteq V$ with $x \mathrel{≺[w]} U$
and $\mathrm{R}[U] \subseteq C$.

- [MV20, §2.5]
- [JMMV20, §4.2]
-/
class HasR : Prop where
  exists_subset_of_rel_rel_s {w x u : M.World} {V : Set M.World} :
    w ≺ x → x ≺ u → u ≺[w] V → ∀ C ∈ M.choiceSets x u,
      ∃ U ⊆ V, x ≺[w] U ∧ ∀ y ∈ U, ∀ z, y ≺ z → z ∈ C

/-- If $u \mathrel{≺[w]} V$, then there is $V' \subseteq V$ with $u \mathrel{≺[w]} V'$ such that no
$≺$-successor of an element of $V'$ has $y \mathrel{≺[w]} V$.

- [MV20, §3]
- [JMMV20, §6.4]
-/
class HasW : Prop where
  exists_subset_of_s {w u : M.World} {V : Set M.World} :
    u ≺[w] V → ∃ V' ⊆ V, u ≺[w] V' ∧ ∀ x ∈ V', ∀ y, x ≺ y → ¬y ≺[w] V

end Verbrugge.Model

end FFL.InterpretabilityLogic

end
