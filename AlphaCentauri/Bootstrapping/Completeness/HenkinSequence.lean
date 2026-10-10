module

public import AlphaCentauri.Bootstrapping.Completeness.Henkin

/-!
# The Henkin set

The decision sequence of Henkin's construction exists and is unique in a model of
$\mathsf{PA}$, and the set of formulas decided positively is $\Delta_2$-definable.

## References

- [Lin97, Theorem 6.4]
- [HP98, Theorem I.4.25]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {L : Language} [L.Encodable] [L.LORDefinable] (S : Theory L) [S.Δ₁]

axiom exists_isHenkinContext :
    ∃ c : V → V, IsHenkinContext S c ∧ 𝚫ᴬ_[2]-Function₁[V] c

open Classical in
/-- The contexts of the decision sequence of the Henkin completion of `S`. -/
noncomputable def henkinContext : V → V := Classical.choose (exists_isHenkinContext (V := V) S)

lemma isHenkinContext_henkinContext : IsHenkinContext S (henkinContext S : V → V) :=
  (Classical.choose_spec (exists_isHenkinContext (V := V) S)).1

lemma henkinContext_definable : 𝚫ᴬ_[2]-Function₁[V] (henkinContext S) :=
  (Classical.choose_spec (exists_isHenkinContext (V := V) S)).2

/-- The Henkin set of `S`: the formulas decided positively along the decision sequence. -/
def HenkinSet (x : V) : Prop := HenkinMem S (henkinContext S) x

axiom henkinSet_definable : 𝚫ᴬ_[2]-Predicate[V] (HenkinSet S)

end FFL.FirstOrder.Arithmetic.Bootstrapping
