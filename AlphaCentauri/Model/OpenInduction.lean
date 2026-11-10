module

public import AlphaCentauri.Schemata.ZRing

/-!
# Models of open induction extending $\mathbb{Z}$-rings

Wilkie's extension theorem: every discretely ordered $\mathbb{Z}$-ring embeds into a discretely
ordered ring satisfying open induction.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- Every model of $\mathsf{ZR}$ embeds into a model of $\mathsf{IOpen}$.
- [Wil78, Lemma 3.2]
- [BO96, Theorem 1.2]
- [Raf10, Wilkie's Extension Theorem] -/
axiom exists_embedding_models_IOpen (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* ZRing] :
    ∃ (N : Type) (_ : ORingStructure N), N↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 ∧ Nonempty (M ↪ₛ[ℒₒᵣ] N)

end FFL.FirstOrder.Arithmetic
