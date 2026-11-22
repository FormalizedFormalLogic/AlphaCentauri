module

public import Foundation.FirstOrder.Arithmetic.Basic.Model
public import Foundation.FirstOrder.LK.Completeness
public import Foundation.FirstOrder.Tarski.Elementary

/-!
# Models of arithmetic

Counter-models for unprovable sentences, and homomorphisms and embeddings of `ℒₒᵣ`-structures.
-/

@[expose] public section

/-! ## Counter-models for unprovable arithmetic sentences

The converse of `FFL.FirstOrder.Arithmetic.complete`: an arithmetic sentence a theory does not
prove fails in some model of that theory.
-/

namespace FFL.FirstOrder
namespace Arithmetic

/-- A sentence unprovable in `T` fails in some model of `T`. -/
lemma exists_countermodel_of_unprovable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T]
    {σ : ArithmeticSentence} (h : T ⊬ σ) :
    ∃ (M : Type) (_ : ORingStructure M) (_ : M↓[ℒₒᵣ] ⊧* T), ¬M↓[ℒₒᵣ] ⊧ σ := by
  by_contra! hc
  exact h (complete T σ fun M _ _ ↦ hc M ‹_› ‹_›)

end Arithmetic

/-! ## Homomorphisms and embeddings of `ℒₒᵣ`-structures

A homomorphism of `ℒₒᵣ`-structures preserves `0`, `1`, `+` and `*`; an embedding also preserves
and reflects `<`.
-/

namespace Tarski.Structure

open Arithmetic

variable {M N F : Type*} [ORingStructure M] [ORingStructure N] [FunLike F M N]

namespace HomClass

variable [HomClass F ℒₒᵣ M N] (f : F)

@[simp] lemma map_zero : f 0 = 0 := by
  simpa [Function.comp_def] using HomClass.func f Language.Zero.zero ![]

@[simp] lemma map_one : f 1 = 1 := by
  simpa [Function.comp_def] using HomClass.func f Language.One.one ![]

@[simp] lemma map_add (x y : M) : f (x + y) = f x + f y := by
  simpa [Function.comp_def] using HomClass.func f Language.Add.add ![x, y]

@[simp] lemma map_mul (x y : M) : f (x * y) = f x * f y := by
  simpa [Function.comp_def] using HomClass.func f Language.Mul.mul ![x, y]

end HomClass

@[simp] lemma EmbeddingClass.map_lt_map_iff [EmbeddingClass F ℒₒᵣ M N] (f : F) {x y : M} :
    f x < f y ↔ x < y := by
  simpa [Function.comp_def] using EmbeddingClass.rel f Language.LT.lt ![x, y]

end Tarski.Structure

end FFL.FirstOrder
