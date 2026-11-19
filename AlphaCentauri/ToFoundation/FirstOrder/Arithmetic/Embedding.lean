module

public import Foundation.FirstOrder.Arithmetic.Basic.Model
public import Foundation.FirstOrder.Tarski.Elementary

/-! # Homomorphisms and embeddings of `ℒₒᵣ`-structures

A homomorphism of `ℒₒᵣ`-structures preserves `0`, `1`, `+` and `*`; an embedding also preserves
and reflects `<`.
-/

@[expose] public section

namespace FFL.FirstOrder.Tarski.Structure

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

end FFL.FirstOrder.Tarski.Structure
