module

public import AlphaCentauri.Model.EndExtension

/-! # Cuts

A cut of an `ℒₒᵣ`-structure `M` is a subset closed under successor and downward closed under `<`.
A closed cut, one closed under the operations of the language, is a substructure of `M`, and `M`
is an end extension of it.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic


open Semiformula Tarski.Structure

universe u v

variable {M : Type u} [ORingStructure M]

/-- A cut of `M`: a subset closed under successor and downward closed under `<`.
- [HP98, Definition IV.1.14] -/
structure Cut (M : Type u) [ORingStructure M] where
  carrier : Set M
  succ_mem {a : M} : a ∈ carrier → a + 1 ∈ carrier
  mem_of_lt {a b : M} : a < b → b ∈ carrier → a ∈ carrier

/-- A cut closed under the operations of `ℒₒᵣ`, hence a substructure of `M`.
- [HP98, Definition IV.2.8(2)] -/
structure ClosedCut (M : Type u) [ORingStructure M] extends Cut M where
  zero_mem : (0 : M) ∈ carrier
  one_mem : (1 : M) ∈ carrier
  add_mem {a b : M} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  mul_mem {a b : M} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier

namespace ClosedCut

variable (I : ClosedCut M)

instance oringStructure : ORingStructure I.carrier where
  zero := ⟨0, I.zero_mem⟩
  one := ⟨1, I.one_mem⟩
  add a b := ⟨a.1 + b.1, I.add_mem a.2 b.2⟩
  mul a b := ⟨a.1 * b.1, I.mul_mem a.2 b.2⟩
  lt a b := a.1 < b.1

/-- `M` is an end extension of each of its closed cuts.
- [HP98, Definition IV.1.3(2)] -/
def endExtension : I.carrier ⊆ₑ M where
  emb := {
    toFun := Subtype.val,
    func' f v := by cases f <;> rfl
    rel' r _ := by cases r; exacts [congrArg Subtype.val, id]
    toFun_inj := Subtype.val_injective
    rel_inv' r _ := by cases r; exacts [Subtype.ext, id]
  }
  mem_range_of_lt {a b} h := ⟨⟨b, I.mem_of_lt h a.2⟩, rfl⟩

@[simp]
lemma endExtension_apply (x : I.carrier) : I.endExtension x = x.val := rfl

end ClosedCut

end FFL.FirstOrder.Arithmetic
