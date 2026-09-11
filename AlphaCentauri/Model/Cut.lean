module

public import AlphaCentauri.Model.Basic
public import Foundation.FirstOrder.Arithmetic.Schemata

/-! # Cuts

A cut of an `ℒₒᵣ`-structure `M` is a downward closed subset closed under the operations of the
language; `M` is an end extension of it.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Semiformula Structure

variable {M : Type u} [ORingStructure M]

/-- A cut of `M`: a subset closed under the operations of `ℒₒᵣ` and downward closed under `<`.
- [HP98, Definition IV.1.14] -/
structure Cut (M : Type u) [ORingStructure M] where
  carrier : Set M
  zero_mem : (0 : M) ∈ carrier
  one_mem : (1 : M) ∈ carrier
  add_mem {a b : M} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  mul_mem {a b : M} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  mem_of_lt {a b : M} : a < b → b ∈ carrier → a ∈ carrier

namespace Cut

variable (I : Cut M)

instance oringStructure : ORingStructure I.carrier where
  zero := ⟨0, I.zero_mem⟩
  one := ⟨1, I.one_mem⟩
  add a b := ⟨a.1 + b.1, I.add_mem a.2 b.2⟩
  mul a b := ⟨a.1 * b.1, I.mul_mem a.2 b.2⟩
  lt a b := a.1 < b.1

/-- `M` is an end extension of each of its cuts.
- [HP98, Definition IV.1.3(2)] -/
@[instance_reducible]
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
lemma endExtension_emb (x : I.carrier) : I.endExtension.emb x = x.val := rfl

end Cut

namespace EndExtension

variable {N : Type u} [hMN : M ⊆ₑ N]

private lemma eval_of_endExtension [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {φ : ArithmeticSemiformula ℕ 1}
    (hφ : Hierarchy 𝚺 0 φ)
    (v : ℕ → M) (h0 : φ.Eval ![0] v) (hs : ∀ x, φ.Eval ![x] v → φ.Eval ![x + 1] v) (a : M) :
    φ.Eval ![a] v := by
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := hMN.models_peanoMinus
  have h₁ : ∀ x : M, φ.Eval ![x] v ↔ φ.Eval ![hMN.emb x] (hMN.emb ∘ v) := by
    intro x;
    simpa [Matrix.comp_vecCons'', Matrix.empty_eq] using
      absolute_of_Delta0 (T := 𝗣𝗔⁻) hφ M N ![x] v
  have h₂ : ∀ y : N, y < hMN.emb a + 1 → φ.Eval ![y] (hMN.emb ∘ v) := by
    refine InductionScheme.succ_induction (C := Hierarchy 𝚺 0)
      ⟨(hMN.emb a + 1) :>ₙ fun j ↦ hMN.emb (v j),
        “#0 < &0” 🡒 (Rew.rewriteMap Nat.succ ▹ φ), by simp [hφ],
        by intro x; simp [Semiformula.eval_rewriteMap, Function.comp_def]⟩
      (by intro _; simpa using (h₁ 0).mp h0) ?_
    intro y ih hy
    have h₃ : y < hMN.emb a := lt_of_lt_of_le (lt_add_one y) (lt_succ_iff_le.mp hy)
    obtain ⟨x, rfl⟩ := hMN.mem_range_of_lt h₃
    simpa using (h₁ (x + 1)).mp (hs x ((h₁ x).mpr (ih (lt_trans h₃ (lt_add_one _)))))
  exact (h₁ a).mpr (h₂ (hMN.emb a) (by simp))

/-- A structure with an end extension modelling `𝗜𝚺₀` is itself a model of `𝗜𝚺₀`.
- [HP98, Remark IV.1.21(2)] -/
theorem models_ISigma0 [hN : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
  simp only [Semantics.ModelsSet.union_iff, InductionScheme];
  and_intros;
  . exact hMN.models_peanoMinus
  . apply Semantics.ModelsSet.setOf_iff.mpr;
    rintro _ ⟨φ, hφ, rfl⟩
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs]
      using hMN.eval_of_endExtension hφ

end EndExtension

end FFL.FirstOrder.Arithmetic
