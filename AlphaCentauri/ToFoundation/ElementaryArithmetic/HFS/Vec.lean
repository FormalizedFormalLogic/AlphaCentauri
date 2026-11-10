module

public import AlphaCentauri.ToFoundation.ElementaryArithmetic.HFS.Fixpoint
public import Foundation.FirstOrder.Arithmetic.HFS.Vec

/-!
# Lists in models of $\mathsf{EA}$

The file `Foundation/FirstOrder/Arithmetic/HFS/Vec.lean` on lists coded by iterated pairing in
models of $\mathsf{I}\Sigma_1$, ported to models of $\mathsf{EA}$: `x ∷ v`, the `i`-th element
`v.[i]`, and induction on lists for locally $\Delta_0$ predicates. The formulas `adjoinDef`,
`mkVec₁Def`, `mkVec₂Def` and `nthDef` define the $\mathsf{EA}$ versions.

- [HP98, §V.3]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

open Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

section adjoin

noncomputable scoped instance : Adjoin V V := ⟨(⟪·, ·⟫ + 1)⟩

lemma adjoin_def (x v : V) : x ∷ v = ⟪x, v⟫ + 1 := rfl

@[simp] lemma fstIdx_adjoin (x v : V) : fstIdx (x ∷ v) = x := by simp [adjoin_def, fstIdx]

@[simp] lemma sndIdx_adjoin (x v : V) : sndIdx (x ∷ v) = v := by simp [adjoin_def, sndIdx]

lemma succ_eq_adjoin (x : V) : x + 1 = π₁ x ∷ π₂ x := by simp [adjoin_def]

@[simp] lemma lt_adjoin (x v : V) : x < x ∷ v := by simp [adjoin_def, lt_succ_iff_le]

@[simp] lemma lt_adjoin' (x v : V) : v < x ∷ v := by simp [adjoin_def, lt_succ_iff_le]

@[simp] lemma zero_lt_adjoin (x v : V) : 0 < x ∷ v := by simp [adjoin_def]

@[simp] lemma adjoin_ne_zero (x v : V) : x ∷ v ≠ 0 := by simp [adjoin_def]

@[simp] lemma zero_ne_adjoin (x v : V) : 0 ≠ x ∷ v := by symm; simp [adjoin_def]

lemma nil_or_adjoin (z : V) : z = 0 ∨ ∃ x v, z = x ∷ v := by
  rcases zero_or_succ z with (rfl | ⟨z, rfl⟩)
  · left; rfl
  · right; exact ⟨π₁ z, π₂ z, by simp [succ_eq_adjoin]⟩

@[simp] lemma adjoin_inj (x₁ x₂ v₁ v₂ : V) :
    x₁ ∷ v₁ = x₂ ∷ v₂ ↔ x₁ = x₂ ∧ v₁ = v₂ := by simp [adjoin_def]

lemma adjoin_le_adjoin {x₁ x₂ v₁ v₂ : V} (hx : x₁ ≤ x₂) (hv : v₁ ≤ v₂) :
    x₁ ∷ v₁ ≤ x₂ ∷ v₂ := by simpa [adjoin_def] using pair_le_pair hx hv

instance adjoin_defined : 𝚺ᴬ₀-Function₂ (adjoin : V → V → V) via adjoinDef := .mk fun v ↦ by
  simp_all [adjoinDef, adjoin_def]

instance adjoin_definable : 𝚺ᴬ₀-Function₂ (adjoin : V → V → V) := adjoin_defined.to_definable

instance adjoin_definable' (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₂ (adjoin : V → V → V) := adjoin_definable.of_zero

instance mkVec₁_defined : 𝚺ᴬ₀-Function₁ (fun x : V ↦ ?[x]) via mkVec₁Def := .mk fun v ↦ by
  simp [mkVec₁Def]

instance mkVec₁_definable : 𝚺ᴬ₀-Function₁ (fun x : V ↦ ?[x]) := mkVec₁_defined.to_definable

instance mkVec₁_definable' (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₁ (fun x : V ↦ ?[x]) := mkVec₁_definable.of_zero

instance mkVec₂_defined : 𝚺ᴬ₁-Function₂ (fun x y : V ↦ ?[x, y]) via mkVec₂Def := .mk fun v ↦ by
  simp [mkVec₂Def]

instance mkVec₂_definable : 𝚺ᴬ₁-Function₂ (fun x y : V ↦ ?[x, y]) := mkVec₂_defined.to_definable

instance mkVec₂_definable' (Γ m) : Γᴬ_[m + 1]-Function₂ (fun x y : V ↦ ?[x, y]) :=
  mkVec₂_definable.of_sigmaOne

lemma LocallyDelta0Function.adjoin : LocallyDelta0Function₂ (adjoin : V → V → V) :=
  LocallyDelta0Function.of_definableBoundedFunction
    ⟨⟨‘x y. (x + y + 1) * (x + y + 1) + 1’, fun v ↦ by
      simpa [adjoin_def, sq] using pair_polybound (v 0) (v 1)⟩, adjoin_definable⟩

end adjoin

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic
