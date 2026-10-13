module

public import Foundation.FirstOrder.Arithmetic.Definability.PrenexDefinable
public import Foundation.FirstOrder.Arithmetic.IOpen.Basic

/-!
# Prenex $\Sigma_1$ definability of existentially quantified relations
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Bounding FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V]

lemma PrenexDefinable.exists_of_sigmaZero {k : ℕ} {R : (Fin k → V) → V → Prop}
    (hR : 𝚺ᴬ₀.Definable fun v : Fin (k + 1) → V ↦ R (fun i ↦ v i.succ) (v 0)) :
    PrenexDefinable 𝚺 1 fun v ↦ ∃ x, R v x := by
  obtain ⟨φ, hφ⟩ := hR
  have h₁ : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 0 φ.val :=
    Bounding.PrenexHierarchy.zero_iff.mpr φ.sigma_prop
  exact ⟨∃¹ φ.val, Bounding.PrenexHierarchy.exs h₁, by intro v; simp [hφ.iff]⟩

private lemma definable_exists_pair [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {k : ℕ} {R : (Fin k → V) → V → V → Prop}
    (hR : 𝚺ᴬ₀.Definable fun v : Fin (k + 2) → V ↦ R (fun i ↦ v i.succ.succ) (v 0) (v 1)) :
    𝚺ᴬ₀.Definable (k := k + 1) fun w ↦
      ∃ y ≤ w 0, ∃ x ≤ w 0, w 0 = ⟪x, y⟫ ∧ R (fun i ↦ w i.succ) x y := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (s := 0)
  have hR₁ : 𝚺ᴬ₀.Definable (k := k + 3) fun w ↦ R (fun i ↦ w i.succ.succ.succ) (w 0) (w 1) :=
    (hR.retraction (Fin.cons 0 (Fin.cons 1 fun i : Fin k ↦ i.succ.succ.succ))).of_iff
      (by intro w; simp)
  have hB : 𝚺ᴬ₀.Definable (k := k + 3) fun w ↦
      w 2 = ⟪w 0, w 1⟫ ∧ R (fun i ↦ w i.succ.succ.succ) (w 0) (w 1) := by
    definability
  have hI : 𝚺ᴬ₀.Definable (k := k + 2) fun u ↦
      ∃ x ≤ u 1, u 1 = ⟪x, u 0⟫ ∧ R (fun i ↦ u i.succ.succ) x (u 0) :=
    (Bounding.HierarchySymbol.Definable.arithmetic_bexs' (P := fun u x ↦
      u 1 = ⟪x, u 0⟫ ∧ R (fun i ↦ u i.succ.succ) x (u 0)) (hB.of_iff (by intro w; simp)) #1).of_iff
      (by intro u; simp)
  exact (Bounding.HierarchySymbol.Definable.arithmetic_bexs' (P := fun w y ↦
      ∃ x ≤ (y :> w) 1, (y :> w) 1 = ⟪x, (y :> w) 0⟫ ∧
        R (fun i ↦ (y :> w) i.succ.succ) x ((y :> w) 0))
    (hI.of_iff (by intro w; simp)) #0).of_iff (by intro w; simp)

lemma PrenexDefinable.exists_exists_of_sigmaZero [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {k : ℕ}
    {R : (Fin k → V) → V → V → Prop}
    (hR : 𝚺ᴬ₀.Definable fun v : Fin (k + 2) → V ↦ R (fun i ↦ v i.succ.succ) (v 0) (v 1)) :
    PrenexDefinable 𝚺 1 fun v ↦ ∃ x y, R v x y := by
  exact (PrenexDefinable.exists_of_sigmaZero
    (R := fun v p ↦ ∃ y ≤ p, ∃ x ≤ p, p = ⟪x, y⟫ ∧ R v x y) (definable_exists_pair hR)).of_iff
    fun v ↦ ⟨fun ⟨x, y, h⟩ ↦ ⟨⟪x, y⟫, y, le_pair_right x y, x, le_pair_left x y, rfl, h⟩,
      fun ⟨_, y, _, x, _, _, h⟩ ↦ ⟨x, y, h⟩⟩

lemma PrenexDefinable.exists_exists_exists_of_sigmaZero [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {k : ℕ}
    {R : (Fin k → V) → V → V → V → Prop}
    (hR : 𝚺ᴬ₀.Definable fun v : Fin (k + 3) → V ↦
      R (fun i ↦ v i.succ.succ.succ) (v 0) (v 1) (v 2)) :
    PrenexDefinable 𝚺 1 fun v ↦ ∃ x y z, R v x y z := by
  have hS := definable_exists_pair
    (R := fun u x y ↦ R (fun i ↦ u i.succ) x y (u 0)) (hR.of_iff (by intro w; simp))
  exact (PrenexDefinable.exists_exists_of_sigmaZero
    (R := fun v p t ↦ ∃ y ≤ p, ∃ x ≤ p, p = ⟪x, y⟫ ∧ R v x y t) hS).of_iff
    fun v ↦ ⟨fun ⟨x, y, z, h⟩ ↦ ⟨⟪x, y⟫, z, y, le_pair_right x y, x, le_pair_left x y, rfl, h⟩,
      fun ⟨_, t, y, _, x, _, _, h⟩ ↦ ⟨x, y, t, h⟩⟩

end FFL.FirstOrder.Arithmetic
