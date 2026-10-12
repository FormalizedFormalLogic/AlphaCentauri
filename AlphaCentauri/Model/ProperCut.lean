module

public import AlphaCentauri.Model.Cut
public import Foundation.FirstOrder.Arithmetic.Definability.PrenexDefinable
public import Foundation.FirstOrder.Arithmetic.Schema.DeltaInduction

/-! # Proper cuts

No proper cut is definable by a $\Sigma_0$ formula with parameters in a model of `𝗜𝚺₀`, and no
model of `𝗜𝚫 s` has a proper cut whose membership relation and complement are both definable by
prenex $\Sigma_s$ formulas with parameters.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Semiformula Tarski.Structure

variable {M : Type*} [ORingStructure M]

/-- A cut is proper when it contains `0` and omits some element.
- [HP98, Definition IV.1.14]
- [Sla04, §1.1] -/
def Cut.Proper (I : Cut M) : Prop := (0 : M) ∈ I.carrier ∧ ∃ c, c ∉ I.carrier

/-- A cut definable by a $\Sigma_0$ formula with parameters is not proper.
- [HP98, Observation IV.1.15] -/
lemma Cut.not_proper_of_definable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] (I : Cut M)
    (hI : 𝚺ᴬ₀.DefinablePred (· ∈ I.carrier)) : ¬I.Proper := by
  rintro ⟨h0, c, hc⟩
  exact hc <| ISigma0.succ_induction (P := (· ∈ I.carrier)) hI h0 (fun _ hx ↦ I.succ_mem hx) c

/-- A proper cut whose membership relation and complement are both definable by prenex $\Sigma_s$
formulas with parameters refutes $\Delta_s$ induction.
- [Sla04, §1.1] -/
lemma not_models_IDelta_of_proper_cut (I : Cut M) (s : ℕ) (hI : I.Proper)
    (hσ : PrenexDefinablePred 𝚺 s (· ∈ I.carrier))
    (hπ : PrenexDefinablePred 𝚺 s (· ∉ I.carrier)) : ¬M↓[ℒₒᵣ] ⊧* 𝗜𝚫 s := by
  intro hM
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_of_ss hM Set.subset_union_left
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (s := 0)
  have : M↓[ℒₒᵣ] ⊧* DeltaInductionScheme (ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 s) :=
    models_of_ss hM Set.subset_union_right
  obtain ⟨e₁, φ, hφ, hφe⟩ := PrenexDefinable.exists_eval_iff hσ
  obtain ⟨e₂, ψ, hψ, hψe⟩ := PrenexDefinable.exists_eval_iff hπ
  have heven : ∀ n : ℕ, 2 * n % 2 = 0 := by intro n; omega
  have hodd : ∀ n : ℕ, (2 * n + 1) % 2 ≠ 0 := by intro n; omega
  have hhalf₁ : ∀ n : ℕ, 2 * n / 2 = n := by intro n; omega
  have hhalf₂ : ∀ n : ℕ, (2 * n + 1) / 2 = n := by intro n; omega
  let e : ℕ → M := fun n ↦ if n % 2 = 0 then e₁ (n / 2) else e₂ (n / 2)
  have hφ' : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 s (Rew.rewriteMap (fun n : ℕ ↦ 2 * n) ▹ φ) :=
    hφ.rew _
  have hψ' : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 s (Rew.rewriteMap (fun n : ℕ ↦ 2 * n + 1) ▹ ψ) :=
    hψ.rew _
  have h₁ : ∀ x : M, (Rew.rewriteMap (fun n : ℕ ↦ 2 * n) ▹ φ).Eval ![x] e ↔ x ∈ I.carrier := by
    intro x
    simpa [Semiformula.eval_rewriteMap, e, heven, hhalf₁] using (hφe ![x]).symm
  have h₂ : ∀ x : M, (Rew.rewriteMap (fun n : ℕ ↦ 2 * n + 1) ▹ ψ).Eval ![x] e ↔ x ∉ I.carrier := by
    intro x
    simpa [Semiformula.eval_rewriteMap, e, hodd, hhalf₂] using (hψe ![x]).symm
  obtain ⟨h0, c, hc⟩ := hI
  have hind := (models_deltaInd_iff _ _).mp
    (Theory.models (T := DeltaInductionScheme (ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 s)) M
      (mem_DeltaInductionScheme_of_mem hφ' hψ')) e
    (fun x ↦ by rw [h₁ x, h₂ x, not_not])
    ((h₁ 0).mpr h0) (fun x hx ↦ (h₁ (x + 1)).mpr (I.succ_mem ((h₁ x).mp hx)))
  exact hc ((h₁ c).mp (hind c))

end FFL.FirstOrder.Arithmetic
