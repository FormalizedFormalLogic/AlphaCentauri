module

public import ProvabilityLogic.ProvabilityLogic.Interpret

@[expose] public section
/-!
# Realizations of finite conjunctions
-/

namespace Formula

open FFL FFL.FirstOrder FFL.FirstOrder.ProvabilityAbstraction FFL.Entailment

variable {L : Language} [L.ReferenceableBy L] [L.DecidableEq] {T₀ T : Theory L}
  {𝔅 : Provability T₀ T} {α : Type*} {f : Realization α L}

lemma interpret_conj_left {Γ : FormulaList α} {B : Formula α} (hB : B ∈ Γ) :
    T ⊢ (FormulaList.conj Γ).interpret f 𝔅 🡒 B.interpret f 𝔅 := by
  induction Γ using FormulaList.conj.induct with
  | case1 => simp at hB
  | case2 C =>
    obtain rfl : B = C := by simpa using hB
    cl_prover
  | case3 C D Γ ih =>
    simp only [FormulaList.conj, Formula.interpret]
    rcases List.mem_cons.mp hB with rfl | hB
    · cl_prover
    · cl_prover [ih hB]

lemma interpret_conj_right {Γ : FormulaList α} {φ : Sentence L}
    (h : ∀ B ∈ Γ, T ⊢ φ 🡒 B.interpret f 𝔅) :
    T ⊢ φ 🡒 (FormulaList.conj Γ).interpret f 𝔅 := by
  induction Γ using FormulaList.conj.induct with
  | case1 => simp only [FormulaList.conj, Formula.interpret]; cl_prover
  | case2 C => simpa using h C (by simp)
  | case3 C D Γ ih =>
    have ih := ih fun B hB ↦ h B (List.mem_cons_of_mem _ hB)
    have hC := h C (by simp)
    simp only [FormulaList.conj, Formula.interpret] at ih ⊢
    cl_prover [ih, hC]

end Formula
