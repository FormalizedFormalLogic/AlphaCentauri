module

public import Foundation.ProvabilityLogic.Arithmetic.Interpret
public import Foundation.ProvabilityLogic.Kripke.Basic

@[expose] public section
/-!
# Finite conjunctions of modal formulas
-/

namespace FFL.ProvabilityLogic

section Kripke

open Kripke.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Kripke.Model κ α} {x : M.World}

lemma Kripke.Model.World.forces_conj₂ {L : List (Formula α)} :
    x ⊩[M] ⋀L ↔ ∀ B ∈ L, x ⊩[M] B := by
  induction L using List.induction_with_singleton with
  | hnil => simp
  | hsingle => simp
  | hcons C L hL ih => simp [List.conj₂_cons_nonempty hL, forces_and, ih]

end Kripke

section interpret

open FFL.FirstOrder FFL.FirstOrder.ProvabilityAbstraction FFL.Entailment

variable {L : Language} [L.ReferenceableBy L] [L.DecidableEq] {T₀ T : Theory L}
  {𝔅 : Provability T₀ T} {α : Type*} {f : Realization α L}

lemma interpret_conj_left {Γ : List (Formula α)} {B : Formula α} (hB : B ∈ Γ) :
    T ⊢ (⋀Γ).interpret f 𝔅 🡒 B.interpret f 𝔅 := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp at hB
  | hsingle a =>
    obtain rfl : B = a := by simpa using hB
    simp only [List.conj₂_singleton]
    cl_prover
  | hcons C Γ hΓ ih =>
    rw [List.conj₂_cons_nonempty hΓ]
    simp only [Formula.interpret] at ih ⊢
    rcases List.mem_cons.mp hB with rfl | hB
    · cl_prover
    · cl_prover [ih hB]

lemma interpret_conj_right {Γ : List (Formula α)} {φ : Sentence L}
    (h : ∀ B ∈ Γ, T ⊢ φ 🡒 B.interpret f 𝔅) :
    T ⊢ φ 🡒 (⋀Γ).interpret f 𝔅 := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp only [List.conj₂_nil, Formula.interpret]; cl_prover
  | hsingle a => simpa using h a (by simp)
  | hcons C Γ hΓ ih =>
    have ih := ih fun B hB ↦ h B (List.mem_cons_of_mem _ hB)
    have hC := h C (by simp)
    rw [List.conj₂_cons_nonempty hΓ]
    simp only [Formula.interpret] at ih ⊢
    cl_prover [ih, hC]

end interpret

end FFL.ProvabilityLogic

end
