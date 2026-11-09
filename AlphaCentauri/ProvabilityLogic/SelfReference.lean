module

public import Foundation.FirstOrder.Incompleteness.Löb

/-!
# Irreducibly self-referential sentences

Every sentence of a $\Sigma_1$-sound theory containing $\mathsf{I}\Sigma_1$ is irreducibly
self-referential.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping ProvabilityAbstraction

/-- A sentence $\varphi$ is irreducibly self-referential over $T$ if there is a formula $\chi(x)$
such that for every sentence $\psi$, the conditions $T \vdash \varphi \leftrightarrow \psi$,
$T \vdash \psi \leftrightarrow \chi(\ulcorner\psi\urcorner)$ and
$T \vdash \chi(\ulcorner\psi\urcorner) \leftrightarrow \varphi$ are equivalent.
- [Sch22] -/
def IrreduciblySelfReferential (T : ArithmeticTheory) (φ : ArithmeticSentence) : Prop :=
  ∃ χ : ArithmeticSemisentence 1, ∀ ψ : ArithmeticSentence,
    (T ⊢ φ 🡘 ψ ↔ T ⊢ ψ 🡘 χ/[⌜ψ⌝]) ∧ (T ⊢ ψ 🡘 χ/[⌜ψ⌝] ↔ T ⊢ χ/[⌜ψ⌝] 🡘 φ)

section

variable (T : ArithmeticTheory) [T.Δ₁]

/-- The formula
$\varphi \leftrightarrow \mathrm{Pr}_T(\ulcorner x \leftrightarrow \varphi\urcorner)$. -/
noncomputable def iffProvabilityWitness (φ : ArithmeticSentence) : ArithmeticSemisentence 1 :=
  “x. !φ ↔ ∀ y, !(iffGraph ℒₒᵣ) y x ↑⌜φ⌝ → !(provable T).val y”

lemma iffProvabilityWitness_iff (φ ψ : ArithmeticSentence) :
    𝗜𝚺₁ ⊢ (iffProvabilityWitness T φ)/[⌜ψ⌝] 🡘 (φ 🡘 provabilityPred T (ψ 🡘 φ)) :=
  complete.{0} 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    suffices V ⊧/![] ((iffProvabilityWitness T φ)/[⌜ψ⌝]) ↔
        (V ⊧/![] φ ↔ Provable T (⌜ψ 🡘 φ⌝ : V)) by
      simpa [models_iff, provabilityPred, Matrix.constant_eq_singleton,
        (Provable.defined (V := V) (T := T)).df]
    have hq := Rew.q_bvar_succ
      (ω := Rew.subst (L := ℒₒᵣ) ![(⌜ψ⌝ : Semiterm ℒₒᵣ Empty 0)]) (0 : Fin 1)
    have e : (⌜ψ 🡘 φ⌝ : V) = iff ℒₒᵣ ⌜ψ⌝ ⌜φ⌝ := by
      simp [Sentence.quote_def, Semiformula.quote_def]
    simp at hq
    simp [iffProvabilityWitness, Semiformula.eval_rew, Function.comp_def, hq, e,
      Matrix.empty_eq (fun _ => _)]

variable {T} [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- Every sentence is irreducibly self-referential over a $\Sigma_1$-sound theory containing
$\mathsf{I}\Sigma_1$.
- [Sch22] -/
theorem irreduciblySelfReferential (φ : ArithmeticSentence) :
    IrreduciblySelfReferential T φ := by
  use iffProvabilityWitness T φ
  intro ψ
  have hW : T ⊢ (iffProvabilityWitness T φ)/[⌜ψ⌝] 🡘 (φ 🡘 provabilityPred T (ψ 🡘 φ)) :=
    Entailment.WeakerThan.pbl (iffProvabilityWitness_iff T φ ψ)
  have hB : T ⊢ φ 🡘 ψ → T ⊢ provabilityPred T (ψ 🡘 φ) := fun h ↦
    Entailment.WeakerThan.pbl <| provable_D1 (T := T) (by cl_prover [h])
  have h₁ : T ⊢ φ 🡘 ψ → T ⊢ ψ 🡘 (iffProvabilityWitness T φ)/[⌜ψ⌝] := by
    intro h
    cl_prover [h, hW, hB h]
  have h₂ : T ⊢ φ 🡘 ψ → T ⊢ (iffProvabilityWitness T φ)/[⌜ψ⌝] 🡘 φ := by
    intro h
    cl_prover [hW, hB h]
  have h₃ : T ⊢ ψ 🡘 (iffProvabilityWitness T φ)/[⌜ψ⌝] → T ⊢ φ 🡘 ψ := by
    intro h
    have : T ⊢ provabilityPred T (ψ 🡘 φ) 🡒 (ψ 🡘 φ) := by cl_prover [h, hW]
    have := löb_theorem this
    cl_prover [this]
  have h₄ : T ⊢ (iffProvabilityWitness T φ)/[⌜ψ⌝] 🡘 φ → T ⊢ φ 🡘 ψ := by
    intro h
    have : T ⊢ provabilityPred T (ψ 🡘 φ) := by cl_prover [h, hW]
    have := provable_sound (U := T) this
    cl_prover [this]
  tauto

end

end FFL.FirstOrder.Arithmetic
