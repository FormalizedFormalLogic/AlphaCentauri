module

public import Foundation.FirstOrder.LK.Basic

/-!
# Relative strength of theories on a class of sentences

Companion of Foundation's `Theory`: `T ⪯[Γ] U` says that `U` proves every `Γ`-sentence that `T`
proves.
-/

@[expose] public section

namespace FFL.FirstOrder

open FFL.Entailment

namespace Theory

variable {L : Language}

/-- `T ⪯[Γ] U`: every sentence satisfying `Γ` that `T` proves is provable in `U`. The literature's
"`U` is `Γ`-conservative over `T`" is `U ⪯[Γ] T`.
- [Bek99, §2] -/
def WeakerThanOn (Γ : Sentence L → Prop) (T U : Theory L) : Prop :=
  ∀ σ, Γ σ → T ⊢ σ → U ⊢ σ

@[inherit_doc] notation:40 T:41 " ⪯[" Γ "] " U:41 => Theory.WeakerThanOn Γ T U

namespace WeakerThanOn

variable {Γ Γ' : Sentence L → Prop} {T U S : Theory L}

@[simp, refl] lemma refl (T : Theory L) (Γ : Sentence L → Prop) : T ⪯[Γ] T := fun _ _ h ↦ h

@[trans] lemma trans (h₁ : T ⪯[Γ] U) (h₂ : U ⪯[Γ] S) : T ⪯[Γ] S :=
  fun σ hσ h ↦ h₂ σ hσ (h₁ σ hσ h)

lemma mono (h : ∀ σ, Γ' σ → Γ σ) (hTU : T ⪯[Γ] U) : T ⪯[Γ'] U := fun σ hσ ↦ hTU σ (h σ hσ)

end WeakerThanOn

end Theory

end FFL.FirstOrder
