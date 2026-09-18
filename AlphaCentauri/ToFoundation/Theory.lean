module

public import Foundation.FirstOrder.LK.Basic
public import Foundation.Meta.ClProver

/-!
# Theories, unions and adjoined sentences

Gaps in Foundation about theories as sets of sentences: union with a fixed theory preserves
relative strength and provable equivalence, refutation transfers along a provable equivalence, and
adjoining a sentence is inconsistent exactly when the theory refutes it.
-/

@[expose] public section

namespace FFL.FirstOrder

open FFL.Entailment

namespace Theory

variable {L : Language} {U S : Theory L}

lemma weakerThan_union_right (h : U ⪯ S) (T : Theory L) : T ∪ U ⪯ T ∪ S :=
  WeakerThan.ofAxm! <| by
    rintro φ (hφ | hφ)
    · exact by_axm (Set.mem_union_left _ hφ)
    · exact WeakerThan.pbl (h.pbl (by_axm hφ))

lemma equiv_union_right (e : U ≊ S) (T : Theory L) : T ∪ U ≊ T ∪ S :=
  Equiv.antisymm
    ⟨weakerThan_union_right e.le T, weakerThan_union_right e.symm.le T⟩

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

lemma of_weakerThan (h : T ⪯ U) : T ⪯[Γ] U := fun _ _ hσ ↦ h.pbl hσ

lemma mono (h : ∀ σ, Γ' σ → Γ σ) (hTU : T ⪯[Γ] U) : T ⪯[Γ'] U := fun σ hσ ↦ hTU σ (h σ hσ)

end WeakerThanOn

end Theory

variable {L : Language} {T : Theory L} {φ ψ : Sentence L} [L.DecidableEq]

lemma provable_neg_iff (e : T ⊢ φ 🡘 ψ) : T ⊢ ∼φ ↔ T ⊢ ∼ψ :=
  ⟨fun h ↦ by cl_prover [e, h], fun h ↦ by cl_prover [e, h]⟩

private lemma inconsistent_insert_iff : Inconsistent (insert φ T) ↔ T ⊢ ∼φ := by
  change Inconsistent (adjoin φ T) ↔ T ⊢ ∼φ
  simpa using (provable_iff_inconsistent_adjoin (𝓢 := T) (φ := ∼φ)).symm

lemma provable_neg_of_inconsistent_insert (h : Inconsistent (insert φ T)) : T ⊢ ∼φ :=
  inconsistent_insert_iff.mp h

lemma inconsistent_insert_of_provable_neg (h : T ⊢ ∼φ) : Inconsistent (insert φ T) :=
  inconsistent_insert_iff.mpr h

end FFL.FirstOrder
