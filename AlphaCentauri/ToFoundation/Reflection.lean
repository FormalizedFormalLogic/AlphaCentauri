module

public import Foundation.FirstOrder.Incompleteness.Reflection.Local

/-!
# Local reflection over the prenex hierarchy

Local reflection for $\Sigma_{s'}$ or $\Pi_{s'}$ prenex sentences yields local reflection for prenex
sentences of a lower or equal level, since a prenex sentence is provably equivalent to one of a
higher level.
-/

@[expose] public section

open scoped FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment ProvabilityAbstraction

variable {T S : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {Γ Γ' : Polarity} {s s' : ℕ}

lemma provable_localReflectionOn_of_provable_iff {C C' : ArithmeticSentence → Prop} (hTS : T ⪯ S)
    (h : S ⊢* 𝗥𝗳𝗻[C'] T) (hC : ∀ σ, C σ → ∃ σ', C' σ' ∧ T ⊢ σ 🡘 σ') :
    S ⊢* 𝗥𝗳𝗻[C] T := by
  have : 𝗜𝚺₁ ⪯ S := (inferInstance : 𝗜𝚺₁ ⪯ T).trans hTS
  rintro φ ⟨σ, hσ, rfl⟩
  obtain ⟨σ', hσ', he⟩ := hC σ hσ
  have hinst : S ⊢ T.standardProvability.refl σ' :=
    h ((Provability.mem_localReflectionOn_iff _).mpr ⟨σ', hσ', rfl⟩)
  have hext : S ⊢ T.standardProvability σ 🡘 T.standardProvability σ' :=
    WeakerThan.pbl (Provability.ext (𝔅 := T.standardProvability) he)
  have he' : S ⊢ σ 🡘 σ' := hTS.pbl he
  cl_prover [hinst, hext, he']

lemma provable_localReflectionOn_prenexHierarchy_of_le (hTS : T ⪯ S) (hs : s ≤ s')
    (h : S ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s'] T) :
    S ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s] T :=
  provable_localReflectionOn_of_provable_iff hTS h fun _ hσ ↦
    (hσ.exists_eval_iff_of_le hs).imp fun _ H ↦ ⟨H.1, by
      simpa using provable_iff_of_models_iff.{0} (T := T) (n := 0) fun V _ _ e ↦ by
        simpa [models_iff] using H.2 V e Empty.elim⟩

lemma provable_localReflectionOn_prenexHierarchy_of_lt (hTS : T ⪯ S) (hs : s < s')
    (h : S ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].PrenexHierarchy Γ' s'] T) :
    S ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s] T :=
  provable_localReflectionOn_of_provable_iff hTS h fun _ hσ ↦
    (hσ.exists_eval_iff_of_lt Γ' hs).imp fun _ H ↦ ⟨H.1, by
      simpa using provable_iff_of_models_iff.{0} (T := T) (n := 0) fun V _ _ e ↦ by
        simpa [models_iff] using H.2 V e Empty.elim⟩

end FFL.FirstOrder.Arithmetic
