module

public import AlphaCentauri.ProvablyTotal.Basic
public import AlphaCentauri.Model.InitialSegment
public import AlphaCentauri.Vorspiel.Completeness
public import AlphaCentauri.Vorspiel.ConstantExtension
public import Foundation.FirstOrder.Ultraproduct

/-!
# Parikh's theorem

A $\Delta_0$ totality proved by `𝗜𝚺₀` is already provable in bounded form, so an `𝗜𝚺₀`-provably
total function with a $\Delta_0$ graph is bounded by a term.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Semiformula

variable {k : ℕ}

section

variable (φ : ArithmeticSemisentence (k + 1))

/-- `𝗜𝚺₀` in the language with `k` new constants, together with the statement that no witness for
`φ` at the constants lies below any of the first `n` closed terms. -/
private def unboundedTheory (n : ℕ) : Theory (Language.oRingConst k) :=
  𝗘𝗤 (Language.oRingConst k)
    ∪ Semiformula.lMap (Language.Hom.add₁ ℒₒᵣ (Language.constant (Fin k))) '' 𝗜𝚺₀
    ∪ (fun t : ClosedSemiterm ℒₒᵣ k ↦ lift ((∼φ).ballLT t)) '' {t | Encodable.encode t < n}

private lemma unboundedTheory_cumulative : Cumulative (unboundedTheory φ) := fun _ ↦
  Set.union_subset_union_right _ <| Set.image_mono fun _ ht ↦ Nat.lt_succ_of_lt ht

private lemma satisfiable_unboundedTheory
    (hc : ∀ t : ClosedSemiterm ℒₒᵣ k, ¬𝗜𝚺₀ ⊢ ∀¹* φ.bexsLT t) (n : ℕ) :
    Satisfiable (unboundedTheory φ n) := by
  obtain ⟨M, _, _, hM⟩ := exists_countermodel_of_unprovable (hc (dominatingTerm k n))
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀)
  obtain ⟨a, ha⟩ : ∃ a : Fin k → M, ∀ y < (dominatingTerm k n).valb a, ¬φ.Evalb (y :> a) := by
    simpa [models_iff, eval_allClosure, eval_bexsLT] using hM
  refine ⟨strucOfTuple M a, Semantics.modelsSet_iff.mpr ?_⟩
  rintro σ ((hσ | hσ) | ⟨t, ht, rfl⟩)
  · exact Semantics.modelsSet_iff.mp (strucOfTuple_models_eq M a) hσ
  · exact Semantics.modelsSet_iff.mp (strucOfTuple_models_lMap_image M a inferInstance) hσ
  · rw [strucOfTuple_models_lift_iff]
    simp only [eval_ballLT, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
    exact fun y hy ↦ ha y (lt_of_lt_of_le hy (valb_le_valb_dominatingTerm ht a))

end

section

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (c : Fin k → M)

/-- The elements of `M` bounded by the value at `c` of some closed term. -/
private def termSegment : InitialSegment M where
  carrier := {x | ∃ t : ClosedSemiterm ℒₒᵣ k, x ≤ t.valb c}
  zero_mem := ⟨‘0’, by simp⟩
  one_mem := ⟨‘1’, by simp⟩
  add_mem := fun ⟨s, hs⟩ ⟨t, ht⟩ ↦ ⟨‘!!s + !!t’, by simpa using add_le_add hs ht⟩
  mul_mem := fun ⟨s, hs⟩ ⟨t, ht⟩ ↦ ⟨‘!!s * !!t’, by
    simpa using mul_le_mul hs ht (by simp) (by simp)⟩
  mem_of_lt := fun hab ⟨t, ht⟩ ↦ ⟨t, le_trans hab.le ht⟩

private lemma mem_termSegment (i : Fin k) : c i ∈ (termSegment c).carrier :=
  ⟨Semiterm.bvar i, by simp⟩

end

section

variable (φ : ArithmeticSemisentence (k + 1)) {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]

private lemma exists_witness_in_segment (I : InitialSegment M) (hφ : Hierarchy 𝚺 0 φ)
    (h : 𝗜𝚺₀ ⊢ ∀¹* ∃¹ φ) (e : Fin k → ↥I.carrier) :
    ∃ b ∈ I.carrier, φ.Evalb (b :> fun i ↦ (e i : M)) := by
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀)
  have hN : I.endExtension↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀)
  have : I.endExtension↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory hN
  have hK : (↥I.carrier)↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := I.endExtension.models_ISigma0
  have : (↥I.carrier)↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory hK
  have h₁ : ∀ w : Fin k → ↥I.carrier, ∃ b, φ.Evalb (b :> w) := by
    simpa [models_iff, eval_allClosure] using
      consequence_iff'.mp (Theory.Proof.sound h) (↥I.carrier)
  obtain ⟨b, hb⟩ := h₁ e
  refine ⟨b, b.2, ?_⟩
  have h₂ := (absolute_of_deltaZero (T := 𝗣𝗔⁻) hφ (↥I.carrier) I.endExtension
    (b :> e) Empty.elim).mp hb
  have h₃ : ⇑I.endExtension.emb ∘ e = fun i ↦ ((e i : M)) := rfl
  simp only [Matrix.comp_vecCons'', Empty.eq_elim, h₃] at h₂
  exact h₂

private lemma false_of_unbounded (hφ : Hierarchy 𝚺 0 φ) (h : 𝗜𝚺₀ ⊢ ∀¹* ∃¹ φ) (c : Fin k → M)
    (H : ∀ (t : ClosedSemiterm ℒₒᵣ k) (y : M), y < t.valb c → ¬φ.Evalb (y :> c)) : False := by
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀)
  obtain ⟨b, ⟨t, ht⟩, hb⟩ :=
    exists_witness_in_segment φ (termSegment c) hφ h fun i ↦ ⟨c i, mem_termSegment c i⟩
  exact H ‘!!t + 1’ b (by simpa using lt_succ_iff_le.mpr ht) (by simpa using hb)

end

/-- **Parikh's theorem**: a totality `𝗜𝚺₀` proves for a $\Delta_0$ formula is provable with the
existential bounded by a term.
- [HP98, Theorem V.1.4]
- [Bus98A, Theorem 1.2.7.1] -/
theorem parikh (φ : ArithmeticSemisentence (k + 1)) (hφ : Hierarchy 𝚺 0 φ)
    (h : 𝗜𝚺₀ ⊢ ∀¹* ∃¹ φ) :
    ∃ t : ClosedSemiterm ℒₒᵣ k, 𝗜𝚺₀ ⊢ ∀¹* ∃¹[“#0 < !!(Rew.bShift t)”] φ := by
  by_contra hcon
  push Not at hcon
  have sat : Satisfiable (⋃ n, unboundedTheory φ n) :=
    (Compact.compact_cumulative (unboundedTheory_cumulative φ)).mpr
      (satisfiable_unboundedTheory φ hcon)
  have : 𝗘𝗤 (Language.oRingConst k) ⪯ ⋃ n, unboundedTheory φ n :=
    Entailment.WeakerThan.ofSubset <| Set.subset_iUnion_of_subset 0 <|
      Set.subset_union_of_subset_left Set.subset_union_left _
  have : (ModelOfSatEq sat)↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ :=
    models_of_lMap_image_subset sat <| Set.subset_iUnion_of_subset 0 <|
      Set.subset_union_of_subset_left Set.subset_union_right _
  refine false_of_unbounded φ hφ h (cstVal sat) fun t ↦ ?_
  have h₁ : (ModelOfSatEq sat)↓[Language.oRingConst k] ⊧ lift ((∼φ).ballLT t) :=
    Semantics.modelsSet_iff.mp (ModelOfSatEq.models sat)
      (Set.mem_iUnion_of_mem (Encodable.encode t + 1)
        (Set.mem_union_right _ ⟨t, Nat.lt_succ_self _, rfl⟩))
  simpa [models_lift_iff, eval_ballLT] using h₁

/-- An `𝗜𝚺₀`-provably total function with a $\Delta_0$ graph is bounded by a term, hence grows at
most polynomially.
- [HP98, Theorem V.1.4]
- [Bus98A, Theorem 1.2.7.1] -/
theorem exists_term_bound_of_provablyTotal {f : (Fin k → ℕ) → ℕ} {φ : 𝚺₁.Semisentence (k + 1)}
    (hφ : Hierarchy 𝚺 0 φ.val) (h : 𝗜𝚺₀.ProvablyTotalVia f φ) :
    ∃ t : ClosedSemiterm ℒₒᵣ k, ∀ v, f v ≤ Semiterm.valb v t := by
  obtain ⟨t, ht⟩ := parikh φ.val hφ h.total
  refine ⟨t, fun v ↦ ?_⟩
  have h₁ : ∀ w : Fin k → ℕ, ∃ y < Semiterm.valb w t, φ.val.Evalb (y :> w) := by
    simpa [models_iff, eval_allClosure, eval_bexsLT] using
      consequence_iff'.mp (Theory.Proof.sound ht) ℕ
  obtain ⟨y, hy, hy'⟩ := h₁ v
  exact le_of_lt (h.graph_iff.mp hy' ▸ hy)

end FFL.FirstOrder.Arithmetic
