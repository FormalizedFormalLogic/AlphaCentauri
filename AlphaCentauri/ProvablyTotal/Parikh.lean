module

public import AlphaCentauri.ProvablyTotal.Basic
public import AlphaCentauri.Model.Cut
public import AlphaCentauri.Vorspiel.Compact
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

open _root_.FFL.Entailment Semiformula
open Semantics (modelsSet_iff)

variable {k : ℕ}

/-- `𝗜𝚺₀` in the language with `k` new constants, together with the statement that no witness for
`φ` at the constants lies below any of the first `n` closed terms. -/
private def unboundedTheory (φ : ArithmeticSemisentence (k + 1)) (n : ℕ) : Theory (Language.oringConst k) :=
  𝗘𝗤 (Language.oringConst k)
    ∪ Semiformula.lMap (Language.Hom.add₁ ℒₒᵣ (Language.constant (Fin k))) '' 𝗜𝚺₀
    ∪ (fun t : ClosedSemiterm ℒₒᵣ k ↦ lift ((∼φ).ballLT t)) '' {t | Encodable.encode t < n}

/-- The elements of `M` bounded by the value at `c` of some closed term. -/
private def termCut {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (c : Fin k → M) : Cut M where
  carrier := {x | ∃ t : ClosedSemiterm ℒₒᵣ k, x ≤ t.valb c}
  zero_mem := ⟨‘0’, by simp⟩
  one_mem := ⟨‘1’, by simp⟩
  add_mem := fun ⟨s, hs⟩ ⟨t, ht⟩ ↦ ⟨‘!!s + !!t’, by
    simpa using add_le_add hs ht
  ⟩
  mul_mem := fun ⟨s, hs⟩ ⟨t, ht⟩ ↦ ⟨‘!!s * !!t’, by
    simpa using mul_le_mul hs ht (by simp) (by simp)
  ⟩
  mem_of_lt := fun hab ⟨t, ht⟩ ↦ ⟨t, le_trans hab.le ht⟩

/-- **Parikh's theorem**: a totality `𝗜𝚺₀` proves for a $\Delta_0$ formula is provable with the
existential bounded by a term.
- [HP98, Theorem V.1.4]
- [Bus98A, Theorem 1.2.7.1] -/
theorem parikh (φ : ArithmeticSemisentence (k + 1)) (hφ : Hierarchy 𝚺 0 φ)
  (h : 𝗜𝚺₀ ⊢ ∀¹* ∃¹ φ) :
  ∃ t : ClosedSemiterm ℒₒᵣ k, 𝗜𝚺₀ ⊢ ∀¹* ∃¹[“#0 < !!(Rew.bShift t)”] φ := by
  by_contra! hcon
  -- Adjoin `k` constants and demand that no witness for `φ` at them be bounded by a closed term.
  -- Each finite fragment holds in a counter-model to the bound by a dominating term.
  set T := ⋃ n, unboundedTheory φ n;
  have sat : Satisfiable T := Compact.satisfiable_iUnion
    (fun _ ↦ Set.union_subset_union_right _ $ Set.image_mono (fun _ ht ↦ Nat.lt_succ_of_lt ht)) $ by
    intro n;
    obtain ⟨M, _, _, hM⟩ := exists_countermodel_of_unprovable (hcon (dominatingTerm k n));
    obtain ⟨a, ha⟩ : ∃ a : Fin k → M, ∀ y < (dominatingTerm k n).valb a, ¬φ.Evalb (y :> a) := by
      simpa [models_iff, eval_allClosure, eval_bexsLT] using hM
    use strucOfTuple M a;
    apply modelsSet_iff.mpr;
    rintro σ ((hσ | hσ) | ⟨t, ht, rfl⟩)
    · exact modelsSet_iff.mp (strucOfTuple_models_eq M a) hσ
    · exact modelsSet_iff.mp (strucOfTuple_models_lMap_image M a inferInstance) hσ
    · rw [strucOfTuple_models_lift_iff]
      simp only [eval_ballLT, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
      exact fun y hy ↦ ha y (lt_of_lt_of_le hy (valb_le_valb_dominatingTerm ht a))

  have : 𝗘𝗤 (Language.oringConst k) ⪯ T := WeakerThan.ofSubset
    <| Set.subset_iUnion_of_subset 0
    <| Set.subset_union_of_subset_left Set.subset_union_left _
  have : (ModelOfSatEq sat)↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_of_lMap_image_subset sat
    <| Set.subset_iUnion_of_subset 0
    <| Set.subset_union_of_subset_left Set.subset_union_right _

  -- The constants have a witness in the initial segment they generate, which is a model of `𝗜𝚺₀`
  -- and, `φ` being `Δ₀`, absolute in the whole model.
  obtain ⟨b, ⟨t, ht⟩, hb⟩ :
    ∃ b : ModelOfSatEq sat, (∃ t : ClosedSemiterm ℒₒᵣ k, b ≤ t.valb (cstVal sat)) ∧ φ.Evalb (b :> cstVal sat) := by
    set I : Cut (ModelOfSatEq sat) := termCut (cstVal sat)
    have : I.endExtension↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := (inferInstance : (ModelOfSatEq sat)↓[ℒₒᵣ] ⊧* 𝗜𝚺₀)
    have hK : (↥I.carrier)↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := I.endExtension.models_ISigma0
    have hwit : ∀ w : Fin k → ↥I.carrier, ∃ b, φ.Evalb (b :> w) := by
      simpa [models_iff, eval_allClosure] using models_of_provable hK h
    obtain ⟨b, hb⟩ := hwit fun i ↦ ⟨cstVal sat i, Semiterm.bvar i, by simp⟩
    refine ⟨b, b.2, ?_⟩
    have h₂ := (absolute_of_Delta0 (T := 𝗣𝗔⁻) hφ (↥I.carrier) I.endExtension _ Empty.elim).mp hb
    simp only [Matrix.comp_vecCons'', Empty.eq_elim] at h₂
    exact h₂
  -- But the theory forbids exactly that.
  have H : ∀ y < t.valb (cstVal sat) + 1, ¬φ.Evalb (y :> cstVal sat) := by
    simpa [models_lift_iff, eval_ballLT] using modelsSet_iff.mp (ModelOfSatEq.models sat)
      <| Set.mem_iUnion_of_mem (Encodable.encode (‘!!t + 1’ : ClosedSemiterm ℒₒᵣ k) + 1)
      <| Set.mem_union_right _ ⟨_, Nat.lt_succ_self _, rfl⟩
  exact H b (by simpa using lt_succ_iff_le.mpr ht) hb

/-- An `𝗜𝚺₀`-provably total function with a $\Delta_0$ graph is bounded by a term, hence grows at
most polynomially.
- [HP98, Theorem V.1.4]
- [Bus98A, Theorem 1.2.7.1] -/
theorem exists_term_bound_of_provablyTotal {f φ}
  (hφ : Hierarchy 𝚺 0 φ.val) (h : 𝗜𝚺₀.ProvablyTotalVia f φ) :
  ∃ t : ClosedSemiterm ℒₒᵣ k, ∀ v, f v ≤ Semiterm.valb v t := by
  obtain ⟨t, ht⟩ := parikh φ.val hφ h.total;
  have h₁ : ∀ v : Fin k → ℕ, ∃ y < Semiterm.valb v t, φ.val.Evalb (y :> v) := by
    simpa [models_iff, eval_allClosure] using models_of_provable (M := ℕ) inferInstance ht
  use t;
  intro v;
  obtain ⟨y, hy, hy'⟩ := h₁ v;
  exact le_of_lt (h.graph_iff.mp hy' ▸ hy)

end FFL.FirstOrder.Arithmetic
