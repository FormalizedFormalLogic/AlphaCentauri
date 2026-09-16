module

public import AlphaCentauri.ProvablyTotal.Basic
public import AlphaCentauri.Model.Cut
public import AlphaCentauri.Vorspiel.Compact
public import AlphaCentauri.Vorspiel.Completeness
public import AlphaCentauri.Vorspiel.ConstantExtension
public import Foundation.FirstOrder.Tarski.Ultraproduct

/-!
# Parikh's theorem

An `𝗜𝚺₀`-provably total function with a $\Delta_0$ graph is bounded by a term, hence grows at
most polynomially.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment Semiformula
open Semantics (modelsSet_iff)

variable {k : ℕ}

section termCut

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- The elements of `M` bounded by the value at `c` of some closed term. -/
private def termCut (c : Fin k → M) : Cut M where
  carrier := {x | ∃ t : ClosedSemiterm ℒₒᵣ k, x ≤ t.valb c}
  succ_mem := fun ⟨t, ht⟩ ↦ ⟨‘!!t + 1’, by simpa using add_le_add_right ht 1⟩
  mem_of_lt := fun hab ⟨t, ht⟩ ↦ ⟨t, le_trans hab.le ht⟩

private instance termCut_closed (c : Fin k → M) : (termCut c).Closed where
  zero_mem := ⟨‘0’, by simp⟩
  one_mem := ⟨‘1’, by simp⟩
  add_mem := fun ⟨s, hs⟩ ⟨t, ht⟩ ↦ ⟨‘!!s + !!t’, by
    simpa using add_le_add hs ht
  ⟩
  mul_mem := fun ⟨s, hs⟩ ⟨t, ht⟩ ↦ ⟨‘!!s * !!t’, by
    simpa using mul_le_mul hs ht (by simp) (by simp)
  ⟩

end termCut

/-- **Parikh's theorem**: a $\Pi^0_2$ sentence provable by `𝗜𝚺₀` is provable with the
existential quantifier bounded by a term. This is proven for $\forall\ldots\forall\exists` formulas, which
have any number of unbounded universal quantifiers, then one unbounded existential.
- [HP98, Theorem V.1.4]
- [Bus98A, Theorem 1.2.7.1] -/
theorem parikh (φ : ArithmeticSemisentence (k + 1)) (hφ : φ.Bounded)
  (h : 𝗜𝚺₀ ⊢ ∀¹* ∃¹ φ) :
  ∃ t : ClosedSemiterm ℒₒᵣ k, 𝗜𝚺₀ ⊢ ∀¹* ∃¹[“#0 < !!(Rew.bShift t)”] φ := by
  by_contra! hcon
  -- In the language with `k` new constants, define for each natural number `n` the theory
  -- consisting of `𝗜𝚺₀` plus, for each of the first `n` terms `t` of `ℒₒᵣ`, the sentence `∀(#0 < t), ∼φ`.
  set Tn : ℕ → Theory (Language.oringConst k) := λ n =>
    𝗘𝗤 _
    ∪ Semiformula.lMap (Language.Hom.add₁ ℒₒᵣ _) '' 𝗜𝚺₀
    ∪ (fun t : ClosedSemiterm ℒₒᵣ k ↦ lift ((∼φ).ballLT t)) '' {t | Encodable.encode t < n}
  have : Cumulative Tn := by
    intro;
    apply Set.union_subset_union_right _;
    apply Set.image_mono;
    intro _ ht;
    exact Nat.lt_succ_of_lt ht;

  set T := ⋃ n, Tn n;
  -- Each `Tn n` is satisfiable: a term dominating the closed terms numbered below
  -- `n` turns the assumption into a counter-model. Thus the union is satisfiable by compactness.
  have sat : Satisfiable T := Compact.satisfiable_iUnion ‹_› $ by
    intro n;
    obtain ⟨M, _, _, hM⟩ := exists_countermodel_of_unprovable $ hcon $ dominatingTerm k n;
    obtain ⟨a, ha⟩ : ∃ a : Fin k → M, ∀ y < (dominatingTerm k n).valb a, ¬φ.Evalb (y :> a) := by
      simpa [models_iff, eval_allClosure, eval_bexsLT] using hM
    use strucOfTuple M a;
    apply modelsSet_iff.mpr;
    rintro σ ((hσ | hσ) | ⟨t, ht, rfl⟩)
    · exact modelsSet_iff.mp (strucOfTuple_models_eq M a) hσ
    · exact modelsSet_iff.mp (strucOfTuple_models_lMap_image M a inferInstance) hσ
    · rw [strucOfTuple_models_lift_iff]
      simp only [eval_ballLT, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
      intro y hy;
      exact ha y (lt_of_lt_of_le hy (valb_le_valb_dominatingTerm ht a))

  -- A model `ModelOfSatEq sat` of `T` is also a model of
  -- `𝗜𝚺₀` in which no witness lies below the value of any closed term.
  have : 𝗘𝗤 (Language.oringConst k) ⪯ T := WeakerThan.ofSubset
    $ Set.subset_iUnion_of_subset 0
    $ Set.subset_union_of_subset_left Set.subset_union_left _
  have hM : (ModelOfSatEq sat)↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_of_lMap_image_subset sat
    $ Set.subset_iUnion_of_subset 0
    $ Set.subset_union_of_subset_left Set.subset_union_right _
  have hunbounded : ∀ (t : ClosedSemiterm ℒₒᵣ k) (y), y < t.valb (cstVal sat) →
      ¬φ.Evalb (y :> cstVal sat) := by
    intro t;
    simpa [models_lift_iff, eval_ballLT] using modelsSet_iff.mp (ModelOfSatEq.models sat)
      $ Set.mem_iUnion_of_mem (Encodable.encode t + 1)
      $ Set.mem_union_right _ ⟨t, Nat.lt_succ_self _, rfl⟩

  -- The elements bounded by the value of a closed term form a cut, which models `𝗜𝚺₀`.
  set K : Cut (ModelOfSatEq sat) := termCut (cstVal sat);
  let _ : K.Closed := termCut_closed _
  let _ : ↥K.carrier ⊆ₑ ModelOfSatEq sat := K.endExtension
  have hK : (↥K.carrier)↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ :=
    EndExtension.models_ISigma0 (M := ↥K.carrier) (N := ModelOfSatEq sat)

  -- Soundness in the cut gives a witness `b ≤ t(c)`, and `φ` being $\Delta_0$ it holds in the
  -- model too.
  have hwit : ∀ w : Fin k → ↥K.carrier, ∃ b, φ.Evalb (b :> w) := by
    simpa [models_iff, eval_allClosure] using models_of_provable hK h
  obtain ⟨b, hb⟩ := hwit fun i ↦ ⟨cstVal sat i, Semiterm.bvar i, by simp⟩
  obtain ⟨t, ht⟩ : ∃ t : ClosedSemiterm ℒₒᵣ k, (b : ModelOfSatEq sat) ≤ t.valb (cstVal sat) := b.2
  have hbM : φ.Evalb ((b : ModelOfSatEq sat) :> cstVal sat) := by
    have h₂ :=
      (absolute_of_bounded (T := 𝗣𝗔⁻) hφ (↥K.carrier) (ModelOfSatEq sat) _ Empty.elim).mp hb
    simp only [Matrix.comp_vecCons'', Empty.eq_elim] at h₂
    exact h₂

  -- But `b` is below the value of `t + 1`, which contradicts that no witness lies
  -- below the closed term `t + 1`.
  exact hunbounded ‘!!t + 1’ b (by simpa using lt_succ_iff_le.mpr ht) hbM

/-- An `𝗜𝚺₀`-provably total function with a $\Delta_0$ graph is bounded by a term, hence grows at
most polynomially.
- [HP98, Theorem V.1.4]
- [Bus98A, Theorem 1.2.7.1] -/
theorem exists_term_bound_of_provablyTotal {f φ}
  (hφ : φ.val.Bounded) (h : 𝗜𝚺₀.ProvablyTotalVia f φ) :
  ∃ t : ClosedSemiterm ℒₒᵣ k, ∀ v, f v ≤ Semiterm.valb v t := by
  obtain ⟨t, ht⟩ := parikh φ.val hφ h.total;
  have h₁ : ∀ v : Fin k → ℕ, ∃ y < Semiterm.valb v t, φ.val.Evalb (y :> v) := by
    simpa [models_iff, eval_allClosure] using models_of_provable (M := ℕ) inferInstance ht
  use t;
  intro v;
  obtain ⟨y, hy, hy'⟩ := h₁ v;
  exact le_of_lt (h.graph_iff.mp hy' ▸ hy)

end FFL.FirstOrder.Arithmetic
