module

public import AlphaCentauri.Axiomatizability.Basic
public import AlphaCentauri.Model.NonnegativePart
public import AlphaCentauri.ToFoundation.OpenFormulaDegree
public import AlphaCentauri.ToMathlib.HahnSeries

/-!
# $\mathsf{IOpen}$ is not finitely axiomatizable

For each `N`, the non-negative part of the ring of Hahn series supported in the non-positive part
of $\mathbb{Z}[1/N!]$ with an integer constant coefficient satisfies induction for the open
formulas of degree at most `N`, but not $\mathsf{IOpen}$. Every finite subset of $\mathsf{IOpen}$
consists of such instances and axioms of $\mathsf{PA}^-$.
-/

@[expose] public section

open FFL FirstOrder OpenPredicate

namespace HahnSeries.factorialIntegerPartSubring

variable (N : ℕ)

/-- The non-negative part of `factorialIntegerPartSubring N` is a model of $\mathsf{PA}^-$ with
induction for the open formulas of degree at most `N`. -/
instance models : (Nonneg (factorialIntegerPartSubring N))↓[ℒₒᵣ] ⊧*
    𝗣𝗔⁻ ∪ Arithmetic.InductionScheme ℒₒᵣ fun φ ↦ φ.Open ∧ φ.degree ≤ N := by
  apply Semantics.ModelsSet.union_iff.mpr
  and_intros
  · infer_instance
  apply Semantics.modelsSet_iff.mpr
  rintro _ ⟨φ, ⟨hφ, hN⟩, rfl⟩
  suffices ∀ f : ℕ → Nonneg (factorialIntegerPartSubring N), φ.Eval ![0] f →
      (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) → ∀ x, φ.Eval ![x] f by
    simpa [models_iff, Semiformula.eval_univCl, Arithmetic.succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this
  intro f h0 hs x
  have hφP (y : Nonneg (factorialIntegerPartSubring N)) :
      φ.Eval ![y] f ↔ φ.Eval ![y.1] fun i ↦ (f i).1 := by
    simpa [Matrix.constant_eq_singleton, Function.comp_def] using
      Semiformula.eval_hom_iff_of_open Nonneg.oRingEmbedding hφ (e₁ := ![y]) (ε₁ := f)
  simp only [hφP] at h0 hs ⊢
  exact induction N (determinedBySigns_eval _ hφ hN) h0
    (fun r hr ↦ hs ⟨r, hr⟩) x x.2

/-- The non-negative part of `factorialIntegerPartSubring N` is not a model of
$\mathsf{IOpen}$. -/
lemma not_models_IOpen : ¬(Nonneg (factorialIntegerPartSubring N))↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := by
  rw [Nonneg.models_IOpen_iff]
  exact not_openInduction N

end HahnSeries.factorialIntegerPartSubring

namespace FFL.FirstOrder.Arithmetic

/-- $\mathsf{IOpen}$ is not finitely axiomatizable.
- [Bou91]
- [Moh11, Corollary E]
- [Kov24, Theorem 2.2] -/
theorem IOpen.not_finiteAxiomatizable : ¬FiniteAxiomatizable 𝗜𝗢𝗽𝗲𝗻 := by
  classical
  apply not_finiteAxiomatizable_iff.mpr
  intro F hsub hfin
  constructor
  · exact Theory.Proof.weakerThan_of_le hsub
  · by_contra! hle;
    let deg (σ : ArithmeticSentence) : ℕ :=
      if h : ∃ φ : ArithmeticSemiformula ℕ 1, φ.Open ∧ σ = .univCl (succInd φ) then h.choose.degree
      else 0
    set N := hfin.toFinset.sup deg
    have hF : F ⊆ 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ fun φ ↦ φ.Open ∧ φ.degree ≤ N := by
      intro σ hσ
      rcases hsub hσ with h | ⟨φ, hφ, rfl⟩
      · exact Or.inl h
      · have h : ∃ φ' : ArithmeticSemiformula ℕ 1, φ'.Open ∧ Semiformula.univCl (succInd φ) =
            .univCl (succInd φ') := by use φ
        have hdeg : deg (.univCl (succInd φ)) ≤ N := Finset.le_sup (by simpa using hσ)
        simp only [deg, h, ↓reduceDIte] at hdeg
        right
        use h.choose
        exact ⟨⟨h.choose_spec.1, hdeg⟩, h.choose_spec.2⟩
    exact HahnSeries.factorialIntegerPartSubring.not_models_IOpen N
      (ModelsTheory.of_provably_subtheory _ 𝗜𝗢𝗽𝗲𝗻 F
      (Semantics.ModelsSet.of_subset (HahnSeries.factorialIntegerPartSubring.models N) hF))

end FFL.FirstOrder.Arithmetic
