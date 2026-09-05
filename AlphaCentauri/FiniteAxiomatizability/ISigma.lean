module

public import AlphaCentauri.Bootstrapping.PartialTruth.Snowing
public import AlphaCentauri.FirstOrder.FiniteAxiomatizability

/-!
# Finite axiomatizability of `𝗜𝚺 n`

`𝗣𝗔⁻` together with the finite Tarski theory and a single instance of the `𝚺-[n + 1]` induction
scheme, stated with the partial truth definition `satSigma n`, is a finite theory equivalent to
`𝗜𝚺 (n + 1)`; hence `𝗜𝚺 n` is finitely axiomatizable for `n ≥ 1`.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

open Bootstrapping

namespace ISigma

/-- The formula saying that the code `z` is `𝚺-[n + 1]`-satisfied by the assignment obtained by
putting `x` in front of the assignment coded by `e`, with `x` as its bound variable and `z`, `e`
as its free variables.
- [HP98, Theorem I.2.52] -/
noncomputable def indFormula (n : ℕ) : ArithmeticSemiformula ℕ 1 :=
  “x. ∃ ev, !adjoinDef.val ev x &1 ∧ !(satSigma n).val &0 ev”

/-- The induction formula is `𝚺-[n + 1]`.
- [HP98, Theorem I.2.52] -/
lemma hierarchy_indFormula (n : ℕ) : Hierarchy 𝚺 (n + 1) (indFormula n) := by
  have h₁ : Hierarchy 𝚺 (n + 1) adjoinDef.val := adjoinDef.sigma_prop.mono (by omega)
  have h₂ : Hierarchy 𝚺 (n + 1) (satSigma n).val := (satSigma n).sigma_prop
  simp [indFormula, h₁, h₂]

/-- The single induction axiom of the finite theory.
- [HP98, Theorem I.2.52] -/
noncomputable def indSentence (n : ℕ) : ArithmeticSentence := .univCl (succInd (indFormula n))

/-- The induction axiom is an instance of the `𝚺-[n + 1]` induction scheme.
- [HP98, Theorem I.2.52] -/
lemma indSentence_mem_inductionScheme (n : ℕ) :
    indSentence n ∈ InductionScheme ℒₒᵣ (Hierarchy 𝚺 (n + 1)) :=
  mem_InductionScheme_of_mem (hierarchy_indFormula n)

/-- The finite theory equivalent to `𝗜𝚺 (n + 1)`.
- [HP98, Theorem I.2.52] -/
noncomputable def finiteAxiomatization (n : ℕ) : ArithmeticTheory :=
  𝗣𝗔⁻ ∪ tarski n ∪ {indSentence n}

/-- The theory `finiteAxiomatization n` is finite.
- [HP98, Theorem I.2.52] -/
lemma finiteAxiomatization_finite (n : ℕ) : (finiteAxiomatization n).Finite :=
  (PeanoMinus.finite.union (tarski_finite n)).union (Set.finite_singleton _)

lemma peanoMinus_subset_finiteAxiomatization (n : ℕ) :
    (𝗣𝗔⁻ : ArithmeticTheory) ⊆ finiteAxiomatization n :=
  Set.subset_union_left.trans Set.subset_union_left

lemma tarski_mem_finiteAxiomatization {n : ℕ} {σ : ArithmeticSentence} (h : tarski n σ) :
    σ ∈ finiteAxiomatization n := Set.mem_union_left _ (Set.mem_union_right _ h)

lemma indSentence_mem_finiteAxiomatization (n : ℕ) :
    indSentence n ∈ finiteAxiomatization n := Set.mem_union_right _ rfl

instance (n : ℕ) : 𝗣𝗔⁻ ⪯ finiteAxiomatization n :=
  Entailment.Axiomatized.le_of_subset (peanoMinus_subset_finiteAxiomatization n)

lemma eval_indFormula {M : Type*} [ORingStructure M] (n : ℕ) (x : M) (g : ℕ → M) :
    (indFormula n).Eval ![x] g ↔
      ∃ ev, Reading.Adjoin ev x (g 1) ∧ Reading.SatSigma n (g 0) ev := by
  simp [indFormula, Reading.Adjoin, Reading.SatSigma]

/-- `𝗜𝚺 (n + 1)` proves the finite theory.
- [HP98, Theorem I.2.52] -/
theorem provable_finiteAxiomatization (n : ℕ) : 𝗜𝚺 (n + 1) ⊢* finiteAxiomatization n := by
  rintro σ ((hσ | hσ) | rfl)
  · exact Entailment.by_axm (Set.mem_union_left _ hσ)
  · exact Entailment.WeakerThan.pbl (h := ISigma_weakerThan_of_le (by omega))
      (ISigma1.provable_tarski n hσ)
  · exact Entailment.by_axm (Set.mem_union_right _ (indSentence_mem_inductionScheme n))

/-! ## The finite theory proves induction for strict prenex formulas -/

open Reading

/-- The substitution sending the bound variable of a formula to `#0` and its free variables below
`φ.fvSup` to the remaining bound variables. -/
private noncomputable def paramSubst (φ : ArithmeticSemiformula ℕ 1) :
    Rew ℒₒᵣ ℕ 1 Empty (φ.fvSup + 1) :=
  Rew.bind ![#0] fun x ↦ if h : x < φ.fvSup then #⟨x + 1, by omega⟩ else #0

/-- A formula with one bound variable, viewed as a semisentence whose extra bound variables are
its free variables. -/
private noncomputable def toSemisentence (φ : ArithmeticSemiformula ℕ 1) :
    ArithmeticSemisentence (φ.fvSup + 1) := paramSubst φ ▹ φ

private lemma eval_toSemisentence {M : Type*} [ORingStructure M]
    (φ : ArithmeticSemiformula ℕ 1) (x : M) (f : ℕ → M) :
    M ⊧/(x :> fun i : Fin φ.fvSup ↦ f i) (toSemisentence φ) ↔ φ.Eval ![x] f := by
  rw [toSemisentence, Semiformula.eval_rew]
  have hb : (Semiterm.val (x :> fun i : Fin φ.fvSup ↦ f i) (Empty.elim) ∘
      paramSubst φ ∘ Semiterm.bvar) = ![x] := by
    funext i
    rw [show i = 0 from Fin.fin_one_eq_zero i]
    simp [paramSubst]
  rw [hb]
  refine Semiformula.eval_iff_of_funEqOn φ fun y hy ↦ ?_
  have : y < φ.fvSup := Semiformula.lt_fvSup_of_fvar? hy
  simp [paramSubst, this]

/-- The finite theory proves the induction axiom of every strict prenex `𝚺-[n + 1]` formula.
- [HP98, Theorem I.2.52] -/
theorem provable_succInd_of_strictHierarchy {n : ℕ} {φ : ArithmeticSemiformula ℕ 1}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) :
    finiteAxiomatization n ⊢ .univCl (succInd φ) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ finiteAxiomatization n :=
    Entailment.WeakerThan.trans (𝓣 := (𝗣𝗔⁻ : ArithmeticTheory)) inferInstance inferInstance
  refine Arithmetic.complete.{0} _ _ ?_
  intro M _ hMT
  have hPA : M↓[ℒₒᵣ] ⊧* (𝗣𝗔⁻ : ArithmeticTheory) :=
    Semantics.ModelsSet.of_subset hMT (peanoMinus_subset_finiteAxiomatization n)
  have hM : ∀ σ : ArithmeticSentence, tarski n σ → M↓[ℒₒᵣ] ⊧ σ := fun _ hσ ↦
    Semantics.ModelsSet.models _ (tarski_mem_finiteAxiomatization hσ)
  have hInd : M↓[ℒₒᵣ] ⊧ indSentence n :=
    Semantics.ModelsSet.models _ (indSentence_mem_finiteAxiomatization n)
  have hind : ∀ g : ℕ → M, (indFormula n).Eval ![0] g →
      (∀ x, (indFormula n).Eval ![x] g → (indFormula n).Eval ![x + 1] g) →
      ∀ x, (indFormula n).Eval ![x] g := by
    simpa [indSentence, models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using hInd
  suffices ∀ f : ℕ → M, φ.Eval ![0] f → (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) →
      ∀ x, φ.Eval ![x] f by
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this
  intro f hzero hsucc
  have hψ : StrictHierarchy 𝚺 (n + 1) (toSemisentence φ) := hφ.rew _
  obtain ⟨e₀, he₀⟩ := exists_codes hM (fun i : Fin φ.fvSup ↦ f i)
  set g : ℕ → M := fun i ↦ if i = 0 then ((⌜toSemisentence φ⌝ : ℕ) : M) else e₀ with hg
  have hg₀ : g 0 = ((⌜toSemisentence φ⌝ : ℕ) : M) := by simp [hg]
  have hg₁ : g 1 = e₀ := by simp [hg]
  have hP : ∀ x : M, (indFormula n).Eval ![x] g ↔ φ.Eval ![x] f := by
    intro x
    rw [eval_indFormula, hg₀, hg₁]
    constructor
    · rintro ⟨ev, hadj, hsat⟩
      exact (eval_toSemisentence φ x f).mp
        ((satSigma_quote_reading hM hψ (codes_cons hM he₀ hadj)).mp hsat)
    · intro h
      obtain ⟨ev, hadj⟩ := read_adjoinTotal hM x e₀
      exact ⟨ev, hadj, (satSigma_quote_reading hM hψ (codes_cons hM he₀ hadj)).mpr
        ((eval_toSemisentence φ x f).mpr h)⟩
  intro x
  refine (hP x).mp (hind g ((hP 0).mpr hzero) (fun y hy ↦ (hP (y + 1)).mpr ?_) x)
  exact hsucc y ((hP y).mp hy)

/-! ## The equivalence with `𝗜𝚺 (n + 1)` -/

/-- A theory extending `𝗣𝗔⁻` that proves the induction axiom of every strict prenex `𝚺-[n + 1]`
formula is at least as strong as `𝗜𝚺 (n + 1)`.
- [HP98, Theorem I.2.15]
- [HP98, Theorem I.2.25] -/
axiom hierarchyInduction_of_strictInduction (n : ℕ) (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T]
    (h : ∀ φ : ArithmeticSemiformula ℕ 1, StrictHierarchy 𝚺 (n + 1) φ →
      T ⊢ .univCl (succInd φ)) : 𝗜𝚺 (n + 1) ⪯ T

/-- The finite theory is equivalent to `𝗜𝚺 (n + 1)`.
- [HP98, Theorem I.2.52] -/
theorem finiteAxiomatization_equiv (n : ℕ) : finiteAxiomatization n ≊ 𝗜𝚺 (n + 1) :=
  Entailment.Equiv.antisymm_iff.mpr
    ⟨Entailment.WeakerThan.ofAxm! (provable_finiteAxiomatization n),
      hierarchyInduction_of_strictInduction n _ fun _ hφ ↦ provable_succInd_of_strictHierarchy hφ⟩

/-- For `n ≥ 1`, `𝗜𝚺 n` is finitely axiomatizable.
- [HP98, Theorem I.2.52] -/
theorem finiteAxiomatizable (n : ℕ) (hn : 1 ≤ n) : Entailment.FiniteAxiomatizable (𝗜𝚺 n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨finiteAxiomatization m, by simpa using finiteAxiomatization_finite m,
    finiteAxiomatization_equiv m⟩

/-- For `n ≥ 1`, `𝗜𝚺 n` is axiomatized by a single `𝚷 (n + 2)` sentence.
- [HP98, Remark I.4.35(1)] -/
axiom exists_pi_sentence (n : ℕ) (hn : 1 ≤ n) :
    ∃ σ : ArithmeticSentence, Hierarchy 𝚷 (n + 2) σ ∧ ({σ} : ArithmeticTheory) ≊ 𝗜𝚺 n

end ISigma

end LO.FirstOrder.Arithmetic
