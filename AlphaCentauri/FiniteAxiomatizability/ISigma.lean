module

public import AlphaCentauri.Bootstrapping.PartialTruth.Snowing
public import AlphaCentauri.FirstOrder.FiniteAxiomatizability
public import AlphaCentauri.Hierarchy.PrenexOfCollection
public import AlphaCentauri.Schemata.Collection
public import AlphaCentauri.Vorspiel.Fvar

/-!
# Finite axiomatizability of `𝗜𝚺 n`

`𝗣𝗔⁻` together with the finite Tarski theory, a single instance of the `𝚺-[n + 1]` induction
scheme and a single instance of the `𝚺-[n + 1]` collection scheme, both stated with the partial
truth definition `satSigma n`, is a finite theory equivalent to `𝗜𝚺 (n + 1)`; hence `𝗜𝚺 n` is
finitely axiomatizable for `n ≥ 1`.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

open Bootstrapping
open _root_.LO.Entailment

namespace ISigma

/-- The formula saying that the code `z` is `𝚺-[n + 1]`-satisfied by the assignment obtained by
putting `x` in front of the assignment coded by `e`, with `x` as its bound variable and `z`, `e`
as its free variables.
- [HP98, Theorem I.2.52] -/
noncomputable def indFormula (n : ℕ) : ArithmeticSemiformula ℕ 1 :=
  “x. ∃ ev, !adjoinDef.val ev x &1 ∧ !(satSigma n).val &0 ev”

/-- The graph of `adjoin` is `𝚺-[n + 1]`. -/
@[simp]
private lemma hierarchy_adjoinDef {n : ℕ} : Hierarchy 𝚺 (n + 1) adjoinDef.val :=
  adjoinDef.sigma_prop.mono (by omega)

/-- The induction formula is `𝚺-[n + 1]`.
- [HP98, Theorem I.2.52] -/
@[simp]
lemma hierarchy_indFormula {n : ℕ} : Hierarchy 𝚺 (n + 1) (indFormula n) := by
  simp [indFormula]

/-- The single induction axiom of the finite theory.
- [HP98, Theorem I.2.52] -/
noncomputable def indSentence (n : ℕ) : ArithmeticSentence := .univCl (succInd (indFormula n))

/-- The induction axiom is an instance of the `𝚺-[n + 1]` induction scheme.
- [HP98, Theorem I.2.52] -/
@[simp]
lemma indSentence_mem_inductionScheme {n : ℕ} :
    indSentence n ∈ InductionScheme ℒₒᵣ (Hierarchy 𝚺 (n + 1)) :=
  mem_InductionScheme_of_mem hierarchy_indFormula

/-- The formula saying that the code `z` is `𝚺-[n + 1]`-satisfied by the assignment obtained by
putting `y` and then `x` in front of the assignment coded by `e`, with `x` and `y` as its bound
variables and `z`, `e` as its free variables.
- [HP98, Theorem I.2.52] -/
noncomputable def collFormula (n : ℕ) : ArithmeticSemiformula ℕ 2 :=
  “x y. ∃ ev₀, !adjoinDef.val ev₀ x &1 ∧ ∃ ev, !adjoinDef.val ev y ev₀ ∧ !(satSigma n).val &0 ev”

/-- The collection formula is `𝚺-[n + 1]`.
- [HP98, Theorem I.2.52] -/
@[simp]
lemma hierarchy_collFormula {n : ℕ} : Hierarchy 𝚺 (n + 1) (collFormula n) := by
  simp [collFormula]

/-- The single collection axiom of the finite theory.
- [HP98, Theorem I.2.52] -/
noncomputable def collSentence (n : ℕ) : ArithmeticSentence :=
  .univCl (collectionAxiom (collFormula n))

/-- The collection axiom is an instance of the `𝚺-[n + 1]` collection scheme.
- [HP98, Theorem I.2.52] -/
@[simp]
lemma collSentence_mem_collectionScheme {n : ℕ} :
    collSentence n ∈ CollectionScheme (Hierarchy 𝚺 (n + 1)) :=
  mem_CollectionScheme_of_mem hierarchy_collFormula

/-- The finite theory equivalent to `𝗜𝚺 (n + 1)`.
- [HP98, Theorem I.2.52] -/
noncomputable def finiteAxiomatization (n : ℕ) : ArithmeticTheory :=
  𝗣𝗔⁻ ∪ tarski n ∪ {indSentence n, collSentence n}

/-- The theory `finiteAxiomatization n` is finite.
- [HP98, Theorem I.2.52] -/
@[simp]
lemma finiteAxiomatization_finite {n : ℕ} : (finiteAxiomatization n).Finite :=
  (PeanoMinus.finite.union (tarski_finite n)).union ((Set.finite_singleton _).insert _)

@[simp]
lemma peanoMinus_subset_finiteAxiomatization {n : ℕ} : 𝗣𝗔⁻ ⊆ finiteAxiomatization n :=
  Set.subset_union_left.trans Set.subset_union_left

@[grind →]
lemma tarski_mem_finiteAxiomatization {n : ℕ} {σ : ArithmeticSentence} (h : tarski n σ) :
    σ ∈ finiteAxiomatization n := Set.mem_union_left _ (Set.mem_union_right _ h)

@[simp]
lemma indSentence_mem_finiteAxiomatization {n : ℕ} :
    indSentence n ∈ finiteAxiomatization n := Set.mem_union_right _ (Set.mem_insert _ _)

@[simp]
lemma collSentence_mem_finiteAxiomatization {n : ℕ} :
    collSentence n ∈ finiteAxiomatization n :=
  Set.mem_union_right _ (Set.mem_insert_of_mem _ rfl)

instance (n : ℕ) : 𝗣𝗔⁻ ⪯ finiteAxiomatization n :=
  Axiomatized.le_of_subset peanoMinus_subset_finiteAxiomatization

instance (n : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ finiteAxiomatization n :=
  WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance inferInstance

section
variable {M : Type*} [ORingStructure M]

@[simp]
lemma eval_indFormula {n : ℕ} (x : M) (g : ℕ → M) :
    (indFormula n).Eval ![x] g ↔
      ∃ ev, Reading.Adjoin ev x (g 1) ∧ Reading.SatSigma n (g 0) ev := by
  simp [indFormula, Reading.Adjoin, Reading.SatSigma]

@[simp]
lemma eval_collFormula {n : ℕ} (x y : M) (g : ℕ → M) :
    (collFormula n).Eval ![x, y] g ↔
      ∃ ev₀, Reading.Adjoin ev₀ x (g 1) ∧
        ∃ ev, Reading.Adjoin ev y ev₀ ∧ Reading.SatSigma n (g 0) ev := by
  simp [collFormula, Reading.Adjoin, Reading.SatSigma]

end

/-- `𝗜𝚺 (n + 1)` proves the finite theory.
- [HP98, Theorem I.2.52] -/
theorem provable_finiteAxiomatization (n : ℕ) : 𝗜𝚺 (n + 1) ⊢* finiteAxiomatization n := by
  rintro σ ((hσ | hσ) | rfl | rfl)
  · exact by_axm (Set.mem_union_left _ hσ)
  · exact WeakerThan.pbl (h := ISigma_weakerThan_of_le (by omega))
      (ISigma1.provable_tarski n hσ)
  · exact by_axm (Set.mem_union_right _ indSentence_mem_inductionScheme)
  · exact WeakerThan.pbl (h := BSigma_weakerThan_ISigma n)
      (by_axm (Set.mem_union_right _ collSentence_mem_collectionScheme))

/-- `𝗣𝗔⁻` holds in a model of the finite theory; the proofs below use it as a local instance.
- [HP98, Theorem I.2.52] -/
lemma models_peanoMinus (n : ℕ) {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* finiteAxiomatization n] : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  Semantics.ModelsSet.of_subset' (peanoMinus_subset_finiteAxiomatization (n := n))

/-- Every axiom of the finite Tarski theory holds in a model of the finite theory.
- [HP98, Theorem I.2.52] -/
lemma models_tarski {n : ℕ} {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* finiteAxiomatization n] {σ : ArithmeticSentence} (hσ : tarski n σ) :
    M↓[ℒₒᵣ] ⊧ σ := Semantics.ModelsSet.models _ (tarski_mem_finiteAxiomatization hσ)

/-! ## The finite theory proves induction for strict prenex formulas -/

open Reading

/-- In a model of the finite theory, the induction formula at the code of a strict prenex
`𝚺-[n + 1]` formula `φ` evaluates exactly like `φ`, under the assignment that carries the code
of `φ` and a code of `φ`'s parameters.
- [HP98, Theorem I.2.52] -/
private lemma exists_assignment_eval_indFormula {M : Type*} [ORingStructure M] {n : ℕ}
    [M↓[ℒₒᵣ] ⊧* finiteAxiomatization n] {φ : ArithmeticSemiformula ℕ 1}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) (f : ℕ → M) :
    ∃ g : ℕ → M, ∀ x : M, (indFormula n).Eval ![x] g ↔ φ.Eval ![x] f := by
  have := models_peanoMinus n (M := M)
  have hM : ∀ σ : ArithmeticSentence, tarski n σ → M↓[ℒₒᵣ] ⊧ σ := fun _ ↦ models_tarski
  have hψ : StrictHierarchy 𝚺 (n + 1) (φ.toSemisentence ![#0]) := hφ.rew _
  obtain ⟨e₀, he₀⟩ := exists_codes hM (fun i : Fin φ.fvSup ↦ f i)
  set g : ℕ → M := fun i ↦ if i = 0 then ((⌜φ.toSemisentence ![#0]⌝ : ℕ) : M) else e₀ with hg
  have hg₀ : g 0 = ((⌜φ.toSemisentence ![#0]⌝ : ℕ) : M) := by simp [hg]
  have hg₁ : g 1 = e₀ := by simp [hg]
  refine ⟨g, fun x ↦ ?_⟩
  rw [eval_indFormula, hg₀, hg₁]
  constructor
  · rintro ⟨ev, hadj, hsat⟩
    exact (φ.eval_toSemisentence_one x f).mp
      ((satSigma_quote_reading hM hψ (codes_cons hM he₀ hadj)).mp hsat)
  · intro h
    obtain ⟨ev, hadj⟩ := read_adjoinTotal hM x e₀
    exact ⟨ev, hadj, (satSigma_quote_reading hM hψ (codes_cons hM he₀ hadj)).mpr
      ((φ.eval_toSemisentence_one x f).mpr h)⟩

/-- The finite theory proves the induction axiom of every strict prenex `𝚺-[n + 1]` formula.
- [HP98, Theorem I.2.52] -/
theorem provable_succInd_of_strictHierarchy {n : ℕ} {φ : ArithmeticSemiformula ℕ 1}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) :
    finiteAxiomatization n ⊢ .univCl (succInd φ) := by
  refine Arithmetic.complete.{0} _ _ ?_
  intro M _ _
  have hInd : M↓[ℒₒᵣ] ⊧ indSentence n :=
    Semantics.ModelsSet.models _ indSentence_mem_finiteAxiomatization
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
  obtain ⟨g, hP⟩ := exists_assignment_eval_indFormula hφ f
  intro x
  refine (hP x).mp (hind g ((hP 0).mpr hzero) (fun y hy ↦ (hP (y + 1)).mpr ?_) x)
  exact hsucc y ((hP y).mp hy)

/-! ## The finite theory proves collection for strict prenex formulas -/

/-- In a model of the finite theory, the collection formula at the code of a strict prenex
`𝚺-[n + 1]` formula `φ` evaluates exactly like `φ`, under the assignment that carries the code
of `φ` and a code of `φ`'s parameters.
- [HP98, Theorem I.2.52] -/
private lemma exists_assignment_eval_collFormula {M : Type*} [ORingStructure M] {n : ℕ}
    [M↓[ℒₒᵣ] ⊧* finiteAxiomatization n] {φ : ArithmeticSemiformula ℕ 2}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) (f : ℕ → M) :
    ∃ g : ℕ → M, ∀ x y : M, (collFormula n).Eval ![x, y] g ↔ φ.Eval ![x, y] f := by
  have := models_peanoMinus n (M := M)
  have hM : ∀ σ : ArithmeticSentence, tarski n σ → M↓[ℒₒᵣ] ⊧ σ := fun _ ↦ models_tarski
  have hψ : StrictHierarchy 𝚺 (n + 1) (φ.toSemisentence ![#1, #0]) := hφ.rew _
  obtain ⟨e₀, he₀⟩ := exists_codes hM (fun i : Fin φ.fvSup ↦ f i)
  set g : ℕ → M := fun i ↦ if i = 0 then ((⌜φ.toSemisentence ![#1, #0]⌝ : ℕ) : M) else e₀ with hg
  have hg₀ : g 0 = ((⌜φ.toSemisentence ![#1, #0]⌝ : ℕ) : M) := by simp [hg]
  have hg₁ : g 1 = e₀ := by simp [hg]
  refine ⟨g, fun x y ↦ ?_⟩
  rw [eval_collFormula, hg₀, hg₁]
  constructor
  · rintro ⟨ev₀, hadj₀, ev, hadj, hsat⟩
    exact (φ.eval_toSemisentence_two x y f).mp
      ((satSigma_quote_reading hM hψ (codes_cons hM (codes_cons hM he₀ hadj₀) hadj)).mp hsat)
  · intro hxy
    obtain ⟨ev₀, hadj₀⟩ := read_adjoinTotal hM x e₀
    obtain ⟨ev, hadj⟩ := read_adjoinTotal hM y ev₀
    exact ⟨ev₀, hadj₀, ev, hadj,
      (satSigma_quote_reading hM hψ (codes_cons hM (codes_cons hM he₀ hadj₀) hadj)).mpr
        ((φ.eval_toSemisentence_two x y f).mpr hxy)⟩

/-- The finite theory proves the collection axiom of every strict prenex `𝚺-[n + 1]` formula.
- [HP98, Theorem I.2.52] -/
theorem provable_collectionAxiom_of_strictHierarchy {n : ℕ} {φ : ArithmeticSemiformula ℕ 2}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) :
    finiteAxiomatization n ⊢ .univCl (collectionAxiom φ) := by
  refine Arithmetic.complete.{0} _ _ ?_
  intro M _ _
  have := models_peanoMinus n (M := M)
  have hColl : M↓[ℒₒᵣ] ⊧ collSentence n :=
    Semantics.ModelsSet.models _ collSentence_mem_finiteAxiomatization
  have hcoll := (models_collectionAxiom_iff (collFormula n)).mp hColl
  rw [models_collectionAxiom_iff]
  intro f a h
  obtain ⟨g, hP⟩ := exists_assignment_eval_collFormula hφ f
  obtain ⟨b, hb⟩ := hcoll g a fun x hx ↦ (h x hx).imp fun y hy ↦ (hP x y).mpr hy
  refine ⟨b, fun x hx ↦ ?_⟩
  obtain ⟨y, hyb, hy⟩ := hb x hx
  exact ⟨y, hyb, (hP x y).mp hy⟩

/-! ## The equivalence with `𝗜𝚺 (n + 1)` -/

/-- A theory extending `𝗣𝗔⁻` that proves the induction axiom and the collection axiom of every
strict prenex `𝚺-[n + 1]` formula is at least as strong as `𝗜𝚺 (n + 1)`.
- [HP98, Theorem I.2.5(3)]
- [HP98, Lemma I.2.9]
- [HP98, Lemma I.2.11] -/
theorem hierarchyInduction_of_strictInduction (n : ℕ) (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T]
    (hind : ∀ φ : ArithmeticSemiformula ℕ 1,
      StrictHierarchy 𝚺 (n + 1) φ → T ⊢ .univCl (succInd φ))
    (hcol : ∀ φ : ArithmeticSemiformula ℕ 2,
      StrictHierarchy 𝚺 (n + 1) φ → T ⊢ .univCl (collectionAxiom φ)) :
    𝗜𝚺 (n + 1) ⪯ T := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T :=
    WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻) inferInstance
  apply WeakerThan.ofAxm!
  intro σ hσ
  rcases hσ with hσ | ⟨φ, hφ, rfl⟩
  · exact WeakerThan.pbl (h := inferInstance) (by_axm hσ)
  · apply Arithmetic.complete.{0}
    intro M _ _
    have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
      models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance
    have hC : StrictCollection M (n + 1) :=
      strictCollection_of_models_collectionAxiom fun ψ hψ ↦
        consequence_iff.mp (Theory.Proof.sound (hcol ψ hψ)) M inferInstance
    suffices ∀ f : ℕ → M, φ.Eval ![0] f → (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) →
        ∀ x, φ.Eval ![x] f by
      simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
        Matrix.constant_eq_singleton] using this
    intro f hzero hsucc
    obtain ⟨ψ, hψ, heval⟩ := exists_strictHierarchy_eval_iff hC hφ f
    have hInd : M↓[ℒₒᵣ] ⊧ (.univCl (succInd ψ) : ArithmeticSentence) :=
      consequence_iff.mp (Theory.Proof.sound (hind ψ hψ)) M inferInstance
    have hind' : ∀ g : ℕ → M, ψ.Eval ![0] g → (∀ x, ψ.Eval ![x] g → ψ.Eval ![x + 1] g) →
        ∀ x, ψ.Eval ![x] g := by
      simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
        Matrix.constant_eq_singleton] using hInd
    intro x
    refine (heval x).mp (hind' f ((heval 0).mpr hzero) (fun y hy ↦ (heval (y + 1)).mpr ?_) x)
    exact hsucc y ((heval y).mp hy)

/-- The finite theory is equivalent to `𝗜𝚺 (n + 1)`.
- [HP98, Theorem I.2.52] -/
theorem finiteAxiomatization_equiv (n : ℕ) : finiteAxiomatization n ≊ 𝗜𝚺 (n + 1) := by
  apply Equiv.antisymm_iff.mpr
  constructor
  · exact WeakerThan.ofAxm! (provable_finiteAxiomatization n)
  · exact hierarchyInduction_of_strictInduction n _
      (fun _ hφ ↦ provable_succInd_of_strictHierarchy hφ)
      (fun _ hφ ↦ provable_collectionAxiom_of_strictHierarchy hφ)

/-- For `n ≥ 1`, `𝗜𝚺 n` is finitely axiomatizable.
- [HP98, Theorem I.2.52] -/
theorem finiteAxiomatizable (n : ℕ) (hn : 1 ≤ n) : FiniteAxiomatizable (𝗜𝚺 n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨finiteAxiomatization m, by simp, finiteAxiomatization_equiv m⟩

/-! ## The level of the finite theory in the arithmetical hierarchy -/

section Hierarchy

variable {n : ℕ}

/-! The induction and the collection axiom are universal closures of Boolean combinations of
formulas of level at most `𝚺-[n + 1]`, so `Hierarchy.iff_iff` splits the biconditionals and
`Hierarchy.dummy_sigma`, `Hierarchy.dummy_pi` absorb the quantifier blocks that raise the level
by one. -/
attribute [local simp] Hierarchy.iff_iff Hierarchy.dummy_sigma Hierarchy.dummy_pi

@[simp]
lemma hierarchy_indSentence : Hierarchy 𝚷 (n + 3) (indSentence n) := by
  have h₂ : ∀ Γ : Polarity, Hierarchy Γ (n + 2) (indFormula n) := fun _ ↦
    hierarchy_indFormula.strict_mono _ (by omega)
  have h₃ : ∀ Γ : Polarity, Hierarchy Γ (n + 3) (indFormula n) := fun _ ↦
    hierarchy_indFormula.strict_mono _ (by omega)
  simp [indSentence, succInd, h₂, h₃]

@[simp]
lemma hierarchy_collSentence : Hierarchy 𝚷 (n + 3) (collSentence n) := by
  have h₂ : ∀ Γ : Polarity, Hierarchy Γ (n + 2) (collFormula n) := fun _ ↦
    hierarchy_collFormula.strict_mono _ (by omega)
  have h₃ : ∀ Γ : Polarity, Hierarchy Γ (n + 3) (collFormula n) := fun _ ↦
    hierarchy_collFormula.strict_mono _ (by omega)
  simp [collSentence, collectionAxiom, h₂, h₃]

/-- Every axiom of the finite theory is `𝚷-[n + 3]`.
- [HP98, Corollary I.4.34(1)] -/
lemma hierarchy_of_mem_finiteAxiomatization {σ : ArithmeticSentence}
    (hσ : σ ∈ finiteAxiomatization n) : Hierarchy 𝚷 (n + 3) σ := by
  rcases hσ with (hσ | hσ) | rfl | rfl
  · exact (Hierarchy.of_mem_peanoMinus hσ).mono (by omega)
  · exact hierarchy_of_tarski hσ
  · exact hierarchy_indSentence
  · exact hierarchy_collSentence

end Hierarchy

/-- Every member of a finset of arithmetic sentences bounds the hierarchy level of its
conjunction. -/
private lemma hierarchy_finsetConj_iff {Γ : Polarity} {s : ℕ} {F : Finset ArithmeticSentence} :
    Hierarchy Γ s F.conj ↔ ∀ σ ∈ F, Hierarchy Γ s σ := by
  simp [Finset.conj]

/-- For `n ≥ 1`, `𝗜𝚺 n` is axiomatized by a single `𝚷-[n + 2]` sentence.
- [HP98, Corollary I.4.34(1)]
- [HP98, Remark I.4.35(1)] -/
theorem exists_pi_axiomatization (n : ℕ) (hn : 1 ≤ n) :
    ∃ σ : 𝚷-[n + 2].Sentence, ({σ.val} : ArithmeticTheory) ≊ 𝗜𝚺 n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨F, hsub, heq⟩ := finiteAxiomatizable_iff_exists_finset.mp
    (FiniteAxiomatizable.of_finite (finiteAxiomatization_finite (n := m)))
  have hσ : Hierarchy 𝚷 (m + 1 + 2) F.conj := by
    rw [show m + 1 + 2 = m + 3 by omega]
    exact hierarchy_finsetConj_iff.mpr fun σ hσ ↦ hierarchy_of_mem_finiteAxiomatization (hsub hσ)
  exact ⟨.mkPi F.conj hσ,
    ((equiv_singleton_Fconj F).trans heq).trans (finiteAxiomatization_equiv m)⟩

end ISigma

end LO.FirstOrder.Arithmetic
