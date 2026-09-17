module

public import Foundation.FirstOrder.Arithmetic.Definability.Absoluteness
public import Foundation.FirstOrder.Arithmetic.Prenex
public import Foundation.FirstOrder.Arithmetic.Schemata
public import Foundation.FirstOrder.LK.Completeness
public import AlphaCentauri.ToFoundation.Hierarchy

/-!
# Provably total functions

Provably total and provably functional functions, their graph formulas, and closure under
composition.
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Arithmetic

section
variable {k l : ℕ} {V : Type*} [ORingStructure V]

/-- The totality sentence `∀ x⃗, ∃ y, φ(y, x⃗)` of a graph formula `φ`.
- [HP98, Definition I.1.51] -/
def totalitySentence (φ : 𝚺₁.Semisentence (k + 1)) : ArithmeticSentence := ∀¹* ∃¹ φ.val

@[simp] lemma hierarchy_totalitySentence (φ : 𝚺₁.Semisentence (k + 1)) :
    Hierarchy 𝚷 2 (totalitySentence φ) :=
  Hierarchy.allClosure_iff.mpr (Hierarchy.accum φ.sigma_prop.exs 𝚷)

lemma models_totalitySentence_iff {φ : 𝚺₁.Semisentence (k + 1)} :
    V↓[ℒₒᵣ] ⊧ totalitySentence φ ↔ ∀ v : Fin k → V, ∃ y, φ.val.Evalb (y :> v) := by
  simp [totalitySentence, models_iff]

/-- The functionality sentence `∀ x⃗, ∀ y y', φ(y, x⃗) ∧ φ(y', x⃗) → y = y'` of a graph formula `φ`.
- [HP98, Definition I.1.51(2)] -/
def functionalitySentence (φ : 𝚺₁.Semisentence (k + 1)) : ArithmeticSentence :=
  ∀¹* ∀¹ ∀¹ (((Rew.subst (#1 :> fun i : Fin k ↦ #i.succ.succ) ▹ φ.val) ⋏
    (Rew.subst (#0 :> fun i : Fin k ↦ #i.succ.succ) ▹ φ.val)) 🡒 “#1 = #0”)

lemma models_functionalitySentence_iff {φ : 𝚺₁.Semisentence (k + 1)} :
    V↓[ℒₒᵣ] ⊧ functionalitySentence φ ↔ ∀ (v : Fin k → V) (y y'),
      φ.val.Evalb (y :> v) → φ.val.Evalb (y' :> v) → y = y' := by
  simp [functionalitySentence, models_iff, Semiformula.eval_rew, Function.comp_def,
    Matrix.comp_vecCons', Empty.eq_elim]

/-- A graph formula for the composite `fun x⃗ ↦ f (fun i ↦ g i x⃗)`.
- [HP98, Lemma I.1.53] -/
def compGraph (ψ : 𝚺₁.Semisentence (l + 1)) (χ : Fin l → 𝚺₁.Semisentence (k + 1)) :
    𝚺₁.Semisentence (k + 1) :=
  .mkSigma
    (Rew.bind ![] (#·) ▹ (∃¹* ((Rew.bind (&0 :> (#·)) Empty.elim ▹ ψ.val) ⋏
      Matrix.conj fun i ↦ Rew.bind (#i :> (&·.succ)) Empty.elim ▹ (χ i).val)))
    (Hierarchy.rew _ (Hierarchy.exsClosure (by simp)))

@[simp] lemma eval_compGraph (ψ : 𝚺₁.Semisentence (l + 1))
    (χ : Fin l → 𝚺₁.Semisentence (k + 1)) (w : Fin (k + 1) → V) :
    (compGraph ψ χ).val.Evalb w ↔
      ∃ z : Fin l → V, ψ.val.Evalb (w 0 :> z) ∧ ∀ i, (χ i).val.Evalb (z i :> (w ·.succ)) := by
  simp [compGraph, Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq,
    Matrix.comp_vecCons', Empty.eq_elim]

/-- `compGraph ψ χ` defines the composite of the functions defined by `ψ` and `χ`.
- [HP98, Lemma I.1.53] -/
lemma definedFunction_compGraph {ψ : 𝚺₁.Semisentence (l + 1)}
    {χ : Fin l → 𝚺₁.Semisentence (k + 1)} {f : (Fin l → V) → V} {g : Fin l → (Fin k → V) → V}
    (hf : 𝚺₁.DefinedFunction f ψ) (hg : ∀ i, 𝚺₁.DefinedFunction (g i) (χ i)) :
    𝚺₁.DefinedFunction (fun v ↦ f fun i ↦ g i v) (compGraph ψ χ) :=
  .mk fun w ↦ by
    simp only [eval_compGraph, hf.iff, (hg _).iff, Matrix.cons_val_zero, Matrix.cons_val_succ]
    exact ⟨fun ⟨z, hz, hχ⟩ ↦ by simpa [funext hχ] using hz,
      fun e ↦ ⟨_, by simpa using e, fun _ ↦ rfl⟩⟩

lemma definablePred_evalb (φ : 𝚺₁.Semisentence (k + 1)) (v : Fin k → V) :
    𝚺₁-Predicate fun y ↦ φ.val.Evalb (y :> v) :=
  HierarchySymbol.Definable.mkPolarity (Γ := 𝚺) (m := 1)
    (Rew.bind (#0 :> fun i ↦ &(v i)) Empty.elim ▹ φ.val)
    (Hierarchy.rew _ (by simp)) fun w ↦ by
      simp [Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons', Empty.eq_elim]

/-- `φ` refined so that the value is the least witness: `φ(y, x⃗) ∧ ∀ y' < y, ¬φ(y', x⃗)`.
- [HP98, Lemma IV.3.4] -/
def leastGraph (φ : 𝚺₁.Semisentence (k + 1)) : ArithmeticSemisentence (k + 1) :=
  φ.val ⋏ (∀¹[“#0 < #1”] ∼(Rew.subst (#0 :> fun i : Fin k ↦ #i.succ.succ) ▹ φ.val))

@[simp] lemma eval_leastGraph (φ : 𝚺₁.Semisentence (k + 1)) (w : Fin (k + 1) → V) :
    (leastGraph φ).Evalb w ↔ φ.val.Evalb w ∧ ∀ y < w 0, ¬φ.val.Evalb (y :> (w ·.succ)) := by
  simp [leastGraph, Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons', Empty.eq_elim]

/-- A $\Delta_0$ matrix `θ` such that `∃ z, θ(z, y, x⃗)` is `𝗜𝚺₁`-provably equivalent to `φ(y, x⃗)`,
fixed once and for all so that it does not depend on the ambient theory.
- [HP98, Theorem I.1.5] -/
noncomputable def minimalGraphMatrix (φ : 𝚺₁.Semisentence (k + 1)) : 𝚺₀.Semisentence (k + 2) :=
  Classical.choose (exists_matrix_provable (Γ := 𝚺) (s := 1) 𝗜𝚺₁ φ.sigma_prop)

lemma provable_iff_exists_minimalGraphMatrix (φ : 𝚺₁.Semisentence (k + 1)) :
    𝗜𝚺₁ ⊢ ∀¹* (φ.val 🡘 ∃¹ (minimalGraphMatrix φ).val) := by
  simpa [minimalGraphMatrix] using
    Classical.choose_spec (exists_matrix_provable (Γ := 𝚺) (s := 1) 𝗜𝚺₁ φ.sigma_prop)

lemma models_iff_exists_minimalGraphMatrix {φ : 𝚺₁.Semisentence (k + 1)} :
    V↓[ℒₒᵣ] ⊧ ∀¹* (φ.val 🡘 ∃¹ (minimalGraphMatrix φ).val) ↔
      ∀ v : Fin (k + 1) → V, φ.val.Evalb v ↔ ∃ z, (minimalGraphMatrix φ).val.Evalb (z :> v) := by
  simp [models_iff]

/-- `∃ z ≤ n, z + y = n ∧ θ(z, y, x⃗)`: there is a pair `(z, y)` with sum `n` at which `θ` holds.
- [HP98, Lemma IV.3.4] -/
def pairGraph (θ : 𝚺₀.Semisentence (k + 2)) : ArithmeticSemisentence (k + 2) :=
  (“(#0 + #2) = #1” ⋏
    (Rew.subst (#0 :> #2 :> fun i : Fin k ↦ #i.succ.succ.succ) ▹ θ.val)).bexsLTSucc
    (#0 : ArithmeticSemiterm Empty (k + 2))

@[simp] lemma eval_pairGraph [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (θ : 𝚺₀.Semisentence (k + 2)) (w : Fin (k + 2) → V) :
    (pairGraph θ).Evalb w ↔
      ∃ z ≤ w 0, z + w 1 = w 0 ∧ θ.val.Evalb (z :> w 1 :> (w ·.succ.succ)) := by
  simp [pairGraph, Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons', Empty.eq_elim,
    Matrix.constant_eq_singleton]

/-- `∃ y' ≤ n, ∃ z' ≤ n, z' + y' = n ∧ θ(z', y', x⃗)`: some pair with sum `n` witnesses `θ`. -/
def existsAtSum (θ : 𝚺₀.Semisentence (k + 2)) : ArithmeticSemisentence (k + 1) :=
  ((“(#0 + #1) = #2” ⋏
    (Rew.subst (#0 :> #1 :> fun i : Fin k ↦ #i.succ.succ.succ) ▹ θ.val)).bexsLTSucc
      (#1 : ArithmeticSemiterm Empty (k + 2))).bexsLTSucc (#0 : ArithmeticSemiterm Empty (k + 1))

@[simp] lemma eval_existsAtSum [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (θ : 𝚺₀.Semisentence (k + 2))
    (w : Fin (k + 1) → V) :
    (existsAtSum θ).Evalb w ↔
      ∃ y' ≤ w 0, ∃ z' ≤ w 0, z' + y' = w 0 ∧ θ.val.Evalb (z' :> y' :> (w ·.succ)) := by
  simp [existsAtSum, Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons', Empty.eq_elim,
    Matrix.constant_eq_singleton]

/-- The minimal-pair refinement of `θ`: the code `n` is least among sums of pairs witnessing `θ`,
and `y` is least among values at that sum.
- [HP98, Lemma IV.3.4] -/
def minimalPairGraph (θ : 𝚺₀.Semisentence (k + 2)) : ArithmeticSemisentence (k + 1) :=
  ∃¹ (pairGraph θ ⋏
    (∀¹[“#0 < #1”] ∼(Rew.subst (#0 :> fun i : Fin k ↦ #i.succ.succ.succ) ▹ existsAtSum θ)) ⋏
    (∀¹[“#0 < #2”] ∼(Rew.subst (#1 :> #0 :> fun i : Fin k ↦ #i.succ.succ.succ) ▹ pairGraph θ)))

@[simp] lemma eval_minimalPairGraph [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (θ : 𝚺₀.Semisentence (k + 2))
    (w : Fin (k + 1) → V) :
    (minimalPairGraph θ).Evalb w ↔
      ∃ n, (∃ z ≤ n, z + w 0 = n ∧ θ.val.Evalb (z :> w 0 :> (w ·.succ))) ∧
        (∀ n' < n, ¬∃ y' ≤ n', ∃ z' ≤ n', z' + y' = n' ∧ θ.val.Evalb (z' :> y' :> (w ·.succ))) ∧
        (∀ y' < w 0, ¬∃ z' ≤ n, z' + y' = n ∧ θ.val.Evalb (z' :> y' :> (w ·.succ))) := by
  simp [minimalPairGraph, Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons',
    Empty.eq_elim]

/-- `φ` refined so that the pair of the existential witness and the value in
`minimalGraphMatrix φ` is least, using only $\Delta_0$ minimization.
- [Bek99, §1]
- [HP98, Lemma IV.3.4] -/
noncomputable def minimalGraph (φ : 𝚺₁.Semisentence (k + 1)) : 𝚺₁.Semisentence (k + 1) :=
  .mkSigma (minimalPairGraph (minimalGraphMatrix φ)) (by
    unfold minimalPairGraph pairGraph existsAtSum
    apply Hierarchy.exs
    simp)

private lemma definablePred_existsAtSum (θ : 𝚺₀.Semisentence (k + 2)) (v : Fin k → V) :
    𝚺₀-Predicate fun n ↦ (existsAtSum θ).Evalb (n :> v) :=
  HierarchySymbol.Definable.mkPolarity (Γ := 𝚺) (m := 0)
    (Rew.bind (#0 :> fun i ↦ &(v i)) Empty.elim ▹ existsAtSum θ)
    (Hierarchy.rew _ (by simp [existsAtSum])) fun w ↦ by
      simp [Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons', Empty.eq_elim]

private lemma definablePred_pairGraph (θ : 𝚺₀.Semisentence (k + 2)) (n₀ : V) (v : Fin k → V) :
    𝚺₀-Predicate fun y ↦ (pairGraph θ).Evalb (n₀ :> y :> v) :=
  HierarchySymbol.Definable.mkPolarity (Γ := 𝚺) (m := 0)
    (Rew.bind (&n₀ :> #0 :> fun i ↦ &(v i)) Empty.elim ▹ pairGraph θ)
    (Hierarchy.rew _ (by simp [pairGraph])) fun w ↦ by
      simp [Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons', Empty.eq_elim]

open PeanoMinus in
/-- In any model of `𝗜𝚺₀`, if a pair witnesses `θ` at all, then the minimal-pair refinement of
`θ` has an existing and unique value.
- [HP98, Lemma IV.3.4] -/
private lemma models_existsUnique_minimalPairGraph {θ : 𝚺₀.Semisentence (k + 2)}
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {v : Fin k → V} (hex : ∃ y z : V, θ.val.Evalb (z :> y :> v)) :
    (∃ y, (minimalPairGraph θ).Evalb (y :> v)) ∧
      ∀ y y', (minimalPairGraph θ).Evalb (y :> v) → (minimalPairGraph θ).Evalb (y' :> v) →
        y = y' := by
  obtain ⟨y₀, z₀, hz₀⟩ := hex
  have hP : (existsAtSum θ).Evalb ((z₀ + y₀) :> v) :=
    (eval_existsAtSum θ _).mpr ⟨y₀, by simp, z₀, by simp, by simp, by simpa using hz₀⟩
  obtain ⟨n₀, hn₀, hnmin⟩ := InductionOnHierarchy.least_number 𝚺 0
    (definablePred_existsAtSum θ v) hP
  obtain ⟨y₁, hy₁len, z₁, hz₁len, hsum₁, hθ₁⟩ := (eval_existsAtSum θ _).mp hn₀
  have hPy : (pairGraph θ).Evalb (n₀ :> y₁ :> v) :=
    (eval_pairGraph θ _).mpr ⟨z₁, hz₁len, hsum₁, hθ₁⟩
  obtain ⟨ymin, hymin, hyminmin⟩ := InductionOnHierarchy.least_number 𝚺 0
    (definablePred_pairGraph θ n₀ v) hPy
  have toExistsAtSum : ∀ {n y : V}, (∃ z ≤ n, z + y = n ∧ θ.val.Evalb (z :> y :> v)) →
      ∃ y' ≤ n, ∃ z' ≤ n, z' + y' = n ∧ θ.val.Evalb (z' :> y' :> v) := by
    rintro n y ⟨z, hzn, hsum, hθ⟩
    exact ⟨y, by rw [← hsum]; simp, z, hzn, hsum, hθ⟩
  refine ⟨⟨ymin, ?_⟩, ?_⟩
  · simp only [eval_minimalPairGraph]
    exact ⟨n₀, by simpa using hymin, by simpa using hnmin, by simpa using hyminmin⟩
  · rintro y y' hy hy'
    simp only [eval_minimalPairGraph] at hy hy'
    obtain ⟨n, hyA, hyB, hyC⟩ := hy
    obtain ⟨n', hy'A, hy'B, hy'C⟩ := hy'
    have hnn' : n = n' := by
      rcases lt_trichotomy n n' with hlt | rfl | hlt
      · exact absurd (toExistsAtSum hyA) (hy'B n hlt)
      · rfl
      · exact absurd (toExistsAtSum hy'A) (hyB n' hlt)
    subst hnn'
    rcases lt_trichotomy y y' with hlt | rfl | hlt
    · exact absurd hyA (hy'C y hlt)
    · rfl
    · exact absurd hy'A (hyC y' hlt)

/-- The unique-existence form of totality, `∀ x⃗, ∃! y, φ*(y, x⃗)`, where `φ*` is the least-witness
refinement `leastGraph φ`.
- [HP98, Definition I.1.51]
- [HP98, Lemma IV.3.4] -/
def uniqueTotalitySentence (φ : 𝚺₁.Semisentence (k + 1)) : ArithmeticSentence :=
  ∀¹* ((∃¹ leastGraph φ) ⋏ (∀¹ ∀¹
    (((Rew.subst (#1 :> fun i : Fin k ↦ #i.succ.succ) ▹ leastGraph φ) ⋏
      (Rew.subst (#0 :> fun i : Fin k ↦ #i.succ.succ) ▹ leastGraph φ)) 🡒 “#1 = #0”)))

lemma models_uniqueTotalitySentence_iff {φ : 𝚺₁.Semisentence (k + 1)} :
    V↓[ℒₒᵣ] ⊧ uniqueTotalitySentence φ ↔ ∀ v : Fin k → V,
      (∃ y, (leastGraph φ).Evalb (y :> v)) ∧
        ∀ y y', (leastGraph φ).Evalb (y :> v) → (leastGraph φ).Evalb (y' :> v) → y = y' := by
  simp [uniqueTotalitySentence, models_iff, Semiformula.eval_rew, Function.comp_def,
    Matrix.comp_vecCons', Empty.eq_elim]

end

end Arithmetic

open Arithmetic

namespace ArithmeticTheory

variable {T U : ArithmeticTheory} {k : ℕ} {f : (Fin k → ℕ) → ℕ} {φ : 𝚺₁.Semisentence (k + 1)}

/-- `f` is `T`-provably total via `φ` iff `φ` defines the graph of `f` over `ℕ` and `T` proves its
totality sentence.
- [HP98, Definition I.1.51]
- [HP98, Definition IV.3.1] -/
structure ProvablyTotalVia (T : ArithmeticTheory) (f : (Fin k → ℕ) → ℕ)
    (φ : 𝚺₁.Semisentence (k + 1)) : Prop where
  defined : HierarchySymbol.DefinedFunction (V := ℕ) f φ
  total : T ⊢ totalitySentence φ

/-- `f` is `T`-provably functional via `φ` iff `f` is `T`-provably total via `φ` and `T` proves
that `φ` is single-valued.
- [HP98, Definition I.1.51(2)] -/
structure ProvablyFunctionalVia (T : ArithmeticTheory) (f : (Fin k → ℕ) → ℕ)
    (φ : 𝚺₁.Semisentence (k + 1)) : Prop extends T.ProvablyTotalVia f φ where
  functional : T ⊢ functionalitySentence φ

/-- `f` is `T`-provably total: some $\Sigma_1$ formula witnesses `T.ProvablyTotalVia f`.
- [HP98, Definition I.1.51]
- [HP98, Definition IV.3.1]
- [AB05, §10.2] -/
def ProvablyTotal (T : ArithmeticTheory) (f : (Fin k → ℕ) → ℕ) : Prop :=
  ∃ φ, T.ProvablyTotalVia f φ

/-- `f` is `T`-provably functional: some $\Sigma_1$ formula witnesses `T.ProvablyFunctionalVia f`.
- [HP98, Definition I.1.51(2)] -/
def ProvablyFunctional (T : ArithmeticTheory) (f : (Fin k → ℕ) → ℕ) : Prop :=
  ∃ φ, T.ProvablyFunctionalVia f φ

/-- The class of `T`-provably total functions of arity `k`.
- [AB05, §10.2]
- [Bek99, §1] -/
def provablyTotalFunctions (T : ArithmeticTheory) (k : ℕ) : Set ((Fin k → ℕ) → ℕ) :=
  {f | T.ProvablyTotal f}

@[simp] lemma mem_provablyTotalFunctions :
    f ∈ T.provablyTotalFunctions k ↔ T.ProvablyTotal f := .rfl

namespace ProvablyTotalVia

lemma toProvablyTotal (h : T.ProvablyTotalVia f φ) : T.ProvablyTotal f := ⟨φ, h⟩

lemma graph_iff (h : T.ProvablyTotalVia f φ) {v : Fin (k + 1) → ℕ} :
    φ.val.Evalb v ↔ v 0 = f (v ·.succ) := h.defined.iff

lemma mono (h : T.ProvablyTotalVia f φ) (hT : T ⪯ U) : U.ProvablyTotalVia f φ :=
  ⟨h.defined, hT.pbl h.total⟩

/-- Provable totality depends only on the $\Pi_2$ consequences of the theory.
- [AB05, §10.2] -/
lemma of_Pi2 (h : T.ProvablyTotalVia f φ)
    (H : ∀ σ : ArithmeticSentence, Hierarchy 𝚷 2 σ → T ⊢ σ → U ⊢ σ) : U.ProvablyTotalVia f φ :=
  ⟨h.defined, H _ (by simp) h.total⟩

lemma models (h : T.ProvablyTotalVia f φ)
    (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (v : Fin k → V) : ∃ y, φ.val.Evalb (y :> v) :=
  models_totalitySentence_iff.mp (consequence_iff'.mp (Theory.Proof.sound h.total) V) v

lemma of_models [𝗘𝗤 ℒₒᵣ ⪯ T] (hf : HierarchySymbol.DefinedFunction (V := ℕ) f φ)
    (H : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T], ∀ v : Fin k → V,
      ∃ y, φ.val.Evalb (y :> v)) : T.ProvablyTotalVia f φ :=
  ⟨hf, Arithmetic.complete T _ fun V _ _ ↦ models_totalitySentence_iff.mpr (H V)⟩

/-- Over `ℕ`, the least-witness refinement of `φ` defines the same graph of `f`.
- [HP98, Lemma IV.3.4] -/
lemma leastGraph_iff (h : T.ProvablyTotalVia f φ) {v : Fin (k + 1) → ℕ} :
    (leastGraph φ).Evalb v ↔ v 0 = f (v ·.succ) := by
  simp [h.graph_iff]
  omega

open PeanoMinus in
/-- Over a theory containing `𝗜𝚺₁`, the `∃` form of totality implies the stronger `∃!` form
stating that the least witness of `φ` exists and is unique in every model of `T`.
- [HP98, Lemma IV.3.4] -/
lemma exists_unique [𝗜𝚺₁ ⪯ T] (h : T.ProvablyTotalVia f φ) : T ⊢ uniqueTotalitySentence φ := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance inferInstance
  refine Arithmetic.complete T _ fun (V : Type) _ _ ↦
    models_uniqueTotalitySentence_iff.mpr fun v ↦ ?_
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ T inferInstance
  constructor
  · obtain ⟨y, hy⟩ := h.models V v
    obtain ⟨y₀, h₀, hmin⟩ := InductionOnHierarchy.least_number 𝚺 1 (definablePred_evalb φ v) hy
    exact ⟨y₀, by simpa using ⟨h₀, hmin⟩⟩
  · intro y y' hy hy'
    simp only [eval_leastGraph, Matrix.cons_val_zero, Matrix.cons_val_succ] at hy hy'
    grind

open PeanoMinus in
/-- Over a theory containing `𝗜𝚺₁`, a `T`-provably total function is `T`-provably functional via
the minimal-pair refinement `minimalGraph φ` of `φ`, which is obtained from `φ` by only
$\Delta_0$ minimization.
- [Bek99, §1]
- [HP98, Lemma IV.3.4] -/
lemma provablyFunctionalVia_minimalGraph [𝗜𝚺₁ ⪯ T] (h : T.ProvablyTotalVia f φ) :
    T.ProvablyFunctionalVia f (minimalGraph φ) := by
  have hTIS1 : T ⊢ ∀¹* (φ.val 🡘 ∃¹ (minimalGraphMatrix φ).val) :=
    Entailment.WeakerThan.pbl (provable_iff_exists_minimalGraphMatrix φ)
  have heqN : ∀ v : Fin (k + 1) → ℕ,
      φ.val.Evalb v ↔ ∃ z, (minimalGraphMatrix φ).val.Evalb (z :> v) :=
    models_iff_exists_minimalGraphMatrix.mp
      (consequence_iff'.mp (Theory.Proof.sound (provable_iff_exists_minimalGraphMatrix φ)) ℕ)
  have hforce : ∀ (y : ℕ) (x : Fin k → ℕ) (z : ℕ),
      (minimalGraphMatrix φ).val.Evalb (z :> y :> x) → y = f x := fun y x z hz ↦ by
    simpa using h.graph_iff.mp ((heqN (y :> x)).mpr ⟨z, hz⟩)
  have hforce' : ∀ (y : ℕ) (x : Fin k → ℕ),
      (minimalPairGraph (minimalGraphMatrix φ)).Evalb (y :> x) → y = f x := fun y x hy ↦ by
    obtain ⟨_, ⟨z, _, _, hθ⟩, _, _⟩ := (eval_minimalPairGraph _ _).mp hy
    exact hforce y x z hθ
  have hmodelN : ∀ x : Fin k → ℕ,
      (∃ y, (minimalPairGraph (minimalGraphMatrix φ)).Evalb (y :> x)) ∧
        ∀ y y', (minimalPairGraph (minimalGraphMatrix φ)).Evalb (y :> x) →
          (minimalPairGraph (minimalGraphMatrix φ)).Evalb (y' :> x) → y = y' := fun x ↦ by
    apply models_existsUnique_minimalPairGraph
    obtain ⟨z, hz⟩ := (heqN (f x :> x)).mp (h.graph_iff.mpr (by simp))
    exact ⟨f x, z, hz⟩
  have hdef : HierarchySymbol.DefinedFunction (V := ℕ) f (minimalGraph φ) := .mk fun v ↦ by
    change (minimalPairGraph (minimalGraphMatrix φ)).Evalb v ↔ v 0 = f (fun i ↦ v i.succ)
    constructor
    · exact fun hv ↦ hforce' (v 0) (fun i ↦ v i.succ) (by simpa using hv)
    · intro hv
      obtain ⟨y₁, hy₁⟩ := (hmodelN (fun i ↦ v i.succ)).1
      have hy₁eq : y₁ = f (fun i ↦ v i.succ) := hforce' y₁ (fun i ↦ v i.succ) hy₁
      have hveq : v = v 0 :> fun i ↦ v i.succ := by
        ext i; cases i using Fin.cases <;> simp
      rw [hveq, hv]
      simpa [hy₁eq] using hy₁
  have hmodelV : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T], ∀ v : Fin k → V,
      (∃ y, (minimalPairGraph (minimalGraphMatrix φ)).Evalb (y :> v)) ∧
        ∀ y y', (minimalPairGraph (minimalGraphMatrix φ)).Evalb (y :> v) →
          (minimalPairGraph (minimalGraphMatrix φ)).Evalb (y' :> v) → y = y' := by
    intro V _ _ v
    have hVIS1 : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₁ T inferInstance
    apply models_existsUnique_minimalPairGraph
    obtain ⟨y, hy⟩ := h.models V v
    exact ⟨y, (models_iff_exists_minimalGraphMatrix.mp
      (consequence_iff'.mp (Theory.Proof.sound hTIS1) V) (y :> v)).mp hy⟩
  have hEQ : 𝗘𝗤 ℒₒᵣ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance inferInstance
  have htotal : T ⊢ totalitySentence (minimalGraph φ) :=
    Arithmetic.complete T _ fun (V : Type) _ _ ↦
      models_totalitySentence_iff.mpr fun v ↦ (hmodelV V v).1
  have hfunctional : T ⊢ functionalitySentence (minimalGraph φ) :=
    Arithmetic.complete T _ fun (V : Type) _ _ ↦
      models_functionalitySentence_iff.mpr fun v y y' hy hy' ↦ by
        simpa [minimalGraph] using (hmodelV V v).2 y y'
          (by simpa [minimalGraph] using hy) (by simpa [minimalGraph] using hy')
  exact ⟨⟨hdef, htotal⟩, hfunctional⟩

section
variable {l : ℕ} {g : (Fin l → ℕ) → ℕ} {h : Fin l → (Fin k → ℕ) → ℕ}
  {ψ : 𝚺₁.Semisentence (l + 1)} {χ : Fin l → 𝚺₁.Semisentence (k + 1)}

/-- The `T`-provably total functions are closed under composition.
- [HP98, Lemma I.1.53] -/
lemma comp [𝗘𝗤 ℒₒᵣ ⪯ T] (hg : T.ProvablyTotalVia g ψ) (hh : ∀ i, T.ProvablyTotalVia (h i) (χ i)) :
    T.ProvablyTotalVia (fun v ↦ g fun i ↦ h i v) (compGraph ψ χ) := by
  apply of_models (definedFunction_compGraph hg.defined fun i ↦ (hh i).defined)
  intro V _ _ v
  choose z hz using fun i ↦ (hh i).models V v
  obtain ⟨y, hy⟩ := hg.models V z
  exact ⟨y, by simpa using ⟨z, hy, hz⟩⟩

end

end ProvablyTotalVia

namespace ProvablyFunctionalVia

lemma toProvablyFunctional (h : T.ProvablyFunctionalVia f φ) : T.ProvablyFunctional f := ⟨φ, h⟩

lemma models (h : T.ProvablyFunctionalVia f φ) (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] :
    ∃ F : (Fin k → V) → V, 𝚺₁.DefinedFunction F φ := by
  have h₁ := models_functionalitySentence_iff.mp
    (consequence_iff'.mp (Theory.Proof.sound h.functional) V)
  choose F hF using h.toProvablyTotalVia.models V
  exact ⟨F, .mk fun v ↦ ⟨fun hv ↦ by simpa using h₁ _ _ _ (by simpa using hv) (hF _),
    fun e ↦ by simpa [← e] using hF (v ·.succ)⟩⟩

lemma of_models [𝗘𝗤 ℒₒᵣ ⪯ T] (hf : HierarchySymbol.DefinedFunction (V := ℕ) f φ)
    (H : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T],
      ∃ F : (Fin k → V) → V, 𝚺₁.DefinedFunction F φ) : T.ProvablyFunctionalVia f φ where
  toProvablyTotalVia := .of_models hf fun V _ _ v ↦ have ⟨F, hF⟩ := H V; ⟨F v, by simp [hF.iff]⟩
  functional := Arithmetic.complete T _ fun V _ _ ↦
    models_functionalitySentence_iff.mpr fun v y y' hy hy' ↦ by
      obtain ⟨F, hF⟩ := H V
      simp_all [hF.iff]

end ProvablyFunctionalVia

namespace ProvablyTotal

lemma mono (h : T.ProvablyTotal f) (hT : T ⪯ U) : U.ProvablyTotal f :=
  have ⟨_, h⟩ := h; ⟨_, h.mono hT⟩

/-- Provable totality depends only on the $\Pi_2$ consequences of the theory.
- [AB05, §10.2] -/
lemma of_Pi2 (h : T.ProvablyTotal f)
    (H : ∀ σ : ArithmeticSentence, Hierarchy 𝚷 2 σ → T ⊢ σ → U ⊢ σ) : U.ProvablyTotal f :=
  have ⟨_, h⟩ := h; ⟨_, h.of_Pi2 H⟩

section
variable [𝗘𝗤 ℒₒᵣ ⪯ T] {l : ℕ} {g : (Fin l → ℕ) → ℕ} {h : Fin l → (Fin k → ℕ) → ℕ}

/-- The `T`-provably total functions are closed under composition.
- [HP98, Lemma I.1.53] -/
lemma comp (hg : T.ProvablyTotal g) (hh : ∀ i, T.ProvablyTotal (h i)) :
    T.ProvablyTotal fun v ↦ g fun i ↦ h i v :=
  have ⟨_, hg⟩ := hg
  have ⟨_, hh⟩ := Classical.skolem.mp hh
  ⟨_, hg.comp hh⟩

end

/-- Over a theory containing `𝗜𝚺₁`, the `∃` form of totality implies the stronger `∃!` form.
- [HP98, Lemma IV.3.4] -/
lemma exists_unique [𝗜𝚺₁ ⪯ T] (h : T.ProvablyTotal f) :
    ∃ φ, T.ProvablyTotalVia f φ ∧ T ⊢ uniqueTotalitySentence φ :=
  have ⟨_, h⟩ := h; ⟨_, h, h.exists_unique⟩

end ProvablyTotal

lemma provablyTotalFunctions_subset (h : T ⪯ U) :
    T.provablyTotalFunctions k ⊆ U.provablyTotalFunctions k := fun _ hf ↦ hf.mono h

/-- The class of provably total functions depends only on the $\Pi_2$ consequences of the theory.
- [AB05, §10.2] -/
lemma provablyTotalFunctions_subset_of_Pi2
    (H : ∀ σ : ArithmeticSentence, Hierarchy 𝚷 2 σ → T ⊢ σ → U ⊢ σ) :
    T.provablyTotalFunctions k ⊆ U.provablyTotalFunctions k := fun _ hf ↦ hf.of_Pi2 H

namespace ProvablyFunctional

lemma toProvablyTotal (h : T.ProvablyFunctional f) : T.ProvablyTotal f :=
  have ⟨_, h⟩ := h; h.toProvablyTotalVia.toProvablyTotal

end ProvablyFunctional

/-- Over a theory containing `𝗜𝚺₁`, `T`-provable totality and `T`-provable functionality
coincide, identifying `provablyTotalFunctions` with Bek99's class of functions with a
`∃!`-provably total graph.
- [Bek99, §1] -/
theorem provablyTotal_iff_provablyFunctional [𝗜𝚺₁ ⪯ T] :
    T.ProvablyTotal f ↔ T.ProvablyFunctional f :=
  ⟨fun h ↦ have ⟨_, h⟩ := h; ⟨_, h.provablyFunctionalVia_minimalGraph⟩,
    ProvablyFunctional.toProvablyTotal⟩

end ArithmeticTheory

end FFL.FirstOrder
