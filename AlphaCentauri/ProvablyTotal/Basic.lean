module

public import Foundation.FirstOrder.Arithmetic.Definability.Absoluteness
public import Foundation.FirstOrder.Completeness

/-!
# Provably total functions

`T.ProvablyTotalVia f φ` says that the `𝚺₁` formula `φ` defines the graph of `f : (Fin k → ℕ) → ℕ`
over `ℕ`, and that `T` proves the totality sentence `∀ x⃗, ∃ y, φ(y, x⃗)`.
-/

@[expose] public section

namespace LO.FirstOrder

namespace Arithmetic

variable {L : Language} [L.LT] {ξ : Type*} {s : ℕ}

/-- Universal closure preserves the `𝚷-[s + 1]` classes.

The `∃¹*` counterpart is Foundation's `Hierarchy.exsClosure`; this is its dual and has no separate
counterpart in the literature. -/
lemma Hierarchy.allClosure :
    {n : ℕ} → {φ : Semiformula L ξ n} → Hierarchy 𝚷 (s + 1) φ → Hierarchy 𝚷 (s + 1) (∀¹* φ)
  |     0, _, hφ => hφ
  | _ + 1, φ, hφ => allClosure (φ := ∀¹ φ) hφ.all

variable {k : ℕ}

/-- The totality sentence `∀ x⃗, ∃ y, φ(y, x⃗)` of a graph formula `φ`.
- [HP98, Definition I.1.51] -/
def totalitySentence (φ : 𝚺₁.Semisentence (k + 1)) : ArithmeticSentence := ∀¹* ∃¹ φ.val

@[simp] lemma hierarchy_totalitySentence (φ : 𝚺₁.Semisentence (k + 1)) :
    Hierarchy 𝚷 2 (totalitySentence φ) :=
  Hierarchy.allClosure (Hierarchy.accum φ.sigma_prop.exs 𝚷)

variable {l : ℕ}

/-- The graph formula of the composite `fun x⃗ ↦ f (fun i ↦ g i x⃗)`, assembled from a graph
formula `ψ` of `f` and graph formulas `χ` of the `g i`: the free variable `0` carries the value and
the free variables `i + 1` the arguments, while the `l` bound variables carry the intermediate
values.
- [HP98, Lemma I.1.53] -/
def compGraph (ψ : 𝚺₁.Semisentence (l + 1)) (χ : Fin l → 𝚺₁.Semisentence (k + 1)) :
    𝚺₁.Semisentence (k + 1) :=
  .mkSigma
    (Rew.bind ![] (#·) ▹ (∃¹* ((Rew.bind (&0 :> (#·)) Empty.elim ▹ ψ.val) ⋏
      Matrix.conj fun i ↦ Rew.bind (#i :> (&·.succ)) Empty.elim ▹ (χ i).val)))
    (Hierarchy.rew _ (Hierarchy.exsClosure (by simp)))

@[simp] lemma eval_compGraph {V : Type*} [ORingStructure V] (ψ : 𝚺₁.Semisentence (l + 1))
    (χ : Fin l → 𝚺₁.Semisentence (k + 1)) (w : Fin (k + 1) → V) :
    (compGraph ψ χ).val.Evalb w ↔
      ∃ z : Fin l → V, ψ.val.Evalb (w 0 :> z) ∧ ∀ i, (χ i).val.Evalb (z i :> (w ·.succ)) := by
  simp [compGraph, Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq,
    Matrix.comp_vecCons', Empty.eq_elim]

lemma models_totalitySentence_iff {V : Type*} [ORingStructure V] {φ : 𝚺₁.Semisentence (k + 1)} :
    V↓[ℒₒᵣ] ⊧ totalitySentence φ ↔ ∀ v : Fin k → V, ∃ y, φ.val.Evalb (y :> v) := by
  simp [totalitySentence, models_iff]

end Arithmetic

open Arithmetic

variable {T U : ArithmeticTheory} {k : ℕ} {f : (Fin k → ℕ) → ℕ} {φ : 𝚺₁.Semisentence (k + 1)}

/-- `f` is `T`-provably total via `φ`: the `𝚺₁` formula `φ` defines the graph of `f` over `ℕ`, and
`T` proves that `φ` defines a total function.

Since `defined` is a `HierarchySymbol.DefinedFunction`, uniqueness of the value holds in `ℕ`; the
difference between the `∃!` form of [HP98] and the `∃` form of [AB05, §10.2] therefore shows up
only in `total`.
- [HP98, Definition I.1.51]
- [HP98, Definition IV.3.1] -/
structure ArithmeticTheory.ProvablyTotalVia (T : ArithmeticTheory) (f : (Fin k → ℕ) → ℕ)
    (φ : 𝚺₁.Semisentence (k + 1)) : Prop where
  defined : HierarchySymbol.DefinedFunction (V := ℕ) f φ
  total : T ⊢ totalitySentence φ

/-- `f` is `T`-provably total: some `𝚺₁` formula witnesses `T.ProvablyTotalVia f`.
- [HP98, Definition I.1.51]
- [HP98, Definition IV.3.1]
- [AB05, §10.2] -/
def ArithmeticTheory.ProvablyTotal (T : ArithmeticTheory) (f : (Fin k → ℕ) → ℕ) : Prop :=
  ∃ φ, T.ProvablyTotalVia f φ

namespace ArithmeticTheory.ProvablyTotalVia

lemma to_provablyTotal (h : T.ProvablyTotalVia f φ) : T.ProvablyTotal f := ⟨φ, h⟩

lemma graph_iff (h : T.ProvablyTotalVia f φ) {v : Fin (k + 1) → ℕ} :
    φ.val.Evalb v ↔ v 0 = f (v ·.succ) := h.defined.iff

/-- Provable totality passes to any stronger theory. -/
lemma mono (h : T.ProvablyTotalVia f φ) (hT : T ⪯ U) : U.ProvablyTotalVia f φ :=
  ⟨h.defined, hT.pbl h.total⟩

/-- Provable totality depends only on the `𝚷₂` consequences of the theory.
- [AB05, §10.2] -/
lemma of_pi2 (h : T.ProvablyTotalVia f φ)
    (H : ∀ σ : ArithmeticSentence, Hierarchy 𝚷 2 σ → T ⊢ σ → U ⊢ σ) : U.ProvablyTotalVia f φ :=
  ⟨h.defined, H _ (by simp) h.total⟩

/-- The model-theoretic face of `total`: in every model of `T`, `φ` defines a total function. -/
lemma models (h : T.ProvablyTotalVia f φ)
    (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (v : Fin k → V) : ∃ y, φ.val.Evalb (y :> v) :=
  models_totalitySentence_iff.mp (consequence_iff'.mp (Theory.Proof.sound h.total) V) v

/-- `total` follows from its model-theoretic face, by completeness. -/
lemma of_models [𝗘𝗤 ℒₒᵣ ⪯ T] (hf : HierarchySymbol.DefinedFunction (V := ℕ) f φ)
    (H : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T], ∀ v : Fin k → V,
      ∃ y, φ.val.Evalb (y :> v)) : T.ProvablyTotalVia f φ :=
  ⟨hf, Arithmetic.complete T _ fun V _ _ ↦ models_totalitySentence_iff.mpr (H V)⟩

section comp

variable {l : ℕ} {g : (Fin l → ℕ) → ℕ} {h : Fin l → (Fin k → ℕ) → ℕ}
  {ψ : 𝚺₁.Semisentence (l + 1)} {χ : Fin l → 𝚺₁.Semisentence (k + 1)}

/-- The `T`-provably total functions are closed under composition.
- [HP98, Lemma I.1.53] -/
lemma comp [𝗘𝗤 ℒₒᵣ ⪯ T] (hg : T.ProvablyTotalVia g ψ) (hh : ∀ i, T.ProvablyTotalVia (h i) (χ i)) :
    T.ProvablyTotalVia (fun v ↦ g fun i ↦ h i v) (compGraph ψ χ) := by
  refine of_models ⟨fun w ↦ ?_⟩ ?_
  · simp only [eval_compGraph]
    constructor
    · rintro ⟨z, hz, hχ⟩
      have e : z = fun i ↦ h i (w ·.succ) := funext fun i ↦ by
        simpa using (hh i).graph_iff.mp (hχ i)
      simpa [e] using hg.graph_iff.mp hz
    · intro e
      exact ⟨fun i ↦ h i (w ·.succ), hg.graph_iff.mpr (by simpa using e),
        fun i ↦ (hh i).graph_iff.mpr (by simp)⟩
  · intro V _ _ v
    choose z hz using fun i ↦ (hh i).models V v
    obtain ⟨y, hy⟩ := hg.models V z
    exact ⟨y, by simpa using ⟨z, by simpa using hy, by simpa using hz⟩⟩

end comp

end ArithmeticTheory.ProvablyTotalVia

namespace ArithmeticTheory.ProvablyTotal

lemma mono (h : T.ProvablyTotal f) (hT : T ⪯ U) : U.ProvablyTotal f :=
  have ⟨_, h⟩ := h; ⟨_, h.mono hT⟩

/-- Provable totality depends only on the `𝚷₂` consequences of the theory.
- [AB05, §10.2] -/
lemma of_pi2 (h : T.ProvablyTotal f)
    (H : ∀ σ : ArithmeticSentence, Hierarchy 𝚷 2 σ → T ⊢ σ → U ⊢ σ) : U.ProvablyTotal f :=
  have ⟨_, h⟩ := h; ⟨_, h.of_pi2 H⟩

/-- The `T`-provably total functions are closed under composition.
- [HP98, Lemma I.1.53] -/
lemma comp [𝗘𝗤 ℒₒᵣ ⪯ T] {l : ℕ} {g : (Fin l → ℕ) → ℕ} {h : Fin l → (Fin k → ℕ) → ℕ}
    (hg : T.ProvablyTotal g) (hh : ∀ i, T.ProvablyTotal (h i)) :
    T.ProvablyTotal fun v ↦ g fun i ↦ h i v :=
  have ⟨_, hg⟩ := hg
  have ⟨_, hh⟩ := Classical.skolem.mp hh
  ⟨_, hg.comp hh⟩

end ArithmeticTheory.ProvablyTotal

end LO.FirstOrder
