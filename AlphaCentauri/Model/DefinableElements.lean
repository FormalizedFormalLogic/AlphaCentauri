module

public import AlphaCentauri.Model.Elementary
public import AlphaCentauri.ToFoundation.Pigeonhole
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.General

/-!
# Definable elements

The $\Sigma_{j+1}$-definable elements of a model `M` of `𝗣𝗔` form a $\Sigma_{j+1}$-elementary
substructure, which satisfies $\mathsf{I}\Sigma_j$ and, when it contains a nonstandard element,
refutes $\mathsf{B}\Sigma_{j+1}$. The elements of `M` below a definable element form a cut, which
satisfies $\mathsf{B}\Sigma_{j+1}$ and refutes $\mathsf{I}\Sigma_{j+1}$.

- [HP98, §IV.1(d)]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Semiformula
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- The elements of `M` defined by a $\Sigma_k$ formula without parameters.
- [HP98, Definition IV.1.32] -/
def definableElements (k : ℕ) (M : Type*) [ORingStructure M] : Set M :=
  {a | ∃ φ : ArithmeticSemisentence 1, ℬ[<, ℒₒᵣ].Hierarchy 𝚺 k φ ∧ ∀ x : M, M ⊧/![x] φ ↔ x = a}

variable {M : Type} [ORingStructure M] {j : ℕ}

lemma definableElements_mono {k k' : ℕ} (h : k ≤ k') :
    definableElements k M ⊆ definableElements k' M := by
  rintro a ⟨φ, hφ, ha⟩
  exact ⟨φ, hφ.mono h, ha⟩

/-- An element defined uniquely from definable elements by a $\Sigma_k$ formula is definable. -/
lemma mem_definableElements_of_unique {k m : ℕ} (hk : 1 ≤ k)
    {ψ : ArithmeticSemisentence (m + 1)} (hψ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 k ψ) {v : Fin m → M}
    (hv : ∀ i, v i ∈ definableElements k M) {a : M} (ha : ∀ x, M ⊧/(x :> v) ψ ↔ x = a) :
    a ∈ definableElements k M := by
  induction m with
  | zero =>
    use ψ
    and_intros
    · exact hψ
    simpa [Matrix.empty_eq] using ha
  | succ m ih =>
    obtain ⟨δ, hδ, hv₀⟩ := hv 0
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
    apply ih (ψ := ∃¹ (δ ⇜ ![#0] ⋏ ψ ⇜ (#1 :> #0 :> fun i ↦ #i.succ.succ))) (v := Fin.tail v)
    · simp [hδ.rew, hψ.rew]
    · intro i
      exact hv i.succ
    · intro x
      have hw : Semiterm.val (v 0 :> x :> Fin.tail v) Empty.elim ∘
          (#1 :> #0 :> fun i ↦ #i.succ.succ : Fin (m + 2) → ArithmeticSemiterm Empty (m + 2)) =
            x :> v := by
        ext i
        cases i using Fin.cases with
        | zero => simp
        | succ i => cases i using Fin.cases <;> simp [Fin.tail]
      simp [← ha x, hv₀, hw]

/-- A $\Pi_j$ formula with parameters among the $\Sigma_{j+1}$-definable elements and a witness
has a least witness, and it is $\Sigma_{j+1}$-definable. -/
axiom exists_least_mem_definableElements [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] {n : ℕ}
    {φ : ArithmeticSemiformula ℕ (n + 1)} (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 j φ) {e : Fin n → M}
    {f : ℕ → M} (he : ∀ i, e i ∈ definableElements (j + 1) M)
    (hf : ∀ i, f i ∈ definableElements (j + 1) M) (h : ∃ x, φ.Eval (x :> e) f) :
    ∃ x ∈ definableElements (j + 1) M, φ.Eval (x :> e) f ∧ ∀ y < x, ¬φ.Eval (y :> e) f

namespace definableElements

axiom oringStructure (j : ℕ) (M : Type) [ORingStructure M] :
    ORingStructure (definableElements (j + 1) M)

attribute [instance] oringStructure

/-- The inclusion of the definable elements into `M`. -/
axiom emb (j : ℕ) (M : Type) [ORingStructure M] : definableElements (j + 1) M ↪ₛ[ℒₒᵣ] M

axiom emb_apply (x : definableElements (j + 1) M) : emb j M x = x.val

/-- [HP98, Lemma IV.1.39] -/
axiom sigmaElementary [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (j : ℕ) : SigmaElementary (emb j M) (j + 1)

/-- [HP98, Corollary IV.1.40] -/
axiom models_ISigma [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (j : ℕ) : (definableElements (j + 1) M)↓[ℒₒᵣ] ⊧* 𝗜𝚺 j

end definableElements

section code

open Bootstrapping

variable {V : Type} [ORingStructure V]

/-- `x` is the element defined by the code `c`: `c` codes the matrix of a prenex $\Pi_j$ formula
in one variable, and `x` is the first component of the least element satisfying it. -/
def DefinesElement [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (j : ℕ) (c x : V) : Prop :=
  ∃ p, π₁ p = x ∧ PrenexSatisfied 𝚷 j (p ∷ 0) c ∧ ∀ q < p, ¬PrenexSatisfied 𝚷 j (q ∷ 0) c

axiom definesElementDef (j : ℕ) : 𝚺ᴬ_[j + 1].Semisentence 2

axiom DefinesElement.defined [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (j : ℕ) :
    𝚺ᴬ_[j + 1]-Relation (DefinesElement j : V → V → Prop) via definesElementDef j

axiom DefinesElement.unique [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {c x x' : V} (h : DefinesElement j c x)
    (h' : DefinesElement j c x') : x = x'

/-- Every $\Sigma_{j+1}$-definable element of a model of $\mathsf{I}\Sigma_{j+1}$ is defined by a
standard code. -/
axiom exists_definesElement [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (j + 1)] {x : V}
    (hx : x ∈ definableElements (j + 1) V) : ∃ c : ℕ, DefinesElement j (c : V) x

/-- In a nonstandard model of $\mathsf{I}\Sigma_{j+1}$ the $\Sigma_{j+1}$-definable elements are
bounded.
- [HP98, Lemma IV.1.37] -/
axiom exists_bound_definableElements [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (j + 1)] {a : V}
    (ha : ∀ m : ℕ, (m : V) < a) : ∃ b, ∀ x ∈ definableElements (j + 1) V, x < b

end code

/-- The definable elements refute $\mathsf{B}\Sigma_{j+1}$ once one of them is nonstandard.
- [HP98, Lemma IV.1.41] -/
axiom definableElements.not_models_BSigma [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] {a : M}
    (ha : a ∈ definableElements (j + 1) M) (hns : ∀ m : ℕ, (m : M) < a) :
    ¬(definableElements (j + 1) M)↓[ℒₒᵣ] ⊧* 𝗕𝚺 (j + 1)

/-- The elements of `M` below a $\Sigma_{j+1}$-definable element.
- [HP98, Definition IV.1.32] -/
axiom definableCut (j : ℕ) (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] : Cut M

namespace definableCut

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

axiom mem_iff {a : M} :
    a ∈ (definableCut j M).carrier ↔ ∃ c ∈ definableElements (j + 1) M, a < c

axiom closed (j : ℕ) (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] : (definableCut j M).Closed

attribute [instance] closed

/-- [HP98, Lemma IV.1.42] -/
axiom sigmaElementary : SigmaElementary (definableCut j M).endExtension.emb j

/-- [HP98, Lemma IV.1.44(1)] -/
axiom models_BSigma {a : M} (ha : a ∈ definableElements (j + 1) M) (hns : ∀ m : ℕ, (m : M) < a) :
    (definableCut j M).carrier↓[ℒₒᵣ] ⊧* 𝗕𝚺 (j + 1)

/-- [HP98, Lemma IV.1.44(3)] -/
axiom not_models_ISigma {a : M} (ha : a ∈ definableElements (j + 1) M)
    (hns : ∀ m : ℕ, (m : M) < a) : ¬(definableCut j M).carrier↓[ℒₒᵣ] ⊧* 𝗜𝚺 (j + 1)

end definableCut

/-- A model of `𝗣𝗔` with a nonstandard $\Sigma_1$-definable element.
- [HP98, Observation IV.1.31] -/
axiom exists_model_nonstandard_definableElement :
    ∃ (M : Type) (_ : ORingStructure M) (_ : M↓[ℒₒᵣ] ⊧* 𝗣𝗔),
      ∃ a ∈ definableElements 1 M, ∀ m : ℕ, (m : M) < a

end FFL.FirstOrder.Arithmetic
