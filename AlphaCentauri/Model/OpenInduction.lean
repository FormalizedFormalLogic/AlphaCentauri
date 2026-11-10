module

public import AlphaCentauri.Schemata.ZRing

/-!
# Models of open induction extending $\mathbb{Z}$-rings

Wilkie's extension theorem: every discretely ordered $\mathbb{Z}$-ring embeds into a discretely
ordered ring satisfying open induction. As a consequence, $\mathsf{IOpen}$ and $\mathsf{ZR}$ prove
the same universal sentences.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- Every model of $\mathsf{ZR}$ embeds into a model of $\mathsf{IOpen}$.
- [Wil78, Lemma 3.2]
- [BO96, Theorem 1.2]
- [Raf10, Wilkie's Extension Theorem] -/
axiom exists_embedding_models_IOpen (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* ZRing] :
    ∃ (N : Type) (_ : ORingStructure N), N↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 ∧ Nonempty (M ↪ₛ[ℒₒᵣ] N)

open Semiformula in
/-- $\mathsf{IOpen}$ and $\mathsf{ZR}$ prove the same universal closures of open formulas.
- [Wil78, §1]
- [Moh11, §1] -/
theorem provable_univCl_IOpen_iff {φ : ArithmeticSemiformula ℕ 0} (hφ : φ.Open) :
    𝗜𝗢𝗽𝗲𝗻 ⊢ φ.univCl ↔ ZRing ⊢ φ.univCl := by
  constructor
  · intro h
    apply complete.{0}
    intro M _ _
    obtain ⟨N, _, hN, ⟨Θ⟩⟩ := exists_embedding_models_IOpen M
    have hN := models_iff_proposition.mp <| models_of_provable hN h
    apply models_iff_proposition.mpr
    intro f
    apply (eval_hom_iff_of_open Θ hφ).mpr
    simpa [Matrix.empty_eq] using hN (Θ ∘ f)
  · exact ZRing_weakerThan_IOpen.pbl

/-- A universal closure of an open formula that fails in a model of $\mathsf{ZR}$ is not provable
in $\mathsf{IOpen}$.
- [Wil78, §1] -/
lemma not_provable_IOpen_allClosure {k : ℕ} {φ : ArithmeticSemiformula Empty k} (hφ : φ.Open)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* ZRing] (h : ¬ M↓[ℒₒᵣ] ⊧ ∀¹* φ) :
    ¬ 𝗜𝗢𝗽𝗲𝗻 ⊢ ∀¹* φ := by
  intro hφ'
  obtain ⟨N, _, hN, ⟨Θ⟩⟩ := exists_embedding_models_IOpen M
  apply h
  have hN := models_of_provable hN hφ'
  rw [models_iff] at hN ⊢
  apply Semiformula.eval_hom_allClosure Θ (φ := φ) (ε₁ := Empty.elim) hφ
  convert hN using 3

end FFL.FirstOrder.Arithmetic
