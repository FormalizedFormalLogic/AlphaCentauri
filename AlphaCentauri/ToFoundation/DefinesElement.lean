module

public import AlphaCentauri.ToFoundation.TypedQuantifierBlock

/-!
# Defining an element by a formula in the internal calculus

The congruence of the graph of a function symbol under equivalent hypotheses, and the internal
formula stating that a formula defines a unique element of a domain.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

section funcGraph

open _root_.FFL.Entailment

/-- `∀ w⃗ (⋀ᵢ (d(wᵢ) ∧ Aᵢ(wᵢ)) → γ(z, w⃗))` with `z` the outer variable. -/
noncomputable def funcGraph {k : ℕ} (d : Semiformula V L 1) (A : Fin k → Semiformula V L 1)
    (γ : Semiformula V L (k + 1)) : Semiformula V L 1 :=
  ∀¹^[k] (Matrix.conj (fun i : Fin k ↦
      d.subst ![Semiterm.bvar (i.addCast 1)] ⋏ (A i).subst ![Semiterm.bvar (i.addCast 1)]) 🡒
    γ.subst (Semiterm.bvar (Fin.cast (Nat.add_comm k 1) (Fin.last k)) :>
      fun i ↦ Semiterm.bvar (i.addCast 1)))

lemma shift_conj_fin {m n : ℕ} (v : Fin m → Semiformula V L n) :
    (Matrix.conj v).shift = Matrix.conj fun i ↦ (v i).shift := by
  induction m with
  | zero => simp
  | succ m ih => simp [Matrix.conj, ih]; rfl

lemma shift_funcGraph {k : ℕ} (d : Semiformula V L 1) (A : Fin k → Semiformula V L 1)
    (γ : Semiformula V L (k + 1)) :
    (funcGraph d A γ).shift = funcGraph d.shift (fun i ↦ (A i).shift) γ.shift := by
  have h₁ : ∀ {m : ℕ} (φ : Semiformula V L (1 + m)), (∀¹^[m] φ).shift = ∀¹^[m] φ.shift := by
    intro m φ
    simpa using Semiformula.shift_iterate_allItr (k := 1) φ
  simp only [funcGraph, Nat.succ_eq_add_one, Nat.reduceAdd, h₁, Semiformula.shift_imp,
    shift_conj_fin, Semiformula.shift_and, Semiformula.shift_substs, Matrix.vecMap_cons',
    Matrix.head_cons, Semiterm.shift_bvar, Matrix.tail_cons, Matrix.vecMap_nil]
  congr 3
  funext i
  cases i using Fin.cases <;> simp

lemma allItr_subst_fvar {k : ℕ} (c : V) (B : Semiformula V L (1 + k)) :
    (∀¹^[k] B).subst ![Semiterm.fvar c] =
      ∀¹^[k] (B.subst fun j : Fin (1 + k) ↦
        if h : (j : ℕ) < k then Semiterm.bvar ((⟨j, h⟩ : Fin k).addCast 0)
          else Semiterm.fvar c) := by
  induction k with
  | zero =>
    simp only [allItr_zero]
    congr 1
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp
  | succ k ih =>
    rw [allItr_succ, allItr_succ, ih, Semiformula.substs_all]
    congr 3
    funext j
    cases j using Fin.cases with
    | zero => simp [Fin.ext_iff]
    | succ i =>
      by_cases hi : (i : ℕ) < k
      · simp [hi, Semiterm.bShift_bvar, Fin.ext_iff]
      · simp [hi]

lemma funcGraph_subst_fvar {k : ℕ} (c : V) (d : Semiformula V L 1)
    (A : Fin k → Semiformula V L 1) (γ : Semiformula V L (k + 1)) :
    (funcGraph d A γ).subst ![Semiterm.fvar c] =
      relativizedImp d A (γ.subst (Semiterm.fvar c :> fun i : Fin k ↦
        Semiterm.bvar (i.addCast 0))) := by
  unfold funcGraph relativizedImp
  rw [allItr_subst_fvar]
  congr 1
  simp only [Semiformula.substs_imp, Semiformula.substs_conj, Semiformula.substs_and,
    Semiformula.substs_substs]
  have h₁ : ∀ i : Fin k, (Semiterm.subst fun j : Fin (1 + k) ↦
      if h : (j : ℕ) < k then Semiterm.bvar ((⟨j, h⟩ : Fin k).addCast 0) else Semiterm.fvar c) ⨟
      ![(Semiterm.bvar (i.addCast 1) : Semiterm V L (1 + k))] =
      ![(Semiterm.bvar (i.addCast 0) : Semiterm V L (0 + k))] := by
    intro i
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp
  have h₂ : (Semiterm.subst fun j : Fin (1 + k) ↦
      if h : (j : ℕ) < k then Semiterm.bvar ((⟨j, h⟩ : Fin k).addCast 0) else Semiterm.fvar c) ⨟
      ((Semiterm.bvar (Fin.cast (Nat.add_comm k 1) (Fin.last k)) : Semiterm V L (1 + k)) :>
        fun i ↦ Semiterm.bvar (i.addCast 1) : SemitermVec V L (k + 1) (1 + k)) =
      (Semiterm.fvar c : Semiterm V L (0 + k)) :> fun i : Fin k ↦
        (Semiterm.bvar (i.addCast 0) : Semiterm V L (0 + k)) := by
    funext j
    cases j using Fin.cases with
    | zero => simp
    | succ i => simp
  simp only [h₁, h₂]

/-- Replacement of domain-equivalent hypotheses in `funcGraph`. -/
theorem funcGraph_congr {k : ℕ} (d : Semiformula V L 1) (A B : Fin k → Semiformula V L 1)
    (γ : Semiformula V L (k + 1)) :
    T.internalize V ⊢ Matrix.conj (fun i ↦ ∀¹ (d 🡒 (A i 🡘 B i))) 🡒
      ∀¹ (funcGraph d A γ 🡘 funcGraph d B γ) := by
  sorry

end funcGraph

section definesElement

open _root_.FFL.Entailment

variable [L.Eq]

/-- `∃ y (d(y) ∧ ∀ z (d(z) → (A(z) ↔ z = y)))`: `A` defines a unique element of `d`. -/
noncomputable def definesElement (d A : Semiformula V L 1) : Formula V L :=
  ∃¹ (d ⋏ (∀¹ (d.subst ![Semiterm.bvar 0] 🡒
    (A.subst ![Semiterm.bvar 0] 🡘 Semiformula.equal (Semiterm.bvar 0) (Semiterm.bvar 1)))))

theorem definesElement_exists (d A : Semiformula V L 1) [𝗘𝗤 L ⪯ T] :
    T.internalize V ⊢ definesElement d A 🡒 ∃¹ (d ⋏ A) := by
  sorry

theorem definesElement_iff_equal (d A : Semiformula V L 1) (b : V) [𝗘𝗤 L ⪯ T] :
    T.internalize V ⊢ definesElement d A 🡒 d.subst ![Semiterm.fvar b] 🡒
      A.subst ![Semiterm.fvar b] 🡒
      ∀¹ (d 🡒 (A 🡘 Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar b))) := by
  sorry

end definesElement

end FFL.FirstOrder.Arithmetic.Bootstrapping
