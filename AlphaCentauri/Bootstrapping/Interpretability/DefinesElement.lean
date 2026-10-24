module

public import AlphaCentauri.ToFoundation.InternalEquality
public import AlphaCentauri.ToFoundation.TypedProof
public import Foundation.Meta.ClProver

/-!
# Defining an element by a formula

The graph of a function symbol under equivalent hypotheses is congruent, and the internal formula
`definesElement d A` states that a formula `A` defines a unique element of the domain `d`.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

attribute [local simp] Semiformula.shift_substs Semiformula.substs_substs

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open scoped FFL.FirstOrder.Arithmetic

variable {L : Language} [L.Encodable] [L.LORDefinable]

section relativizedImp

open _root_.FFL.Entailment

variable {T : Theory L} [T.Δ₁]

/-- `∀ w⃗ (⋀ᵢ (d(wᵢ) ∧ Aᵢ(wᵢ)) → C(w⃗))`, the shape of a translated atomic formula. -/
noncomputable def relativizedImp {k : ℕ} (d : Semiformula V L 1) (A : Fin k → Semiformula V L 1)
    (C : Semiformula V L (0 + k)) : Formula V L :=
  ∀¹^[k] (Matrix.conj (fun i : Fin k ↦
      d.subst ![Semiterm.bvar (i.addCast 0)] ⋏ (A i).subst ![Semiterm.bvar (i.addCast 0)]) 🡒 C)

lemma relativizedImp_imp_relativizedImp {k : ℕ} {H : Formula V L} (d : Semiformula V L 1)
    (A B : Fin k → Semiformula V L 1) (C : Semiformula V L (0 + k))
    (hH : ∀ i, T.internalize V ⊢ H 🡒 ∀¹ (d 🡒 B i 🡒 A i)) :
    T.internalize V ⊢ H 🡒 relativizedImp d A C 🡒 relativizedImp d B C := by
  have h₁ : ∀ i : Fin k, T.internalize V ⊢ Semiformula.shift^[k] H 🡒
      (Semiformula.shift^[k] d).subst ![Semiterm.fvar (i : V)] 🡒
        (Semiformula.shift^[k] (B i)).subst ![Semiterm.fvar (i : V)] 🡒
          (Semiformula.shift^[k] (A i)).subst ![Semiterm.fvar (i : V)] := by
    intro i
    have := TProof.shift_iterate! (hH i) k
    simp only [Semiformula.shift_iterate_imp, Semiformula.shift_iterate_all] at this
    have h₂ := TProof.all_imp_subst (T := T)
      (Semiformula.shift^[k] d 🡒 Semiformula.shift^[k] (B i) 🡒 Semiformula.shift^[k] (A i))
      (Semiterm.fvar (i : V))
    simp only [Semiformula.substs_imp] at h₂
    exact C_trans this h₂
  apply CC_of_CK
  apply TProof.allItr_generalize_imp
  simp only [relativizedImp, Semiformula.shift_iterate_and, Semiformula.shift_iterate_allItr]
  apply C_trans (CKK_of_C' (TProof.allItr_specialize _ fun i ↦ Semiterm.fvar (i : V)))
  simp only [Semiformula.shift_iterate_imp, Semiformula.substs_imp, Semiformula.shift_iterate_conj,
    Semiformula.substs_conj, Semiformula.shift_iterate_and, Semiformula.substs_and,
    Semiformula.subst_shift_iterate_subst_bvar, Fin.addCast_val]
  have h₂ := matrixConj_imp_matrixConj (𝓢 := T.internalize V)
    (v := fun i : Fin k ↦ (Semiformula.shift^[k] d).subst ![Semiterm.fvar (i : V)] ⋏
      (Semiformula.shift^[k] (B i)).subst ![Semiterm.fvar (i : V)])
    (u := fun i : Fin k ↦ (Semiformula.shift^[k] d).subst ![Semiterm.fvar (i : V)] ⋏
      (Semiformula.shift^[k] (A i)).subst ![Semiterm.fvar (i : V)]) fun i ↦ by
    have := h₁ i
    cl_prover [this]
  cl_prover [h₂]

/-- Replacement of domain-equivalent hypotheses in `relativizedImp`. -/
theorem relativizedImp_congr {k : ℕ} (d : Semiformula V L 1) (A B : Fin k → Semiformula V L 1)
    (C : Semiformula V L (0 + k)) :
    T.internalize V ⊢ Matrix.conj (fun i ↦ ∀¹ (d 🡒 (A i 🡘 B i))) 🡒
      (relativizedImp d A C 🡘 relativizedImp d B C) := by
  have h₁ := relativizedImp_imp_relativizedImp (T := T) d A B C fun i ↦
    C_trans (matrixConj_elim (fun i ↦ ∀¹ (d 🡒 (A i 🡘 B i))) i)
      (all_iff_imp_all_imp_imp_left d (A i) (B i))
  have h₂ := relativizedImp_imp_relativizedImp (T := T) d B A C fun i ↦
    C_trans (matrixConj_elim (fun i ↦ ∀¹ (d 🡒 (A i 🡘 B i))) i)
      (all_iff_imp_all_imp_imp_right d (A i) (B i))
  cl_prover [h₁, h₂]

end relativizedImp

section defines

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

lemma shift_funcGraph {k : ℕ} (d : Semiformula V L 1) (A : Fin k → Semiformula V L 1)
    (γ : Semiformula V L (k + 1)) :
    (funcGraph d A γ).shift = funcGraph d.shift (fun i ↦ (A i).shift) γ.shift := by
  simp [funcGraph]

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
    obtain rfl := Subsingleton.elim j 0
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
  simp

/-- Replacement of domain-equivalent hypotheses in `funcGraph`. -/
theorem funcGraph_congr {k : ℕ} (d : Semiformula V L 1) (A B : Fin k → Semiformula V L 1)
    (γ : Semiformula V L (k + 1)) :
    T.internalize V ⊢ Matrix.conj (fun i ↦ ∀¹ (d 🡒 (A i 🡘 B i))) 🡒
      ∀¹ (funcGraph d A γ 🡘 funcGraph d B γ) := by
  apply TProof.generalize_imp
  simp only [Semiformula.free, Semiformula.shift_conj, Semiformula.shift_all,
    Semiformula.shift_imp, Semiformula.shift_iff, shift_funcGraph, Semiformula.substs_imply,
    funcGraph_subst_fvar]
  exact relativizedImp_congr (T := T) d.shift (fun i ↦ (A i).shift) (fun i ↦ (B i).shift) _

end funcGraph

section definesElement

open _root_.FFL.Entailment

variable [L.Eq]

/-- The matrix `d(y) ∧ ∀ z (d(z) → (A(z) ↔ z = y))` of `definesElement`. -/
noncomputable def definesElementBody (d A : Semiformula V L 1) : Semiformula V L 1 :=
  d ⋏ (∀¹ (d.subst ![Semiterm.bvar 0] 🡒
    (A.subst ![Semiterm.bvar 0] 🡘 Semiformula.equal (Semiterm.bvar 0) (Semiterm.bvar 1))))

/-- `∃ y (d(y) ∧ ∀ z (d(z) → (A(z) ↔ z = y)))`: `A` defines a unique element of `d`. -/
noncomputable def definesElement (d A : Semiformula V L 1) : Formula V L :=
  ∃¹ definesElementBody d A

/-- The matrix `d(z) → (A(z) ↔ z = c)` of the uniqueness clause of `definesElement`. -/
noncomputable def uniqueAt (d A : Semiformula V L 1) (c : V) : Semiformula V L 1 :=
  d 🡒 (A 🡘 Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar c))

@[simp] lemma shift_uniqueAt (d A : Semiformula V L 1) (c : V) :
    (uniqueAt d A c).shift = uniqueAt d.shift A.shift (c + 1) := by
  simp [uniqueAt]

@[simp] lemma shift_definesElementBody (d A : Semiformula V L 1) :
    (definesElementBody d A).shift = definesElementBody d.shift A.shift := by
  simp [definesElementBody]

lemma shift_iterate_definesElementBody (d A : Semiformula V L 1) (k : ℕ) :
    Semiformula.shift^[k] (definesElementBody d A) =
      definesElementBody (Semiformula.shift^[k] d) (Semiformula.shift^[k] A) :=
  Function.Semiconj₂.iterate (op := definesElementBody) shift_definesElementBody k d A

lemma definesElementBody_subst_fvar (d A : Semiformula V L 1) (c : V) :
    ((definesElementBody d A).subst ![Semiterm.fvar c] : Formula V L) =
      d.subst ![Semiterm.fvar c] ⋏ (∀¹ (uniqueAt d A c)) := by
  simp [definesElementBody, uniqueAt]

lemma definesElementBody_free (d A : Semiformula V L 1) :
    (definesElementBody d A).free = d.free ⋏ (∀¹ (uniqueAt d.shift A.shift 0)) := by
  simp [Semiformula.free, definesElementBody_subst_fvar]

lemma tprovable_unique_specialize (d A : Semiformula V L 1) (c y : V) :
    T.internalize V ⊢ ∀¹ (uniqueAt d A c) 🡒
      d.subst ![Semiterm.fvar y] 🡒
        (A.subst ![Semiterm.fvar y] 🡘 Semiformula.equal (Semiterm.fvar y) (Semiterm.fvar c)) := by
  simpa [uniqueAt] using TProof.all_imp_subst (T := T) (uniqueAt d A c) (Semiterm.fvar y)

theorem definesElement_exists (d A : Semiformula V L 1) [𝗘𝗤 L ⪯ T] :
    T.internalize V ⊢ definesElement d A 🡒 ∃¹ (d ⋏ A) := by
  unfold definesElement
  refine FiniteContext.emptyPrf <| TProof.exs_imp_exs! (Γ := []) <| FiniteContext.of ?_
  have h₁ : T.internalize V ⊢ ∀¹ (uniqueAt d.shift A.shift 0) 🡒
        d.free 🡒 (A.free 🡘 Semiformula.equal (Semiterm.fvar 0) (Semiterm.fvar 0)) :=
    tprovable_unique_specialize d.shift A.shift 0 0
  have h₂ := tprovable_equal_refl (S := T) (Semiterm.fvar (0 : V))
  rw [definesElementBody_free, Semiformula.free_and]
  cl_prover [h₁, h₂]

omit [L.Eq] in
private lemma uniq_combine {Hq Dx Ax Dz Az Exc Ecx Ezc Ezx : Formula V L}
    (h₁ : T.internalize V ⊢ Hq 🡒 Dz 🡒 (Az 🡘 Ezc))
    (h₂ : T.internalize V ⊢ Hq 🡒 Dx 🡒 (Ax 🡘 Exc))
    (h₃ : T.internalize V ⊢ Exc 🡒 Ecx)
    (h₄ : T.internalize V ⊢ Ezc ⋏ Ecx 🡒 Ezx)
    (h₅ : T.internalize V ⊢ Ezx ⋏ Exc 🡒 Ezc) :
    T.internalize V ⊢ Hq 🡒 Dx 🡒 Ax 🡒 Dz 🡒 (Az 🡘 Ezx) := by
  have k₁ : T.internalize V ⊢ Hq 🡒 Dx 🡒 Ax 🡒 Exc := by cl_prover 128 [h₂]
  have k₂ : T.internalize V ⊢ Hq 🡒 Dz 🡒 (Az 🡒 Ezc) := by cl_prover 128 [h₁]
  have k₃ : T.internalize V ⊢ Hq 🡒 Dz 🡒 (Ezc 🡒 Az) := by cl_prover 128 [h₁]
  have g₁ : T.internalize V ⊢ Hq 🡒 Dx 🡒 Ax 🡒 Dz 🡒 (Az 🡒 Ezx) := by
    cl_prover 128 [k₁, k₂, h₃, h₄]
  have g₂ : T.internalize V ⊢ Hq 🡒 Dx 🡒 Ax 🡒 Dz 🡒 (Ezx 🡒 Az) := by
    cl_prover 128 [k₁, k₃, h₅]
  cl_prover 128 [g₁, g₂]

omit [L.Eq] in
private lemma conj_of_curry {P Q R S : Formula V L} (h : T.internalize V ⊢ P 🡒 Q 🡒 R 🡒 S) :
    T.internalize V ⊢ (P ⋏ Q ⋏ R) 🡒 S := by
  cl_prover [h]

omit [L.Eq] in
private lemma conj_of_curry_swap {P Q R S : Formula V L}
    (h : T.internalize V ⊢ P 🡒 Q 🡒 R 🡒 S) : T.internalize V ⊢ (Q ⋏ R) 🡒 (P 🡒 S) := by
  cl_prover [h]

lemma definesElement_imp_theta (d A : Semiformula V L 1) [𝗘𝗤 L ⪯ T] (c x : V) :
    T.internalize V ⊢ ∀¹ (uniqueAt d A c) 🡒 d.subst ![Semiterm.fvar x] 🡒
      A.subst ![Semiterm.fvar x] 🡒 ∀¹ (uniqueAt d A x) := by
  have key : T.internalize V ⊢ ((∀¹ (uniqueAt d A c)) ⋏ d.subst ![Semiterm.fvar x] ⋏
      A.subst ![Semiterm.fvar x]) 🡒 ∀¹ (uniqueAt d A x) := by
    apply TProof.generalize_imp
    have h := uniq_combine (tprovable_unique_specialize (T := T) d.shift A.shift (c + 1) 0)
      (tprovable_unique_specialize (T := T) d.shift A.shift (c + 1) (x + 1))
      (tprovable_equal_symm_imp T (Semiterm.fvar (x + 1)) (Semiterm.fvar (c + 1)))
      (tprovable_equal_trans_imp T (Semiterm.fvar 0) (Semiterm.fvar (c + 1))
        (Semiterm.fvar (x + 1)))
      (tprovable_equal_trans_imp T (Semiterm.fvar 0) (Semiterm.fvar (x + 1))
        (Semiterm.fvar (c + 1)))
    simpa [Semiformula.free, uniqueAt] using conj_of_curry h
  cl_prover [key]

theorem definesElement_iff_equal (d A : Semiformula V L 1) (b : V) [𝗘𝗤 L ⪯ T] :
    T.internalize V ⊢ definesElement d A 🡒 d.subst ![Semiterm.fvar b] 🡒
      A.subst ![Semiterm.fvar b] 🡒 ∀¹ (uniqueAt d A b) := by
  have hi := definesElement_imp_theta (T := T) d.shift A.shift 0 (b + 1)
  apply TProof.exs_imp_of_free
  rw [definesElementBody_free]
  have : T.internalize V ⊢ (d.free ⋏ (∀¹ (uniqueAt d.shift A.shift 0))) 🡒
      (d.shift.subst ![Semiterm.fvar (b + 1)] 🡒 A.shift.subst ![Semiterm.fvar (b + 1)] 🡒
        ∀¹ (uniqueAt d.shift A.shift (b + 1))) := by
    cl_prover [hi]
  simpa using this

/-- The conjunction of the witnessed definitions `definesElementBody d (A i)` at `c i`. -/
noncomputable def witnessConj (d : Semiformula V L 1) {k : ℕ} (A : Fin k → Semiformula V L 1)
    (c : Fin k → V) : Formula V L :=
  Matrix.conj (fun i ↦ (definesElementBody d (A i)).subst ![Semiterm.fvar (c i)])

lemma witnessConj_dA [𝗘𝗤 L ⪯ T] (d : Semiformula V L 1) {k : ℕ} (A : Fin k → Semiformula V L 1)
    (c : Fin k → V) :
    T.internalize V ⊢ witnessConj d A c 🡒
      Matrix.conj (fun i ↦
        d.subst ![Semiterm.fvar (c i)] ⋏ (A i).subst ![Semiterm.fvar (c i)]) := by
  apply matrixConj_intro
  intro i
  have h₁ := matrixConj_elim (𝓢 := T.internalize V)
    (fun i ↦ (definesElementBody d (A i)).subst ![Semiterm.fvar (c i)]) i
  rw [definesElementBody_subst_fvar] at h₁
  have h₂ := tprovable_unique_specialize (T := T) d (A i) (c i) (c i)
  have h₃ := tprovable_equal_refl (S := T) (Semiterm.fvar (c i))
  cl_prover [h₁, h₂, h₃]

@[simp] private lemma cast_zero_add_addCast {k : ℕ} (i : Fin k) :
    Fin.cast (Nat.zero_add k) (Fin.addCast 0 i) = i := rfl

lemma funcGraph_specialize_witness [𝗘𝗤 L ⪯ T] {k : ℕ} (d : Semiformula V L 1)
    (γ : Semiformula V L (k + 1)) (A : Fin k → Semiformula V L 1) (z : V) (c : Fin k → V) :
    T.internalize V ⊢ (funcGraph d A γ).subst ![Semiterm.fvar z] 🡒
      (Matrix.conj (fun i ↦ d.subst ![Semiterm.fvar (c i)] ⋏ (A i).subst ![Semiterm.fvar (c i)]) 🡒
        γ.subst (Semiterm.fvar z :> fun i ↦ Semiterm.fvar (c i))) := by
  rw [funcGraph_subst_fvar]
  unfold relativizedImp
  have h₁ := TProof.allItr_specialize (T := T)
    (Matrix.conj (fun i : Fin k ↦ d.subst ![Semiterm.bvar (i.addCast 0)] ⋏
      (A i).subst ![Semiterm.bvar (i.addCast 0)]) 🡒
        γ.subst (Semiterm.fvar z :> fun i : Fin k ↦ Semiterm.bvar (i.addCast 0)))
    (fun i : Fin (0 + k) ↦ Semiterm.fvar (c (Fin.cast (Nat.zero_add k) i)))
  simpa using h₁

omit [L.Eq] in
lemma witnessConj_dom (d : Semiformula V L 1) {k : ℕ} (A : Fin k → Semiformula V L 1)
    (c : Fin k → V) :
    T.internalize V ⊢
      Matrix.conj (fun i ↦ d.subst ![Semiterm.fvar (c i)] ⋏ (A i).subst ![Semiterm.fvar (c i)]) 🡒
        Matrix.conj (fun i ↦ d.subst ![Semiterm.fvar (c i)]) := by
  apply matrixConj_intro
  intro i
  have h₁ := matrixConj_elim (𝓢 := T.internalize V)
    (fun i ↦ d.subst ![Semiterm.fvar (c i)] ⋏ (A i).subst ![Semiterm.fvar (c i)]) i
  cl_prover [h₁]

lemma witness_eq_mem [𝗘𝗤 L ⪯ T] (d : Semiformula V L 1) {k : ℕ} (A : Fin k → Semiformula V L 1)
    (c w : Fin k → V) (i : Fin k) :
    T.internalize V ⊢ witnessConj d A c 🡒
      (d.subst ![Semiterm.fvar (w i)] ⋏ (A i).subst ![Semiterm.fvar (w i)]) 🡒
        Semiformula.equal (Semiterm.fvar (c i)) (Semiterm.fvar (w i)) := by
  have h₁ := matrixConj_elim (𝓢 := T.internalize V)
    (fun i ↦ (definesElementBody d (A i)).subst ![Semiterm.fvar (c i)]) i
  rw [definesElementBody_subst_fvar] at h₁
  have h₂ := tprovable_unique_specialize (T := T) d (A i) (c i) (w i)
  have h₃ := tprovable_equal_symm_imp (S := T) (Semiterm.fvar (w i)) (Semiterm.fvar (c i))
  cl_prover [h₁, h₂, h₃]

@[simp] lemma shift_iterate_equal {n : ℕ} (s t : Semiterm V L n) (k : ℕ) :
    Semiformula.shift^[k] (Semiformula.equal s t) =
      Semiformula.equal (Semiterm.shift^[k] s) (Semiterm.shift^[k] t) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', ih]

@[simp] lemma shift_witnessConj (d : Semiformula V L 1) {k : ℕ} (A : Fin k → Semiformula V L 1)
    (c : Fin k → V) :
    (witnessConj d A c).shift = witnessConj d.shift (fun i ↦ (A i).shift) (fun i ↦ c i + 1) := by
  simp [witnessConj]

lemma shift_iterate_witnessConj (d : Semiformula V L 1) {k : ℕ} (A : Fin k → Semiformula V L 1)
    (c : Fin k → V) (n : ℕ) :
    Semiformula.shift^[n] (witnessConj d A c) =
      witnessConj (Semiformula.shift^[n] d) (fun i ↦ Semiformula.shift^[n] (A i))
        (fun i ↦ c i + (n : V)) := by
  simp [witnessConj, shift_iterate_definesElementBody, Semiformula.shift_iterate_subst]

section funcGraphWitness

variable [𝗘𝗤 L ⪯ T] {k : ℕ} (d : Semiformula V L 1) (γ : Semiformula V L (k + 1))
  (hd : d.shift = d) (hγ : γ.shift = γ) (A : Fin k → Semiformula V L 1)
  (huniq : ∀ (y z : Term V L) (w : Fin k → Term V L), T.internalize V ⊢
    Matrix.conj (fun i ↦ d.subst ![w i]) ⋏ d.subst ![y] ⋏ d.subst ![z] ⋏
      γ.subst (y :> w) ⋏ γ.subst (z :> w) 🡒 Semiformula.equal y z)
  (hcongr : ∀ (y z : Term V L) (w w' : Fin k → Term V L), T.internalize V ⊢
    Semiformula.equal y z ⋏ Matrix.conj (fun i ↦ Semiformula.equal (w i) (w' i)) 🡒
      γ.subst (y :> w) 🡒 γ.subst (z :> w'))

include hcongr in
lemma back_core (c w : Fin k → V) (e z : V) :
    T.internalize V ⊢ witnessConj d A c 🡒 γ.subst (Semiterm.fvar e :> fun i ↦ Semiterm.fvar (c i)) 🡒
      Semiformula.equal (Semiterm.fvar z) (Semiterm.fvar e) 🡒
        Matrix.conj (fun i ↦ d.subst ![Semiterm.fvar (w i)] ⋏ (A i).subst ![Semiterm.fvar (w i)]) 🡒
          γ.subst (Semiterm.fvar z :> fun i ↦ Semiterm.fvar (w i)) := by
  have hcon : T.internalize V ⊢
      (witnessConj d A c ⋏ Matrix.conj (fun i ↦ d.subst ![Semiterm.fvar (w i)] ⋏
        (A i).subst ![Semiterm.fvar (w i)])) 🡒
          Matrix.conj (fun i ↦ Semiformula.equal (Semiterm.fvar (c i)) (Semiterm.fvar (w i))) := by
    apply matrixConj_intro
    intro i
    have h₁ := matrixConj_elim (𝓢 := T.internalize V) (fun i ↦ d.subst ![Semiterm.fvar (w i)] ⋏
      (A i).subst ![Semiterm.fvar (w i)]) i
    have h₂ := witness_eq_mem (T := T) d A c w i
    cl_prover [h₁, h₂]
  have hsymm := tprovable_equal_symm_imp (S := T) (Semiterm.fvar z) (Semiterm.fvar e)
  have hc := hcongr (Semiterm.fvar e) (Semiterm.fvar z) (fun i ↦ Semiterm.fvar (c i))
    (fun i ↦ Semiterm.fvar (w i))
  cl_prover [hcon, hsymm, hc]

include hd hγ hcongr in
lemma back_funcGraph (c : Fin k → V) (e z : V) :
    T.internalize V ⊢ witnessConj d A c 🡒 γ.subst (Semiterm.fvar e :> fun i ↦ Semiterm.fvar (c i)) 🡒
      Semiformula.equal (Semiterm.fvar z) (Semiterm.fvar e) 🡒
        (funcGraph d A γ).subst ![Semiterm.fvar z] := by
  rw [funcGraph_subst_fvar]
  unfold relativizedImp
  have key : T.internalize V ⊢
      (witnessConj d A c ⋏ γ.subst (Semiterm.fvar e :> fun i ↦ Semiterm.fvar (c i)) ⋏
        Semiformula.equal (Semiterm.fvar z) (Semiterm.fvar e)) 🡒
        ∀¹^[k] (Matrix.conj (fun i : Fin k ↦ d.subst ![Semiterm.bvar (i.addCast 0)] ⋏
          (A i).subst ![Semiterm.bvar (i.addCast 0)]) 🡒
            γ.subst (Semiterm.fvar z :> fun i : Fin k ↦ Semiterm.bvar (i.addCast 0))) := by
    apply TProof.allItr_generalize_imp (k := k)
    have hb := back_core (T := T) d γ (fun i ↦ Semiformula.shift^[k] (A i)) hcongr
      (fun i ↦ c i + (k : V)) (fun i : Fin k ↦ (i : V)) (e + k) (z + k)
    have hd' := Function.iterate_fixed hd k
    have hγ' := Function.iterate_fixed hγ k
    simpa [shift_iterate_witnessConj, hd', hγ'] using conj_of_curry hb
  cl_prover [key]

include huniq in
lemma front_core (c : Fin k → V) (z e : V) :
    T.internalize V ⊢ witnessConj d A c 🡒 (funcGraph d A γ).subst ![Semiterm.fvar z] 🡒
      d.subst ![Semiterm.fvar z] 🡒 d.subst ![Semiterm.fvar e] 🡒
        γ.subst (Semiterm.fvar e :> fun i ↦ Semiterm.fvar (c i)) 🡒
          Semiformula.equal (Semiterm.fvar z) (Semiterm.fvar e) := by
  have hsp := funcGraph_specialize_witness (T := T) d γ A z c
  have hdA := witnessConj_dA (T := T) d A c
  have hD := witnessConj_dom (T := T) d A c
  have hu := huniq (Semiterm.fvar z) (Semiterm.fvar e) (fun i ↦ Semiterm.fvar (c i))
  cl_prover [hu, hsp, hdA, hD]

include hd hγ huniq hcongr in
lemma funcGraph_iff_equal (c : Fin k → V) (e z : V) :
    T.internalize V ⊢ witnessConj d A c 🡒 d.subst ![Semiterm.fvar e] 🡒
      γ.subst (Semiterm.fvar e :> fun i ↦ Semiterm.fvar (c i)) 🡒 d.subst ![Semiterm.fvar z] 🡒
        ((funcGraph d A γ).subst ![Semiterm.fvar z] 🡘
          Semiformula.equal (Semiterm.fvar z) (Semiterm.fvar e)) := by
  have f := front_core (T := T) d γ A huniq c z e
  have b := back_funcGraph (T := T) d γ hd hγ A hcongr c e z
  have fwd : T.internalize V ⊢ witnessConj d A c 🡒 d.subst ![Semiterm.fvar e] 🡒
      γ.subst (Semiterm.fvar e :> fun i ↦ Semiterm.fvar (c i)) 🡒 d.subst ![Semiterm.fvar z] 🡒
        ((funcGraph d A γ).subst ![Semiterm.fvar z] 🡒
          Semiformula.equal (Semiterm.fvar z) (Semiterm.fvar e)) := by
    cl_prover 128 [f]
  have bwd : T.internalize V ⊢ witnessConj d A c 🡒 d.subst ![Semiterm.fvar e] 🡒
      γ.subst (Semiterm.fvar e :> fun i ↦ Semiterm.fvar (c i)) 🡒 d.subst ![Semiterm.fvar z] 🡒
        (Semiformula.equal (Semiterm.fvar z) (Semiterm.fvar e) 🡒
          (funcGraph d A γ).subst ![Semiterm.fvar z]) := by
    cl_prover 128 [b]
  cl_prover 128 [fwd, bwd]

include hd hγ huniq hcongr in
lemma witness_body_imp (c : Fin k → V) (e : V) :
    T.internalize V ⊢ (witnessConj d A c ⋏ d.subst ![Semiterm.fvar e] ⋏
      γ.subst (Semiterm.fvar e :> fun i ↦ Semiterm.fvar (c i))) 🡒
        (∀¹ (d 🡒 (funcGraph d A γ 🡘 Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar e)))) := by
  apply TProof.generalize_imp
  have hz := funcGraph_iff_equal (T := T) d γ hd hγ (fun i ↦ (A i).shift) huniq hcongr
    (fun i ↦ c i + 1) (e + 1) 0
  have hΦ : (funcGraph d A γ).shift = funcGraph d (fun i ↦ (A i).shift) γ := by
    rw [shift_funcGraph, hd, hγ]
  simpa [Semiformula.free, hd, hγ, hΦ] using conj_of_curry hz

include hd hγ huniq hcongr in
lemma exists_body (c : Fin k → V) (e : V) :
    T.internalize V ⊢ witnessConj d A c 🡒 d.subst ![Semiterm.fvar e] 🡒
      γ.subst (Semiterm.fvar e :> fun i ↦ Semiterm.fvar (c i)) 🡒
        ∃¹ definesElementBody d (funcGraph d A γ) := by
  have s₂ := witness_body_imp (T := T) d γ hd hγ A huniq hcongr c e
  have intro := TProof.subst_imp_exs (T := T) (definesElementBody d (funcGraph d A γ))
    (Semiterm.fvar e)
  rw [definesElementBody_subst_fvar] at intro
  cl_prover 128 [s₂, intro]

include hd hγ huniq hcongr in
lemma free_premise (c : Fin k → V) :
    T.internalize V ⊢
      (d ⋏ γ.subst (Semiterm.bvar 0 :> fun i ↦ (Semiterm.fvar (c i) : Semiterm V L 1))).free 🡒
        (witnessConj d A c 🡒 ∃¹ definesElementBody d (funcGraph d A γ)).shift := by
  have ex := exists_body (T := T) d γ hd hγ (fun i ↦ (A i).shift) huniq hcongr
    (fun i ↦ c i + 1) 0
  simpa [Semiformula.free, hd, hγ, shift_funcGraph] using conj_of_curry_swap ex

include hd hγ huniq hcongr in
theorem definesElement_funcGraph
    (hex : ∀ w : Fin k → Term V L, T.internalize V ⊢
      Matrix.conj (fun i ↦ d.subst ![w i]) 🡒
        ∃¹ (d ⋏ γ.subst (Semiterm.bvar 0 :> fun i ↦ (w i).bShift)))
    (c : Fin k → V) :
    T.internalize V ⊢
      Matrix.conj (fun i ↦ (definesElementBody d (A i)).subst ![Semiterm.fvar (c i)]) 🡒
        definesElement d (funcGraph d A γ) := by
  have h1 : T.internalize V ⊢ Matrix.conj (fun i ↦ d.subst ![Semiterm.fvar (c i)]) 🡒
      ∃¹ (d ⋏ γ.subst (Semiterm.bvar 0 :> fun i ↦ (Semiterm.fvar (c i) : Semiterm V L 1))) := by
    simpa using hex (fun i ↦ Semiterm.fvar (c i))
  have S1 : T.internalize V ⊢ witnessConj d A c 🡒
      ∃¹ (d ⋏ γ.subst (Semiterm.bvar 0 :> fun i ↦ (Semiterm.fvar (c i) : Semiterm V L 1))) := by
    have h₂ := witnessConj_dA (T := T) d A c
    have h₃ := witnessConj_dom (T := T) d A c
    cl_prover 128 [h1, h₂, h₃]
  have hex2 := TProof.exs_imp_of_free (T := T)
    (φ := d ⋏ γ.subst (Semiterm.bvar 0 :> fun i ↦ (Semiterm.fvar (c i) : Semiterm V L 1)))
    (R := witnessConj d A c 🡒 ∃¹ definesElementBody d (funcGraph d A γ))
    (free_premise (T := T) d γ hd hγ A huniq hcongr c)
  unfold definesElement
  cl_prover 128 [S1, hex2]

end funcGraphWitness

end definesElement

end defines

end FFL.FirstOrder.Arithmetic.Bootstrapping
