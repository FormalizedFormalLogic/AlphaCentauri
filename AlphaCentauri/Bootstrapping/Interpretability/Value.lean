module

public import AlphaCentauri.Bootstrapping.Interpretability.TranslationTable
public import AlphaCentauri.Bootstrapping.Proof.ExistsElimination
public import AlphaCentauri.Interpretability.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Typed
public import Foundation.Meta.ClProver
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Provable

/-!
# Values of closed terms along the internal translation

The internal formula `definesElement d A` states that a formula `A` defines a unique element of the
domain `d`, and the graph of a function symbol under equivalent hypotheses is congruent. Along a
table, the internal translation of a typed term or formula of $L_2$ is the typed formula built from
the entries of the table. Along a table of a translation, the internal value of a closed typed term
is defined by a formula, these defining formulas are derivable under the negated domain instances of
the term, and the defining formula is transported along the substitution of a closed term for a
variable.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section

attribute [local simp] Semiformula.shift_substs Semiformula.substs_substs


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

lemma relativizedImp_imp_relativizedImp_of_imp {k : ℕ} (d d' : Semiformula V L 1)
    (A B : Fin k → Semiformula V L 1) (C C' : Semiformula V L (0 + k))
    (hA : ∀ i, T.internalize V ⊢ ∀¹ (d' ⋏ B i 🡒 d ⋏ A i))
    (hC : T.internalize V ⊢ (Semiformula.shift^[k] C).subst (fun i ↦ Semiterm.fvar (i : V)) 🡒
      (Semiformula.shift^[k] C').subst fun i ↦ Semiterm.fvar (i : V)) :
    T.internalize V ⊢ relativizedImp d A C 🡒 relativizedImp d' B C' := by
  have h₁ (i : Fin k) : T.internalize V ⊢
      (Semiformula.shift^[k] d').subst ![Semiterm.fvar (i : V)] ⋏
        (Semiformula.shift^[k] (B i)).subst ![Semiterm.fvar (i : V)] 🡒
      (Semiformula.shift^[k] d).subst ![Semiterm.fvar (i : V)] ⋏
        (Semiformula.shift^[k] (A i)).subst ![Semiterm.fvar (i : V)] := by
    have := TProof.shift_iterate! (hA i) k
    simp only [Semiformula.shift_iterate_imp, Semiformula.shift_iterate_all,
      Semiformula.shift_iterate_and] at this
    have h₂ := TProof.all_imp_subst (T := T)
      (Semiformula.shift^[k] d' ⋏ Semiformula.shift^[k] (B i) 🡒
        Semiformula.shift^[k] d ⋏ Semiformula.shift^[k] (A i)) (Semiterm.fvar (i : V))
    simp only [Semiformula.substs_imp, Semiformula.substs_and] at h₂
    exact h₂ ⨀ this
  apply TProof.allItr_generalize_imp
  simp only [relativizedImp, Semiformula.shift_iterate_allItr]
  apply C_trans (TProof.allItr_specialize _ fun i ↦ Semiterm.fvar (i : V))
  simp only [Semiformula.shift_iterate_imp, Semiformula.substs_imp, Semiformula.shift_iterate_conj,
    Semiformula.substs_conj, Semiformula.shift_iterate_and, Semiformula.substs_and,
    Semiformula.subst_shift_iterate_subst_bvar, Fin.addCast_val]
  have h₂ := matrixConj_imp_matrixConj (𝓢 := T.internalize V) (φ := ⊤)
    (v := fun i : Fin k ↦ (Semiformula.shift^[k] d').subst ![Semiterm.fvar (i : V)] ⋏
      (Semiformula.shift^[k] (B i)).subst ![Semiterm.fvar (i : V)])
    (u := fun i : Fin k ↦ (Semiformula.shift^[k] d).subst ![Semiterm.fvar (i : V)] ⋏
      (Semiformula.shift^[k] (A i)).subst ![Semiterm.fvar (i : V)]) fun i ↦ by
    have := h₁ i
    cl_prover [this]
  cl_prover [h₂, hC]

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

variable [L.Eq] [𝗘𝗤 L ⪯ T]

/-- If every instance of the domain `d` is provable and `X` is preserved by equal arguments, then
`∀ w⃗ (⋀ᵢ (d(wᵢ) ∧ wᵢ = uᵢ) → X(w⃗))` is provably equivalent to `X(u⃗)`. -/
lemma tprovable_relativizedImp_equal_iff {k : ℕ} (d : Semiformula V L 1)
    (hd : ∀ t : Term V L, T.internalize V ⊢ d.subst ![t]) (u : Fin k → Term V L)
    (X : Semiformula V L k)
    (hX : ∀ (j : ℕ) (s w : Fin k → Term V L), T.internalize V ⊢
      Matrix.conj (fun i ↦ Semiformula.equal (s i) (w i)) 🡒
        (Semiformula.shift^[j] X).subst w 🡒 (Semiformula.shift^[j] X).subst s) :
    T.internalize V ⊢ relativizedImp d (fun i ↦ Semiformula.equal (Semiterm.bvar 0) (u i).bShift)
      (X.subst fun i ↦ Semiterm.bvar (i.addCast 0)) 🡘 X.subst u := by
  have h₁ := TProof.allItr_specialize (T := T) (Matrix.conj (fun i : Fin k ↦
      d.subst ![Semiterm.bvar (i.addCast 0)] ⋏
        (Semiformula.equal (Semiterm.bvar 0) (u i).bShift).subst ![Semiterm.bvar (i.addCast 0)]) 🡒
      X.subst fun i ↦ Semiterm.bvar (i.addCast 0)) (fun j ↦ u (Fin.cast (zero_add k) j))
  simp only [Semiformula.substs_equal, Semiterm.substs_bvar, Matrix.cons_val_fin_one,
    Semiterm.bShift_substs_succ, Matrix.tail_cons, Semiformula.substs_imp, Semiformula.substs_conj,
    Semiformula.substs_and, Semiformula.substs_substs, Matrix.vecMap_cons', Matrix.head_cons,
    Matrix.vecMap_nil, Semiterm.substs_substs, Semiterm.bShift_substs_zero,
    Semiterm.substs_vecMap_bvar] at h₁
  have hc : T.internalize V ⊢ Matrix.conj fun i ↦ d.subst ![u i] ⋏ Semiformula.equal (u i) (u i) :=
    tprovable_conj T fun i ↦ K_intro (hd (u i)) (tprovable_equal_refl T (u i))
  have h₂ : T.internalize V ⊢ X.subst u 🡒 relativizedImp d
      (fun i ↦ Semiformula.equal (Semiterm.bvar 0) (u i).bShift)
      (X.subst fun i ↦ Semiterm.bvar (i.addCast 0)) := by
    unfold relativizedImp
    apply TProof.allItr_generalize_imp
    simp only [Semiformula.shift_iterate_subst, Semiformula.substs_equal, Semiterm.substs_bvar,
      Matrix.cons_val_fin_one, Semiterm.bShift_substs_succ, Matrix.tail_cons,
      Semiformula.shift_iterate_imp, Semiformula.shift_iterate_conj, Semiformula.shift_iterate_and,
      Matrix.vecMap_cons', Matrix.head_cons, Semiterm.shift_iterate_bvar, Matrix.vecMap_nil,
      Semiformula.shift_iterate_equal, Semiterm.shift_iterate_subst_nil,
      Semiterm.shift_iterate_vecMap_bvar, Semiformula.substs_imp, Semiformula.substs_conj,
      Semiformula.substs_and, Semiformula.substs_substs, Fin.addCast_val, Semiterm.subst_nil_subst,
      Semiterm.bShift_substs_zero, Semiterm.substs_vecMap_bvar]
    have h₃ := hX k (fun i ↦ Semiterm.fvar ((i : ℕ) : V)) (fun i ↦ Semiterm.shift^[k] (u i))
    have h₄ := matrixConj_imp_matrixConj (𝓢 := T.internalize V) (φ := ⊤)
      (v := fun i : Fin k ↦ (Semiformula.shift^[k] d).subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
        Semiformula.equal (Semiterm.fvar ((i : ℕ) : V)) (Semiterm.shift^[k] (u i)))
      (u := fun i : Fin k ↦
        Semiformula.equal (Semiterm.fvar ((i : ℕ) : V)) (Semiterm.shift^[k] (u i)))
      fun i ↦ by cl_prover
    cl_prover [h₃, h₄]
  unfold relativizedImp at h₂ ⊢
  simp only [Semiformula.substs_equal, Semiterm.substs_bvar, Matrix.cons_val_fin_one,
    Semiterm.bShift_substs_succ, Matrix.tail_cons] at h₂ ⊢
  cl_prover [h₁, h₂, hc]

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

end

section

attribute [local simp] Semiformula.substs_substs



/-! ## Translation of typed formulas -/

section typedShapes

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] {tbl : V}

/-- The coded translation of a closed typed term, as a typed formula in one variable. -/
noncomputable def varEqualT (hT : IsTable L₁ L₂ tbl) (t : Term V L₂) : Semiformula V L₁ 1 :=
  ⟨varEqual L₁ L₂ tbl t.val, by simpa using IsSemiformula.varEqual hT t.isSemiterm⟩

@[simp] lemma varEqualT_val (hT : IsTable L₁ L₂ tbl) (t : Term V L₂) :
    (varEqualT hT t).val = varEqual L₁ L₂ tbl t.val := rfl

lemma varEqualT_fvar (hT : IsTable L₁ L₂ tbl) (x : V) :
    varEqualT hT (Semiterm.fvar x) =
      Semiformula.rel (Language.Eq.eq : L₁.Rel 2) ![Semiterm.bvar 0, Semiterm.fvar x] := by
  ext
  simp [varEqual_fvar]
  rfl

omit [L₁.Eq] in
lemma val_bvar_addCast_vec {k l : ℕ} :
    SemitermVec.val (fun i : Fin k ↦ (Semiterm.bvar (i.addCast l) : Semiterm V L₁ (l + k))) =
      bvarVec 0 (k : V) := by
  rw [bvarVec_zero_eq_matrixToVec (L := L₁) l k]
  rfl

section guard

lemma varEqualVec_typed (hT : IsTable L₁ L₂ tbl) {k : ℕ} (v : Fin k → Term V L₂) :
    varEqualVec L₁ L₂ tbl k (SemitermVec.val v) = matrixToVec fun i ↦ (varEqualT hT (v i)).val := by
  change varEqualVec L₁ L₂ tbl k (matrixToVec fun i ↦ (v i).val) = _
  have hv : IsUTermVec L₂ (k : V) (matrixToVec fun i ↦ (v i).val) :=
    (SemitermVec.isSemitermVec v).isUTerm
  rw [eq_matrixToVec_iff]
  constructor
  · exact (len_varEqualVec hv).symm
  · intro i
    rw [nth_varEqualVec (i := (i : V)) hv (by simp)]
    simp

omit [L₁.Eq] in
lemma domainAt_typed {n k : ℕ} (d : Semiformula V L₁ 1) (hd : d.val = tableDomain tbl)
    (i : Fin k) : domainAt L₁ tbl (i : V) = (d.subst ![Semiterm.bvar (i.addCast n)]).val := by
  rw [Semiformula.val_substs, hd, domainAt]
  simp

omit [L₁.Eq] in
lemma relocate_typed {n k : ℕ} (s : V) (A : Semiformula V L₁ 1) (i : Fin k) :
    relocate L₁ (i : V) s A.val = (A.subst ![Semiterm.bvar (i.addCast n)]).val := by
  rw [relocate_eq_subst (L := L₁) (n := 0) (by simp),
    Semiformula.val_substs]
  simp

omit [L₁.Eq] in
lemma guardVec_typed {n k : ℕ} (s : V) (d : Semiformula V L₁ 1) (hd : d.val = tableDomain tbl)
    (A : Fin k → Semiformula V L₁ 1) :
    guardVec L₁ tbl s (matrixToVec fun i ↦ (A i).val) k =
      matrixToVec fun i ↦ (d.subst ![Semiterm.bvar (i.addCast n)] ⋏
        (A i).subst ![Semiterm.bvar (i.addCast n)]).val := by
  rw [eq_matrixToVec_iff]
  constructor
  · simp
  · intro i
    rw [nth_guardVec _ _ _ _ _ (by simp), matrixToVec_nth, Semiformula.val_and,
      domainAt_typed d hd, relocate_typed]

end guard

section table

variable (hT : IsTable L₁ L₂ tbl)

lemma funcTail_typed {k : ℕ} (F : L₂.Func k) :
    funcTail L₁ tbl (k : V) (⌜F⌝ : V) =
      ((hT.funcT F).subst (Semiterm.bvar (Fin.cast (Nat.add_comm k 1) (Fin.last k)) :>
        fun i : Fin k ↦ Semiterm.bvar (i.addCast 1))).val := by
  have hw : SemitermVec.val (Semiterm.bvar (Fin.cast (Nat.add_comm k 1) (Fin.last k)) :>
      fun i : Fin k ↦ (Semiterm.bvar (i.addCast 1) : Semiterm V L₁ (1 + k))) =
        ^#(k : V) ∷ bvarVec 0 (k : V) := by
    rw [SemitermVec.val_cons, val_bvar_addCast_vec]
    simp
  rw [funcTail, Semiformula.val_substs, hw]
  rfl

lemma tableRel_typed {k : ℕ} (R : L₂.Rel k) :
    tableRel tbl (k : V) (⌜R⌝ : V) =
      ((hT.relT R).subst (fun i : Fin k ↦ Semiterm.bvar (i.addCast 0))).val := by
  rw [Semiformula.val_substs, val_bvar_addCast_vec]
  symm
  exact subst_eq_self (hT.relT R).isSemiformula (IsSemitermVec.bvarVec (by simp))
    (fun i hi ↦ by simp [nth_bvarVec _ _ _ hi])

lemma varEqualT_func {k : ℕ} (F : L₂.Func k) (v : Fin k → Term V L₂) :
    varEqualT hT (Semiterm.func F v) =
      funcGraph hT.domT (fun i ↦ varEqualT hT (v i)) (hT.funcT F) := by
  ext
  rw [varEqualT_val, Semiterm.func_val, varEqual_func (f := (⌜F⌝ : V)) (by simp)
    (SemitermVec.isUTermVec v), varEqualVec_typed hT v,
    guardVec_typed (A := fun i ↦ varEqualT hT (v i)) (d := hT.domT) (n := 1) (k + 1 : V) rfl,
    funcGraph, val_allItr_imp_conj, funcTail_typed hT F]

lemma translate_rel_typed {k : ℕ} (R : L₂.Rel k) (v : Fin k → Term V L₂) :
    translate L₁ L₂ tbl (Semiformula.rel R v : Formula V L₂).val =
      (relativizedImp hT.domT (fun i ↦ varEqualT hT (v i))
        ((hT.relT R).subst (fun i ↦ Semiterm.bvar (i.addCast 0)))).val := by
  rw [Semiformula.rel_val, translate_rel (by simp) (SemitermVec.isUTermVec v), translateRel,
    varEqualVec_typed hT v, guardVec_typed (A := fun i ↦ varEqualT hT (v i))
      (d := hT.domT) (n := 0) (k : V) rfl,
    tableRel_typed hT R, relativizedImp, val_allItr_imp_conj]

end table

end typedShapes

/-! ## Derivability of the defining formulas -/

section valueLemma

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

section definesCode

variable (L : Language) [L.Encodable] [L.LORDefinable] [L.Eq]

/-- The code of `definesElement`. -/
noncomputable def definesCode (d e : V) : V :=
  ^∃ (d ^⋏ ^∀ (imp L (subst L ?[^#0] d) (iff L (subst L ?[^#0] e)
    (^rel 2 (Encodable.encode (Language.Eq.eq : L.Rel 2) : V) ?[^#0, ^#1]))))

instance definesCode.definable : 𝚺ᴬ₁-Function₂[V] definesCode L := by
  definability

end definesCode

section definesElementVal

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq]

lemma definesElement_val (d A : Semiformula V L 1) :
    (definesElement d A).val = definesCode L d.val A.val := by
  simp only [definesElement, definesElementBody, definesCode, Semiformula.val_exs,
    Semiformula.val_and, Semiformula.val_all, Semiformula.val_imp, Semiformula.val_iff,
    Semiformula.val_substs]
  simp [Semiformula.equal]
  rfl

end definesElementVal

section fvar

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] {T : Theory L} [T.Δ₁]

lemma tprovable_definesElement_fvar [𝗘𝗤 L ⪯ T] (d : Semiformula V L 1) (x : V) :
    T.internalize V ⊢ d.subst ![Semiterm.fvar x] 🡒
      definesElement d
        (Semiformula.rel (Language.Eq.eq : L.Rel 2) ![Semiterm.bvar 0, Semiterm.fvar x]) := by
  change T.internalize V ⊢ d.subst ![Semiterm.fvar x] 🡒
    definesElement d (Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar x))
  have h₁ : T.internalize V ⊢
      ∀¹ (uniqueAt d (Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar x)) x) := by
    apply TProof.all!
    simp only [uniqueAt, Semiformula.free_imp, Semiformula.free_iff]
    cl_prover
  have h₂ : T.internalize V ⊢ d.subst ![Semiterm.fvar x] 🡒
      (definesElementBody d (Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar x))).subst
        ![Semiterm.fvar x] := by
    rw [definesElementBody_subst_fvar]
    cl_prover [h₁]
  have h₃ := TProof.subst_imp_exs (T := T)
    (definesElementBody d (Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar x)))
    (Semiterm.fvar x)
  unfold definesElement
  cl_prover [h₂, h₃]

end fvar

section value

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S]
  {tbl : V}

omit [𝗘𝗤 L₁ ⪯ S] in
lemma definesElement_domT_val (h : IsTranslationTable L₂ S tbl) (t : Term V L₂) :
    (definesElement h.domT (varEqualT h.toIsTable t)).val =
      definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl t.val) := by
  have hd : tbl.[0] = h.domT.val := rfl
  rw [definesElement_val, varEqualT_val, ← hd]

lemma derivable_definesElement_fvar (h : IsTranslationTable L₂ S tbl) (x : V) :
    Derivable S (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl ^&x))
      (negDomSet L₁ tbl.[0] ^&x)) := by
  have hT := h.toIsTable
  have hd : tbl.[0] = h.domT.val := rfl
  have hs : IsFormulaSet L₁ (negDomSet L₁ tbl.[0] ^&x) :=
    IsFormulaSet.negDomSet hT.domain _
  have hφv : (h.domT.subst ![Semiterm.fvar x] : Formula V L₁).val = substs1 L₁ ^&x tbl.[0] := by
    rw [Semiformula.val_subst_fvar, hd]
  have hm : neg L₁ (h.domT.subst ![Semiterm.fvar x] : Formula V L₁).val ∈
      negDomSet L₁ tbl.[0] ^&x := by
    rw [mem_negDomSet_iff]
    exact ⟨x, var_lt_qqFvar x, by rw [hφv]⟩
  have hF : IsFormulaSet L₁ (insert (h.domT.subst ![Semiterm.fvar x] : Formula V L₁).val
      (negDomSet L₁ tbl.[0] ^&x)) :=
    IsFormulaSet.insert_iff.mpr ⟨Semiformula.isSemiformula_zero _, hs⟩
  have hφD : Derivable S (insert (h.domT.subst ![Semiterm.fvar x] : Formula V L₁).val
      (negDomSet L₁ tbl.[0] ^&x)) :=
    Derivable.em hF ((h.domT.subst ![Semiterm.fvar x] : Formula V L₁).val)
      (mem_bitInsert_iff.mpr (Or.inl rfl)) (mem_bitInsert_iff.mpr (Or.inr hm))
  have hTP := tprovable_definesElement_fvar (T := S) h.domT x
  rw [← varEqualT_fvar hT x] at hTP
  have h₁ := Derivable.of_tprovable_imp hTP hφD
  rw [definesElement_domT_val h] at h₁
  exact h₁

omit [L₂.Eq] in
lemma exists_func_termVec (hL₂ : L₂.SymbolsStandard V) {k f v : V}
    (ht : IsSemiterm L₂ 0 (^func k f v)) :
    ∃ (k' : ℕ) (F : L₂.Func k') (u : Fin k' → Term V L₂),
      k = k' ∧ f = (⌜F⌝ : V) ∧ SemitermVec.val u = v := by
  obtain ⟨hfun, hv⟩ := IsSemiterm.func.mp ht
  obtain ⟨k', F, rfl, rfl⟩ := hL₂.2 _ _ hfun
  obtain ⟨u, hu⟩ := exists_termVec hv
  exact ⟨k', F, u, rfl, rfl, hu⟩

lemma derivable_definesElement_func (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTranslationTable L₂ S tbl) {k : ℕ} (F : L₂.Func k) (u : Fin k → Term V L₂)
    (ih : ∀ i, Derivable S (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl (u i).val))
      (negDomSet L₁ tbl.[0] (u i).val))) :
    Derivable S (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl (Semiterm.func F u).val))
      (negDomSet L₁ tbl.[0] (Semiterm.func F u).val)) := by
  have hT := h.toIsTable
  have hd : tbl.[0] = h.domT.val := rfl
  have hsF : IsFormulaSet L₁ (negDomSet L₁ tbl.[0] (Semiterm.func F u).val) :=
    IsFormulaSet.negDomSet hT.domain _
  have hlt (i : Fin k) : (u i).val < (Semiterm.func F u).val := by
    have h₁ := nth_lt_qqFunc_of_lt (i := ((i : ℕ) : V)) (k := (k : V)) (f := (⌜F⌝ : V))
      (v := SemitermVec.val u) (by simp)
    rw [Semiterm.func_val]
    simpa using h₁
  have hsU (i : Fin k) : Derivable S (insert (definesElement h.domT (varEqualT hT (u i))).val
      (negDomSet L₁ tbl.[0] (Semiterm.func F u).val)) := by
    have hv := definesElement_domT_val h (u i)
    have hF : IsFormulaSet L₁ (insert (definesElement h.domT (varEqualT hT (u i))).val
        (negDomSet L₁ tbl.[0] (Semiterm.func F u).val)) :=
      IsFormulaSet.insert_iff.mpr ⟨Semiformula.isSemiformula_zero _, hsF⟩
    have hsub : insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl (u i).val))
        (negDomSet L₁ tbl.[0] (u i).val) ⊆ insert (definesElement h.domT (varEqualT hT (u i))).val
          (negDomSet L₁ tbl.[0] (Semiterm.func F u).val) := by
      intro x hx
      rcases mem_bitInsert_iff.mp hx with rfl | hx
      · exact mem_bitInsert_iff.mpr (Or.inl hv.symm)
      · exact mem_bitInsert_iff.mpr (Or.inr ((negDomSet_mono (L := L₁) (hlt i).le) hx))
    exact Derivable.wk hF hsub (ih i)
  have hY (c : Fin k → V) : S.internalize V ⊢
      Matrix.conj (fun i ↦ (definesElementBody h.domT (varEqualT hT (u i))).subst
        ![Semiterm.fvar (c i)]) 🡒
        definesElement h.domT (funcGraph h.domT (fun i ↦ varEqualT hT (u i)) (h.funcT F)) :=
    definesElement_funcGraph h.domT (h.funcT F) (h.domT_shift) (h.funcT_shift F)
      (fun i ↦ varEqualT hT (u i)) (h.tprovable_func_unique F) (h.tprovable_func_congr F)
      (h.tprovable_func_exists F) c
  have hfin := Derivable.conj_exs_elim hS (fun i ↦ definesElementBody h.domT (varEqualT hT (u i)))
    (definesElement h.domT (funcGraph h.domT (fun i ↦ varEqualT hT (u i)) (h.funcT F))) hsF
    hY hsU
  have hYeq : definesElement h.domT (funcGraph h.domT (fun i ↦ varEqualT hT (u i))
      (h.funcT F)) = definesElement h.domT (varEqualT hT (Semiterm.func F u)) := by
    rw [varEqualT_func hT F u]
  rw [hYeq, definesElement_domT_val h] at hfin
  exact hfin

theorem derivable_definesElement (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTranslationTable L₂ S tbl) (hL₂ : L₂.SymbolsStandard V) {t : V}
    (ht : IsSemiterm L₂ 0 t) :
    Derivable S
      (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl t)) (negDomSet L₁ tbl.[0] t)) := by
  have hP : 𝚺ᴬ₁-Predicate fun t : V ↦
      Derivable S
        (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl t)) (negDomSet L₁ tbl.[0] t)) := by
    definability
  exact IsSemiterm.sigma1_induction hP (fun z hz ↦ absurd hz (by simp))
    (fun x ↦ derivable_definesElement_fvar h x)
    (fun k f v hf hv ih ↦ by
      obtain ⟨k', F, u, rfl, rfl, rfl⟩ := exists_func_termVec hL₂ (IsSemiterm.func.mpr ⟨hf, hv⟩)
      have ih' (i : Fin k') : Derivable S
          (insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl (u i).val))
            (negDomSet L₁ tbl.[0] (u i).val)) := by
        simpa using ih ((i : ℕ) : V) (by simp)
      have h₂ := derivable_definesElement_func hS h F u ih'
      rw [Semiterm.func_val] at h₂
      exact h₂)
    t ht

end value

end valueLemma

/-! ## Substitution of a closed term -/

section termSubst

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

section defs

variable (L₁ L₂ : Language) [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable]

/-- The coded set of `¬δ(&b)`, `¬E_t(&b)` and `¬δ(&i)` for `i < t`, where `δ` is the domain formula
of the table and `E_t` is the coded formula of the value of `t`. -/
noncomputable def substHyp (tbl t b : V) : V :=
  insert (neg L₁ (substs1 L₁ (^&b) tbl.[0]))
    (insert (neg L₁ (substs1 L₁ (^&b) (varEqual L₁ L₂ tbl t))) (negDomSet L₁ tbl.[0] t))

instance substHyp.definable : 𝚺ᴬ₁-Function₃[V] substHyp L₁ L₂ := by
  definability

/-- The code of `∀ z (δ z → (E_{s[t]}(z) ↔ E_{s[&b]}(z)))`. -/
noncomputable def termSubstEquiv (tbl t b s : V) : V :=
  ^∀ (imp L₁ tbl.[0] (iff L₁ (varEqual L₁ L₂ tbl (termSubst L₂ ?[t] s))
    (varEqual L₁ L₂ tbl (termSubst L₂ ?[^&b] s))))

instance termSubstEquiv.definable : 𝚺ᴬ₁-Function₄[V] termSubstEquiv L₁ L₂ := by
  definability

end defs

section value

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.LORDefinable] [L₂.Eq] {S : Theory L₁} [S.Δ₁] [𝗘𝗤 _ ⪯ S]
  {tbl : V}

omit [L₂.Eq] in
lemma isFormulaSet_substHyp (hT : IsTable L₁ L₂ tbl) {t : V} (ht : IsSemiterm L₂ 0 t) (b : V) :
    IsFormulaSet L₁ (substHyp L₁ L₂ tbl t b) := by
  have h₁ : IsSemiformula L₁ 1 (varEqual L₁ L₂ tbl t) := by
    simpa using IsSemiformula.varEqual hT ht
  exact IsFormulaSet.insert_iff.mpr ⟨(IsSemiformula.substs1 (n := 0) (by simp) hT.domain).neg,
    IsFormulaSet.insert_iff.mpr ⟨(IsSemiformula.substs1 (n := 0) (by simp) h₁).neg,
      IsFormulaSet.negDomSet hT.domain t⟩⟩

lemma derivable_definesElement_substHyp
    (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTranslationTable L₂ S tbl) (hL₂ : L₂.SymbolsStandard V) {t : V}
    (ht : IsSemiterm L₂ 0 t) (b : V) :
    Derivable S (insert (definesElement h.domT
      (varEqualT h.toIsTable (⟨t, ht⟩ : Term V L₂))).val (substHyp L₁ L₂ tbl t b)) := by
  have hT := h.toIsTable
  have hd : tbl.[0] = h.domT.val := rfl
  have hv := definesElement_domT_val h (⟨t, ht⟩ : Term V L₂)
  have hF : IsFormulaSet L₁ (insert (definesElement h.domT
      (varEqualT hT (⟨t, ht⟩ : Term V L₂))).val (substHyp L₁ L₂ tbl t b)) :=
    IsFormulaSet.insert_iff.mpr ⟨Semiformula.isSemiformula_zero _, isFormulaSet_substHyp hT ht b⟩
  have hsub : insert (definesCode L₁ tbl.[0] (varEqual L₁ L₂ tbl t)) (negDomSet L₁ tbl.[0] t)
      ⊆ insert (definesElement h.domT (varEqualT hT (⟨t, ht⟩ : Term V L₂))).val
        (substHyp L₁ L₂ tbl t b) := by
    intro x hx
    rcases mem_bitInsert_iff.mp hx with rfl | hx
    · exact mem_bitInsert_iff.mpr (Or.inl hv.symm)
    · exact mem_bitInsert_iff.mpr (Or.inr (by simp [substHyp, hx]))
  exact Derivable.wk hF hsub (derivable_definesElement hS h hL₂ ht)

omit [𝗘𝗤 L₁ ⪯ S] in
lemma termSubstEquiv_eq_typed (h : IsTranslationTable L₂ S tbl) {t b s : V}
    {u u' : Term V L₂} (hu : u.val = termSubst L₂ ?[t] s) (hu' : u'.val = termSubst L₂ ?[^&b] s) :
    termSubstEquiv L₁ L₂ tbl t b s =
      (∀¹ (h.domT 🡒 (varEqualT h.toIsTable u 🡘 varEqualT h.toIsTable u'))).val := by
  have hd : tbl.[0] = h.domT.val := rfl
  simp only [termSubstEquiv, Semiformula.val_all, Semiformula.val_imp, Semiformula.val_iff,
    varEqualT_val, hu, hu', hd]

omit [L₂.Eq] in
lemma termSubst_func_val {k : ℕ} (F : L₂.Func k) {c v : V} (hc : IsSemiterm L₂ 0 c)
    (hv : IsSemitermVec L₂ (k : V) 1 v) :
    ∃ u : Fin k → Term V L₂, (∀ i : Fin k, (u i).val = termSubst L₂ ?[c] v.[(i : ℕ)]) ∧
      termSubst L₂ ?[c] (^func (k : V) ⌜F⌝ v) = (Semiterm.func F u).val := by
  have hw : IsSemitermVec L₂ (1 : V) 0 ?[c] := by simp [hc]
  have hi (i : Fin k) : IsSemiterm L₂ 0 (termSubst L₂ ?[c] v.[(i : ℕ)]) :=
    IsSemitermVec.termSubst hw (hv.nth (by simp))
  refine ⟨fun i ↦ ⟨termSubst L₂ ?[c] v.[(i : ℕ)], hi i⟩, fun i ↦ rfl, ?_⟩
  rw [termSubst_func (codeIn_func_quote F) hv.isUTerm, Semiterm.func_val]
  congr 1
  change termSubstVec L₂ (k : V) ?[c] v = matrixToVec fun i : Fin k ↦ termSubst L₂ ?[c] v.[(i : ℕ)]
  rw [eq_matrixToVec_iff]
  constructor
  · simp [hv.isUTerm]
  · intro i
    rw [nth_termSubstVec hv.isUTerm (by simp)]

lemma derivable_termSubstEquiv_bvar
    (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTranslationTable L₂ S tbl) (hL₂ : L₂.SymbolsStandard V) {t b : V}
    (ht : IsSemiterm L₂ 0 t) :
    Derivable S (insert (termSubstEquiv L₁ L₂ tbl t b (^#0)) (substHyp L₁ L₂ tbl t b)) := by
  have hT := h.toIsTable
  have hd : tbl.[0] = h.domT.val := rfl
  have hH := isFormulaSet_substHyp hT ht b
  have hD := derivable_definesElement_substHyp hS h hL₂ ht b
  have hTP := definesElement_iff_equal (T := S) h.domT (varEqualT hT (⟨t, ht⟩ : Term V L₂)) b
  have h₁ := Derivable.of_tprovable_imp hTP hD
  have hφδ : (h.domT.subst ![Semiterm.fvar b] : Formula V L₁).val = substs1 L₁ (^&b) tbl.[0] := by
    rw [Semiformula.val_subst_fvar, hd]
  have hφA : ((varEqualT hT (⟨t, ht⟩ : Term V L₂)).subst ![Semiterm.fvar b] : Formula V L₁).val =
      substs1 L₁ (^&b) (varEqual L₁ L₂ tbl t) := by
    rw [Semiformula.val_subst_fvar, varEqualT_val]
  have hm₁ : neg L₁ (substs1 L₁ (^&b) tbl.[0]) ∈ substHyp L₁ L₂ tbl t b :=
    mem_bitInsert_iff.mpr (Or.inl rfl)
  have hm₂ : neg L₁ (substs1 L₁ (^&b) (varEqual L₁ L₂ tbl t)) ∈ substHyp L₁ L₂ tbl t b :=
    mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inl rfl)))
  have hδ : Derivable S (insert (h.domT.subst ![Semiterm.fvar b] : Formula V L₁).val
      (substHyp L₁ L₂ tbl t b)) :=
    Derivable.em (IsFormulaSet.insert_iff.mpr ⟨Semiformula.isSemiformula_zero _, hH⟩)
      (h.domT.subst ![Semiterm.fvar b] : Formula V L₁).val
      (mem_bitInsert_iff.mpr (Or.inl rfl))
      (mem_bitInsert_iff.mpr (Or.inr (by rw [hφδ]; exact hm₁)))
  have hE : Derivable S (insert ((varEqualT hT (⟨t, ht⟩ : Term V L₂)).subst ![Semiterm.fvar b] :
      Formula V L₁).val (substHyp L₁ L₂ tbl t b)) :=
    Derivable.em (IsFormulaSet.insert_iff.mpr ⟨Semiformula.isSemiformula_zero _, hH⟩)
      ((varEqualT hT (⟨t, ht⟩ : Term V L₂)).subst ![Semiterm.fvar b] : Formula V L₁).val
      (mem_bitInsert_iff.mpr (Or.inl rfl))
      (mem_bitInsert_iff.mpr (Or.inr (by rw [hφA]; exact hm₂)))
  have h₂ := Derivable.modusPonens_typed h₁ hδ
  have h₃ := Derivable.modusPonens_typed h₂ hE
  have hu : (⟨t, ht⟩ : Term V L₂).val = termSubst L₂ ?[t] ^#0 := by simp
  have hu' : (Semiterm.fvar b : Term V L₂).val = termSubst L₂ ?[^&b] ^#0 := by simp
  have hC : (∀¹ (h.domT 🡒 (varEqualT hT (⟨t, ht⟩ : Term V L₂) 🡘
      varEqualT hT (Semiterm.fvar b)))) = ∀¹ (h.domT 🡒 (varEqualT hT (⟨t, ht⟩ : Term V L₂) 🡘
        Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar b))) := by
    rw [varEqualT_fvar]
    rfl
  rw [termSubstEquiv_eq_typed h hu hu', hC]
  exact h₃

omit [𝗘𝗤 L₁ ⪯ S] in
lemma derivable_termSubstEquiv_fvar (h : IsTranslationTable L₂ S tbl)
    {t b : V} (ht : IsSemiterm L₂ 0 t) (x : V) :
    Derivable S (insert (termSubstEquiv L₁ L₂ tbl t b (^&x)) (substHyp L₁ L₂ tbl t b)) := by
  have hT := h.toIsTable
  have hH := isFormulaSet_substHyp hT ht b
  have hA : S.internalize V ⊢ ∀¹ (h.domT 🡒 (varEqualT hT (Semiterm.fvar x : Term V L₂) 🡘
      varEqualT hT (Semiterm.fvar x : Term V L₂))) := by
    apply TProof.all!
    simp only [Semiformula.free, Nat.succ_eq_add_one, Nat.reduceAdd, Semiformula.shift_imp,
      Semiformula.shift_iff, Semiformula.substs_imp, Semiformula.substs_imply]
    cl_prover
  have hV := termSubstEquiv_eq_typed h (t := t) (b := b) (s := ^&x)
    (u := (Semiterm.fvar x : Term V L₂)) (u' := (Semiterm.fvar x : Term V L₂)) (by simp) (by simp)
  rw [hV]
  exact Derivable.of_tprovable hH hA

omit [𝗘𝗤 L₁ ⪯ S] in
lemma derivable_termSubstEquiv_func
    (h : IsTranslationTable L₂ S tbl) {t b : V} (ht : IsSemiterm L₂ 0 t)
    {k : ℕ} (F : L₂.Func k) {v : V} (hv : IsSemitermVec L₂ (k : V) 1 v)
    (ih : ∀ i < (k : V), Derivable S (insert (termSubstEquiv L₁ L₂ tbl t b v.[i])
      (substHyp L₁ L₂ tbl t b))) :
    Derivable S (insert (termSubstEquiv L₁ L₂ tbl t b (^func (k : V) ⌜F⌝ v))
      (substHyp L₁ L₂ tbl t b)) := by
  have hT := h.toIsTable
  have hH := isFormulaSet_substHyp hT ht b
  obtain ⟨u, hu, hfu⟩ := termSubst_func_val F ht hv
  obtain ⟨u', hu', hfu'⟩ := termSubst_func_val F (c := ^&b) (by simp) hv
  have hΦ (i : Fin k) : Derivable S (insert (∀¹ (h.domT 🡒
      (varEqualT hT (u i) 🡘 varEqualT hT (u' i)))).val (substHyp L₁ L₂ tbl t b)) := by
    rw [← termSubstEquiv_eq_typed h (hu i) (hu' i)]
    exact ih ((i : ℕ) : V) (by simp)
  have hc : Derivable S (insert (Matrix.conj fun i : Fin k ↦ ∀¹ (h.domT 🡒
      (varEqualT hT (u i) 🡘 varEqualT hT (u' i)))).val (substHyp L₁ L₂ tbl t b)) :=
    Derivable.conj_typed hH hΦ
  have hg := Derivable.of_tprovable_imp (funcGraph_congr h.domT
    (fun i ↦ varEqualT hT (u i)) (fun i ↦ varEqualT hT (u' i)) (h.funcT F)) hc
  have hg' := Derivable.of_tprovable_imp (tprovable_all_imp_all (T := S) h.domT _) hg
  rw [termSubstEquiv_eq_typed h hfu.symm hfu'.symm, varEqualT_func hT F u,
    varEqualT_func hT F u']
  exact hg'

theorem derivable_termSubstEquiv (hS : ∀ p ∈ S.Δ₁Class (V := V), Bootstrapping.shift L₁ p = p)
    (h : IsTranslationTable L₂ S tbl) (hL₂ : L₂.SymbolsStandard V) {t b s : V}
    (ht : IsSemiterm L₂ 0 t)
    (hs : IsSemiterm L₂ 1 s) :
    Derivable S (insert (termSubstEquiv L₁ L₂ tbl t b s) (substHyp L₁ L₂ tbl t b)) := by
  have hP : 𝚺ᴬ₁-Predicate fun s : V ↦
      Derivable S (insert (termSubstEquiv L₁ L₂ tbl t b s) (substHyp L₁ L₂ tbl t b)) := by
    definability
  exact IsSemiterm.sigma1_induction hP
    (fun z hz ↦ by
      obtain rfl : z = 0 := by simpa using hz
      exact derivable_termSubstEquiv_bvar hS h hL₂ ht)
    (fun x ↦ derivable_termSubstEquiv_fvar h ht x)
    (fun k f v hf hv ih ↦ by
      obtain ⟨k', F, rfl, rfl⟩ := hL₂.2 _ _ hf
      exact derivable_termSubstEquiv_func h ht F hv ih)
    s hs

end value

end termSubst

end

end FFL.FirstOrder.Arithmetic.Bootstrapping
