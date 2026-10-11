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
  refine TProof.allItr_generalize_imp (k := 1) ?_
  have h₁ : (fun i : Fin 1 ↦ (Semiterm.fvar (i : V) : Semiterm V L 0)) = ![Semiterm.fvar 0] := by
    funext i
    obtain rfl := Subsingleton.elim i 0
    simp
  simp only [Function.iterate_one, Semiformula.shift_iff, shift_funcGraph, h₁,
    Semiformula.substs_imply, funcGraph_subst_fvar, Semiformula.shift_imp, shift_conj_fin,
    Semiformula.shift_all]
  exact relativizedImp_congr (T := T) d.shift (fun i ↦ (A i).shift) (fun i ↦ (B i).shift) _

end funcGraph

section definesElement

open _root_.FFL.Entailment

variable [L.Eq]

/-- `∃ y (d(y) ∧ ∀ z (d(z) → (A(z) ↔ z = y)))`: `A` defines a unique element of `d`. -/
noncomputable def definesElement (d A : Semiformula V L 1) : Formula V L :=
  ∃¹ (d ⋏ (∀¹ (d.subst ![Semiterm.bvar 0] 🡒
    (A.subst ![Semiterm.bvar 0] 🡘 Semiformula.equal (Semiterm.bvar 0) (Semiterm.bvar 1)))))

lemma shift_equal_eq {n : ℕ} (s t : Semiterm V L n) :
    (Semiformula.equal s t).shift = Semiformula.equal s.shift t.shift := by
  unfold Semiformula.equal
  simp only [Semiformula.shift_rel]
  congr 1
  funext j
  match j with
  | 0 => rfl
  | 1 => rfl

omit [L.Eq] in
lemma shift_vec_fvar (x : V) :
    (Semiterm.shift ⨟ ![(Semiterm.fvar x : Semiterm V L 0)]) = ![Semiterm.fvar (x + 1)] := by
  funext j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simp

omit [L.Eq] in
lemma shift_vec_bvar {n : ℕ} :
    (Semiterm.shift ⨟ ![(Semiterm.bvar 0 : Semiterm V L (n + 1))]) = ![Semiterm.bvar 0] := by
  funext j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simp

omit [L.Eq] in
lemma q_fvar_one (x : V) :
    SemitermVec.q ![(Semiterm.fvar x : Semiterm V L 0)] 1 = Semiterm.fvar x := by
  rw [show (1 : Fin 2) = Fin.succ 0 from rfl, SemitermVec.q_succ]
  simp

omit [L.Eq] in
lemma shift_vec_q_fvar (x : V) :
    ((Semiterm.shift : Semiterm V L 1 → Semiterm V L 1) ⨟
      (SemitermVec.q ![(Semiterm.fvar x : Semiterm V L 0)])) =
      (SemitermVec.q ![(Semiterm.fvar (x + 1) : Semiterm V L 0)]) := by
  funext j
  cases j using Fin.cases with
  | zero => simp
  | succ i =>
    obtain rfl := Subsingleton.elim i 0
    change Semiterm.shift (SemitermVec.q ![(Semiterm.fvar x : Semiterm V L 0)] (Fin.succ 0)) =
      SemitermVec.q ![(Semiterm.fvar (x + 1) : Semiterm V L 0)] (Fin.succ 0)
    simp only [SemitermVec.q_succ]
    simp

omit [L.Eq] in
lemma fvar_vec_fin_one :
    (fun i : Fin 1 ↦ (Semiterm.fvar (i : V) : Semiterm V L 0)) = ![Semiterm.fvar 0] := by
  funext i
  obtain rfl := Subsingleton.elim i 0
  simp

theorem definesElement_exists (d A : Semiformula V L 1) [𝗘𝗤 L ⪯ T] :
    T.internalize V ⊢ definesElement d A 🡒 ∃¹ (d ⋏ A) := by
  unfold definesElement
  refine FiniteContext.emptyPrf <| TProof.exs_imp_exs! (Γ := []) <| FiniteContext.of ?_
  have h₁ := TProof.all_imp_subst (T := T)
    (d.shift.subst ![Semiterm.bvar 0] 🡒
      (A.shift.subst ![Semiterm.bvar 0] 🡘 Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar 0)))
    (Semiterm.fvar 0)
  have h₂ := tprovable_equal_refl (S := T) (Semiterm.fvar (0 : V))
  have v₁ : ((Semiterm.subst (SemitermVec.q ![(Semiterm.fvar 0 : Semiterm V L 0)]))⨟
      (Semiterm.shift ⨟ ![(Semiterm.bvar 0 : Semiterm V L 2)])) =
      ![(Semiterm.bvar 0 : Semiterm V L 1)] := by
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp
  have v₂ : SemitermVec.q ![(Semiterm.fvar 0 : Semiterm V L 0)] 1 = Semiterm.fvar 0 := by
    rw [show (1 : Fin 2) = Fin.succ 0 from rfl, SemitermVec.q_succ]
    simp
  have v₃ : ((Semiterm.subst ![(Semiterm.fvar 0 : Semiterm V L 0)])⨟
      ![(Semiterm.bvar 0 : Semiterm V L 1)]) = ![(Semiterm.fvar 0 : Semiterm V L 0)] := by
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp
  simp only [Semiformula.free, Semiformula.shift_and, Semiformula.shift_all, Semiformula.shift_imp,
    Semiformula.shift_iff, Semiformula.substs_and, Semiformula.substs_all, Semiformula.substs_imp,
    Semiformula.substs_imply, Semiformula.substs_substs, Semiformula.shift_substs,
    shift_equal_eq, Semiformula.substs_equal, Semiterm.shift_bvar, Semiterm.substs_bvar,
    SemitermVec.q_zero, Semiterm.substs_fvar, Matrix.cons_val_zero, v₁, v₂, v₃] at h₁ ⊢
  cl_prover [h₁, h₂]

omit [L.Eq] in
lemma TProof.exs_imp_of_free {φ : Semiformula V L 1} {R : Formula V L}
    (h : T.internalize V ⊢ φ.free 🡒 R.shift) : T.internalize V ⊢ ∃¹ φ 🡒 R := by
  have h₁ : [∼R] ⊢[T.internalize V] ∀¹ (∼φ) := by
    apply TProof.generalize!
    apply FiniteContext.provable_iff.mpr
    have h₄ : T.internalize V ⊢ ∼R.shift 🡒 ∼(φ.free) := by cl_prover [h]
    simpa [Semiformula.free] using h₄
  have h₂ : T.internalize V ⊢ ∀¹ (∼φ) 🡒 ∼(∃¹ φ) := by
    simp
  have h₃ : T.internalize V ⊢ ∼R 🡒 ∀¹ (∼φ) := by
    simpa using FiniteContext.provable_iff.mp h₁
  cl_prover [h₂, h₃]

omit [L.Eq] in
private lemma prop_combine {Dc Hq Dx Ax Dz Az Ezc Ezx : Formula V L}
    (h₁ : T.internalize V ⊢ Hq 🡒 Dz 🡒 (Az 🡘 Ezc))
    (h₂ : T.internalize V ⊢ Hq 🡒 Dx 🡒 Ax 🡒 Dz 🡒 (Ezc 🡒 Ezx))
    (h₃ : T.internalize V ⊢ Hq 🡒 Dx 🡒 Ax 🡒 Dz 🡒 (Ezx 🡒 Ezc)) :
    T.internalize V ⊢ (Dc ⋏ Hq) 🡒 Dx 🡒 Ax 🡒 Dz 🡒 (Az 🡘 Ezx) := by
  have k₁ : T.internalize V ⊢ Hq 🡒 Dz 🡒 (Az 🡒 Ezc) := by
    cl_prover 128 [h₁]
  have k₂ : T.internalize V ⊢ Hq 🡒 Dz 🡒 (Ezc 🡒 Az) := by
    cl_prover 128 [h₁]
  have g₁ : T.internalize V ⊢ (Dc ⋏ Hq) 🡒 Dx 🡒 Ax 🡒 Dz 🡒 (Az 🡒 Ezx) := by
    cl_prover 128 [k₁, h₂]
  have g₂ : T.internalize V ⊢ (Dc ⋏ Hq) 🡒 Dx 🡒 Ax 🡒 Dz 🡒 (Ezx 🡒 Az) := by
    cl_prover 128 [k₂, h₃]
  cl_prover 128 [g₁, g₂]

lemma definesElement_inner (d A : Semiformula V L 1) [𝗘𝗤 L ⪯ T] (c x z : V) :
    T.internalize V ⊢
      (d ⋏ (∀¹ (d.subst ![Semiterm.bvar 0] 🡒
        (A.subst ![Semiterm.bvar 0] 🡘
              Semiformula.equal (Semiterm.bvar 0) (Semiterm.bvar 1))))).subst
          ![Semiterm.fvar c] 🡒
      d.subst ![Semiterm.fvar x] 🡒 A.subst ![Semiterm.fvar x] 🡒
        (d.subst ![Semiterm.fvar z] 🡒
          (A.subst ![Semiterm.fvar z] 🡘
            Semiformula.equal (Semiterm.fvar z) (Semiterm.fvar x))) := by
  have h₁ := TProof.all_imp_subst (T := T)
    (d.subst ![Semiterm.bvar 0] 🡒
      (A.subst ![Semiterm.bvar 0] 🡘 Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar c)))
    (Semiterm.fvar z)
  have h₂ := TProof.all_imp_subst (T := T)
    (d.subst ![Semiterm.bvar 0] 🡒
      (A.subst ![Semiterm.bvar 0] 🡘 Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar c)))
    (Semiterm.fvar x)
  have h₃ : T.internalize V ⊢ Semiformula.equal (Semiterm.fvar x) (Semiterm.fvar c) 🡒
      Semiformula.equal (Semiterm.fvar c) (Semiterm.fvar x) :=
    tprovable_equal_symm_imp (S := T) (Semiterm.fvar x) (Semiterm.fvar c)
  have h₄ : T.internalize V ⊢ Semiformula.equal (Semiterm.fvar z) (Semiterm.fvar c) ⋏
      Semiformula.equal (Semiterm.fvar c) (Semiterm.fvar x) 🡒
        Semiformula.equal (Semiterm.fvar z) (Semiterm.fvar x) :=
    tprovable_equal_trans_imp (S := T) (Semiterm.fvar z) (Semiterm.fvar c) (Semiterm.fvar x)
  have h₅ : T.internalize V ⊢ Semiformula.equal (Semiterm.fvar z) (Semiterm.fvar x) ⋏
      Semiformula.equal (Semiterm.fvar x) (Semiterm.fvar c) 🡒
        Semiformula.equal (Semiterm.fvar z) (Semiterm.fvar c) :=
    tprovable_equal_trans_imp (S := T) (Semiterm.fvar z) (Semiterm.fvar x) (Semiterm.fvar c)
  have v₁ : ∀ c : V, SemitermVec.q ![(Semiterm.fvar c : Semiterm V L 0)] 1 =
      Semiterm.fvar c := by
    intro c
    rw [show (1 : Fin 2) = Fin.succ 0 from rfl, SemitermVec.q_succ]
    simp
  have w₁ : ∀ z : V, ((Semiterm.subst ![(Semiterm.fvar z : Semiterm V L 0)])⨟
      ![(Semiterm.bvar 0 : Semiterm V L 1)]) = ![Semiterm.fvar z] := by
    intro z
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp
  have w₂ : ∀ c : V, ((Semiterm.subst (SemitermVec.q ![(Semiterm.fvar c : Semiterm V L 0)]))⨟
      ![(Semiterm.bvar 0 : Semiterm V L 2)]) = ![(Semiterm.bvar 0 : Semiterm V L 1)] := by
    intro c
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp
  simp only [Semiformula.substs_and, Semiformula.substs_all, Semiformula.substs_imp,
    Semiformula.substs_imply, Semiformula.substs_substs, Semiformula.substs_equal,
    Semiterm.substs_bvar, Semiterm.substs_fvar, SemitermVec.q_zero, Matrix.cons_val_zero,
    v₁, w₁, w₂, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue] at h₁ h₂ ⊢
  have h₁' : T.internalize V ⊢ (∀¹ (d.subst ![Semiterm.bvar 0] 🡒 (A.subst ![Semiterm.bvar 0] 🡘
        Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar c)))) 🡒
      (d.subst ![Semiterm.fvar z] 🡒
        (A.subst ![Semiterm.fvar z] 🡘 Semiformula.equal (Semiterm.fvar z) (Semiterm.fvar c))) :=
    h₁
  have h₂' : T.internalize V ⊢ (∀¹ (d.subst ![Semiterm.bvar 0] 🡒 (A.subst ![Semiterm.bvar 0] 🡘
        Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar c)))) 🡒
      (d.subst ![Semiterm.fvar x] 🡒
        (A.subst ![Semiterm.fvar x] 🡘 Semiformula.equal (Semiterm.fvar x) (Semiterm.fvar c))) :=
    h₂
  have kB : T.internalize V ⊢ (∀¹ (d.subst ![Semiterm.bvar 0] 🡒 (A.subst ![Semiterm.bvar 0] 🡘
        Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar c)))) 🡒
      d.subst ![Semiterm.fvar x] 🡒 A.subst ![Semiterm.fvar x] 🡒
        Semiformula.equal (Semiterm.fvar c) (Semiterm.fvar x) := by
    cl_prover [h₂', h₃]
  have kB₂ : T.internalize V ⊢ (∀¹ (d.subst ![Semiterm.bvar 0] 🡒 (A.subst ![Semiterm.bvar 0] 🡘
        Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar c)))) 🡒
      d.subst ![Semiterm.fvar x] 🡒 A.subst ![Semiterm.fvar x] 🡒
        Semiformula.equal (Semiterm.fvar x) (Semiterm.fvar c) := by
    cl_prover [h₂']
  have kH : T.internalize V ⊢ (∀¹ (d.subst ![Semiterm.bvar 0] 🡒 (A.subst ![Semiterm.bvar 0] 🡘
        Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar c)))) 🡒
      d.subst ![Semiterm.fvar z] 🡒 (A.subst ![Semiterm.fvar z] 🡘
            Semiformula.equal (Semiterm.fvar z) (Semiterm.fvar c)) := by
    cl_prover [h₁']
  have m₁ : T.internalize V ⊢ (∀¹ (d.subst ![Semiterm.bvar 0] 🡒 (A.subst ![Semiterm.bvar 0] 🡘
        Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar c)))) 🡒
      d.subst ![Semiterm.fvar x] 🡒 A.subst ![Semiterm.fvar x] 🡒 d.subst ![Semiterm.fvar z] 🡒
        (Semiformula.equal (Semiterm.fvar z) (Semiterm.fvar c) 🡒
              Semiformula.equal (Semiterm.fvar z) (Semiterm.fvar x)) := by
    cl_prover [h₄, kB]
  have m₂ : T.internalize V ⊢ (∀¹ (d.subst ![Semiterm.bvar 0] 🡒 (A.subst ![Semiterm.bvar 0] 🡘
        Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar c)))) 🡒
      d.subst ![Semiterm.fvar x] 🡒 A.subst ![Semiterm.fvar x] 🡒 d.subst ![Semiterm.fvar z] 🡒
        (Semiformula.equal (Semiterm.fvar z) (Semiterm.fvar x) 🡒
              Semiformula.equal (Semiterm.fvar z) (Semiterm.fvar c)) := by
    cl_prover [h₅, kB₂]
  exact prop_combine kH m₁ m₂

lemma definesElement_imp_theta (d A : Semiformula V L 1) [𝗘𝗤 L ⪯ T] (c x : V) :
    T.internalize V ⊢
      (d ⋏ (∀¹ (d.subst ![Semiterm.bvar 0] 🡒
        (A.subst ![Semiterm.bvar 0] 🡘
              Semiformula.equal (Semiterm.bvar 0) (Semiterm.bvar 1))))).subst
          ![Semiterm.fvar c] 🡒
      d.subst ![Semiterm.fvar x] 🡒 A.subst ![Semiterm.fvar x] 🡒
        (∀¹ (d 🡒 (A 🡘 Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar x)))) := by
  have key : T.internalize V ⊢
      ((d ⋏ (∀¹ (d.subst ![Semiterm.bvar 0] 🡒
        (A.subst ![Semiterm.bvar 0] 🡘
              Semiformula.equal (Semiterm.bvar 0) (Semiterm.bvar 1))))).subst
          ![Semiterm.fvar c] ⋏
        d.subst ![Semiterm.fvar x] ⋏ A.subst ![Semiterm.fvar x]) 🡒
        (∀¹ (d 🡒 (A 🡘 Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar x)))) := by
    refine TProof.allItr_generalize_imp (k := 1) ?_
    have h₁ := definesElement_inner (T := T) d.shift A.shift (c + 1) (x + 1) 0
    simp only [Function.iterate_one, Semiformula.shift_and, Semiformula.shift_imp,
      Semiformula.shift_iff, Semiformula.shift_substs, Semiformula.shift_all,
      shift_vec_fvar, shift_vec_bvar, q_fvar_one, fvar_vec_fin_one,
      shift_equal_eq, Semiterm.shift_bvar,
      Semiterm.shift_fvar, Semiformula.substs_and, Semiformula.substs_imp, Semiformula.substs_imply,
      Semiformula.substs_all, Semiformula.substs_equal, Semiterm.substs_bvar, Semiterm.substs_fvar,
      SemitermVec.q_zero, Matrix.cons_val_zero] at h₁ ⊢
    rw [shift_vec_q_fvar]
    cl_prover 128 [h₁]
  cl_prover [key]

theorem definesElement_iff_equal (d A : Semiformula V L 1) (b : V) [𝗘𝗤 L ⪯ T] :
    T.internalize V ⊢ definesElement d A 🡒 d.subst ![Semiterm.fvar b] 🡒
      A.subst ![Semiterm.fvar b] 🡒
      ∀¹ (d 🡒 (A 🡘 Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar b))) := by
  have hi := definesElement_imp_theta (T := T) d.shift A.shift 0 (b + 1)
  have h₁ : T.internalize V ⊢
      (d ⋏ (∀¹ (d.subst ![Semiterm.bvar 0] 🡒
        (A.subst ![Semiterm.bvar 0] 🡘 Semiformula.equal (Semiterm.bvar 0) (Semiterm.bvar 1))))).free
        🡒 (d.subst ![Semiterm.fvar b] 🡒 A.subst ![Semiterm.fvar b] 🡒
          ∀¹ (d 🡒 (A 🡘 Semiformula.equal (Semiterm.bvar 0) (Semiterm.fvar b)))).shift := by
    simp only [Semiformula.free, Semiformula.shift_and, Semiformula.shift_all,
      Semiformula.shift_imp, Semiformula.shift_iff, Semiformula.shift_substs,
      shift_vec_fvar, shift_vec_bvar, shift_equal_eq, Semiterm.shift_bvar, Semiterm.shift_fvar,
      Semiformula.substs_and, Semiformula.substs_imp, Semiformula.substs_imply,
      Semiformula.substs_all, Semiformula.substs_equal, Semiterm.substs_bvar,
      SemitermVec.q_zero] at hi ⊢
    exact hi
  have h₂ := TProof.exs_imp_of_free (T := T) h₁
  unfold definesElement
  exact h₂

end definesElement

end FFL.FirstOrder.Arithmetic.Bootstrapping
