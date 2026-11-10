module

public import AlphaCentauri.Bootstrapping.Interpretability.Soundness

/-!
# Relativized blocks of quantifiers

Blocks of universal quantifiers relativized to a domain `d`: their specialisation, their
generalisation over fresh free variables under a hypothesis, and the equivalence of a block of
implications with a block over a conjunction under hypotheses on the domain.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic
namespace Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

open _root_.FFL.Entailment


section relAllItr

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- `∀ x₁ (d(x₁) → ∀ x₂ (d(x₂) → … φ))`, the block of `k` universal quantifiers relativized to
`d`. -/
noncomputable def relAllItr {n : ℕ} (d : Semiformula V L 1) :
    (k : ℕ) → Semiformula V L (n + k) → Semiformula V L n
  | 0, φ => φ
  | k + 1, φ => relAllItr d k (∀¹ (d.subst ![Semiterm.bvar 0] 🡒 φ))

@[simp] lemma relAllItr_zero {n : ℕ} (d : Semiformula V L 1) (φ : Semiformula V L (n + 0)) :
    relAllItr d 0 φ = φ := rfl

lemma relAllItr_succ {n k : ℕ} (d : Semiformula V L 1) (φ : Semiformula V L (n + (k + 1))) :
    relAllItr d (k + 1) φ = relAllItr d k (∀¹ (d.subst ![Semiterm.bvar 0] 🡒 φ)) := rfl

/-- `∀ x₁ (d(x₁) → ∀ x₂ (d(x₂) → … φ))`, the block of universal quantifiers relativized to `d`
closing all the bound variables of `φ`. -/
noncomputable def relAlls (d : Semiformula V L 1) : {n : ℕ} → Semiformula V L n → Formula V L
  | 0, φ => φ
  | _ + 1, φ => relAlls d (∀¹ (d.subst ![Semiterm.bvar 0] 🡒 φ))

end relAllItr

/-! ## Relativized blocks of quantifiers -/

section relAllItrProof

variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

lemma shift_iterate_relAllItr {n : ℕ} {d : Semiformula V L 1} (hd : d.shift = d) (j : ℕ) :
    ∀ (k : ℕ) (φ : Semiformula V L (n + k)),
      Semiformula.shift^[j] (relAllItr d k φ) = relAllItr d k (Semiformula.shift^[j] φ)
  | 0, φ => rfl
  | k + 1, φ => by
    have hd' : Semiformula.shift^[j] d = d := Function.iterate_fixed hd j
    rw [relAllItr_succ, relAllItr_succ, shift_iterate_relAllItr hd j k]
    simp [Semiformula.shift_iterate_subst, hd']

/-- Specialisation of a relativized block of `k` universal quantifiers. -/
lemma relAllItr_specialize (d : Semiformula V L 1) :
    ∀ {k : ℕ} (φ : Semiformula V L (0 + k)) (w : SemitermVec V L (0 + k) 0),
      T.internalize V ⊢ relAllItr d k φ 🡒 Matrix.conj (fun i ↦ d.subst ![w i]) 🡒 φ.subst w
  | 0, φ, w => by
    rw [Semiformula.subst_nil_eq_self]
    simp only [relAllItr_zero]
    cl_prover
  | k + 1, φ, w => by
    have h₁ := relAllItr_specialize d (∀¹ (d.subst ![Semiterm.bvar 0] 🡒 φ)) (Matrix.vecTail w)
    rw [Semiformula.substs_all] at h₁
    have h₂ := TProof.all_imp_subst (T := T)
      ((d.subst ![Semiterm.bvar 0] 🡒 φ).subst (SemitermVec.q (Matrix.vecTail w))) (w 0)
    rw [Semiformula.substs_q_substs_single,
      show (w 0 :> Matrix.vecTail w) = w from Matrix.cons_head_tail w] at h₂
    simp only [Semiformula.substs_imp, Semiformula.substs_substs, Matrix.vecMap_cons',
      Matrix.head_cons, Matrix.vecMap_nil, Semiterm.substs_bvar] at h₁ h₂
    rw [relAllItr_succ]
    simp only [Matrix.conj]
    cl_prover [h₁, h₂]

/-- Specialisation of a relativized block of universal quantifiers. -/
lemma relAlls_specialize (d : Semiformula V L 1) :
    ∀ {n : ℕ} (φ : Semiformula V L n) (w : SemitermVec V L n 0),
      T.internalize V ⊢ relAlls d φ 🡒 Matrix.conj (fun i ↦ d.subst ![w i]) 🡒 φ.subst w
  | 0, φ, w => by
    rw [Semiformula.subst_nil_eq_self]
    simp only [relAlls]
    cl_prover
  | n + 1, φ, w => by
    have h₁ := relAlls_specialize d (∀¹ (d.subst ![Semiterm.bvar 0] 🡒 φ)) (Matrix.vecTail w)
    rw [Semiformula.substs_all] at h₁
    have h₂ := TProof.all_imp_subst (T := T)
      ((d.subst ![Semiterm.bvar 0] 🡒 φ).subst (SemitermVec.q (Matrix.vecTail w))) (w 0)
    rw [Semiformula.substs_q_substs_single,
      show (w 0 :> Matrix.vecTail w) = w from Matrix.cons_head_tail w] at h₂
    simp only [Semiformula.substs_imp, Semiformula.substs_substs, Matrix.vecMap_cons',
      Matrix.head_cons, Matrix.vecMap_nil, Semiterm.substs_bvar] at h₁ h₂
    simp only [relAlls, Matrix.conj]
    cl_prover [h₁, h₂]

omit [T.Δ₁] in
lemma free_subst_q_fvar' {k : ℕ} (ψ : Semiformula V L (k + 1)) :
    (ψ.subst (SemitermVec.q fun i : Fin k ↦ Semiterm.fvar (i : V))).free =
      ψ.shift.subst fun i ↦ Semiterm.fvar (i : V) := by
  rw [Semiformula.free, Semiformula.shift_substs, Semiformula.substs_substs]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp

/-- Generalisation of a relativized block of `k` universal quantifiers over `k` fresh free
variables under a hypothesis. -/
lemma relAllItr_generalize_imp {d : Semiformula V L 1} (hd : d.shift = d) :
    ∀ {k : ℕ} {C : Formula V L} {φ : Semiformula V L (0 + k)},
      T.internalize V ⊢ Semiformula.shift^[k] C 🡒
        Matrix.conj (fun i : Fin (0 + k) ↦ d.subst ![Semiterm.fvar ((i : ℕ) : V)]) 🡒
          (Semiformula.shift^[k] φ).subst (fun i ↦ Semiterm.fvar ((i : ℕ) : V)) →
      T.internalize V ⊢ C 🡒 relAllItr d k φ
  | 0, C, φ, h => by
    rw [Semiformula.subst_nil_eq_self] at h
    simp only [Function.iterate_zero, id_eq, relAllItr_zero, Matrix.conj] at h ⊢
    cl_prover [h]
  | k + 1, C, φ, h => by
    rw [relAllItr_succ]
    apply relAllItr_generalize_imp hd
    rw [Semiformula.shift_iterate_all, Semiformula.substs_all]
    apply CC_of_CK
    apply TProof.generalize_imp
    rw [free_subst_q_fvar' (k := 0 + k), ← Function.iterate_succ_apply' Semiformula.shift]
    simp only [Semiformula.shift_and, Semiformula.shift_conj, Semiformula.shift_substs, hd,
      Semiformula.shift_iterate_imp, Semiformula.substs_imp, Semiformula.shift_iterate_subst,
      Function.iterate_fixed hd, Semiformula.substs_substs, Matrix.vecMap_cons', Matrix.vecMap_nil,
      Semiterm.shift_fvar, Semiterm.shift_iterate_bvar, Matrix.head_cons, Semiterm.substs_bvar,
      ← Function.iterate_succ_apply' Semiformula.shift] at h ⊢
    simp only [Matrix.conj] at h
    simp only [Nat.succ_eq_add_one, Function.iterate_succ, Function.comp_apply, Nat.reduceAdd,
      Fin.coe_ofNat_eq_mod, zero_add, Nat.zero_mod, Nat.cast_zero] at h ⊢
    cl_prover [h]

omit [T.Δ₁] in
lemma conj_fin_zero_add {α : Type*} [Top α] [Wedge α] (k : ℕ) (f : ℕ → α) :
    Matrix.conj (fun i : Fin (0 + k) ↦ f i) = Matrix.conj (fun i : Fin k ↦ f i) := by
  have : ∀ m (_ : m = k),
      Matrix.conj (fun i : Fin m ↦ f i) = Matrix.conj (fun i : Fin k ↦ f i) := by
    rintro m rfl; rfl
  exact this _ (zero_add k)

/-- Under hypotheses that `B i` and `C i` agree on `d`, the block `relativizedImp (d ⋏ e) B G` is
equivalent to the block of quantifiers relativized to `d` over `⋀ᵢ (e(wᵢ) ∧ Cᵢ(wᵢ)) → G`. -/
lemma relativizedImp_iff_relAllItr {k : ℕ} {d : Semiformula V L 1} (hd : d.shift = d)
    (e : Semiformula V L 1) (B C : Fin k → Semiformula V L 1) (G : Semiformula V L (0 + k)) :
    T.internalize V ⊢ Matrix.conj (fun i ↦ ∀¹ (d 🡒 (B i 🡘 C i))) 🡒
      (relativizedImp (d ⋏ e) B G 🡘 relAllItr d k (Matrix.conj (fun i : Fin k ↦
        e.subst ![Semiterm.bvar (i.addCast 0)] ⋏ (C i).subst ![Semiterm.bvar (i.addCast 0)]) 🡒
          G)) := by
  have hdk : Semiformula.shift^[k] d = d := Function.iterate_fixed hd k
  have hH (i : Fin k) : T.internalize V ⊢
      Semiformula.shift^[k] (Matrix.conj fun i ↦ ∀¹ (d 🡒 (B i 🡘 C i))) 🡒
        d.subst ![Semiterm.fvar ((i : ℕ) : V)] 🡒
          ((Semiformula.shift^[k] (B i)).subst ![Semiterm.fvar ((i : ℕ) : V)] 🡘
            (Semiformula.shift^[k] (C i)).subst ![Semiterm.fvar ((i : ℕ) : V)]) := by
    rw [Semiformula.shift_iterate_conj]
    have h₁ := matrixConj_elim (𝓢 := T.internalize V)
      (fun i ↦ Semiformula.shift^[k] (∀¹ (d 🡒 (B i 🡘 C i)))) i
    have h₂ := TProof.all_imp_subst (T := T) (Semiformula.shift^[k] (d 🡒 (B i 🡘 C i)))
      (Semiterm.fvar ((i : ℕ) : V))
    simp only [Semiformula.shift_iterate_all, Semiformula.shift_iterate_imp,
      Semiformula.shift_iterate_iff, hdk] at h₁ h₂ ⊢
    simp only [LogicalConnective.iff, Semiformula.substs_imp, Semiformula.substs_and] at h₁ h₂ ⊢
    exact C_trans h₁ h₂
  have h₁ : T.internalize V ⊢ Matrix.conj (fun i ↦ ∀¹ (d 🡒 (B i 🡘 C i))) ⋏
      relativizedImp (d ⋏ e) B G 🡒 relAllItr d k (Matrix.conj (fun i : Fin k ↦
        e.subst ![Semiterm.bvar (i.addCast 0)] ⋏ (C i).subst ![Semiterm.bvar (i.addCast 0)]) 🡒
          G) := by
    apply relAllItr_generalize_imp (k := k) hd
    have hs := TProof.allItr_specialize (T := T) (Semiformula.shift^[k]
      (Matrix.conj (fun i : Fin k ↦ (d ⋏ e).subst ![Semiterm.bvar (i.addCast 0)] ⋏
        (B i).subst ![Semiterm.bvar (i.addCast 0)]) 🡒 G))
      (fun i ↦ Semiterm.fvar ((i : ℕ) : V))
    simp only [relativizedImp, Semiformula.shift_iterate_and, Semiformula.shift_iterate_allItr,
      Semiformula.shift_iterate_imp, Semiformula.substs_imp, Semiformula.shift_iterate_conj,
      Semiformula.substs_conj, Semiformula.substs_and, Semiformula.subst_shift_iterate_subst_bvar,
      Fin.addCast_val, hdk] at hs ⊢
    simp only [conj_fin_zero_add k (fun j ↦ d.subst ![Semiterm.fvar (j : V)])] at hs ⊢
    have hZ : T.internalize V ⊢ (Matrix.conj fun i ↦ Semiformula.shift^[k] (∀¹ (d 🡒 (B i 🡘 C i)))) ⋏
        (Matrix.conj fun i : Fin k ↦ d.subst ![Semiterm.fvar ((i : ℕ) : V)]) ⋏
        (Matrix.conj fun i : Fin k ↦
          (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
          (Semiformula.shift^[k] (C i)).subst ![Semiterm.fvar ((i : ℕ) : V)]) 🡒
        Matrix.conj fun i : Fin k ↦ (d.subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
          (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)]) ⋏
          (Semiformula.shift^[k] (B i)).subst ![Semiterm.fvar ((i : ℕ) : V)] :=
      matrixConj_intro fun i ↦ by
        have a := matrixConj_elim (𝓢 := T.internalize V)
          (fun i : Fin k ↦ d.subst ![Semiterm.fvar ((i : ℕ) : V)]) i
        have b := matrixConj_elim (𝓢 := T.internalize V)
          (fun i : Fin k ↦ (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
            (Semiformula.shift^[k] (C i)).subst ![Semiterm.fvar ((i : ℕ) : V)]) i
        have c := hH i
        rw [Semiformula.shift_iterate_conj] at c
        cl_prover [a, b, c]
    cl_prover [hs, hZ]
  have h₂ : T.internalize V ⊢ Matrix.conj (fun i ↦ ∀¹ (d 🡒 (B i 🡘 C i))) ⋏
      relAllItr d k (Matrix.conj (fun i : Fin k ↦
        e.subst ![Semiterm.bvar (i.addCast 0)] ⋏ (C i).subst ![Semiterm.bvar (i.addCast 0)]) 🡒
          G) 🡒 relativizedImp (d ⋏ e) B G := by
    unfold relativizedImp
    apply TProof.allItr_generalize_imp
    have hs := relAllItr_specialize (T := T) d (Semiformula.shift^[k]
      (Matrix.conj (fun i : Fin k ↦ e.subst ![Semiterm.bvar (i.addCast 0)] ⋏
        (C i).subst ![Semiterm.bvar (i.addCast 0)]) 🡒 G))
      (fun i ↦ Semiterm.fvar ((i : ℕ) : V))
    simp only [Semiformula.shift_iterate_and, shift_iterate_relAllItr hd,
      Semiformula.shift_iterate_imp, Semiformula.substs_imp, Semiformula.shift_iterate_conj,
      Semiformula.substs_conj, Semiformula.substs_and, Semiformula.subst_shift_iterate_subst_bvar,
      Fin.addCast_val, hdk] at hs ⊢
    simp only [conj_fin_zero_add k (fun j ↦ d.subst ![Semiterm.fvar (j : V)])] at hs ⊢
    have hXY : T.internalize V ⊢
        (Matrix.conj fun i ↦ Semiformula.shift^[k] (∀¹ (d 🡒 (B i 🡘 C i)))) ⋏
        (Matrix.conj fun i : Fin k ↦ (d.subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
          (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)]) ⋏
          (Semiformula.shift^[k] (B i)).subst ![Semiterm.fvar ((i : ℕ) : V)]) 🡒
        (Matrix.conj fun i : Fin k ↦ d.subst ![Semiterm.fvar ((i : ℕ) : V)]) ⋏
        (Matrix.conj fun i : Fin k ↦
          (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
          (Semiformula.shift^[k] (C i)).subst ![Semiterm.fvar ((i : ℕ) : V)]) := by
      have a := matrixConj_intro (𝓢 := T.internalize V)
        (φ := (Matrix.conj fun i ↦ Semiformula.shift^[k] (∀¹ (d 🡒 (B i 🡘 C i)))) ⋏
          (Matrix.conj fun i : Fin k ↦ (d.subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
            (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)]) ⋏
            (Semiformula.shift^[k] (B i)).subst ![Semiterm.fvar ((i : ℕ) : V)]))
        (v := fun i : Fin k ↦ d.subst ![Semiterm.fvar ((i : ℕ) : V)]) fun i ↦ by
          have b := matrixConj_elim (𝓢 := T.internalize V)
            (fun i : Fin k ↦ (d.subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
              (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)]) ⋏
              (Semiformula.shift^[k] (B i)).subst ![Semiterm.fvar ((i : ℕ) : V)]) i
          cl_prover [b]
      have b := matrixConj_intro (𝓢 := T.internalize V)
        (φ := (Matrix.conj fun i ↦ Semiformula.shift^[k] (∀¹ (d 🡒 (B i 🡘 C i)))) ⋏
          (Matrix.conj fun i : Fin k ↦ (d.subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
            (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)]) ⋏
            (Semiformula.shift^[k] (B i)).subst ![Semiterm.fvar ((i : ℕ) : V)]))
        (v := fun i : Fin k ↦ (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
          (Semiformula.shift^[k] (C i)).subst ![Semiterm.fvar ((i : ℕ) : V)]) fun i ↦ by
          have b := matrixConj_elim (𝓢 := T.internalize V)
            (fun i : Fin k ↦ (d.subst ![Semiterm.fvar ((i : ℕ) : V)] ⋏
              (Semiformula.shift^[k] e).subst ![Semiterm.fvar ((i : ℕ) : V)]) ⋏
              (Semiformula.shift^[k] (B i)).subst ![Semiterm.fvar ((i : ℕ) : V)]) i
          have c := hH i
          rw [Semiformula.shift_iterate_conj] at c
          cl_prover [b, c]
      cl_prover [a, b]
    cl_prover [hs, hXY]
  cl_prover [h₁, h₂]

end relAllItrProof

end Bootstrapping
end FFL.FirstOrder.Arithmetic
