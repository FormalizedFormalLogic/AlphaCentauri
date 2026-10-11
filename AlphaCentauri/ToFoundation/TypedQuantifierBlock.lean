module

public import AlphaCentauri.ToFoundation.TypedBridge
public import AlphaCentauri.ToFoundation.Entailment
public import AlphaCentauri.ToFoundation.InternalEquality
public import Foundation.Meta.ClProver

/-!
# Blocks of universal quantifiers in the typed internal calculus

Specialisation and generalisation of `∀¹^[k]` in the typed internal proof system.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

section shiftIterate

variable {n k : ℕ}

@[simp] lemma Semiterm.shift_iterate_bvar (z : Fin n) :
    Semiterm.shift^[k] (Semiterm.bvar z : Semiterm V L n) = Semiterm.bvar z := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', ih]

@[simp] lemma Semiterm.shift_iterate_fvar (x : V) :
    Semiterm.shift^[k] (Semiterm.fvar x : Semiterm V L n) = Semiterm.fvar (x + k) := by
  induction k with
  | zero => simp
  | succ k ih => simp [Function.iterate_succ_apply', ih, add_assoc]

namespace Semiformula

@[simp] lemma shift_iterate_verum : shift^[k] (⊤ : Semiformula V L n) = ⊤ := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', ih]

@[simp] lemma shift_iterate_and (φ ψ : Semiformula V L n) :
    shift^[k] (φ ⋏ ψ) = shift^[k] φ ⋏ shift^[k] ψ := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', ih]

@[simp] lemma shift_iterate_neg (φ : Semiformula V L n) : shift^[k] (∼φ) = ∼shift^[k] φ := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', ih]

@[simp] lemma shift_iterate_imp (φ ψ : Semiformula V L n) :
    shift^[k] (φ 🡒 ψ) = shift^[k] φ 🡒 shift^[k] ψ := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', ih]

@[simp] lemma shift_iterate_iff (φ ψ : Semiformula V L n) :
    shift^[k] (φ 🡘 ψ) = shift^[k] φ 🡘 shift^[k] ψ := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', ih]

@[simp] lemma shift_iterate_all (φ : Semiformula V L (n + 1)) :
    shift^[k] (∀¹ φ) = ∀¹ shift^[k] φ := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', ih]

@[simp] lemma shift_iterate_exs (φ : Semiformula V L (n + 1)) :
    shift^[k] (∃¹ φ) = ∃¹ shift^[k] φ := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', ih]

@[simp] lemma shift_iterate_conj {m : ℕ} (v : Fin m → Semiformula V L n) :
    shift^[k] (Matrix.conj v) = Matrix.conj fun i ↦ shift^[k] (v i) := by
  induction m with
  | zero => simp
  | succ m ih => simp [Matrix.conj, ih]; rfl

@[simp] lemma shift_iterate_allItr {m : ℕ} (φ : Semiformula V L (n + m)) :
    shift^[k] (∀¹^[m] φ) = ∀¹^[m] shift^[k] φ := by
  induction m with
  | zero => rfl
  | succ m ih => simp [allItr_succ, ih (∀¹ φ)]

lemma shift_iterate_subst {m : ℕ} (w : SemitermVec V L n m) (φ : Semiformula V L n) :
    shift^[k] (φ.subst w) = (shift^[k] φ).subst fun i ↦ Semiterm.shift^[k] (w i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply', ih, shift_substs]
    rfl

end Semiformula

end shiftIterate

section allItr

open _root_.FFL.Entailment

variable {T : Theory L} [T.Δ₁]

lemma TProof.all_imp_subst (φ : Semiformula V L 1) (t : Term V L) :
    T.internalize V ⊢ ∀¹ φ 🡒 φ.subst ![t] := ⟨by
  rw [Semiformula.imp_def, Semiformula.neg_all]
  apply TDerivation.or
  apply TDerivation.exs t
  simpa using TDerivation.em (φ.subst ![t])⟩

lemma TProof.subst_imp_exs (φ : Semiformula V L 1) (t : Term V L) :
    T.internalize V ⊢ φ.subst ![t] 🡒 ∃¹ φ := ⟨by
  rw [Semiformula.imp_def]
  apply TDerivation.or
  apply TDerivation.rotate₁
  apply TDerivation.exs t
  exact TDerivation.em (φ.subst ![t])⟩

private lemma subst_q_subst {k : ℕ} (φ : Semiformula V L (k + 1)) (w : SemitermVec V L (k + 1) 0) :
    (φ.subst (SemitermVec.q (Matrix.vecTail w))).subst ![w 0] = φ.subst w := by
  rw [Semiformula.substs_substs]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp; rfl

/-- Specialisation of `k` universal quantifiers. -/
lemma TProof.allItr_specialize {k : ℕ} (φ : Semiformula V L (0 + k))
    (w : SemitermVec V L (0 + k) 0) : T.internalize V ⊢ (∀¹^[k] φ) 🡒 φ.subst w := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h₁ := ih (∀¹ φ) (Matrix.vecTail w)
    have h₂ := all_imp_subst (T := T) (φ.subst (SemitermVec.q (Matrix.vecTail w))) (w 0)
    rw [subst_q_subst (k := 0 + k)] at h₂
    rw [Semiformula.substs_all] at h₁
    exact C_trans h₁ h₂

private lemma free_subst_q_fvar {k : ℕ} (ψ : Semiformula V L (k + 1)) :
    (ψ.subst (SemitermVec.q fun i : Fin k ↦ Semiterm.fvar (i : V))).free =
      ψ.shift.subst fun i ↦ Semiterm.fvar (i : V) := by
  rw [Semiformula.free, Semiformula.shift_substs, Semiformula.substs_substs]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp

/-- Generalisation over `k` fresh free variables under a hypothesis. -/
lemma TProof.allItr_generalize_imp {k : ℕ} {C : Formula V L} {φ : Semiformula V L (0 + k)}
    (h : T.internalize V ⊢ Semiformula.shift^[k] C 🡒
      (Semiformula.shift^[k] φ).subst fun i ↦ Semiterm.fvar (i : V)) :
    T.internalize V ⊢ C 🡒 ∀¹^[k] φ := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih (φ := ∀¹ φ)
    rw [Semiformula.shift_iterate_all, Semiformula.substs_all]
    apply Nonempty.map TProof.generalizeAux
    rw [free_subst_q_fvar (k := 0 + k), ← Function.iterate_succ_apply' Semiformula.shift,
      ← Function.iterate_succ_apply' Semiformula.shift]
    exact h

lemma TProof.conj_shift_iterate (Γ : List (Formula V L)) (k : ℕ) :
    Semiformula.shift^[k] (⋀Γ) = ⋀(Γ.map Semiformula.shift^[k]) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, TProof.conj_shift, List.map_map,
      ← Function.iterate_succ']

/-- Generalisation over `k` fresh free variables, in a finite context. -/
lemma TProof.allItr_generalize {k : ℕ} {Γ : List (Formula V L)} {φ : Semiformula V L (0 + k)}
    (h : Γ.map (Semiformula.shift^[k]) ⊢[T.internalize V]
      (Semiformula.shift^[k] φ).subst fun i ↦ Semiterm.fvar (i : V)) :
    Γ ⊢[T.internalize V] ∀¹^[k] φ := by
  apply FiniteContext.provable_iff.mpr
  apply allItr_generalize_imp
  rw [conj_shift_iterate]
  exact FiniteContext.provable_iff.mp h

lemma TProof.shift_iterate! {φ : Formula V L} (h : T.internalize V ⊢ φ) (k : ℕ) :
    T.internalize V ⊢ Semiformula.shift^[k] φ := by
  induction k with
  | zero => exact h
  | succ k ih => simpa [Function.iterate_succ_apply'] using TProof.shift! ih

lemma Semiformula.subst_shift_iterate_subst_bvar {n k : ℕ} (χ : Semiformula V L 1) (j : Fin n)
    (w : SemitermVec V L n 0) :
    (Semiformula.shift^[k] (χ.subst ![Semiterm.bvar j])).subst w =
      (Semiformula.shift^[k] χ).subst ![w j] := by
  rw [Semiformula.shift_iterate_subst, Semiformula.substs_substs]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => exact i.elim0

lemma TProof.all_imp_all_of_free {φ ψ : Semiformula V L 1}
    (h : T.internalize V ⊢ φ.free 🡒 ψ.free) : T.internalize V ⊢ ∀¹ φ 🡒 ∀¹ ψ :=
  FiniteContext.emptyPrf <| TProof.all_imp_all! (Γ := []) <| FiniteContext.of h

end allItr

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

private lemma all_iff_imp_all_imp_imp_left (d A B : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (d 🡒 (A 🡘 B)) 🡒 ∀¹ (d 🡒 B 🡒 A) := by
  apply TProof.all_imp_all_of_free
  simp only [Semiformula.free, Semiformula.shift_imp, Semiformula.shift_iff,
    Semiformula.substs_imp, Semiformula.substs_imply]
  cl_prover

private lemma all_iff_imp_all_imp_imp_right (d A B : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (d 🡒 (A 🡘 B)) 🡒 ∀¹ (d 🡒 A 🡒 B) := by
  apply TProof.all_imp_all_of_free
  simp only [Semiformula.free, Semiformula.shift_imp, Semiformula.shift_iff,
    Semiformula.substs_imp, Semiformula.substs_imply]
  cl_prover

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

end FFL.FirstOrder.Arithmetic.Bootstrapping
