module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Equality
public import AlphaCentauri.ToFoundation.Logic.Entailment
public import AlphaCentauri.ToMathlib.Data.Vector.Basic
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Typed
public import Foundation.Meta.ClProver

/-!
# Blocks of universal quantifiers in the typed internal calculus

Term vectors of bound variables, and the typed internal derivations of blocks of universal
quantifiers.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Term vectors -/

section vecBvar

variable {L : Language} [L.Encodable] [L.LORDefinable] {n m k : ℕ}

@[simp high] lemma Semiterm.shift_vecMap_bvar (f : Fin k → Fin n) :
    (Semiterm.shift ⨟ fun i ↦ (Semiterm.bvar (f i) : Semiterm V L n)) =
      fun i ↦ Semiterm.bvar (f i) := by
  funext i; simp

@[simp high] lemma Semiterm.substs_vecMap_bvar (w : SemitermVec V L n m) (f : Fin k → Fin n) :
    ((Semiterm.subst w)⨟ fun i ↦ (Semiterm.bvar (f i) : Semiterm V L n)) = fun i ↦ w (f i) := by
  funext i; simp

@[simp high] lemma Semiterm.shift_vecMap_fvar (f : Fin k → V) :
    (Semiterm.shift ⨟ fun i ↦ (Semiterm.fvar (f i) : Semiterm V L n)) =
      fun i ↦ Semiterm.fvar (f i + 1) := by
  funext i; simp

@[simp high] lemma Semiterm.substs_vecMap_bvar_id (w : SemitermVec V L n m) :
    ((Semiterm.subst w)⨟ (Semiterm.bvar : Fin n → Semiterm V L n)) = w := by
  funext i; simp

@[simp high] lemma Semiterm.substs_vecMap_fvar (w : SemitermVec V L n m) (f : Fin k → V) :
    ((Semiterm.subst w)⨟ fun i ↦ (Semiterm.fvar (f i) : Semiterm V L n)) =
      fun i ↦ Semiterm.fvar (f i) := by
  funext i; simp

lemma SemitermVec.q_eq_cons (w : Fin k → Term V L) :
    SemitermVec.q w = (Semiterm.bvar 0 :> fun i ↦ (w i).bShift) := by
  funext j
  cases j using Fin.cases <;> simp [SemitermVec.q]

@[simp] lemma SemitermVec.q_one {m : ℕ} (w : SemitermVec V L 1 m) : w.q 1 = (w 0).bShift :=
  SemitermVec.q_succ w 0

lemma Semiterm.subst_nil_subst (t : Term V L) (w : SemitermVec V L n m) :
    (t.subst ![] : Semiterm V L n).subst w = t.subst ![] := by
  rw [Semiterm.substs_substs]
  congr 1
  funext i
  exact i.elim0

lemma Semiterm.shift_iterate_subst_nil (t : Term V L) (j : ℕ) :
    Semiterm.shift^[j] (t.subst ![] : Semiterm V L n) = (Semiterm.shift^[j] t).subst ![] := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, Semiterm.shift_substs]
    congr 1
    funext i
    exact i.elim0

end vecBvar

/-! ## Blocks of universal quantifiers -/

section quantifierBlock

open scoped FFL.FirstOrder.Arithmetic

variable {L : Language} [L.Encodable] [L.LORDefinable]

section shiftIterate

variable {n k : ℕ}

@[simp] lemma Semiterm.shift_iterate_bvar (z : Fin n) :
    Semiterm.shift^[k] (Semiterm.bvar z : Semiterm V L n) = Semiterm.bvar z :=
  Function.iterate_fixed (by simp) k

@[simp] lemma Semiterm.shift_iterate_fvar (x : V) :
    Semiterm.shift^[k] (Semiterm.fvar x : Semiterm V L n) = Semiterm.fvar (x + k) := by
  induction k with
  | zero => simp
  | succ k ih => simp [Function.iterate_succ_apply', ih, add_assoc]

@[simp high] lemma Semiterm.shift_iterate_vecMap_bvar (f : Fin k → Fin n) (a : ℕ) :
    (Semiterm.shift^[a] ⨟ fun i ↦ (Semiterm.bvar (f i) : Semiterm V L n)) =
      fun i ↦ Semiterm.bvar (f i) := by
  funext i; simp

@[simp high] lemma Semiterm.shift_iterate_vecMap_fvar (f : Fin k → V) (a : ℕ) :
    (Semiterm.shift^[a] ⨟ fun i ↦ (Semiterm.fvar (f i) : Semiterm V L n)) =
      fun i ↦ Semiterm.fvar (f i + a) := by
  funext i; simp

namespace Semiformula

@[simp] lemma shift_iterate_verum : shift^[k] (⊤ : Semiformula V L n) = ⊤ :=
  Function.iterate_fixed shift_verum k

@[simp] lemma shift_iterate_and (φ ψ : Semiformula V L n) :
    shift^[k] (φ ⋏ ψ) = shift^[k] φ ⋏ shift^[k] ψ :=
  Function.Semiconj₂.iterate (op := (· ⋏ ·)) shift_and k φ ψ

@[simp] lemma shift_iterate_imp (φ ψ : Semiformula V L n) :
    shift^[k] (φ 🡒 ψ) = shift^[k] φ 🡒 shift^[k] ψ :=
  Function.Semiconj₂.iterate (op := (· 🡒 ·)) shift_imp k φ ψ

@[simp] lemma shift_iterate_iff (φ ψ : Semiformula V L n) :
    shift^[k] (φ 🡘 ψ) = shift^[k] φ 🡘 shift^[k] ψ :=
  Function.Semiconj₂.iterate (op := (· 🡘 ·)) shift_iff k φ ψ

@[simp] lemma shift_iterate_all (φ : Semiformula V L (n + 1)) :
    shift^[k] (∀¹ φ) = ∀¹ shift^[k] φ :=
  ((Function.Semiconj.iterate_right (f := (∀¹ ·)) (fun φ ↦ (shift_all φ).symm) k) φ).symm

@[simp] lemma shift_conj {m : ℕ} (v : Fin m → Semiformula V L n) :
    (Matrix.conj v).shift = Matrix.conj fun i ↦ (v i).shift :=
  Matrix.conj_map shift shift_verum shift_and v

@[simp] lemma shift_iterate_conj {m : ℕ} (v : Fin m → Semiformula V L n) :
    shift^[k] (Matrix.conj v) = Matrix.conj fun i ↦ shift^[k] (v i) :=
  Matrix.conj_map shift^[k] shift_iterate_verum shift_iterate_and v

@[simp] lemma shift_iterate_allItr {m : ℕ} (φ : Semiformula V L (n + m)) :
    shift^[k] (∀¹^[m] φ) = ∀¹^[m] shift^[k] φ := by
  induction m with
  | zero => rfl
  | succ m ih => simp [allItr_succ, ih (∀¹ φ)]

@[simp] lemma shift_allItr {m : ℕ} (φ : Semiformula V L (n + m)) :
    (∀¹^[m] φ).shift = ∀¹^[m] φ.shift := by
  simpa using shift_iterate_allItr (k := 1) φ

attribute [local simp] shift_substs in
@[simp] lemma shift_iterate_subst {m : ℕ} (w : SemitermVec V L n m) (φ : Semiformula V L n) :
    shift^[k] (φ.subst w) = (shift^[k] φ).subst (Semiterm.shift^[k] ⨟ w) := by
  induction k generalizing φ w with
  | zero => rfl
  | succ k ih => simp [ih, Matrix.vecMap_vecMap_comp]

end Semiformula

end shiftIterate

namespace Semiformula

@[simp] lemma free_and (φ ψ : Semiformula V L 1) : (φ ⋏ ψ).free = φ.free ⋏ ψ.free := by
  simp [free]

@[simp] lemma free_neg (φ : Semiformula V L 1) : (∼φ).free = ∼φ.free := by simp [free]

@[simp] lemma free_imp (φ ψ : Semiformula V L 1) : (φ 🡒 ψ).free = φ.free 🡒 ψ.free := by
  simp [free]

@[simp] lemma free_iff (φ ψ : Semiformula V L 1) : (φ 🡘 ψ).free = φ.free 🡘 ψ.free := by
  simp [free]

end Semiformula

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

/-- Specialisation of `k` universal quantifiers. -/
lemma TProof.allItr_specialize {k : ℕ} (φ : Semiformula V L (0 + k))
    (w : SemitermVec V L (0 + k) 0) : T.internalize V ⊢ (∀¹^[k] φ) 🡒 φ.subst w := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h₁ := ih (∀¹ φ) (Matrix.vecTail w)
    have h₂ := all_imp_subst (T := T) (φ.subst (SemitermVec.q (Matrix.vecTail w))) (w 0)
    rw [Semiformula.substs_q_substs_single,
      show (w 0 :> Matrix.vecTail w) = w from Matrix.cons_head_tail w] at h₂
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

lemma TProof.generalize_imp {C : Formula V L} {φ : Semiformula V L 1}
    (h : T.internalize V ⊢ C.shift 🡒 φ.free) : T.internalize V ⊢ C 🡒 ∀¹ φ :=
  Nonempty.map TProof.generalizeAux h

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

lemma tprovable_all_imp_all (d φ : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ φ 🡒 ∀¹ (d 🡒 φ) :=
  TProof.all_imp_all_of_free <| by simp only [Semiformula.free_imp]; cl_prover

lemma tprovable_all_imp_imp_all (E F : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (E 🡒 F) 🡒 ∀¹ E 🡒 ∀¹ F := by
  have h₂ := TProof.all_imp_subst (T := T) (E.shift 🡒 F.shift) (Semiterm.fvar 0)
  have h₃ := TProof.all_imp_subst (T := T) E.shift (Semiterm.fvar 0)
  simp only [Semiformula.substs_imp] at h₂ h₃
  have h₁ : T.internalize V ⊢ ((∀¹ (E 🡒 F)) ⋏ (∀¹ E)) 🡒 ∀¹ F := by
    apply TProof.generalize_imp
    simp only [Semiformula.shift_and, Semiformula.shift_all, Semiformula.shift_imp,
      Semiformula.free]
    cl_prover [h₂, h₃]
  cl_prover [h₁]

lemma all_iff_imp_all_imp_imp_left (d A B : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (d 🡒 (A 🡘 B)) 🡒 ∀¹ (d 🡒 B 🡒 A) :=
  TProof.all_imp_all_of_free <| by simp only [Semiformula.free_imp, Semiformula.free_iff]; cl_prover

lemma all_iff_imp_all_imp_imp_right (d A B : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (d 🡒 (A 🡘 B)) 🡒 ∀¹ (d 🡒 A 🡒 B) :=
  TProof.all_imp_all_of_free <| by simp only [Semiformula.free_imp, Semiformula.free_iff]; cl_prover

lemma tprovable_all_iff_all (E F : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (E 🡘 F) 🡒 (∀¹ E 🡘 ∀¹ F) := by
  have h₁ : T.internalize V ⊢ ∀¹ (E 🡘 F : Semiformula V L 1) 🡒 ∀¹ (E 🡒 F) :=
    TProof.all_imp_all_of_free <| by
      simp only [Semiformula.free_imp, Semiformula.free_iff]; cl_prover
  have h₂ : T.internalize V ⊢ ∀¹ (E 🡘 F : Semiformula V L 1) 🡒 ∀¹ (F 🡒 E) :=
    TProof.all_imp_all_of_free <| by
      simp only [Semiformula.free_imp, Semiformula.free_iff]; cl_prover
  cl_prover [h₁, h₂, tprovable_all_imp_imp_all (T := T) E F,
    tprovable_all_imp_imp_all (T := T) F E]

lemma tprovable_all_iff_all_domain (d A B : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (A 🡘 B) 🡒 (∀¹ (d 🡒 A) 🡘 ∀¹ (d 🡒 B)) := by
  have h₁ : T.internalize V ⊢ ∀¹ (A 🡘 B : Semiformula V L 1) 🡒
      ∀¹ ((d 🡒 A) 🡘 (d 🡒 B) : Semiformula V L 1) :=
    TProof.all_imp_all_of_free <| by
      simp only [Semiformula.free_imp, Semiformula.free_iff]; cl_prover
  cl_prover [h₁, tprovable_all_iff_all (T := T) (d 🡒 A) (d 🡒 B)]

lemma tprovable_all_iff_exs_domain (d A B : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (A 🡘 B) 🡒 (∃¹ (d ⋏ A) 🡘 ∃¹ (d ⋏ B)) := by
  have h₁ : T.internalize V ⊢ ∀¹ (A 🡘 B : Semiformula V L 1) 🡒
      ∀¹ (∼(d ⋏ A) 🡘 ∼(d ⋏ B) : Semiformula V L 1) :=
    TProof.all_imp_all_of_free <| by
      simp only [Semiformula.free_iff, Semiformula.free_neg, Semiformula.free_and]; cl_prover
  have h₂ : T.internalize V ⊢ ∀¹ (∼(d ⋏ A) 🡘 ∼(d ⋏ B)) 🡒 (∼(∃¹ (d ⋏ A)) 🡘 ∼(∃¹ (d ⋏ B))) := by
    simpa using tprovable_all_iff_all (T := T) (∼(d ⋏ A)) (∼(d ⋏ B))
  cl_prover [h₁, h₂]

lemma tprovable_all_iff_exs (E F : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (E 🡘 F) 🡒 (∃¹ E 🡘 ∃¹ F) := by
  have h₁ : T.internalize V ⊢ ∀¹ (E 🡘 F : Semiformula V L 1) 🡒 ∀¹ (∼E 🡘 ∼F : Semiformula V L 1) :=
    TProof.all_imp_all_of_free <| by
      simp only [Semiformula.free_iff, Semiformula.free_neg]; cl_prover
  have h₂ : T.internalize V ⊢ ∀¹ (∼E 🡘 ∼F) 🡒 (∼(∃¹ E) 🡘 ∼(∃¹ F)) := by
    simpa using tprovable_all_iff_all (T := T) (∼E) (∼F)
  cl_prover [h₁, h₂]

lemma tprovable_all_iff_trans {A B C : Semiformula V L 1} (h₁ : T.internalize V ⊢ ∀¹ (A 🡘 B))
    (h₂ : T.internalize V ⊢ ∀¹ (B 🡘 C)) : T.internalize V ⊢ ∀¹ (A 🡘 C) := by
  have h₃ : T.internalize V ⊢ ∀¹ ((A 🡘 B) 🡒 (B 🡘 C) 🡒 (A 🡘 C)) := by
    apply TProof.all!
    simp only [Semiformula.free_imp, Semiformula.free_iff]
    cl_prover
  exact tprovable_all_imp_imp_all _ _ ⨀ (tprovable_all_imp_imp_all _ _ ⨀ h₃ ⨀ h₁) ⨀ h₂

lemma tprovable_all_of_all_imp_imp {E F G : Semiformula V L 1}
    (h : T.internalize V ⊢ ∀¹ (E 🡒 F 🡒 G)) (h₁ : T.internalize V ⊢ ∀¹ E)
    (h₂ : T.internalize V ⊢ ∀¹ F) : T.internalize V ⊢ ∀¹ G :=
  tprovable_all_imp_imp_all F G ⨀ (tprovable_all_imp_imp_all E (F 🡒 G) ⨀ h ⨀ h₁) ⨀ h₂

lemma tprovable_all_iff_symm {A B : Semiformula V L 1} (h : T.internalize V ⊢ ∀¹ (A 🡘 B)) :
    T.internalize V ⊢ ∀¹ (B 🡘 A) := by
  have h₁ : T.internalize V ⊢ ∀¹ ((A 🡘 B) 🡒 (B 🡘 A)) := by
    apply TProof.all!
    simp only [Semiformula.free_imp, Semiformula.free_iff]
    cl_prover
  exact tprovable_all_imp_imp_all _ _ ⨀ h₁ ⨀ h

lemma tprovable_all_iff_all_of_domain {d : Semiformula V L 1} (hd : T.internalize V ⊢ ∀¹ d)
    (A B : Semiformula V L 1) : T.internalize V ⊢ ∀¹ (A 🡘 B) 🡒 (∀¹ A 🡘 ∀¹ (d 🡒 B)) := by
  have h₁ := TProof.all_imp_subst (T := T) (A.shift 🡘 B.shift) (Semiterm.fvar 0)
  have h₂ := TProof.all_imp_subst (T := T) d.shift (Semiterm.fvar 0)
  simp only [Semiformula.substs_imply] at h₁
  have h₃ : T.internalize V ⊢ ((∀¹ (A 🡘 B)) ⋏ (∀¹ d)) 🡒 ∀¹ (A 🡘 (d 🡒 B)) := by
    apply TProof.generalize_imp
    simp only [Semiformula.shift_and, Semiformula.shift_all, Semiformula.shift_iff,
      Semiformula.shift_imp, Semiformula.free, Semiformula.substs_imply, Semiformula.substs_imp]
    cl_prover [h₁, h₂]
  cl_prover [hd, h₃, tprovable_all_iff_all (T := T) A (d 🡒 B)]

lemma tprovable_exs_iff_exs_of_domain {d : Semiformula V L 1} (hd : T.internalize V ⊢ ∀¹ d)
    (A B : Semiformula V L 1) : T.internalize V ⊢ ∀¹ (A 🡘 B) 🡒 (∃¹ A 🡘 ∃¹ (d ⋏ B)) := by
  have h₁ := TProof.all_imp_subst (T := T) (A.shift 🡘 B.shift) (Semiterm.fvar 0)
  have h₂ := TProof.all_imp_subst (T := T) d.shift (Semiterm.fvar 0)
  simp only [Semiformula.substs_imply] at h₁
  have h₃ : T.internalize V ⊢ ((∀¹ (A 🡘 B)) ⋏ (∀¹ d)) 🡒 ∀¹ (A 🡘 (d ⋏ B)) := by
    apply TProof.generalize_imp
    simp only [Semiformula.shift_and, Semiformula.shift_all, Semiformula.shift_iff,
      Semiformula.free, Semiformula.substs_imply, Semiformula.substs_and]
    cl_prover [h₁, h₂]
  cl_prover [hd, h₃, tprovable_all_iff_exs (T := T) A (d ⋏ B)]

end allItr

end quantifierBlock

end FFL.FirstOrder.Arithmetic.Bootstrapping
