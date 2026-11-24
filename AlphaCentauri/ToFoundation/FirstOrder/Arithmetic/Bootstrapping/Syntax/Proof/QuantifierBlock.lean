module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Basic

/-!
# Provability of formula codes with quantifier blocks

Internal provability of codes of formulas with blocks of quantifiers.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic
namespace Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {n m k : ℕ} {T : Theory L} [T.Δ₁] {φ ψ : Semiformula V L 1}

/-! ## Term vectors -/

@[simp high]
lemma Semiterm.shift_vecMap_bvar (f : Fin k → Fin n) :
    (Semiterm.shift ⨟ fun i ↦ (Semiterm.bvar (f i) : Semiterm V L n)) =
      fun i ↦ Semiterm.bvar (f i) := by
  funext i; simp

@[simp high]
lemma Semiterm.substs_vecMap_bvar (w : SemitermVec V L n m) (f : Fin k → Fin n) :
    ((Semiterm.subst w)⨟ fun i ↦ (Semiterm.bvar (f i) : Semiterm V L n)) = fun i ↦ w (f i) := by
  funext i; simp

@[simp high]
lemma Semiterm.shift_vecMap_fvar (f : Fin k → V) :
    (Semiterm.shift ⨟ fun i ↦ (Semiterm.fvar (f i) : Semiterm V L n)) =
      fun i ↦ Semiterm.fvar (f i + 1) := by
  funext i; simp

@[simp high]
lemma Semiterm.substs_vecMap_bvar_id (w : SemitermVec V L n m) :
    ((Semiterm.subst w)⨟ (Semiterm.bvar : Fin n → Semiterm V L n)) = w := by
  funext i; simp

@[simp high]
lemma Semiterm.substs_vecMap_fvar (w : SemitermVec V L n m) (f : Fin k → V) :
    ((Semiterm.subst w)⨟ fun i ↦ (Semiterm.fvar (f i) : Semiterm V L n)) =
      fun i ↦ Semiterm.fvar (f i) := by
  funext i; simp

lemma SemitermVec.q_eq_cons (w : Fin k → Term V L) :
    SemitermVec.q w = (Semiterm.bvar 0 :> fun i ↦ (w i).bShift) := by
  funext j
  cases j using Fin.cases <;> simp [SemitermVec.q]

@[simp]
lemma SemitermVec.q_one (w : SemitermVec V L 1 m) : w.q 1 = (w 0).bShift :=
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

/-! ## Blocks of universal quantifiers -/

@[simp]
lemma Semiterm.shift_iterate_bvar (z : Fin n) :
    Semiterm.shift^[k] (Semiterm.bvar z : Semiterm V L n) = Semiterm.bvar z :=
  Function.iterate_fixed (by simp) k

@[simp]
lemma Semiterm.shift_iterate_fvar (x : V) :
    Semiterm.shift^[k] (Semiterm.fvar x : Semiterm V L n) = Semiterm.fvar (x + k) := by
  induction k with
  | zero => simp
  | succ k ih => simp [Function.iterate_succ_apply', ih, add_assoc]

@[simp high]
lemma Semiterm.shift_iterate_vecMap_bvar (f : Fin k → Fin n) (a : ℕ) :
    (Semiterm.shift^[a] ⨟ fun i ↦ (Semiterm.bvar (f i) : Semiterm V L n)) =
      fun i ↦ Semiterm.bvar (f i) := by
  funext i; simp

@[simp high]
lemma Semiterm.shift_iterate_vecMap_fvar (f : Fin k → V) (a : ℕ) :
    (Semiterm.shift^[a] ⨟ fun i ↦ (Semiterm.fvar (f i) : Semiterm V L n)) =
      fun i ↦ Semiterm.fvar (f i + a) := by
  funext i; simp

namespace Semiformula

@[simp]
lemma shift_iterate_verum : shift^[k] (⊤ : Semiformula V L n) = ⊤ :=
  Function.iterate_fixed shift_verum k

@[simp]
lemma shift_iterate_and (φ ψ : Semiformula V L n) : shift^[k] (φ ⋏ ψ) = shift^[k] φ ⋏ shift^[k] ψ :=
  Function.Semiconj₂.iterate (op := (· ⋏ ·)) shift_and k φ ψ

@[simp]
lemma shift_iterate_imp (φ ψ : Semiformula V L n) : shift^[k] (φ 🡒 ψ) = shift^[k] φ 🡒 shift^[k] ψ :=
  Function.Semiconj₂.iterate (op := (· 🡒 ·)) shift_imp k φ ψ

@[simp]
lemma shift_iterate_iff (φ ψ : Semiformula V L n) : shift^[k] (φ 🡘 ψ) = shift^[k] φ 🡘 shift^[k] ψ :=
  Function.Semiconj₂.iterate (op := (· 🡘 ·)) shift_iff k φ ψ

@[simp]
lemma shift_iterate_all (φ : Semiformula V L (n + 1)) : shift^[k] (∀¹ φ) = ∀¹ shift^[k] φ :=
  ((Function.Semiconj.iterate_right (f := (∀¹ ·)) (fun φ ↦ (shift_all φ).symm) k) φ).symm

@[simp]
lemma shift_conj (v : Fin m → Semiformula V L n) :
    (Matrix.conj v).shift = Matrix.conj fun i ↦ (v i).shift :=
  Matrix.conj_map shift shift_verum shift_and v

@[simp]
lemma shift_iterate_conj (v : Fin m → Semiformula V L n) :
    shift^[k] (Matrix.conj v) = Matrix.conj fun i ↦ shift^[k] (v i) :=
  Matrix.conj_map shift^[k] shift_iterate_verum shift_iterate_and v

@[simp]
lemma shift_iterate_allItr (φ : Semiformula V L (n + m)) :
    shift^[k] (∀¹^[m] φ) = ∀¹^[m] shift^[k] φ := by
  induction m with
  | zero => rfl
  | succ m ih => simp [allItr_succ, ih (∀¹ φ)]

@[simp]
lemma shift_allItr (φ : Semiformula V L (n + m)) : (∀¹^[m] φ).shift = ∀¹^[m] φ.shift := by
  simpa using shift_iterate_allItr (k := 1) φ

attribute [local simp] shift_substs in
@[simp]
lemma shift_iterate_subst (w : SemitermVec V L n m) (φ : Semiformula V L n) :
    shift^[k] (φ.subst w) = (shift^[k] φ).subst (Semiterm.shift^[k] ⨟ w) := by
  induction k generalizing φ w with
  | zero => rfl
  | succ k ih => simp [ih, Matrix.vecMap_vecMap_comp]

@[simp]
lemma free_and (φ ψ : Semiformula V L 1) : (φ ⋏ ψ).free = φ.free ⋏ ψ.free := by
  simp [free]

@[simp]
lemma free_neg (φ : Semiformula V L 1) : (∼φ).free = ∼φ.free := by simp [free]

@[simp]
lemma free_imp (φ ψ : Semiformula V L 1) : (φ 🡒 ψ).free = φ.free 🡒 ψ.free := by
  simp [free]

@[simp]
lemma free_iff (φ ψ : Semiformula V L 1) : (φ 🡘 ψ).free = φ.free 🡘 ψ.free := by
  simp [free]

end Semiformula

open _root_.FFL.Entailment

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
lemma TProof.allItr_specialize (φ : Semiformula V L (0 + k))
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

private lemma free_subst_q_fvar (ψ : Semiformula V L (k + 1)) :
    (ψ.subst (SemitermVec.q fun i : Fin k ↦ Semiterm.fvar (i : V))).free =
      ψ.shift.subst fun i ↦ Semiterm.fvar (i : V) := by
  rw [Semiformula.free, Semiformula.shift_substs, Semiformula.substs_substs]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp

/-- Generalisation over `k` fresh free variables under a hypothesis. -/
lemma TProof.allItr_generalize_imp {C : Formula V L} {φ : Semiformula V L (0 + k)}
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

lemma TProof.generalize_imp {C : Formula V L} (h : T.internalize V ⊢ C.shift 🡒 φ.free) :
    T.internalize V ⊢ C 🡒 ∀¹ φ :=
  Nonempty.map TProof.generalizeAux h

lemma TProof.shift_iterate! {φ : Formula V L} (h : T.internalize V ⊢ φ) (k : ℕ) :
    T.internalize V ⊢ Semiformula.shift^[k] φ := by
  induction k with
  | zero => exact h
  | succ k ih => simpa [Function.iterate_succ_apply'] using TProof.shift! ih

lemma Semiformula.subst_shift_iterate_subst_bvar (χ : Semiformula V L 1) (j : Fin n)
    (w : SemitermVec V L n 0) :
    (Semiformula.shift^[k] (χ.subst ![Semiterm.bvar j])).subst w =
      (Semiformula.shift^[k] χ).subst ![w j] := by
  rw [Semiformula.shift_iterate_subst, Semiformula.substs_substs]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => exact i.elim0

lemma TProof.all_imp_all_of_free (h : T.internalize V ⊢ φ.free 🡒 ψ.free) :
    T.internalize V ⊢ ∀¹ φ 🡒 ∀¹ ψ :=
  FiniteContext.emptyPrf <| TProof.all_imp_all! (Γ := []) <| FiniteContext.of h

lemma TProof.exs_imp_of_free {R : Formula V L} (h : T.internalize V ⊢ φ.free 🡒 R.shift) :
    T.internalize V ⊢ ∃¹ φ 🡒 R := by
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

lemma tprovable_all_imp_all (D φ : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ φ 🡒 ∀¹ (D 🡒 φ) :=
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

lemma all_iff_imp_all_imp_imp_left (D A B : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (D 🡒 (A 🡘 B)) 🡒 ∀¹ (D 🡒 B 🡒 A) :=
  TProof.all_imp_all_of_free <| by simp only [Semiformula.free_imp, Semiformula.free_iff]; cl_prover

lemma all_iff_imp_all_imp_imp_right (D A B : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (D 🡒 (A 🡘 B)) 🡒 ∀¹ (D 🡒 A 🡒 B) :=
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

lemma tprovable_all_iff_all_domain (D A B : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (A 🡘 B) 🡒 (∀¹ (D 🡒 A) 🡘 ∀¹ (D 🡒 B)) := by
  have h₁ : T.internalize V ⊢ ∀¹ (A 🡘 B : Semiformula V L 1) 🡒
      ∀¹ ((D 🡒 A) 🡘 (D 🡒 B) : Semiformula V L 1) :=
    TProof.all_imp_all_of_free <| by
      simp only [Semiformula.free_imp, Semiformula.free_iff]; cl_prover
  cl_prover [h₁, tprovable_all_iff_all (T := T) (D 🡒 A) (D 🡒 B)]

lemma tprovable_all_iff_exs_domain (D A B : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (A 🡘 B) 🡒 (∃¹ (D ⋏ A) 🡘 ∃¹ (D ⋏ B)) := by
  have h₁ : T.internalize V ⊢ ∀¹ (A 🡘 B : Semiformula V L 1) 🡒
      ∀¹ (∼(D ⋏ A) 🡘 ∼(D ⋏ B) : Semiformula V L 1) :=
    TProof.all_imp_all_of_free <| by
      simp only [Semiformula.free_iff, Semiformula.free_neg, Semiformula.free_and]; cl_prover
  have h₂ : T.internalize V ⊢ ∀¹ (∼(D ⋏ A) 🡘 ∼(D ⋏ B)) 🡒 (∼(∃¹ (D ⋏ A)) 🡘 ∼(∃¹ (D ⋏ B))) := by
    simpa using tprovable_all_iff_all (T := T) (∼(D ⋏ A)) (∼(D ⋏ B))
  cl_prover [h₁, h₂]

/-- Equivalence on the domain `D` of the matrices of universal quantifiers relativized to `D`. -/
lemma tprovable_all_imp_iff_all_domain (D A B : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (D 🡒 (A 🡘 B)) 🡒 (∀¹ (D 🡒 A) 🡘 ∀¹ (D 🡒 B)) := by
  have h₁ : T.internalize V ⊢ ∀¹ (D 🡒 (A 🡘 B)) 🡒
      ∀¹ ((D 🡒 A) 🡘 (D 🡒 B) : Semiformula V L 1) :=
    TProof.all_imp_all_of_free <| by
      simp only [Semiformula.free_imp, Semiformula.free_iff]; cl_prover
  cl_prover [h₁, tprovable_all_iff_all (T := T) (D 🡒 A) (D 🡒 B)]

lemma tprovable_all_iff_exs (E F : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (E 🡘 F) 🡒 (∃¹ E 🡘 ∃¹ F) := by
  have h₁ : T.internalize V ⊢ ∀¹ (E 🡘 F : Semiformula V L 1) 🡒 ∀¹ (∼E 🡘 ∼F : Semiformula V L 1) :=
    TProof.all_imp_all_of_free <| by
      simp only [Semiformula.free_iff, Semiformula.free_neg]; cl_prover
  have h₂ : T.internalize V ⊢ ∀¹ (∼E 🡘 ∼F) 🡒 (∼(∃¹ E) 🡘 ∼(∃¹ F)) := by
    simpa using tprovable_all_iff_all (T := T) (∼E) (∼F)
  cl_prover [h₁, h₂]

/-- Equivalence on the domain `D` of the matrices of existential quantifiers relativized to `D`. -/
lemma tprovable_all_imp_iff_exs_domain (D A B : Semiformula V L 1) :
    T.internalize V ⊢ ∀¹ (D 🡒 (A 🡘 B)) 🡒 (∃¹ (D ⋏ A) 🡘 ∃¹ (D ⋏ B)) := by
  have h₁ : T.internalize V ⊢ ∀¹ (D 🡒 (A 🡘 B)) 🡒
      ∀¹ ((D ⋏ A) 🡘 (D ⋏ B) : Semiformula V L 1) :=
    TProof.all_imp_all_of_free <| by
      simp only [Semiformula.free_imp, Semiformula.free_iff, Semiformula.free_and]; cl_prover
  cl_prover [h₁, tprovable_all_iff_exs (T := T) (D ⋏ A) (D ⋏ B)]

/-- Transitivity of equivalence under a universal quantifier, the second equivalence holding on the
domain `D`. -/
lemma tprovable_all_iff_imp_all_imp_iff {D A B C : Semiformula V L 1}
    (h : T.internalize V ⊢ ∀¹ (D 🡒 (B 🡘 C))) :
    T.internalize V ⊢ ∀¹ (A 🡘 B) 🡒 ∀¹ (D 🡒 (A 🡘 C)) := by
  apply TProof.generalize_imp
  have h₁ := TProof.all_imp_subst (T := T) (A 🡘 B).shift (Semiterm.fvar 0)
  have h₂ := TProof.all_imp_subst (T := T) (D 🡒 (B 🡘 C)).shift (Semiterm.fvar 0)
  have h₃ : T.internalize V ⊢ ∀¹ (D 🡒 (B 🡘 C)).shift := by simpa using TProof.shift! h
  simp only [Semiformula.free, Semiformula.shift_all, Semiformula.shift_imp,
    Semiformula.shift_and, LogicalConnective.iff, Semiformula.substs_imp, Semiformula.substs_and]
    at h₁ h₂ h₃ ⊢
  cl_prover 256 [h₁, h₂, h₃]

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

lemma tprovable_all_iff_all_of_domain {D : Semiformula V L 1} (hd : T.internalize V ⊢ ∀¹ D)
    (A B : Semiformula V L 1) : T.internalize V ⊢ ∀¹ (A 🡘 B) 🡒 (∀¹ A 🡘 ∀¹ (D 🡒 B)) := by
  have h₁ := TProof.all_imp_subst (T := T) (A.shift 🡘 B.shift) (Semiterm.fvar 0)
  have h₂ := TProof.all_imp_subst (T := T) D.shift (Semiterm.fvar 0)
  simp only [Semiformula.substs_imply] at h₁
  have h₃ : T.internalize V ⊢ ((∀¹ (A 🡘 B)) ⋏ (∀¹ D)) 🡒 ∀¹ (A 🡘 (D 🡒 B)) := by
    apply TProof.generalize_imp
    simp only [Semiformula.shift_and, Semiformula.shift_all, Semiformula.shift_iff,
      Semiformula.shift_imp, Semiformula.free, Semiformula.substs_imply, Semiformula.substs_imp]
    cl_prover [h₁, h₂]
  cl_prover [hd, h₃, tprovable_all_iff_all (T := T) A (D 🡒 B)]

lemma tprovable_exs_iff_exs_of_domain {D : Semiformula V L 1} (hd : T.internalize V ⊢ ∀¹ D)
    (A B : Semiformula V L 1) : T.internalize V ⊢ ∀¹ (A 🡘 B) 🡒 (∃¹ A 🡘 ∃¹ (D ⋏ B)) := by
  have h₁ := TProof.all_imp_subst (T := T) (A.shift 🡘 B.shift) (Semiterm.fvar 0)
  have h₂ := TProof.all_imp_subst (T := T) D.shift (Semiterm.fvar 0)
  simp only [Semiformula.substs_imply] at h₁
  have h₃ : T.internalize V ⊢ ((∀¹ (A 🡘 B)) ⋏ (∀¹ D)) 🡒 ∀¹ (A 🡘 (D ⋏ B)) := by
    apply TProof.generalize_imp
    simp only [Semiformula.shift_and, Semiformula.shift_all, Semiformula.shift_iff,
      Semiformula.free, Semiformula.substs_imply, Semiformula.substs_and]
    cl_prover [h₁, h₂]
  cl_prover [hd, h₃, tprovable_all_iff_exs (T := T) A (D ⋏ B)]

/-! ## Provable equivalences of formula codes -/

variable {d d' p q X X' Y Y' : V}

lemma provable_iff_iff_tprovable (hp : IsFormula L p) (hq : IsFormula L q) :
    Provable T (iff L p q) ↔ T.internalize V ⊢ (⟨p, hp⟩ : Formula V L) 🡘 ⟨q, hq⟩ := by
  rw [tprovable_iff_provable, Semiformula.val_iff]

lemma provable_iff_and (hX : IsFormula L X) (hX' : IsFormula L X') (hY : IsFormula L Y)
    (hY' : IsFormula L Y') (h₁ : Provable T (iff L X X')) (h₂ : Provable T (iff L Y Y')) :
    Provable T (iff L (X ^⋏ Y) (X' ^⋏ Y')) := by
  rw [provable_iff_iff_tprovable hX hX'] at h₁
  rw [provable_iff_iff_tprovable hY hY'] at h₂
  have h₃ : T.internalize V ⊢ ((⟨X, hX⟩ : Formula V L) ⋏ ⟨Y, hY⟩) 🡘
      ((⟨X', hX'⟩ : Formula V L) ⋏ ⟨Y', hY'⟩) := by cl_prover [h₁, h₂]
  simpa only [tprovable_iff_provable, Semiformula.val_iff, Semiformula.val_and] using h₃

lemma provable_iff_or (hX : IsFormula L X) (hX' : IsFormula L X') (hY : IsFormula L Y)
    (hY' : IsFormula L Y') (h₁ : Provable T (iff L X X')) (h₂ : Provable T (iff L Y Y')) :
    Provable T (iff L (X ^⋎ Y) (X' ^⋎ Y')) := by
  rw [provable_iff_iff_tprovable hX hX'] at h₁
  rw [provable_iff_iff_tprovable hY hY'] at h₂
  have h₃ : T.internalize V ⊢ ((⟨X, hX⟩ : Formula V L) ⋎ ⟨Y, hY⟩) 🡘
      ((⟨X', hX'⟩ : Formula V L) ⋎ ⟨Y', hY'⟩) := by cl_prover [h₁, h₂]
  simpa only [tprovable_iff_provable, Semiformula.val_iff, Semiformula.val_or] using h₃

lemma provable_iff_neg (hX : IsFormula L X) (hX' : IsFormula L X') (h : Provable T (iff L X X')) :
    Provable T (iff L (neg L X) (neg L X')) := by
  rw [provable_iff_iff_tprovable hX hX'] at h
  have h₁ : T.internalize V ⊢ (∼(⟨X, hX⟩ : Formula V L)) 🡘 ∼⟨X', hX'⟩ := by cl_prover [h]
  simpa only [tprovable_iff_provable, Semiformula.val_iff, Semiformula.val_neg] using h₁

lemma provable_all_iff_of_free (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q)
    (h : Provable T (iff L (free L p) (free L q))) : Provable T (^∀ iff L p q) := by
  have h₁ : T.internalize V ⊢
      ((⟨p, by simpa using hp⟩ : Semiformula V L 1) 🡘 ⟨q, by simpa using hq⟩).free := by
    simpa only [tprovable_iff_provable, Semiformula.free_iff, Semiformula.val_iff,
      Semiformula.free_val] using h
  simpa only [tprovable_iff_provable, Semiformula.val_all, Semiformula.val_iff] using
    TProof.all! h₁

lemma provable_all_iff_all_of_domain (hd : IsSemiformula L 1 d) (hdp : Provable T (^∀ d))
    (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q)
    (h : Provable T (iff L (free L p) (free L q))) : Provable T (iff L (^∀ p) (^∀ imp L d q)) := by
  have h₁ : T.internalize V ⊢ ∀¹ ((⟨p, by simpa using hp⟩ : Semiformula V L 1) 🡘
      ⟨q, by simpa using hq⟩) := by
    simpa only [tprovable_iff_provable, Semiformula.val_all, Semiformula.val_iff] using
      provable_all_iff_of_free hp hq h
  have h₂ : T.internalize V ⊢ ∀¹ (⟨d, by simpa using hd⟩ : Semiformula V L 1) :=
    tprovable_iff_provable.mpr hdp
  simpa only [tprovable_iff_provable, Semiformula.val_iff, Semiformula.val_all,
    Semiformula.val_imp] using tprovable_all_iff_all_of_domain h₂ _ _ ⨀ h₁

lemma provable_exs_iff_exs_of_domain (hd : IsSemiformula L 1 d) (hdp : Provable T (^∀ d))
    (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q)
    (h : Provable T (iff L (free L p) (free L q))) : Provable T (iff L (^∃ p) (^∃ (d ^⋏ q))) := by
  have h₁ : T.internalize V ⊢ ∀¹ ((⟨p, by simpa using hp⟩ : Semiformula V L 1) 🡘
      ⟨q, by simpa using hq⟩) := by
    simpa only [tprovable_iff_provable, Semiformula.val_all, Semiformula.val_iff] using
      provable_all_iff_of_free hp hq h
  have h₂ : T.internalize V ⊢ ∀¹ (⟨d, by simpa using hd⟩ : Semiformula V L 1) :=
    tprovable_iff_provable.mpr hdp
  simpa only [tprovable_iff_provable, Semiformula.val_iff, Semiformula.val_exs,
    Semiformula.val_and] using tprovable_exs_iff_exs_of_domain h₂ _ _ ⨀ h₁

lemma provable_all_imp_iff_all_imp (hd : IsSemiformula L 1 d) (hd' : IsSemiformula L 1 d')
    (hdd : Provable T (^∀ iff L d d')) (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q)
    (h : Provable T (iff L (free L p) (free L q))) :
    Provable T (iff L (^∀ imp L d p) (^∀ imp L d' q)) := by
  set P : Semiformula V L 1 := ⟨p, by simpa using hp⟩
  set Q : Semiformula V L 1 := ⟨q, by simpa using hq⟩
  set D : Semiformula V L 1 := ⟨d, by simpa using hd⟩
  set D' : Semiformula V L 1 := ⟨d', by simpa using hd'⟩
  have h₁ : T.internalize V ⊢ ∀¹ (P 🡘 Q) := by
    simpa only [tprovable_iff_provable, Semiformula.val_all, Semiformula.val_iff] using
      provable_all_iff_of_free hp hq h
  have h₂ : T.internalize V ⊢ ∀¹ (D 🡘 D') := by
    simpa only [tprovable_iff_provable, Semiformula.val_all, Semiformula.val_iff] using hdd
  have h₃ : T.internalize V ⊢ ∀¹ ((D 🡘 D') 🡒 (P 🡘 Q) 🡒 ((D 🡒 P) 🡘 (D' 🡒 Q))) := by
    apply TProof.all!
    simp only [Semiformula.free_imp, Semiformula.free_iff]
    cl_prover
  simpa only [tprovable_iff_provable, Semiformula.val_iff, Semiformula.val_all,
    Semiformula.val_imp] using
      tprovable_all_iff_all _ _ ⨀ tprovable_all_of_all_imp_imp h₃ h₂ h₁

lemma provable_exs_and_iff_exs_and (hd : IsSemiformula L 1 d) (hd' : IsSemiformula L 1 d')
    (hdd : Provable T (^∀ iff L d d')) (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q)
    (h : Provable T (iff L (free L p) (free L q))) :
    Provable T (iff L (^∃ (d ^⋏ p)) (^∃ (d' ^⋏ q))) := by
  set P : Semiformula V L 1 := ⟨p, by simpa using hp⟩
  set Q : Semiformula V L 1 := ⟨q, by simpa using hq⟩
  set D : Semiformula V L 1 := ⟨d, by simpa using hd⟩
  set D' : Semiformula V L 1 := ⟨d', by simpa using hd'⟩
  have h₁ : T.internalize V ⊢ ∀¹ (P 🡘 Q) := by
    simpa only [tprovable_iff_provable, Semiformula.val_all, Semiformula.val_iff] using
      provable_all_iff_of_free hp hq h
  have h₂ : T.internalize V ⊢ ∀¹ (D 🡘 D') := by
    simpa only [tprovable_iff_provable, Semiformula.val_all, Semiformula.val_iff] using hdd
  have h₃ : T.internalize V ⊢ ∀¹ ((D 🡘 D') 🡒 (P 🡘 Q) 🡒 ((D ⋏ P) 🡘 (D' ⋏ Q))) := by
    apply TProof.all!
    simp only [Semiformula.free_imp, Semiformula.free_iff, Semiformula.free_and]
    cl_prover
  simpa only [tprovable_iff_provable, Semiformula.val_iff, Semiformula.val_exs,
    Semiformula.val_and] using tprovable_all_iff_exs _ _ ⨀ tprovable_all_of_all_imp_imp h₃ h₂ h₁

end Bootstrapping
end FFL.FirstOrder.Arithmetic
