module

public import AlphaCentauri.ToFoundation.Entailment
public import AlphaCentauri.ToFoundation.InternalEquality
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Typed
public import Foundation.Meta.ClProver

/-!
# The typed internal calculus

Typed internal provability `T.internalize V ⊢ φ` is transferred to `Derivable T` on sequents given
as codes. Specialisation and generalisation of `∀¹^[k]` are available in the typed internal proof
system.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## From typed proofs to derivability -/

section typedBridge

open scoped FFL.FirstOrder.Arithmetic

variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

lemma Derivable.of_tprovable {s : V} {φ : Formula V L} (hs : IsFormulaSet L s)
    (h : T.internalize V ⊢ φ) : Derivable T (insert φ.val s) := by
  obtain ⟨b⟩ := h
  have := (TDerivation.wk (Γ := insert φ ⟨s, hs⟩) b (by intro x; simp; tauto)).toDerivable
  simpa using! this

lemma Derivable.modusPonens_typed {s : V} {φ ψ : Formula V L}
    (hφψ : Derivable T (insert (φ 🡒 ψ).val s)) (hφ : Derivable T (insert φ.val s)) :
    Derivable T (insert ψ.val s) := by
  let Γ : Sequent V L := ⟨s, (IsFormulaSet.insert_iff.mp hφ.isFormulaSet).2⟩
  have d₁ : T.internalize V ⊢!ᵈᵉʳ insert (φ 🡒 ψ) Γ :=
    Derivable.toTDerivation _ (by simpa [Γ] using! hφψ)
  have d₂ : T.internalize V ⊢!ᵈᵉʳ insert φ Γ := Derivable.toTDerivation _ (by simpa [Γ] using! hφ)
  simpa [Γ] using! (TDerivation.modusPonens d₁ d₂).toDerivable

lemma Derivable.of_tprovable_imp {s : V} {φ ψ : Formula V L}
    (h : T.internalize V ⊢ φ 🡒 ψ) (hφ : Derivable T (insert φ.val s)) :
    Derivable T (insert ψ.val s) :=
  modusPonens_typed (of_tprovable (IsFormulaSet.insert_iff.mp hφ.isFormulaSet).2 h) hφ

lemma Derivable.of_tprovable_imp₂ {s : V} {φ ψ χ : Formula V L}
    (h : T.internalize V ⊢ φ 🡒 ψ 🡒 χ) (hφ : Derivable T (insert φ.val s))
    (hψ : Derivable T (insert ψ.val s)) : Derivable T (insert χ.val s) :=
  modusPonens_typed (of_tprovable_imp h hφ) hψ

lemma Derivable.conj_typed {s : V} (hs : IsFormulaSet L s) :
    ∀ {k : ℕ} {φ : Fin k → Formula V L}, (∀ i, Derivable T (insert (φ i).val s)) →
      Derivable T (insert (Matrix.conj φ).val s)
  | 0, _, _ => Derivable.verum (by simpa using hs) (by simp)
  | k + 1, φ, h => by
    have := conj_typed hs (φ := Matrix.vecTail φ) fun i ↦ h i.succ
    simpa [Matrix.conj] using Derivable.and (h 0) this

lemma Derivable.insert_neg_of_imp {s : V} {φ ψ : Formula V L}
    (h : Derivable T (insert (φ 🡒 ψ).val s)) :
    Derivable T (insert (∼φ).val (insert ψ.val s)) := by
  have hs : IsFormulaSet L s := (IsFormulaSet.insert_iff.mp h.isFormulaSet).2
  have d : T.internalize V ⊢!ᵈᵉʳ insert (φ 🡒 ψ) ⟨s, hs⟩ :=
    Derivable.toTDerivation _ (by simpa using! h)
  have d' : T.internalize V ⊢!ᵈᵉʳ insert (∼φ) (insert ψ ⟨s, hs⟩) :=
    TDerivation.orInv (by simpa [Semiformula.imp_def] using d)
  simpa using! d'.toDerivable

lemma derivable_of_iff_mp {s : V} (X Y : Formula V L)
    (hI : Derivable T (insert (X 🡘 Y).val s)) (hX : Derivable T (insert X.val s)) :
    Derivable T (insert Y.val s) :=
  Derivable.of_tprovable_imp₂ (by cl_prover) hI hX

lemma derivable_insert_or {nd tf s : V} (hs : IsFormulaSet L s)
    (hnd : IsFormula L nd) (htf : IsFormula L tf) (h : Derivable T (insert nd (insert tf s))) :
    Derivable T (insert (nd ^⋎ tf) s) := by
  have hX : IsFormula L (nd ^⋎ tf) := IsSemiformula.or.mpr ⟨hnd, htf⟩
  have hsub : insert nd (insert tf s) ⊆ insert nd (insert tf (insert (nd ^⋎ tf) s)) := by
    intro x hx
    simp only [mem_bitInsert_iff] at hx ⊢
    tauto
  have hF : IsFormulaSet L (insert nd (insert tf (insert (nd ^⋎ tf) s))) :=
    IsFormulaSet.insert_iff.mpr ⟨hnd, IsFormulaSet.insert_iff.mpr ⟨htf,
      IsFormulaSet.insert_iff.mpr ⟨hX, hs⟩⟩⟩
  exact Derivable.or_m (mem_bitInsert_iff.mpr (Or.inl rfl)) (Derivable.wk hF hsub h)

lemma Semiformula.val_subst_fvar {φ : Semiformula V L 1} {u : V} :
    (φ.subst ![(Semiterm.fvar u : Semiterm V L 0)]).val = substs1 L ^&u φ.val := by
  simp [substs1]

end typedBridge

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

end allItr

end quantifierBlock

end FFL.FirstOrder.Arithmetic.Bootstrapping
