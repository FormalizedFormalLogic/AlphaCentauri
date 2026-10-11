module

public import AlphaCentauri.Bootstrapping.Completeness.HenkinFunction

/-!
# Equality of terms in the Henkin set

Equality of arbitrary terms in the Henkin set is symmetric and transitive, and function and
relation symbols respect it.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq]
variable (S : Theory L) [S.Δ₁] [𝗘𝗤 L ⪯ S]
variable (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p) (hcons : S.Consistent V)
include hS hcons

omit [L.Eq] [𝗘𝗤 L ⪯ S] in
theorem henkinSet_conj_iff {k : ℕ} (v : Fin k → Formula V L) :
    HenkinSet S (Matrix.conj v).val ↔ ∀ i, HenkinSet S (v i).val := by
  induction k with
  | zero =>
    simpa using henkinSet_of_tprovable S (φ := (⊤ : Formula V L)) (by simp)
  | succ k ih =>
    rw [Matrix.conj, henkinSet_and_iff S hS hcons, ih, Fin.forall_fin_succ]
    exact Iff.rfl

omit hS hcons in
theorem henkinSet_equal_refl (t : Semiterm V L 0) : HenkinSet S (Semiformula.equal t t).val :=
  henkinSet_of_tprovable S <| tprovable_equal_refl S t

theorem henkinSet_equal_symm {s t : Semiterm V L 0}
    (h : HenkinSet S (Semiformula.equal s t).val) : HenkinSet S (Semiformula.equal t s).val :=
  henkinSet_of_tprovable_imp S hS hcons (tprovable_equal_symm_imp S s t) h

theorem henkinSet_equal_trans {s t u : Semiterm V L 0}
    (h₁ : HenkinSet S (Semiformula.equal s t).val)
    (h₂ : HenkinSet S (Semiformula.equal t u).val) : HenkinSet S (Semiformula.equal s u).val :=
  henkinSet_of_tprovable_imp S hS hcons (tprovable_equal_trans_imp S s t u)
    ((henkinSet_and_iff S hS hcons).mpr ⟨h₁, h₂⟩)

theorem henkinSet_equal_func {k : ℕ} (f : L.Func k) {s u : SemitermVec V L k 0}
    (h : ∀ i, HenkinSet S (Semiformula.equal (s i) (u i)).val) :
    HenkinSet S (Semiformula.equal (Semiterm.func f s) (Semiterm.func f u)).val :=
  henkinSet_of_tprovable_imp S hS hcons (tprovable_equal_func_imp S f s u)
    ((henkinSet_conj_iff S hS hcons _).mpr h)

private theorem henkinSet_rel_imp {k : ℕ} (R : L.Rel k) {s u : SemitermVec V L k 0}
    (h : ∀ i, HenkinSet S (Semiformula.equal (s i) (u i)).val)
    (hs : HenkinSet S (Semiformula.rel R s).val) : HenkinSet S (Semiformula.rel R u).val :=
  HenkinSet.modus_ponens hS hcons hs <|
    henkinSet_of_tprovable_imp S hS hcons (tprovable_rel_congr_imp S R s u)
      ((henkinSet_conj_iff S hS hcons _).mpr h)

theorem henkinSet_rel_iff {k : ℕ} (R : L.Rel k) {s u : SemitermVec V L k 0}
    (h : ∀ i, HenkinSet S (Semiformula.equal (s i) (u i)).val) :
    HenkinSet S (Semiformula.rel R s).val ↔ HenkinSet S (Semiformula.rel R u).val :=
  ⟨henkinSet_rel_imp S hS hcons R h,
    henkinSet_rel_imp S hS hcons R fun i ↦ henkinSet_equal_symm S hS hcons (h i)⟩

end FFL.FirstOrder.Arithmetic.Bootstrapping
