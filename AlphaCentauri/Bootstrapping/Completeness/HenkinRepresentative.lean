module

public import AlphaCentauri.Bootstrapping.Completeness.HenkinTyped

/-!
# Representatives of provably equal free variables

Provable equality of free variables in the Henkin set is an equivalence relation, and every class
has a least element, its representative.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq]
variable (S : Theory L) [S.Δ₁]

section equality

variable [𝗘𝗤 L ⪯ S]

/-- The free variables `^&u` and `^&v` are provably equal in the Henkin set. -/
def HenkinEq (u v : V) : Prop :=
  HenkinSet S (Semiformula.equal (Semiterm.fvar u) (Semiterm.fvar v) : Formula V L).val

/-- The free variable `^&a` is the least of the free variables provably equal to it. -/
def IsRepresentative (a : V) : Prop := ∀ y < a, ¬HenkinEq S y a

omit [𝗘𝗤 L ⪯ S] in
private lemma henkinEq_definable (u : V) : 𝚫ᴬ_[2]-Predicate[V] fun a ↦ HenkinEq S a u := by
  have hf : 𝚺ᴬ₁-Function₁[V] fun a ↦
      (Semiformula.equal (Semiterm.fvar a) (Semiterm.fvar u) : Formula V L).val := by
    simp only [Semiformula.equal, Semiformula.rel_val, Nat.cast_ofNat, SemitermVec.val_succ,
      Matrix.head_cons, Semiterm.fvar_val, Matrix.tail_cons, SemitermVec.val_nil]
    definability
  exact (henkinSet_definable S).comp (hf.of_lt (by simp))

variable (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p) (hcons : S.Consistent V)
include hS hcons

omit hS hcons in
theorem HenkinEq.refl (u : V) : HenkinEq S u u :=
  henkinSet_of_tprovable S (tprovable_equal_refl S (Semiterm.fvar u))

theorem HenkinEq.symm {u v : V} (h : HenkinEq S u v) : HenkinEq S v u :=
  henkinSet_of_tprovable_imp S hS hcons
    (tprovable_equal_symm_imp S (Semiterm.fvar u) (Semiterm.fvar v)) h

theorem HenkinEq.trans {u v w : V} (h₁ : HenkinEq S u v) (h₂ : HenkinEq S v w) :
    HenkinEq S u w :=
  henkinSet_of_tprovable_imp S hS hcons
    (tprovable_equal_trans_imp S (Semiterm.fvar u) (Semiterm.fvar v) (Semiterm.fvar w))
    ((henkinSet_and_iff S hS hcons).mpr ⟨h₁, h₂⟩)

theorem exists_isRepresentative (u : V) : ∃ a, IsRepresentative S a ∧ HenkinEq S a u := by
  obtain ⟨a, ha, hmin⟩ := InductionOnHierarchy.least_number_sigma 𝚫 2
    (P := fun a ↦ HenkinEq S a u) (henkinEq_definable S u) (x := u) (HenkinEq.refl S u)
  exact ⟨a, fun y hy hya ↦ hmin y hy (HenkinEq.trans S hS hcons hya ha), ha⟩

theorem IsRepresentative.eq_of_henkinEq {a b : V} (ha : IsRepresentative S a)
    (hb : IsRepresentative S b) (h : HenkinEq S a b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (hb a hab h).elim
  · exact hab
  · exact (ha b hab (HenkinEq.symm S hS hcons h)).elim

end equality

end FFL.FirstOrder.Arithmetic.Bootstrapping
