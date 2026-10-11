module

public import AlphaCentauri.Bootstrapping.Completeness.HenkinDefinability
public import AlphaCentauri.ToFoundation.InternalEquality

/-!
# The Henkin set on typed formulas

The Henkin set of a theory $S$ in a model of $\mathsf{PA}$ in which $S$ is consistent behaves like
the set of sentences true in a term model: it is a complete theory closed under internal
provability with the Henkin property. Provable equality of free variables is an equivalence
relation, and every class has a least element.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq]
variable (S : Theory L) [S.Δ₁]

section closure

variable (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p) (hcons : S.Consistent V)
include hS hcons
omit [L.Eq]

omit hS hcons in
theorem henkinSet_of_tprovable {φ : Formula V L} (h : S.internalize V ⊢ φ) :
    HenkinSet S φ.val :=
  HenkinSet.of_provable S (Semiformula.isSemiformula_zero φ) (tprovable_iff_provable.mp h)

theorem henkinSet_of_tprovable_imp {φ ψ : Formula V L} (h : S.internalize V ⊢ φ 🡒 ψ)
    (hφ : HenkinSet S φ.val) : HenkinSet S ψ.val :=
  HenkinSet.modus_ponens hS hcons hφ (henkinSet_of_tprovable S h)

theorem henkinSet_neg_iff {φ : Formula V L} : HenkinSet S (∼φ).val ↔ ¬HenkinSet S φ.val :=
  HenkinSet.neg_iff hS hcons (Semiformula.isSemiformula_zero φ)

theorem henkinSet_not_falsum : ¬HenkinSet S (⊥ : Formula V L).val := by
  have h : HenkinSet S (∼(⊥ : Formula V L)).val :=
    henkinSet_of_tprovable S <| by simp [Entailment.verum]
  exact (henkinSet_neg_iff S hS hcons).mp h

theorem henkinSet_and_iff {φ ψ : Formula V L} :
    HenkinSet S (φ ⋏ ψ).val ↔ HenkinSet S φ.val ∧ HenkinSet S ψ.val := by
  constructor
  · intro h
    exact ⟨henkinSet_of_tprovable_imp S hS hcons Entailment.and₁ h,
      henkinSet_of_tprovable_imp S hS hcons Entailment.and₂ h⟩
  · rintro ⟨h₁, h₂⟩
    exact HenkinSet.modus_ponens hS hcons h₂
      (henkinSet_of_tprovable_imp S hS hcons Entailment.and₃ h₁)

theorem henkinSet_or_iff {φ ψ : Formula V L} :
    HenkinSet S (φ ⋎ ψ).val ↔ HenkinSet S φ.val ∨ HenkinSet S ψ.val := by
  have e : φ ⋎ ψ = ∼(∼φ ⋏ ∼ψ) := by simp
  rw [e, henkinSet_neg_iff S hS hcons, henkinSet_and_iff S hS hcons, henkinSet_neg_iff S hS hcons,
    henkinSet_neg_iff S hS hcons]
  tauto

omit hS hcons in
private lemma tprovable_subst_imp_exs (φ : Semiformula V L 1) (t : Semiterm V L 0) :
    S.internalize V ⊢ φ.subst ![t] 🡒 ∃¹ φ := ⟨by
  rw [Semiformula.imp_def]
  apply TDerivation.or
  apply TDerivation.rotate₁
  apply TDerivation.exs t
  exact TDerivation.em (φ.subst ![t])⟩

omit hS hcons in
private lemma tprovable_all_imp_subst (φ : Semiformula V L 1) (t : Semiterm V L 0) :
    S.internalize V ⊢ ∀¹ φ 🡒 φ.subst ![t] := ⟨by
  rw [Semiformula.imp_def, Semiformula.neg_all]
  apply TDerivation.or
  apply TDerivation.exs t
  simpa using TDerivation.em (φ.subst ![t])⟩

theorem henkinSet_exs_iff {φ : Semiformula V L 1} :
    HenkinSet S (∃¹ φ).val ↔
      ∃ u : V, HenkinSet S (φ.subst ![(Semiterm.fvar u : Semiterm V L 0)]).val := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := HenkinSet.exists_substs1 hS hcons (Semiformula.isSemiformula_one φ) h
    exact ⟨u, by simpa [substs1] using hu⟩
  · rintro ⟨u, hu⟩
    exact henkinSet_of_tprovable_imp S hS hcons (tprovable_subst_imp_exs S φ _) hu

theorem henkinSet_all_iff {φ : Semiformula V L 1} :
    HenkinSet S (∀¹ φ).val ↔
      ∀ u : V, HenkinSet S (φ.subst ![(Semiterm.fvar u : Semiterm V L 0)]).val := by
  constructor
  · intro h u
    exact henkinSet_of_tprovable_imp S hS hcons (tprovable_all_imp_subst S φ _) h
  · intro h
    by_contra hn
    have h₁ : HenkinSet S (∼(∀¹ φ)).val := (henkinSet_neg_iff S hS hcons).mpr hn
    rw [Semiformula.neg_all] at h₁
    obtain ⟨u, hu⟩ := (henkinSet_exs_iff S hS hcons).mp h₁
    rw [Semiformula.substs_neg, henkinSet_neg_iff S hS hcons] at hu
    exact hu (h u)

end closure

end FFL.FirstOrder.Arithmetic.Bootstrapping
