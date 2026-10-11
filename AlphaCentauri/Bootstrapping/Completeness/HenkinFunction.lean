module

public import AlphaCentauri.Bootstrapping.Completeness.HenkinRepresentative

/-!
# Function symbols in the Henkin set

Every application of a function symbol to free variables equals the free variable of a
representative in the Henkin set, and that representative is unique.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq]
variable (S : Theory L) [S.Δ₁] [𝗘𝗤 L ⪯ S]
variable (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p) (hcons : S.Consistent V)
include hS hcons

theorem exists_isRepresentative_henkinFunc {k : ℕ} (f : L.Func k) (v : Fin k → V) :
    ∃ y, IsRepresentative S y ∧
      HenkinSet S (Semiformula.equal (Semiterm.func f (fun i ↦ Semiterm.fvar (v i)))
        (Semiterm.fvar y) : Formula V L).val := by
  set t : Semiterm V L 0 := Semiterm.func f (fun i ↦ Semiterm.fvar (v i))
  have h₁ : S.internalize V ⊢ ∃¹ (Semiformula.equal t.bShift (Semiterm.bvar 0)) :=
    TProof.ex_intro! _ t <| by simpa [Semiformula.equal] using tprovable_equal_refl S t
  obtain ⟨u, hu⟩ := (henkinSet_exs_iff S hS hcons).mp (henkinSet_of_tprovable S h₁)
  obtain ⟨a, ha, hau⟩ := exists_isRepresentative S hS hcons u
  have h₂ : HenkinSet S (Semiformula.equal t (Semiterm.fvar u) : Formula V L).val := by
    simpa [Semiformula.equal] using hu
  have h₃ : HenkinSet S (Semiformula.equal (Semiterm.fvar u) (Semiterm.fvar a) :
      Formula V L).val := HenkinEq.symm S hS hcons hau
  exact ⟨a, ha, henkinSet_of_tprovable_imp S hS hcons
    (tprovable_equal_trans_imp S t (Semiterm.fvar u) (Semiterm.fvar a))
    ((henkinSet_and_iff S hS hcons).mpr ⟨h₂, h₃⟩)⟩

theorem IsRepresentative.eq_of_henkinFunc {k : ℕ} (f : L.Func k) (v : Fin k → V) {y y' : V}
    (hy : IsRepresentative S y) (hy' : IsRepresentative S y')
    (h : HenkinSet S (Semiformula.equal (Semiterm.func f (fun i ↦ Semiterm.fvar (v i)))
      (Semiterm.fvar y) : Formula V L).val)
    (h' : HenkinSet S (Semiformula.equal (Semiterm.func f (fun i ↦ Semiterm.fvar (v i)))
      (Semiterm.fvar y') : Formula V L).val) : y = y' := by
  set t : Semiterm V L 0 := Semiterm.func f (fun i ↦ Semiterm.fvar (v i))
  have h₁ : HenkinEq S y y' :=
    henkinSet_of_tprovable_imp S hS hcons
      (tprovable_equal_trans_imp S (Semiterm.fvar y) t (Semiterm.fvar y'))
      ((henkinSet_and_iff S hS hcons).mpr
        ⟨henkinSet_of_tprovable_imp S hS hcons
          (tprovable_equal_symm_imp S t (Semiterm.fvar y)) h, h'⟩)
  exact hy.eq_of_henkinEq S hS hcons hy' h₁

theorem henkinSet_equal_fvar_iff {a b : V} (ha : IsRepresentative S a) (hb : IsRepresentative S b) :
    HenkinSet S (Semiformula.equal (Semiterm.fvar a) (Semiterm.fvar b) : Formula V L).val ↔
      a = b := by
  constructor
  · intro h
    exact ha.eq_of_henkinEq S hS hcons hb h
  · rintro rfl
    exact HenkinEq.refl S a

end FFL.FirstOrder.Arithmetic.Bootstrapping
