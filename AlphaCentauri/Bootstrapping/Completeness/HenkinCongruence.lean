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

theorem henkinSet_equal_refl (t : Semiterm V L 0) : HenkinSet S (Semiformula.equal t t).val := by
  sorry

theorem henkinSet_equal_symm {s t : Semiterm V L 0}
    (h : HenkinSet S (Semiformula.equal s t).val) : HenkinSet S (Semiformula.equal t s).val := by
  sorry

theorem henkinSet_equal_trans {s t u : Semiterm V L 0}
    (h₁ : HenkinSet S (Semiformula.equal s t).val)
    (h₂ : HenkinSet S (Semiformula.equal t u).val) : HenkinSet S (Semiformula.equal s u).val := by
  sorry

theorem henkinSet_equal_func {k : ℕ} (f : L.Func k) {s u : SemitermVec V L k 0}
    (h : ∀ i, HenkinSet S (Semiformula.equal (s i) (u i)).val) :
    HenkinSet S (Semiformula.equal (Semiterm.func f s) (Semiterm.func f u)).val := by
  sorry

theorem henkinSet_rel_iff {k : ℕ} (R : L.Rel k) {s u : SemitermVec V L k 0}
    (h : ∀ i, HenkinSet S (Semiformula.equal (s i) (u i)).val) :
    HenkinSet S (Semiformula.rel R s).val ↔ HenkinSet S (Semiformula.rel R u).val := by
  sorry

end FFL.FirstOrder.Arithmetic.Bootstrapping
