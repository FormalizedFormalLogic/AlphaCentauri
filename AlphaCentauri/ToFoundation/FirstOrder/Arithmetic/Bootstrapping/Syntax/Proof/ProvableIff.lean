module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.QuantifierBlock
public import AlphaCentauri.ToFoundation.Logic.Entailment
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Typed
public import Foundation.Meta.ClProver

/-!
# Provable equivalences of formula codes

Provable equivalences between formula codes in the typed internal calculus.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic
namespace Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Provable equivalences of formula codes -/

open scoped FFL.FirstOrder.Arithmetic

variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

lemma provable_iff_iff_tprovable {p q : V} (hp : IsFormula L p) (hq : IsFormula L q) :
    Provable T (iff L p q) ↔ T.internalize V ⊢ (⟨p, hp⟩ : Formula V L) 🡘 ⟨q, hq⟩ := by
  rw [tprovable_iff_provable, Semiformula.val_iff]

lemma provable_iff_and {X X' Y Y' : V} (hX : IsFormula L X) (hX' : IsFormula L X')
    (hY : IsFormula L Y) (hY' : IsFormula L Y') (h₁ : Provable T (iff L X X'))
    (h₂ : Provable T (iff L Y Y')) : Provable T (iff L (X ^⋏ Y) (X' ^⋏ Y')) := by
  rw [provable_iff_iff_tprovable hX hX'] at h₁
  rw [provable_iff_iff_tprovable hY hY'] at h₂
  have h₃ : T.internalize V ⊢ ((⟨X, hX⟩ : Formula V L) ⋏ ⟨Y, hY⟩) 🡘
      ((⟨X', hX'⟩ : Formula V L) ⋏ ⟨Y', hY'⟩) := by cl_prover [h₁, h₂]
  simpa only [tprovable_iff_provable, Semiformula.val_iff, Semiformula.val_and] using h₃

lemma provable_iff_or {X X' Y Y' : V} (hX : IsFormula L X) (hX' : IsFormula L X')
    (hY : IsFormula L Y) (hY' : IsFormula L Y') (h₁ : Provable T (iff L X X'))
    (h₂ : Provable T (iff L Y Y')) : Provable T (iff L (X ^⋎ Y) (X' ^⋎ Y')) := by
  rw [provable_iff_iff_tprovable hX hX'] at h₁
  rw [provable_iff_iff_tprovable hY hY'] at h₂
  have h₃ : T.internalize V ⊢ ((⟨X, hX⟩ : Formula V L) ⋎ ⟨Y, hY⟩) 🡘
      ((⟨X', hX'⟩ : Formula V L) ⋎ ⟨Y', hY'⟩) := by cl_prover [h₁, h₂]
  simpa only [tprovable_iff_provable, Semiformula.val_iff, Semiformula.val_or] using h₃

lemma provable_iff_neg {X X' : V} (hX : IsFormula L X) (hX' : IsFormula L X')
    (h : Provable T (iff L X X')) : Provable T (iff L (neg L X) (neg L X')) := by
  rw [provable_iff_iff_tprovable hX hX'] at h
  have h₁ : T.internalize V ⊢ (∼(⟨X, hX⟩ : Formula V L)) 🡘 ∼⟨X', hX'⟩ := by cl_prover [h]
  simpa only [tprovable_iff_provable, Semiformula.val_iff, Semiformula.val_neg] using h₁

lemma provable_all_iff_of_free {p q : V} (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q)
    (h : Provable T (iff L (free L p) (free L q))) : Provable T (^∀ iff L p q) := by
  have h₁ : T.internalize V ⊢
      ((⟨p, by simpa using hp⟩ : Semiformula V L 1) 🡘 ⟨q, by simpa using hq⟩).free := by
    simpa only [tprovable_iff_provable, Semiformula.free_iff, Semiformula.val_iff,
      Semiformula.free_val] using h
  simpa only [tprovable_iff_provable, Semiformula.val_all, Semiformula.val_iff] using
    TProof.all! h₁

lemma provable_all_iff_all_of_domain {d p q : V} (hd : IsSemiformula L 1 d)
    (hdp : Provable T (^∀ d)) (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q)
    (h : Provable T (iff L (free L p) (free L q))) :
    Provable T (iff L (^∀ p) (^∀ imp L d q)) := by
  have h₁ : T.internalize V ⊢ ∀¹ ((⟨p, by simpa using hp⟩ : Semiformula V L 1) 🡘
      ⟨q, by simpa using hq⟩) := by
    simpa only [tprovable_iff_provable, Semiformula.val_all, Semiformula.val_iff] using
      provable_all_iff_of_free hp hq h
  have h₂ : T.internalize V ⊢ ∀¹ (⟨d, by simpa using hd⟩ : Semiformula V L 1) :=
    tprovable_iff_provable.mpr hdp
  simpa only [tprovable_iff_provable, Semiformula.val_iff, Semiformula.val_all,
    Semiformula.val_imp] using tprovable_all_iff_all_of_domain h₂ _ _ ⨀ h₁

lemma provable_exs_iff_exs_of_domain {d p q : V} (hd : IsSemiformula L 1 d)
    (hdp : Provable T (^∀ d)) (hp : IsSemiformula L 1 p) (hq : IsSemiformula L 1 q)
    (h : Provable T (iff L (free L p) (free L q))) :
    Provable T (iff L (^∃ p) (^∃ (d ^⋏ q))) := by
  have h₁ : T.internalize V ⊢ ∀¹ ((⟨p, by simpa using hp⟩ : Semiformula V L 1) 🡘
      ⟨q, by simpa using hq⟩) := by
    simpa only [tprovable_iff_provable, Semiformula.val_all, Semiformula.val_iff] using
      provable_all_iff_of_free hp hq h
  have h₂ : T.internalize V ⊢ ∀¹ (⟨d, by simpa using hd⟩ : Semiformula V L 1) :=
    tprovable_iff_provable.mpr hdp
  simpa only [tprovable_iff_provable, Semiformula.val_iff, Semiformula.val_exs,
    Semiformula.val_and] using tprovable_exs_iff_exs_of_domain h₂ _ _ ⨀ h₁

lemma provable_all_imp_iff_all_imp {d d' p q : V} (hd : IsSemiformula L 1 d)
    (hd' : IsSemiformula L 1 d') (hdd : Provable T (^∀ iff L d d')) (hp : IsSemiformula L 1 p)
    (hq : IsSemiformula L 1 q) (h : Provable T (iff L (free L p) (free L q))) :
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

lemma provable_exs_and_iff_exs_and {d d' p q : V} (hd : IsSemiformula L 1 d)
    (hd' : IsSemiformula L 1 d') (hdd : Provable T (^∀ iff L d d')) (hp : IsSemiformula L 1 p)
    (hq : IsSemiformula L 1 q) (h : Provable T (iff L (free L p) (free L q))) :
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
