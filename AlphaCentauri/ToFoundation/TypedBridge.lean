module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Typed

/-!
# From typed internal proofs to derivability of formula-code sequents

Typed internal provability `T.internalize V ⊢ φ` transferred to `Derivable T` on sequents given as
codes.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
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

end FFL.FirstOrder.Arithmetic.Bootstrapping
