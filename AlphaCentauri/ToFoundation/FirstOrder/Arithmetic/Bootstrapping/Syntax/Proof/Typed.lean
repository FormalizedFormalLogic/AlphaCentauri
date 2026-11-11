module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Equality
public import AlphaCentauri.ToFoundation.Logic.Entailment
public import AlphaCentauri.ToMathlib.Data.Vector.Basic
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Typed
public import Foundation.Meta.ClProver

/-!
# The typed internal calculus

Typed internal provability `T.internalize V ⊢ φ` is transferred to `Derivable T` on sequents given
as codes. Specialisation and generalisation of `∀¹^[k]` are available in the typed internal proof
system.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic
namespace Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## From typed proofs to derivability -/

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

end Bootstrapping
end FFL.FirstOrder.Arithmetic
