module

public import AlphaCentauri.Bootstrapping.Proof.Substitution
public import AlphaCentauri.ToFoundation.TypedBridge
public import Foundation.Meta.ClProver

/-!
# Existential elimination for a conjunction of hypotheses

Internal `∃`-elimination with fresh eigenvariables, iterated over a finite conjunction of
existential hypotheses.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

lemma Derivable.insert_neg_of_imp {s : V} {φ ψ : Formula V L}
    (h : Derivable T (insert (φ 🡒 ψ).val s)) :
    Derivable T (insert (∼φ).val (insert ψ.val s)) := by
  have hs : IsFormulaSet L s := (IsFormulaSet.insert_iff.mp h.isFormulaSet).2
  have d : T.internalize V ⊢!ᵈᵉʳ insert (φ 🡒 ψ) ⟨s, hs⟩ :=
    Derivable.toTDerivation _ (by simpa using! h)
  have d' : T.internalize V ⊢!ᵈᵉʳ insert (∼φ) (insert ψ ⟨s, hs⟩) :=
    TDerivation.orInv (by simpa [Semiformula.imp_def] using d)
  simpa using! d'.toDerivable

lemma Semiformula.val_subst_fvar {φ : Semiformula V L 1} {u : V} :
    (φ.subst ![(Semiterm.fvar u : Semiterm V L 0)]).val = substs1 L ^&u φ.val := by
  simp [substs1]

/-- If `T` proves `⋀ᵢ ψᵢ(uᵢ) 🡒 Y` for every assignment `u` of free variables, and each `∃¹ ψᵢ` is
derivable under `s`, then `Y` is derivable under `s`.
- [HP98, Theorem I.4.9] -/
theorem Derivable.conj_exs_elim
    (hT : ∀ p ∈ T.Δ₁Class (V := V), Bootstrapping.shift L p = p) {k : ℕ}
    (ψ : Fin k → Semiformula V L 1) (Y : Formula V L) {s : V} (hs : IsFormulaSet L s)
    (hY : ∀ u : Fin k → V, T.internalize V ⊢
      Matrix.conj (fun i ↦ (ψ i).subst ![Semiterm.fvar (u i)]) 🡒 Y)
    (h : ∀ i, Derivable T (insert (∃¹ ψ i).val s)) :
    Derivable T (insert Y.val s) := by
  induction k generalizing Y with
  | zero =>
    have h₁ : T.internalize V ⊢ ⊤ 🡒 Y := hY fun i ↦ i.elim0
    exact Derivable.of_tprovable hs (by cl_prover [h₁])
  | succ k ih =>
    obtain ⟨u₀, hsu, hpu⟩ : ∃ u₀ : V, insert Y.val s ≤ u₀ ∧ (ψ 0).val ≤ u₀ :=
      ⟨(ψ 0).val + insert Y.val s, le_add_self, le_self_add⟩
    have e : ∀ f : Fin (k + 1) → Formula V L,
        Matrix.conj f = f 0 ⋏ Matrix.conj (fun i ↦ f i.succ) := fun _ ↦ rfl
    have hY' : ∀ u : Fin k → V, T.internalize V ⊢
        Matrix.conj (fun i ↦ (ψ i.succ).subst ![Semiterm.fvar (u i)]) 🡒
          (ψ 0).subst ![Semiterm.fvar u₀] 🡒 Y := by
      intro u
      have h₀ := hY (Fin.cons u₀ u)
      rw [e] at h₀
      simp only [Fin.cons_zero, Fin.cons_succ] at h₀
      cl_prover [h₀]
    have h₁ : Derivable T (insert (((ψ 0).subst ![Semiterm.fvar u₀]) 🡒 Y).val s) :=
      ih (fun i ↦ ψ i.succ) _ hY' (fun i ↦ h i.succ)
    have h₂ : Derivable T (insert (neg L (substs1 L ^&u₀ (ψ 0).val)) (insert Y.val s)) := by
      have h₂' := Derivable.insert_neg_of_imp h₁
      rwa [Semiformula.val_neg, Semiformula.val_subst_fvar] at h₂'
    have h₃ : Derivable T (insert (neg L (^∃ (ψ 0).val)) (insert Y.val s)) :=
      Derivable.neg_exs_of_fresh hT hsu hpu (by simp) h₂
    have hF : IsFormulaSet L (insert (∃¹ ψ 0).val (insert Y.val s)) := by
      simp [hs]
    have h₄ : Derivable T (insert (∃¹ ψ 0).val (insert Y.val s)) :=
      Derivable.wk hF (by intro x; simp; tauto) (h 0)
    exact Derivable.cut (∃¹ ψ 0).val h₄ h₃

end

end FFL.FirstOrder.Arithmetic.Bootstrapping
