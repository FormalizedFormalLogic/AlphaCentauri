module

public import AlphaCentauri.ToFoundation.Provable
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Hierarchy

/-!
# The provability formula at a numeral

For an element `x` of a model of `𝗜𝚺₁`, `provabilityFormula T x` is the internal sentence
obtained by substituting the numeral of `x` into the provability formula of `T`. Its internal
provability follows from the provability of `x`, it satisfies the internal form of the
derivability condition $\mathbf{D2}$, and every internal $\Sigma_1$ sentence internally implies
its own `provabilityFormula`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open FirstOrder Bootstrapping.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {T : ArithmeticTheory} [T.Δ₁]

@[simp] lemma models_provabilityPred_iff (σ : ArithmeticSentence) :
    V↓[ℒₒᵣ] ⊧ provabilityPred T σ ↔ Provable T (⌜σ⌝ : V) := by
  simp [models_iff]

variable (T) in
noncomputable def provabilityFormula (x : V) : Formula V ℒₒᵣ :=
  (⌜(provable T).val⌝ : Semiformula V ℒₒᵣ 1).subst ![𝕹 x]

@[simp] lemma typed_quote_provabilityPred (σ : ArithmeticSentence) :
    (⌜provabilityPred T σ⌝ : Formula V ℒₒᵣ) = provabilityFormula T ⌜σ⌝ := by
  simp [provabilityPred, typed_quote_rew_subst, provabilityFormula, Matrix.constant_eq_singleton]

lemma tprovable_provabilityFormula [𝗣𝗔⁻ ⪯ T] {x : V} (h : Provable T x) :
    T.internalize V ⊢ provabilityFormula T x := by
  simpa [provabilityFormula, Matrix.constant_eq_singleton] using
    bold_sigma_one_complete (V := V) T (φ := (provable T).val) (by simp) (w := ![x])
      (by simpa using h)

variable (T) in
private noncomputable def provableImpFormula : ArithmeticSemisentence 3 :=
  (impGraph ℒₒᵣ).val 🡒 (Rew.subst ![#0] ▹ (provable T).val) 🡒
    (Rew.subst ![#1] ▹ (provable T).val) 🡒 (Rew.subst ![#2] ▹ (provable T).val)

lemma tprovable_provabilityFormula_imp [𝗜𝚺₁ ⪯ T] (φ ψ : Formula V ℒₒᵣ) :
    T.internalize V ⊢
      provabilityFormula T (φ 🡒 ψ).val 🡒 provabilityFormula T φ.val 🡒
        provabilityFormula T ψ.val := by
  have h₁ := tprovable_subst_numeral_of_models (T := T) (φ := provableImpFormula T)
    (fun W _ _ e ↦ by
      simp only [provableImpFormula];
      simpa using fun h ↦ h ▸ provable_of_provable_imp_of_provable)
    ![(φ 🡒 ψ).val, φ.val, ψ.val];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (φ := (impGraph ℒₒᵣ).val) (by simp)
    (w := ![(φ 🡒 ψ).val, φ.val, ψ.val]) (by simp);
  simp [provableImpFormula, typed_quote_rew_subst, Semiformula.substs_substs] at h₁;
  simpa [provabilityFormula, Matrix.constant_eq_singleton] using h₁ ⨀ h₂

/-- Every internal $\Sigma_1$ sentence internally implies its own provability. -/
axiom tprovable_imp_provabilityFormula_of_sigma1 [𝗜𝚺₁ ⪯ T] (φ : Formula V ℒₒᵣ)
    (hφ : IsSigma 1 φ.val) (hs : φ.shift = φ) :
    T.internalize V ⊢ φ 🡒 provabilityFormula T φ.val

end FFL.FirstOrder.Arithmetic.Bootstrapping
