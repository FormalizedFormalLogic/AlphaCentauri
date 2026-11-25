module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.InternalTSchema

/-!
# The provability formula at a numeral
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic
namespace Bootstrapping

open FirstOrder Bootstrapping.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {T : ArithmeticTheory} [T.Δ₁]

lemma isPrenexHierarchy_allBallOrBall {A B : Semiformula V ℒₒᵣ 1} (hA : IsBounded A.val)
    (hB : IsBounded B.val) : IsPrenexHierarchy 𝚷 1 (allBallOrBall A B).val := by
  have hw := SemitermVec.isSemitermVec (V := V) (L := ℒₒᵣ) (k := 1) (n := 2) ![Semiterm.bvar 0]
  have hA' : IsBounded (A.subst ![Semiterm.bvar 0] : Semiformula V ℒₒᵣ 2).val := by
    rw [Semiformula.val_substs]; exact IsBounded.subst hw A.isSemiformula hA
  have hB' : IsBounded (B.subst ![Semiterm.bvar 0] : Semiformula V ℒₒᵣ 2).val := by
    rw [Semiformula.val_substs]; exact IsBounded.subst hw B.isSemiformula hB
  have ht := (Semiterm.bvar 0 + 𝕹 1 : Semiterm V ℒₒᵣ 1).isSemiterm.isUTerm
  change IsPrenexHierarchy 𝚷 (0 + 1) (qqQuant 𝚷 _)
  rw [IsPrenexHierarchy.quant_iff]
  simpa [IsPrenexHierarchy, qqBall] using And.intro (IsBounded.ball ht hA') (IsBounded.ball ht hB')


variable (σ : ArithmeticSentence)

@[simp]
lemma models_provabilityPred_iff :
    V↓[ℒₒᵣ] ⊧ provabilityPred T σ ↔ Provable T (⌜σ⌝ : V) := by
  simp [models_iff]

variable (T) in
noncomputable def provabilityFormula (x : V) : Formula V ℒₒᵣ :=
  (⌜(provable T).val⌝ : Semiformula V ℒₒᵣ 1).subst ![𝕹 x]

@[simp]
lemma typed_quote_provabilityPred :
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

variable [𝗜𝚺₁ ⪯ T] (φ : Formula V ℒₒᵣ)

lemma tprovable_provabilityFormula_imp (ψ : Formula V ℒₒᵣ) :
    T.internalize V ⊢
      provabilityFormula T (φ 🡒 ψ).val 🡒 provabilityFormula T φ.val 🡒
        provabilityFormula T ψ.val := by
  have h₁ := tprovable_subst_numeral_of_models (T := T) (φ := provableImpFormula T)
    (fun W _ _ e ↦ by
      simp only [provableImpFormula];
      simpa using fun h ↦ h ▸ provable_of_provable_imp_of_provable)
    ![(φ 🡒 ψ).val, φ.val, ψ.val];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) (impGraph ℒₒᵣ)
    (w := ![(φ 🡒 ψ).val, φ.val, ψ.val]) (by simp);
  simp [provableImpFormula, typed_quote_rew_subst, Semiformula.substs_substs] at h₁;
  simpa [provabilityFormula, Matrix.constant_eq_singleton] using h₁ ⨀ h₂

omit [𝗜𝚺₁ ⪯ T] in
private noncomputable def provableSubstNumeralFormula (ψ : ArithmeticSemisentence 1) :
    ArithmeticSemisentence 2 :=
  (Rew.subst ![#0] ▹ ψ) 🡒 ssnum.val/[#1, ⌜ψ⌝, #0] 🡒 (Rew.subst ![#1] ▹ (provable T).val)

lemma val_subst_numeral (φ : Semiformula V ℒₒᵣ 1) :
    ∀ z : V, (φ.subst ![𝕹 z] : Formula V ℒₒᵣ).val = substNumeral φ.val z := by
  intro z
  simp [substNumeral]

/-- A standard $\Sigma_1$ formula with one parameter internally implies its own provability at
every numeral. -/
lemma tprovable_imp_provabilityFormula_subst (ψ : 𝚺ᴬ₁.Semisentence 1) (z : V) :
    T.internalize V ⊢ (⌜ψ.val⌝ : Semiformula V ℒₒᵣ 1).subst ![𝕹 z] 🡒
      provabilityFormula T ((⌜ψ.val⌝ : Semiformula V ℒₒᵣ 1).subst ![𝕹 z] : Formula V ℒₒᵣ).val := by
  have h₁ := tprovable_subst_numeral_of_models (T := T)
    (φ := provableSubstNumeralFormula (T := T) ψ.val)
    (fun W _ _ e ↦ by
      have key : W ⊧/![e 0] ψ.val → Provable T (substNumeral (⌜ψ.val⌝ : W) (e 0)) := by
        intro hz
        simpa [substNumeral, Matrix.constant_eq_singleton, Sentence.quote_eq] using
          tprovable_iff_provable.mp <|
            bold_sigma_one_complete (V := W) T ψ.sigma_prop (w := ![e 0]) hz;
      simpa [provableSubstNumeralFormula] using fun hz (he : e 1 = _) ↦ he ▸ key hz)
    ![z, substNumeral ⌜ψ.val⌝ z];
  have h₂ := tprovable_subst_numeral_of_sigma1 (T := T) ssnum
    (w := ![substNumeral ⌜ψ.val⌝ z, ⌜ψ.val⌝, z]) (by simp);
  have h₃ : T.internalize V ⊢ (⌜ψ.val⌝ : Semiformula V ℒₒᵣ 1).subst ![𝕹 z] 🡒
      (⌜ssnum.val⌝ : Semiformula V ℒₒᵣ 3).subst ![𝕹 (substNumeral ⌜ψ.val⌝ z), 𝕹 ⌜ψ.val⌝, 𝕹 z] 🡒
      (⌜(provable T).val⌝ : Semiformula V ℒₒᵣ 1).subst ![𝕹 (substNumeral ⌜ψ.val⌝ z)] := by
    simpa [provableSubstNumeralFormula, typed_quote_rew_subst, Semiformula.substs_substs,
      Matrix.vecHead, Matrix.vecTail, Matrix.constant_eq_singleton] using h₁;
  have h₄ : T.internalize V ⊢ (⌜ψ.val⌝ : Semiformula V ℒₒᵣ 1).subst ![𝕹 z] 🡒
      (⌜(provable T).val⌝ : Semiformula V ℒₒᵣ 1).subst ![𝕹 (substNumeral ⌜ψ.val⌝ z)] := by
    cl_prover [h₂, h₃];
  simpa [provabilityFormula, val_subst_numeral, substNumeral, Sentence.quote_eq] using h₄

/-- Every internal prenex $\Sigma_1$ sentence internally implies its own provability. -/
theorem tprovable_imp_provabilityFormula_of_sigma1 (hφ : IsPrenexHierarchy 𝚺 1 φ.val)
    (hs : φ.shift = φ) :
    T.internalize V ⊢ φ 🡒 provabilityFormula T φ.val := by
  have h₁ := tprovable_iff_partialTrue (T := T) φ hφ hs;
  have h₂ := tprovable_imp_provabilityFormula_subst (T := T) (partialTrue 𝚺 1) φ.val;
  have h₃ := tprovable_provabilityFormula <| tprovable_iff_provable.mp <| Entailment.K_right h₁;
  have h₄ := tprovable_provabilityFormula_imp (T := T)
    ((⌜(partialTrue 𝚺 1).val⌝ : Semiformula V ℒₒᵣ 1).subst ![𝕹 φ.val]) φ;
  cl_prover [h₁, h₂, h₃, h₄]

end Bootstrapping
end FFL.FirstOrder.Arithmetic
