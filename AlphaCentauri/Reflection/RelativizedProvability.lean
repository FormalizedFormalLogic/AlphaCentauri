module

public import AlphaCentauri.Bootstrapping.PartialTruth.Snowing
public import AlphaCentauri.Reflection.StandardProvability

/-!
# Provability relativized to true $\Pi_n$ sentences

The provability predicate `Prov^n_T(x) := ∃ s (True_{Π_n}(s) ∧ Prov_T(s →̇ x))`, a $\Sigma_{n + 1}$
formula, packaged as a `Provability` structure. For `n = 0` it is definitionally the standard
provability predicate.

- [Bek99, §3]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping ProvabilityAbstraction

variable {T : ArithmeticTheory} [T.Δ₁] {n : ℕ}

/-- The $\Sigma_{n + 1}$ formula `Prov^n_T(x) := ∃ s (True_{Π_n}(s) ∧ Prov_T(s →̇ x))`. For
`n = 0` this is definitionally the standard provability predicate of `T`.
- [Bek99, §3] -/
noncomputable def _root_.FFL.FirstOrder.Theory.relativizedProvabilityPred
    (T : ArithmeticTheory) [T.Δ₁] :
    (n : ℕ) → 𝚺-[n + 1].Semisentence 1
  | 0 => provable T
  | n + 1 => .mkSigma
      “x. ∃ s, !(piSatisfaction n).val s 0 ∧ ∃ i, !(impGraph ℒₒᵣ).val i s x ∧ !(provable T).val i”
      (by
        have h1 : Hierarchy 𝚺 (n + 2) (piSatisfaction n).val := (piSatisfaction n).pi_prop.accum 𝚺
        have h2 : Hierarchy 𝚺 (n + 2) (impGraph ℒₒᵣ).val :=
          (impGraph ℒₒᵣ).sigma_prop.mono (by omega)
        have h3 : Hierarchy 𝚺 (n + 2) (provable T).val := (provable T).sigma_prop.mono (by omega)
        simp [h1, h2, h3])

@[simp] lemma relativizedProvabilityPred_zero :
    T.relativizedProvabilityPred 0 = provable T := rfl

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The `V`-relation defined by `relativizedProvabilityPred (n + 1)`: some code `s` of a true
$\Pi_{n + 1}$ sentence has `T`'s standard provability predicate hold of `s →̇ x`. -/
def RelativizedProv (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) (x : V) : Prop :=
  ∃ s, PiSatisfaction (n + 1) s 0 ∧ ∃ i, Bootstrapping.imp ℒₒᵣ s x = i ∧ Provable T i

instance RelativizedProv.defined (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) :
    𝚺-[n + 2]-Predicate[V] (RelativizedProv T n) via T.relativizedProvabilityPred (n + 1) :=
  .mk fun v ↦ by
    simp [RelativizedProv, Theory.relativizedProvabilityPred, (PiSatisfaction.defined n).df,
      (imp.defined (V := V) (L := ℒₒᵣ)).df, (Provable.defined (T := T) (V := V)).df]

end

private lemma quote_imp_sentence {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (σ τ : ArithmeticSentence) :
    (⌜(σ 🡒 τ)⌝ : V) = Bootstrapping.imp ℒₒᵣ (⌜σ⌝ : V) (⌜τ⌝ : V) := by
  simp [Sentence.quote_def, Semiformula.quote_def]

private lemma piSatisfaction_top {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (n : ℕ) :
    PiSatisfaction (n + 1) (⌜(⊤ : ArithmeticSentence)⌝ : V) 0 := by
  have hT : StrictHierarchy 𝚷 (n + 1) (⊤ : ArithmeticSentence) :=
    (StrictHierarchy.zero (show Hierarchy 𝚺 0 (⊤ : ArithmeticSentence) by simp)).mono
      (Nat.zero_le _)
  simpa [matrixToVec] using (piSatisfaction_quote_iff hT Fin.elim0).mpr (by simp)

/-- The derivability condition D1 for `Prov^n_T`. -/
theorem _root_.FFL.FirstOrder.Theory.relativizedProvability_D1
    (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) {σ : ArithmeticSentence} (h : T ⊢ σ) :
    𝗜𝚺₁ ⊢ (T.relativizedProvabilityPred n).val/[⌜σ⌝] := by
  match n with
  | 0 => simpa using provable_D1 h
  | m + 1 =>
    exact complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
      have hTop : T ⊢ (⊤ : ArithmeticSentence) 🡒 σ := by cl_prover [h]
      have hProv : Provable T (⌜((⊤ : ArithmeticSentence) 🡒 σ)⌝ : V) :=
        internalize_provability hTop
      have hProv' :
          Provable T (Bootstrapping.imp ℒₒᵣ (⌜(⊤ : ArithmeticSentence)⌝ : V) (⌜σ⌝ : V)) := by
        rw [← quote_imp_sentence]; exact hProv
      have hTrue : PiSatisfaction (m + 1) (⌜(⊤ : ArithmeticSentence)⌝ : V) 0 :=
        piSatisfaction_top m
      have hRel : RelativizedProv T m (⌜σ⌝ : V) :=
        ⟨⌜(⊤ : ArithmeticSentence)⌝, hTrue,
          Bootstrapping.imp ℒₒᵣ (⌜(⊤ : ArithmeticSentence)⌝ : V) (⌜σ⌝ : V), rfl, hProv'⟩
      simpa [models_iff, (RelativizedProv.defined T m).df] using hRel

/-- Provability relativized to true $\Pi_n$ sentences, as a `Provability 𝗜𝚺₁ T` instance.
- [Bek99, §3] -/
noncomputable def _root_.FFL.FirstOrder.Theory.relativizedProvability
    (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) : Provability 𝗜𝚺₁ T where
  prov := (T.relativizedProvabilityPred n).val
  bew_def h := T.relativizedProvability_D1 n h

/-- The standard provability predicate implies provability relativized to true $\Pi_n$
sentences, over the standard model.
- [Bek99, §3] -/
theorem models_relativizedProvability_of_standardProvability {n : ℕ} {σ : ArithmeticSentence}
    (h : ℕ↓[ℒₒᵣ] ⊧ T.standardProvability σ) :
    ℕ↓[ℒₒᵣ] ⊧ (T.relativizedProvabilityPred n).val/[⌜σ⌝] :=
  models_of_provable inferInstance
    (T.relativizedProvability_D1 n (T.standardProvability.sound_on h))

/-- Provability relativized to true $\Pi_n$ sentences is monotone in `n`, over the standard
model.
- [Bek99, §3] -/
theorem models_relativizedProvability_succ_of_models_relativizedProvability {n : ℕ}
    {σ : ArithmeticSentence} (h : ℕ↓[ℒₒᵣ] ⊧ (T.relativizedProvabilityPred n).val/[⌜σ⌝]) :
    ℕ↓[ℒₒᵣ] ⊧ (T.relativizedProvabilityPred (n + 1)).val/[⌜σ⌝] := by
  match n with
  | 0 => exact models_relativizedProvability_of_standardProvability h
  | m + 1 =>
    have hRel : RelativizedProv T m (⌜σ⌝ : ℕ) := by
      simpa [models_iff, (RelativizedProv.defined T m).df] using h
    obtain ⟨s, hs, i, hi, hProv⟩ := hRel
    have hDvd : ℕ↓[ℒₒᵣ] ⊧ (T.relativizedProvabilityPred (m + 2)).val/[⌜σ⌝] := by
      have hTrue : PiSatisfaction (m + 2) s 0 :=
        (PiSatisfaction.mono (by omega) hs.dom.1 hs.dom.2).mp hs
      have hRel' : RelativizedProv T (m + 1) (⌜σ⌝ : ℕ) := ⟨s, hTrue, i, hi, hProv⟩
      simpa [models_iff, (RelativizedProv.defined T (m + 1)).df] using hRel'
    simpa using hDvd

/-- If some true $\Pi_{n + 1}$ sentence `π` witnesses `T ⊢ π → σ`, then `Prov^{n + 1}_T(σ)` holds
in the standard model.
- [Bek99, §3] -/
theorem models_relativizedProvability_of_true_pi {m : ℕ} {π σ : ArithmeticSentence}
    (hπ : StrictHierarchy 𝚷 (m + 1) π) (hπtrue : ℕ↓[ℒₒᵣ] ⊧ π) (h : T ⊢ π 🡒 σ) :
    ℕ↓[ℒₒᵣ] ⊧ (T.relativizedProvabilityPred (m + 1)).val/[⌜σ⌝] := by
  have hTrue : PiSatisfaction (m + 1) (⌜π⌝ : ℕ) 0 := by
    simpa [matrixToVec] using (piSatisfaction_quote_iff hπ ![]).mpr
      (by simpa [models_iff] using hπtrue)
  have hProv : Provable T (⌜(π 🡒 σ)⌝ : ℕ) := provable_iff_provable.mpr h
  have hProv' : Provable T (Bootstrapping.imp ℒₒᵣ (⌜π⌝ : ℕ) (⌜σ⌝ : ℕ)) := by
    rw [← quote_imp_sentence]; exact hProv
  have hRel : RelativizedProv T m (⌜σ⌝ : ℕ) :=
    ⟨⌜π⌝, hTrue, Bootstrapping.imp ℒₒᵣ (⌜π⌝ : ℕ) (⌜σ⌝ : ℕ), rfl, hProv'⟩
  simpa [models_iff, (RelativizedProv.defined T m).df] using hRel

end FFL.FirstOrder.Arithmetic

