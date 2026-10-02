module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.General
public import AlphaCentauri.Reflection.StandardProvability

/-!
# Provability relativized to true $\Pi_n$ sentences

The provability predicate `Prov^n_T(x) := ∃ s (True_{Π_n}(s) ∧ Prov_T(s →̇ x))`, a $\Sigma_{n + 1}$
formula, packaged as a `Provability` structure. The truth predicate `True_{Π_n}` is read
cumulatively: `s` codes a true prenex $\Pi_k$ sentence for some `1 ≤ k ≤ n`, the case `k = 0`
being `Prov_T(x)` itself. For `n = 0` it is definitionally the standard provability predicate.

- [Bek99, §3]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping ProvabilityAbstraction

variable (T : ArithmeticTheory) [T.Δ₁] {n : ℕ}

/-- The $\Sigma_{n + 1}$ formula `Prov^n_T(x)`: `Prov^0_T` is the standard provability predicate of
`T`, and `Prov^{n + 1}_T(x) := Prov^n_T(x) ∨ ∃ s (True_{Π_{n + 1}}(s) ∧ Prov_T(s →̇ x))`, with
`True_{Π_{n + 1}}` the partial truth predicate for prenex $\Pi_{n + 1}$ sentences.
- [Bek99, §3] -/
noncomputable def _root_.FFL.FirstOrder.Theory.relativizedProvabilityPred :
    (n : ℕ) → 𝚺ᴬ-[n + 1].Semisentence 1
  | 0 => provable T
  | n + 1 => .mkSigma
      “x. !(Theory.relativizedProvabilityPred n).val x ∨
        ∃ s, !(partialTruth 𝚷 (n + 1)).val s ∧ ∃ i, !(impGraph ℒₒᵣ).val i s x ∧
          !(provable T).val i”
      (by
        have h0 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (n + 2) (Theory.relativizedProvabilityPred n).val :=
          (Theory.relativizedProvabilityPred n).sigma_prop.mono (by omega)
        have h1 := (partialTruth 𝚷 (n + 1)).pi_prop.accum 𝚺
        have h2 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (n + 2) (impGraph ℒₒᵣ).val :=
          (impGraph ℒₒᵣ).sigma_prop.mono (by omega)
        have h3 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (n + 2) (provable T).val :=
          (provable T).sigma_prop.mono (by omega)
        simp [h0, h1, h2, h3])

@[simp] lemma relativizedProvabilityPred_zero :
    T.relativizedProvabilityPred 0 = provable T := rfl

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The `V`-relation defined by `relativizedProvabilityPred n`: `x` is provable in `T`, or follows
in `T` from the code of a true prenex $\Pi_k$ sentence for some `1 ≤ k ≤ n`. -/
def RelativizedProv : ℕ → V → Prop
  | 0, x => Provable T x
  | n + 1, x => RelativizedProv n x ∨ ∃ s, PartialTruth 𝚷 (n + 1) s ∧ Provable T (imp ℒₒᵣ s x)

instance RelativizedProv.defined : (n : ℕ) →
    𝚺ᴬ-[n + 1]-Predicate[V] (RelativizedProv T n) via T.relativizedProvabilityPred n
  | 0 => Provable.defined
  | n + 1 => .mk fun v ↦ by
    simp [RelativizedProv, Theory.relativizedProvabilityPred, (RelativizedProv.defined n).df,
      (PartialTruth.pi_defined (V := V) (n + 1)).df, (imp.defined (V := V) (L := ℒₒᵣ)).df,
      (Provable.defined (T := T) (V := V)).df]

lemma RelativizedProv.of_provable {x : V} (h : Provable T x) : ∀ n, RelativizedProv T n x
  | 0 => h
  | n + 1 => Or.inl (of_provable h n)

end

@[simp] private lemma quote_imp_sentence {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (σ τ : ArithmeticSentence) :
    (⌜(σ 🡒 τ)⌝ : V) = Bootstrapping.imp ℒₒᵣ (⌜σ⌝ : V) (⌜τ⌝ : V) := by
  simp [Sentence.quote_def, Semiformula.quote_def]

/-- If some true prenex $\Pi_{n + 1}$ sentence `π` witnesses `T ⊢ π → σ`, then `Prov^{n + 1}_T(σ)`
holds. -/
private lemma relativizedProv_of_pi {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (n : ℕ) {π σ : ArithmeticSentence} (hπ : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 1) π)
    (hπtrue : V↓[ℒₒᵣ] ⊧ π) (h : T ⊢ π 🡒 σ) : RelativizedProv T (n + 1) (⌜σ⌝ : V) := by
  obtain ⟨φ, rfl⟩ := hπ
  exact Or.inr ⟨⌜φ.val⌝, (partialTruth_quote_iff φ).mpr hπtrue,
    by simpa using internalize_provability (V := V) h⟩

/-- The derivability condition D1 for `Prov^n_T`. -/
theorem _root_.FFL.FirstOrder.Theory.relativizedProvability_D1
    (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) {σ : ArithmeticSentence} (h : T ⊢ σ) :
    𝗜𝚺₁ ⊢ (T.relativizedProvabilityPred n).val/[⌜σ⌝] :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff, (RelativizedProv.defined T n).df] using
      RelativizedProv.of_provable T (internalize_provability (V := V) h) n

/-- Provability relativized to true $\Pi_n$ sentences, as a `Provability 𝗜𝚺₁ T` instance.
- [Bek99, §3] -/
noncomputable def _root_.FFL.FirstOrder.Theory.relativizedProvability
    (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) : Provability 𝗜𝚺₁ T where
  prov := (T.relativizedProvabilityPred n).val
  bew_def h := T.relativizedProvability_D1 n h

/-- The standard provability predicate implies provability relativized to true $\Pi_n$
sentences, over the standard model.
- [Bek99, §3] -/
theorem models_relativizedProvability_of_standardProvability {σ : ArithmeticSentence}
    (h : ℕ↓[ℒₒᵣ] ⊧ T.standardProvability σ) :
    ℕ↓[ℒₒᵣ] ⊧ (T.relativizedProvabilityPred n).val/[⌜σ⌝] :=
  models_of_provable inferInstance
    (T.relativizedProvability_D1 n (T.standardProvability.sound_on h))

/-- Provability relativized to true $\Pi_n$ sentences is monotone in `n`, over the standard
model.
- [Bek99, §3] -/
theorem models_relativizedProvability_succ_of_models_relativizedProvability
    {σ : ArithmeticSentence} (h : ℕ↓[ℒₒᵣ] ⊧ (T.relativizedProvabilityPred n).val/[⌜σ⌝]) :
    ℕ↓[ℒₒᵣ] ⊧ (T.relativizedProvabilityPred (n + 1)).val/[⌜σ⌝] := by
  have hRel : RelativizedProv T (n + 1) (⌜σ⌝ : ℕ) :=
    Or.inl <| by simpa [models_iff, (RelativizedProv.defined T n).df] using h
  simpa [models_iff, (RelativizedProv.defined T (n + 1)).df] using hRel

/-- If some true prenex $\Pi_{m + 1}$ sentence `π` witnesses `T ⊢ π → σ`, then `Prov^{m + 1}_T(σ)`
holds in the standard model.
- [Bek99, §3] -/
theorem models_relativizedProvability_of_true_pi {m : ℕ} {π σ : ArithmeticSentence}
    (hπ : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (m + 1) π) (hπtrue : ℕ↓[ℒₒᵣ] ⊧ π) (h : T ⊢ π 🡒 σ) :
    ℕ↓[ℒₒᵣ] ⊧ (T.relativizedProvabilityPred (m + 1)).val/[⌜σ⌝] := by
  simpa [models_iff, (RelativizedProv.defined T (m + 1)).df] using
    relativizedProv_of_pi T m hπ hπtrue h

section
variable [𝗜𝚺₁ ⪯ T]

/-- A true $\Pi_n$ sentence witnesses its own relativized provability: formalized $\Sigma_{n + 1}$
completeness restricted to sentences that are themselves prenex $\Pi_n$.
- [Bek99, Lemma 3.1(1)] -/
theorem relativizedProvability_formalizedCompleteOn_of_pi (n : ℕ) {σ : ArithmeticSentence}
    (hσ : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 n σ) :
    𝗜𝚺₁ ⊢ σ 🡒 T.relativizedProvability n σ := by
  match n with
  | 0 =>
    have h1 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 σ := (Bounding.PrenexHierarchy.zero_iff.mp hσ).of_zero
    simpa [Theory.relativizedProvability, Provability.pr] using
      provable_sigma_one_complete (T := T) h1
  | m + 1 =>
    exact complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
      simp only [models_iff, LogicalConnective.HomClass.map_imply]
      intro hVσ
      have hProv : T ⊢ σ 🡒 σ := by cl_prover
      simpa [Theory.relativizedProvability, Provability.pr,
        (RelativizedProv.defined T (m + 1)).df] using relativizedProv_of_pi T m hσ hVσ hProv

end

/-- Raising the level of the relativization is provable: `𝗜𝚺₁` proves that what `Prov^n_T` proves,
`Prov^(n + 1)_T` proves.
- [Bek99, Lemma 3.1(2)] -/
theorem provable_relativizedProvability_succ_of_relativizedProvability (n : ℕ)
    {σ : ArithmeticSentence} :
    𝗜𝚺₁ ⊢ T.relativizedProvability n σ 🡒 T.relativizedProvability (n + 1) σ :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simp only [models_iff, LogicalConnective.HomClass.map_imply]
    intro hVσ
    have hRel : RelativizedProv T (n + 1) (⌜σ⌝ : V) :=
      Or.inl <| by
        simpa [Theory.relativizedProvability, Provability.pr,
          (RelativizedProv.defined T n).df] using hVσ
    simpa [Theory.relativizedProvability, Provability.pr,
      (RelativizedProv.defined T (n + 1)).df] using hRel

/-- Raising the level of the relativization to any higher one is provable.
- [Bek99, Lemma 3.1(2)] -/
theorem provable_relativizedProvability_of_le [𝗜𝚺₁ ⪯ T] {n m : ℕ} (hnm : n ≤ m)
    {σ : ArithmeticSentence} :
    𝗜𝚺₁ ⊢ T.relativizedProvability n σ 🡒 T.relativizedProvability m σ := by
  induction m, hnm using Nat.le_induction with
  | base => cl_prover
  | succ m _ ih =>
    have h := provable_relativizedProvability_succ_of_relativizedProvability T m (σ := σ)
    cl_prover [ih, h]

end FFL.FirstOrder.Arithmetic
