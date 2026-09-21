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

variable (T : ArithmeticTheory) [T.Δ₁] {n : ℕ}

/-- The $\Sigma_{n + 1}$ formula `Prov^n_T(x) := ∃ s (True_{Π_n}(s) ∧ Prov_T(s →̇ x))`. For
`n = 0` this is definitionally the standard provability predicate of `T`.
- [Bek99, §3] -/
noncomputable def _root_.FFL.FirstOrder.Theory.relativizedProvabilityPred :
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
def RelativizedProv (n : ℕ) (x : V) : Prop :=
  ∃ s, PiSatisfaction (n + 1) s 0 ∧ ∃ i, Bootstrapping.imp ℒₒᵣ s x = i ∧ Provable T i

instance RelativizedProv.defined (n : ℕ) :
    𝚺-[n + 2]-Predicate[V] (RelativizedProv T n) via T.relativizedProvabilityPred (n + 1) :=
  .mk fun v ↦ by
    simp [RelativizedProv, Theory.relativizedProvabilityPred, (PiSatisfaction.defined n).df,
      (imp.defined (V := V) (L := ℒₒᵣ)).df, (Provable.defined (T := T) (V := V)).df]

end

@[simp] private lemma quote_imp_sentence {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (σ τ : ArithmeticSentence) :
    (⌜(σ 🡒 τ)⌝ : V) = Bootstrapping.imp ℒₒᵣ (⌜σ⌝ : V) (⌜τ⌝ : V) := by
  simp [Sentence.quote_def, Semiformula.quote_def]

/-- `⊤` lies at every level of the $\Pi$ hierarchy. -/
private lemma top_strictHierarchy_pi (n : ℕ) : StrictHierarchy 𝚷 n (⊤ : ArithmeticSentence) :=
  (StrictHierarchy.of_bounded (φ := (⊤ : ArithmeticSentence)) (by simp)).mono (Nat.zero_le _)

/-- A true strict $\Pi_{n + 1}$ sentence's code satisfies the level-$(n + 1)$ partial truth
predicate. -/
private lemma piSatisfaction_of_pi {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {n : ℕ} {π : ArithmeticSentence} (hπ : StrictHierarchy 𝚷 (n + 1) π)
    (hπtrue : V↓[ℒₒᵣ] ⊧ π) : PiSatisfaction (n + 1) (⌜π⌝ : V) 0 := by
  simpa [matrixToVec] using
    (piSatisfaction_quote_iff hπ ![]).mpr (by simpa [models_iff] using hπtrue)

private lemma piSatisfaction_top {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (n : ℕ) :
    PiSatisfaction (n + 1) (⌜(⊤ : ArithmeticSentence)⌝ : V) 0 :=
  piSatisfaction_of_pi (top_strictHierarchy_pi (n + 1)) (by simp)

/-- If `T` proves `Provable T ⌜π 🡒 σ⌝` for some true strict $\Pi_{n + 1}$ sentence `π`, then
`Prov^n_T(σ)` holds. -/
private lemma relativizedProv_of_provable_imp {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (n : ℕ) {π σ : ArithmeticSentence}
    (hπ : StrictHierarchy 𝚷 (n + 1) π) (hπtrue : V↓[ℒₒᵣ] ⊧ π)
    (hProv : Provable T (⌜(π 🡒 σ)⌝ : V)) : RelativizedProv T n (⌜σ⌝ : V) :=
  ⟨⌜π⌝, piSatisfaction_of_pi hπ hπtrue, _, rfl, by simpa using hProv⟩

/-- If some true strict $\Pi_{n + 1}$ sentence `π` witnesses `T ⊢ π → σ`, then `Prov^n_T(σ)`
holds. -/
private lemma relativizedProv_of_pi {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (n : ℕ) {π σ : ArithmeticSentence}
    (hπ : StrictHierarchy 𝚷 (n + 1) π) (hπtrue : V↓[ℒₒᵣ] ⊧ π) (h : T ⊢ π 🡒 σ) :
    RelativizedProv T n (⌜σ⌝ : V) :=
  relativizedProv_of_provable_imp T n hπ hπtrue (internalize_provability h)

/-- `Prov^n_T` is monotone in `n`. -/
private lemma relativizedProv_succ_of_relativizedProv {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {x : V}
    (h : RelativizedProv T n x) : RelativizedProv T (n + 1) x := by
  obtain ⟨s, hs, i, hi, hProv⟩ := h
  exact ⟨s, (PiSatisfaction.mono (by omega) hs.dom.1 hs.dom.2).mp hs, i, hi, hProv⟩

/-- The derivability condition D1 for `Prov^n_T`. -/
theorem _root_.FFL.FirstOrder.Theory.relativizedProvability_D1
    (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) {σ : ArithmeticSentence} (h : T ⊢ σ) :
    𝗜𝚺₁ ⊢ (T.relativizedProvabilityPred n).val/[⌜σ⌝] := by
  match n with
  | 0 => simpa using provable_D1 h
  | m + 1 =>
    exact complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
      have hTop : T ⊢ (⊤ : ArithmeticSentence) 🡒 σ := by cl_prover [h]
      have hRel : RelativizedProv T m (⌜σ⌝ : V) :=
        relativizedProv_of_pi T m (top_strictHierarchy_pi (m + 1)) (by simp) hTop
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
  match n with
  | 0 => exact models_relativizedProvability_of_standardProvability T h
  | m + 1 =>
    have hRel : RelativizedProv T m (⌜σ⌝ : ℕ) := by
      simpa [models_iff, (RelativizedProv.defined T m).df] using h
    simpa [models_iff, (RelativizedProv.defined T (m + 1)).df] using
      relativizedProv_succ_of_relativizedProv T hRel

/-- If some true $\Pi_{n + 1}$ sentence `π` witnesses `T ⊢ π → σ`, then `Prov^{n + 1}_T(σ)` holds
in the standard model.
- [Bek99, §3] -/
theorem models_relativizedProvability_of_true_pi {m : ℕ} {π σ : ArithmeticSentence}
    (hπ : StrictHierarchy 𝚷 (m + 1) π) (hπtrue : ℕ↓[ℒₒᵣ] ⊧ π) (h : T ⊢ π 🡒 σ) :
    ℕ↓[ℒₒᵣ] ⊧ (T.relativizedProvabilityPred (m + 1)).val/[⌜σ⌝] :=
  have hRel : RelativizedProv T m (⌜σ⌝ : ℕ) := relativizedProv_of_pi T m hπ hπtrue h
  by simpa [models_iff, (RelativizedProv.defined T m).df] using hRel

section
variable [𝗜𝚺₁ ⪯ T]

/-- A true $\Pi_n$ sentence witnesses its own relativized provability: formalized $\Sigma_{n + 1}$
completeness restricted to sentences that are themselves strict $\Pi_n$.
- [Bek99, Lemma 3.1(1)] -/
theorem relativizedProvability_formalizedCompleteOn_of_pi (n : ℕ) {σ : ArithmeticSentence}
    (hσ : StrictHierarchy 𝚷 n σ) :
    𝗜𝚺₁ ⊢ σ 🡒 T.relativizedProvability n σ := by
  match n with
  | 0 =>
    have h1 : Hierarchy 𝚺 1 σ := hσ.hierarchy.of_zero
    simpa [Theory.relativizedProvability, Provability.pr] using
      provable_sigma_one_complete (T := T) h1
  | m + 1 =>
    exact complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
      simp only [models_iff, LogicalConnective.HomClass.map_imply]
      intro hVσ
      have hProv : T ⊢ σ 🡒 σ := by cl_prover
      have hRel : RelativizedProv T m (⌜σ⌝ : V) := relativizedProv_of_pi T m hσ hVσ hProv
      simpa [Theory.relativizedProvability, Provability.pr,
        (RelativizedProv.defined T m).df] using hRel

end

/-- Raising the level of the relativization is provable: `𝗜𝚺₁` proves that what `Prov^n_T` proves,
`Prov^(n + 1)_T` proves.
- [Bek99, Lemma 3.1(2)] -/
theorem provable_relativizedProvability_succ_of_relativizedProvability (n : ℕ)
    {σ : ArithmeticSentence} :
    𝗜𝚺₁ ⊢ T.relativizedProvability n σ 🡒 T.relativizedProvability (n + 1) σ := by
  match n with
  | 0 =>
    exact complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
      simp only [models_iff, LogicalConnective.HomClass.map_imply]
      intro hVσ
      have hVσ' : Provable T (⌜σ⌝ : V) := by
        simpa [Theory.relativizedProvability, Provability.pr] using hVσ
      have hTop : T ⊢ σ 🡒 ((⊤ : ArithmeticSentence) 🡒 σ) := by cl_prover
      have hProvImp : Provable T (⌜(σ 🡒 ((⊤ : ArithmeticSentence) 🡒 σ))⌝ : V) :=
        internalize_provability hTop
      have hProv'' : Provable T (⌜((⊤ : ArithmeticSentence) 🡒 σ)⌝ : V) :=
        Bootstrapping.modus_ponens_sentence T hProvImp hVσ'
      have hRel : RelativizedProv T 0 (⌜σ⌝ : V) :=
        relativizedProv_of_provable_imp T 0 (top_strictHierarchy_pi 1) (by simp) hProv''
      simpa [Theory.relativizedProvability, Provability.pr,
        (RelativizedProv.defined T 0).df] using hRel
  | m + 1 =>
    exact complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
      simp only [models_iff, LogicalConnective.HomClass.map_imply]
      intro hVσ
      have hRel : RelativizedProv T m (⌜σ⌝ : V) := by
        simpa [Theory.relativizedProvability, Provability.pr,
          (RelativizedProv.defined T m).df] using hVσ
      simpa [Theory.relativizedProvability, Provability.pr,
        (RelativizedProv.defined T (m + 1)).df] using
        relativizedProv_succ_of_relativizedProv T hRel

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

