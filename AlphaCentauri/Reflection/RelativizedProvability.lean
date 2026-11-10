module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.General
public import AlphaCentauri.Reflection.StandardProvability
public import AlphaCentauri.ToFoundation.Provable

/-!
# Provability relativized to true $\Pi_n$ sentences

The provability predicate `Prov^n_T(x)` of `T` extended by the true $\Pi_n$ sentences, a
$\Sigma_{n + 1}$ formula packaged as a `Provability 𝗜𝚺₁ T` satisfying the Hilbert–Bernays–Löb
derivability conditions and formalized $\Sigma_{n + 1}$-completeness. For `n = 0` it is
definitionally the standard provability predicate. For `n + 1`, the true $\Pi_{n+1}$ sentences
enter as a finite set `c` of tagged satisfied prenex formulas `⟪k + 1, θ, e⟫`, `k ≤ n`, and
`Prov^{n + 1}_T(x)` says that `T` proves `x` from the formula stating this of `c`.

- [Bek99, §3]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping Bootstrapping.Arithmetic ProvabilityAbstraction

section hypothesis

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `p = ⟪k, θ, e⟫` with the prenex $\Pi_k$ formula of matrix `θ` satisfied under `e`. -/
def TaggedPrenexSatisfied (k : ℕ) (p : V) : Prop :=
  ∃ θ e, p = ⟪(k : V), θ, e⟫ ∧ PrenexSatisfied 𝚷 k e θ

noncomputable def taggedPrenexSatisfied (k : ℕ) [NeZero k] : 𝚷ᴬ_[k].Semisentence 1 := .mkPi
  “p. ∃ θ <⁺ p, ∃ e <⁺ p, !pair₃Def p ↑k θ e ∧ !(prenexSatisfied 𝚷 k).val e θ”
  (by simp [(prenexSatisfied 𝚷 k).pi_prop])

instance TaggedPrenexSatisfied.defined (k : ℕ) [NeZero k] :
    𝚷ᴬ_[k]-Predicate (TaggedPrenexSatisfied k : V → Prop) via taggedPrenexSatisfied k :=
  .mk fun v ↦ by
    suffices (∃ θ ≤ v 0, ∃ e ≤ v 0, v 0 = ⟪(k : V), θ, e⟫ ∧ PrenexSatisfied 𝚷 k e θ) ↔
        TaggedPrenexSatisfied k (v 0) by
      simpa [taggedPrenexSatisfied, (PrenexSatisfied.pi_defined (V := V) k).df,
        numeral_eq_natCast] using this
    constructor
    · rintro ⟨θ, -, e, -, h⟩
      exact ⟨θ, e, h⟩
    · rintro ⟨θ, e, h, hs⟩
      exact ⟨θ, h ▸ (le_pair_left θ e).trans (le_pair_right _ _), e,
        h ▸ (le_pair_right θ e).trans (le_pair_right _ _), h, hs⟩

lemma TaggedPrenexSatisfied.of_eq {k j : ℕ} {p θ e : V} (h : TaggedPrenexSatisfied k p)
    (hp : p = ⟪(j : V), θ, e⟫) : k = j ∧ PrenexSatisfied 𝚷 k e θ := by
  obtain ⟨θ', e', rfl, hs⟩ := h
  obtain ⟨hk, rfl, rfl⟩ : (k : V) = j ∧ θ' = θ ∧ e' = e := by simpa using hp
  exact ⟨by exact_mod_cast hk, hs⟩

/-- `c` is a set of tagged satisfied prenex $\Pi_{k + 1}$ formulas with `k ≤ n`. -/
def RelativizedHypothesis (n : ℕ) (c : V) : Prop :=
  ∀ p ∈ c, ∃ k ≤ n, TaggedPrenexSatisfied (k + 1) p

noncomputable def relativizedHypothesisMember : (n : ℕ) → 𝚷ᴬ_[n + 1].Semisentence 1
  | 0 => taggedPrenexSatisfied 1
  | n + 1 => .mkPi
      “p. !(relativizedHypothesisMember n).val p ∨ !(taggedPrenexSatisfied (n + 2)).val p”
      (by
        have h : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (n + 2) (relativizedHypothesisMember n).val :=
          (relativizedHypothesisMember n).pi_prop.mono (by omega)
        simp [h])

/-- The $\Pi_{n + 1}$ formula defining `RelativizedHypothesis n`. -/
noncomputable def relativizedHypothesis (n : ℕ) : 𝚷ᴬ_[n + 1].Semisentence 1 := .mkPi
  “c. ∀ p ∈' c, !(relativizedHypothesisMember n).val p”

lemma eval_relativizedHypothesisMember : (n : ℕ) → (p : V) →
    V ⊧/![p] (relativizedHypothesisMember n).val ↔ ∃ k ≤ n, TaggedPrenexSatisfied (k + 1) p
  | 0, p => by simp [relativizedHypothesisMember, (TaggedPrenexSatisfied.defined (V := V) 1).df]
  | n + 1, p => by
    simp [relativizedHypothesisMember, eval_relativizedHypothesisMember n,
      (TaggedPrenexSatisfied.defined (V := V) (n + 2)).df, Nat.le_succ_iff]

instance RelativizedHypothesis.defined (n : ℕ) :
    𝚷ᴬ_[n + 1]-Predicate (RelativizedHypothesis n : V → Prop) via relativizedHypothesis n :=
  .mk fun v ↦ by
    simp [relativizedHypothesis, RelativizedHypothesis, eval_relativizedHypothesisMember]

end hypothesis

variable (T : ArithmeticTheory) [T.Δ₁] {n : ℕ}

/-- The $\Sigma_{n + 1}$ formula `Prov^n_T(x)`: `Prov^0_T` is the standard provability predicate
of `T`, and `Prov^{n + 1}_T(x)` says that `T` proves `x` from the formula `H(c̄)` stating that `c`
is a set of tagged satisfied prenex $\Pi_{k + 1}$ formulas with `k ≤ n`, for some `c` for which
this holds.
- [Bek99, §3] -/
noncomputable def _root_.FFL.FirstOrder.Theory.relativizedProvabilityPred :
    (n : ℕ) → 𝚺ᴬ_[n + 1].Semisentence 1
  | 0 => provable T
  | n + 1 => .mkSigma
      “x. ∃ c, !(relativizedHypothesis n).val c ∧
        ∃ h, !ssnum h !!(⌜(relativizedHypothesis n).val⌝) c ∧ ∃ i, !(impGraph ℒₒᵣ).val i h x ∧
          !(provable T).val i”
      (by
        have h0 := (relativizedHypothesis n).pi_prop.accum 𝚺
        have h1 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (n + 2) ssnum.val := ssnum.sigma_prop.mono (by omega)
        have h2 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (n + 2) (impGraph ℒₒᵣ).val :=
          (impGraph ℒₒᵣ).sigma_prop.mono (by omega)
        have h3 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (n + 2) (provable T).val :=
          (provable T).sigma_prop.mono (by omega)
        simp [h0, h1, h2, h3])

@[simp] lemma relativizedProvabilityPred_zero :
    T.relativizedProvabilityPred 0 = provable T := rfl

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The `V`-relation defined by `relativizedProvabilityPred n`. -/
def RelativizedProv : ℕ → V → Prop
  | 0, x => Provable T x
  | n + 1, x => ∃ c, RelativizedHypothesis n c ∧
      Provable T (imp ℒₒᵣ (substNumeral ⌜(relativizedHypothesis n).val⌝ c) x)

instance RelativizedProv.defined : (n : ℕ) →
    𝚺ᴬ_[n + 1]-Predicate[V] (RelativizedProv T n) via T.relativizedProvabilityPred n
  | 0 => Provable.defined
  | n + 1 => .mk fun v ↦ by
    simp [RelativizedProv, Theory.relativizedProvabilityPred,
      (RelativizedHypothesis.defined (V := V) n).df, (imp.defined (V := V) (L := ℒₒᵣ)).df,
      (Provable.defined (T := T) (V := V)).df, (substNumeral.defined (V := V)).df]

/-- The internal formula `H(c̄)`: `relativizedHypothesis n` at the numeral of `c`. -/
noncomputable abbrev hypothesisFormula (n : ℕ) (c : V) : Bootstrapping.Formula V ℒₒᵣ :=
  (⌜(relativizedHypothesis n).val⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1).subst ![𝕹 c]

variable {T}

lemma relativizedProv_succ_iff {σ : ArithmeticSentence} :
    RelativizedProv T (n + 1) (⌜σ⌝ : V) ↔
      ∃ c : V, RelativizedHypothesis n c ∧ T.internalize V ⊢ hypothesisFormula n c 🡒 ⌜σ⌝ := by
  simp [RelativizedProv, tprovable_iff_provable, substNumeral, Sentence.quote_eq]

lemma RelativizedProv.of_provable {σ : ArithmeticSentence} (h : Provable T (⌜σ⌝ : V)) :
    ∀ n, RelativizedProv T n (⌜σ⌝ : V)
  | 0 => h
  | _ + 1 => relativizedProv_succ_iff.mpr ⟨0, fun p hp ↦ by simp [← emptyset_def] at hp,
      Entailment.C_of_conseq (tprovable_tquote_iff_provable_quote_sentence.mpr h)⟩

variable [𝗜𝚺₁ ⪯ T]

/-- No element of `c` is tagged `m + 2`. -/
private noncomputable def noTag (m : ℕ) : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
  “c. ∀ p ∈' c, ∀ θ <⁺ p, ∀ e <⁺ p, ¬!pair₃Def p ↑(m + 2) θ e”

lemma RelativizedProv.succ {σ : ArithmeticSentence} :
    ∀ {n}, RelativizedProv T n (⌜σ⌝ : V) → RelativizedProv T (n + 1) (⌜σ⌝ : V)
  | 0, h => RelativizedProv.of_provable h 1
  | m + 1, h => by
    obtain ⟨c, hc, hσ⟩ := relativizedProv_succ_iff.mp h
    refine relativizedProv_succ_iff.mpr ⟨c, fun p hp ↦ ?_, ?_⟩
    · obtain ⟨k, hk, hp⟩ := hc p hp
      exact ⟨k, by omega, hp⟩
    have hno := tprovable_subst_numeral_of_sigma1 (T := T) (noTag m).sigma_prop (w := ![c]) (by
      suffices ∀ p ∈ c, ∀ θ ≤ p, ∀ e ≤ p, p ≠ ⟪((m + 2 : ℕ) : V), θ, e⟫ by
        simpa [noTag, numeral_eq_natCast] using this
      intro p hp θ _ e _ he
      obtain ⟨k, hk, hp⟩ := hc p hp
      have := (hp.of_eq he).1
      omega)
    have hstd := tprovable_subst_numeral_of_models (T := T)
      (φ := “c. !(noTag m).val c → !(relativizedHypothesis (m + 1)).val c →
        !(relativizedHypothesis m).val c”) (by
      intro W _ _ e
      suffices (∀ p ∈ e 0, ∀ θ ≤ p, ∀ x ≤ p, p ≠ ⟪((m + 2 : ℕ) : W), θ, x⟫) →
          RelativizedHypothesis (m + 1) (e 0) → RelativizedHypothesis m (e 0) by
        simpa [noTag, (RelativizedHypothesis.defined (V := W) _).df, numeral_eq_natCast] using this
      intro hn hc p hp
      obtain ⟨k, hk, θ, x, rfl, hs⟩ := hc p hp
      rcases Nat.lt_or_ge k (m + 1) with hk' | hk'
      · exact ⟨k, by omega, θ, x, rfl, hs⟩
      · exact absurd (by rw [show k = m + 1 by omega]) (hn _ hp θ
          ((le_pair_left θ x).trans (le_pair_right _ _)) x
          ((le_pair_right θ x).trans (le_pair_right _ _)))) ![c]
    simp [Matrix.constant_eq_singleton] at hno hstd
    simpa [hypothesisFormula] using Entailment.C_trans (hstd ⨀ hno) hσ

lemma tprovable_hypothesisFormula_of_subset {c d : V} (h : c ⊆ d) :
    T.internalize V ⊢ hypothesisFormula n d 🡒 hypothesisFormula n c := by
  have hs := tprovable_subst_numeral_of_sigma1 (T := T) (φ := bitSubsetDef.val) (by simp)
    (w := ![c, d]) (by simpa using h)
  have hstd := tprovable_subst_numeral_of_models (T := T)
    (φ := “c d. !bitSubsetDef c d → !(relativizedHypothesis n).val d →
      !(relativizedHypothesis n).val c”) (by
    intro W _ _ e
    suffices e 0 ⊆ e 1 → RelativizedHypothesis n (e 1) → RelativizedHypothesis n (e 0) by
      simpa [(RelativizedHypothesis.defined (V := W) _).df] using this
    exact fun hs h p hp ↦ h p (hs hp)) ![c, d]
  simp only [Sentence.typed_quote_def, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
    LCWQIsoGödelQuote.imply, Rewriting.emb_subst_eq_subst_emb, Semiformula.typed_quote_substs,
    Fin.Fin1.eq_one, Matrix.cons_val_fin_one, Rew.emb_bvar, Semiterm.typed_quote_bvar,
    Semiformula.substs_imp, Semiformula.substs_substs, Matrix.vecMap_cons', Matrix.vecHead,
    Matrix.cons_val_zero, Semiterm.substs_bvar, Matrix.vecTail, Function.comp_apply,
    Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.vecMap_nil, hypothesisFormula] at hs hstd ⊢
  exact hstd ⨀ hs

lemma RelativizedProv.modusPonens {σ τ : ArithmeticSentence} :
    ∀ {n}, RelativizedProv T n (⌜σ 🡒 τ⌝ : V) → RelativizedProv T n (⌜σ⌝ : V) →
      RelativizedProv T n (⌜τ⌝ : V)
  | 0, h₁, h₂ => modus_ponens_sentence T h₁ h₂
  | n + 1, h₁, h₂ => by
    obtain ⟨c₁, hc₁, hστ⟩ := relativizedProv_succ_iff.mp h₁
    obtain ⟨c₂, hc₂, hσ⟩ := relativizedProv_succ_iff.mp h₂
    refine relativizedProv_succ_iff.mpr ⟨c₁ ∪ c₂, fun p hp ↦ ?_, ?_⟩
    · rcases mem_cup_iff.mp hp with hp | hp
      exacts [hc₁ p hp, hc₂ p hp]
    have e₁ := tprovable_hypothesisFormula_of_subset (T := T) (n := n)
      (show c₁ ⊆ c₁ ∪ c₂ from fun _ hp ↦ mem_cup_iff.mpr (Or.inl hp))
    have e₂ := tprovable_hypothesisFormula_of_subset (T := T) (n := n)
      (show c₂ ⊆ c₁ ∪ c₂ from fun _ hp ↦ mem_cup_iff.mpr (Or.inr hp))
    have hστ' : T.internalize V ⊢ hypothesisFormula n c₁ 🡒 (⌜σ⌝ 🡒 ⌜τ⌝) := by simpa using hστ
    exact Entailment.mdp₁ (Entailment.C_trans e₁ hστ') (Entailment.C_trans e₂ hσ)

/-- The $\Sigma_1$ part of `Prov^{n + 1}_T(σ)` for the hypothesis set `c`. -/
private noncomputable def provableFromHypothesis (n : ℕ) (σ : ArithmeticSentence) :
    𝚺ᴬ₁.Semisentence 1 := .mkSigma
  “c. ∃ h, !ssnum h !!(⌜(relativizedHypothesis n).val⌝) c ∧
    ∃ i, !(impGraph ℒₒᵣ).val i h !!(⌜σ⌝) ∧ !(provable T).val i”

omit [𝗜𝚺₁ ⪯ T] in
private lemma eval_provableFromHypothesis {W : Type*} [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (σ : ArithmeticSentence) (v : Fin 1 → W) :
    W ⊧/v (provableFromHypothesis (T := T) n σ).val ↔
      Provable T (imp ℒₒᵣ (substNumeral ⌜(relativizedHypothesis n).val⌝ (v 0)) ⌜σ⌝) := by
  simp [provableFromHypothesis, (imp.defined (V := W) (L := ℒₒᵣ)).df,
    (Provable.defined (T := T) (V := W)).df, (substNumeral.defined (V := W)).df]

lemma RelativizedProv.internalize {σ : ArithmeticSentence} :
    ∀ {n}, RelativizedProv T n (⌜σ⌝ : V) →
      RelativizedProv T n (⌜((T.relativizedProvabilityPred n).val/[⌜σ⌝] : ArithmeticSentence)⌝ : V)
  | 0, h => provable_internalize T h
  | n + 1, h => by
    obtain ⟨c, hc, hσ⟩ := relativizedProv_succ_iff.mp h
    refine relativizedProv_succ_iff.mpr ⟨c, hc, ?_⟩
    have hρ := tprovable_subst_numeral_of_sigma1 (T := T)
      (provableFromHypothesis (T := T) n σ).sigma_prop (w := ![c])
      ((eval_provableFromHypothesis (T := T) σ ![c]).mpr (by
        simpa [tprovable_iff_provable, substNumeral, Sentence.quote_eq] using hσ))
    have hstd := tprovable_subst_numeral_of_models (T := T)
      (φ := “c. !(relativizedHypothesis n).val c → !(provableFromHypothesis (T := T) n σ).val c →
        !(T.relativizedProvabilityPred (n + 1)).val !!(⌜σ⌝)”) (by
      intro W _ _ e
      suffices RelativizedHypothesis n (e 0) →
          Provable T (imp ℒₒᵣ (substNumeral ⌜(relativizedHypothesis n).val⌝ (e 0)) ⌜σ⌝) →
            RelativizedProv T (n + 1) (⌜σ⌝ : W) by
        simpa [(RelativizedHypothesis.defined (V := W) _).df, eval_provableFromHypothesis,
          (RelativizedProv.defined T (n + 1)).df] using this
      exact fun h₁ h₂ ↦ ⟨e 0, h₁, h₂⟩) ![c]
    simp only [Fin.Fin1.eq_one, Fin.isValue, Matrix.cons_val_fin_one, Matrix.constant_eq_singleton,
      Sentence.typed_quote_def, Nat.succ_eq_add_one, Nat.reduceAdd, Rewriting.subst1_bvar0_eq,
      LCWQIsoGödelQuote.imply, Rewriting.emb_subst_eq_subst_emb, rew_gödelNumber',
      Semiformula.typed_quote_substs, Sentence.quote_quote_eq_numeral, Semiformula.substs_imp,
      Semiformula.substs_substs, Matrix.vecMap_cons', Matrix.head_cons, subst_numeral,
      Matrix.tail_cons, Matrix.vecMap_nil, hypothesisFormula] at hρ hstd ⊢
    exact Entailment.mdp₁ hstd (Entailment.C_of_conseq hρ)

/-- `c` contains `⟪n + 1, ⌜θ⌝, y ∷ 0⟫`. -/
private noncomputable def memHypothesis {k : ℕ} (n : ℕ) (θ : ArithmeticSemisentence k) :
    𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “c y. ∃ e, !adjoinDef e y 0 ∧ ∃ p, !pair₃Def p ↑(n + 1) !!(⌜θ⌝) e ∧ p ∈ c”

omit [𝗜𝚺₁ ⪯ T] in
private lemma eval_memHypothesis {W : Type*} [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {k : ℕ}
    (θ : ArithmeticSemisentence k) (v : Fin 2 → W) :
    W ⊧/v (memHypothesis n θ).val ↔ ⟪((n + 1 : ℕ) : W), (⌜θ⌝ : W), v 1 ∷ 0⟫ ∈ v 0 := by
  simp [memHypothesis, numeral_eq_natCast]

/-- A true $\Sigma_{n + 2}$ sentence `∃¹ ψ`, with `ψ` prenex $\Pi_{n + 1}$, is
`Prov^{n + 1}_T`-provable. -/
lemma RelativizedProv.of_sigma (φ : ℬ[<, ℒₒᵣ].Prenex 𝚷 (n + 1) Empty 1)
    {ψ : ArithmeticSemisentence 1} (hψ : φ.val = ψ) {y : V} (hy : V ⊧/![y] ψ) :
    RelativizedProv T (n + 1) (⌜(∃¹ ψ : ArithmeticSentence)⌝ : V) := by
  let c : V := {⟪((n + 1 : ℕ) : V), (⌜φ.matrix.val⌝ : V), y ∷ 0⟫}
  refine relativizedProv_succ_iff.mpr ⟨c, fun p hp ↦ ?_, ?_⟩
  · obtain rfl : p = ⟪((n + 1 : ℕ) : V), (⌜φ.matrix.val⌝ : V), y ∷ 0⟫ := by simpa [c] using hp
    exact ⟨n, le_rfl, _, _, rfl, by simpa using (prenexSatisfied_quote_iff φ ![y]).mpr (hψ ▸ hy)⟩
  have hm := tprovable_subst_numeral_of_sigma1 (T := T) (memHypothesis n φ.matrix.val).sigma_prop
    (w := ![c, y]) (by simp [eval_memHypothesis, c])
  have hstd := tprovable_subst_numeral_of_models (T := T)
    (φ := “c y. !(memHypothesis n φ.matrix.val).val c y → !(relativizedHypothesis n).val c →
      !ψ y”) (by
    intro W _ _ e
    suffices ⟪((n + 1 : ℕ) : W), (⌜φ.matrix.val⌝ : W), e 1 ∷ 0⟫ ∈ e 0 →
        RelativizedHypothesis n (e 0) → W ⊧/![e 1] ψ by
      simpa [eval_memHypothesis, (RelativizedHypothesis.defined (V := W) _).df,
        Matrix.constant_eq_singleton] using this
    intro hmem h
    obtain ⟨k, -, hs⟩ := h _ hmem
    obtain ⟨hk, hs⟩ := hs.of_eq rfl
    obtain rfl : k = n := by omega
    exact hψ ▸ (prenexSatisfied_quote_iff φ ![e 1]).mp (by simpa using hs)) ![c, y]
  have hex := TProof.subst_imp_exs (T := T) (⌜ψ⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1) (𝕹 y)
  simp only [Sentence.typed_quote_def, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
    LCWQIsoGödelQuote.imply, Rewriting.emb_subst_eq_subst_emb, Semiformula.typed_quote_substs,
    Fin.Fin1.eq_one, Matrix.cons_val_fin_one, Rew.emb_bvar, Matrix.constant_eq_singleton,
    Semiterm.typed_quote_bvar, Semiformula.substs_imp, Semiformula.substs_substs,
    Matrix.vecMap_cons', Matrix.vecHead, Matrix.cons_val_zero, Semiterm.substs_bvar,
    Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.cons_val_one,
    Matrix.vecMap_nil, hypothesisFormula, LCWQIsoGödelQuote.exs] at hm hstd hex ⊢
  exact Entailment.C_trans (hstd ⨀ hm) hex

end

/-- The derivability condition D1 for `Prov^n_T`. -/
theorem _root_.FFL.FirstOrder.Theory.relativizedProvability_D1 (n : ℕ) {σ : ArithmeticSentence}
    (h : T ⊢ σ) : 𝗜𝚺₁ ⊢ (T.relativizedProvabilityPred n).val/[⌜σ⌝] :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff, (RelativizedProv.defined T n).df] using
      RelativizedProv.of_provable (internalize_provability (V := V) h) n

/-- Provability relativized to true $\Pi_n$ sentences, as a `Provability 𝗜𝚺₁ T` instance.
- [Bek99, §3] -/
noncomputable def _root_.FFL.FirstOrder.Theory.relativizedProvability (n : ℕ) :
    Provability 𝗜𝚺₁ T where
  prov := (T.relativizedProvabilityPred n).val
  bew_def h := T.relativizedProvability_D1 n h

private lemma models_relativizedProvability_iff {V : Type} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {σ : ArithmeticSentence} :
    V↓[ℒₒᵣ] ⊧ T.relativizedProvability n σ ↔ RelativizedProv T n (⌜σ⌝ : V) := by
  simp [Theory.relativizedProvability, Provability.pr, models_iff,
    (RelativizedProv.defined T n).df]

/-- The standard provability predicate implies provability relativized to true $\Pi_n$
sentences, over the standard model.
- [Bek99, §3] -/
lemma models_relativizedProvability_of_standardProvability {σ : ArithmeticSentence}
    (h : ℕ↓[ℒₒᵣ] ⊧ T.standardProvability σ) :
    ℕ↓[ℒₒᵣ] ⊧ T.relativizedProvability n σ :=
  models_of_provable inferInstance
    (T.relativizedProvability_D1 n (T.standardProvability.sound_on h))

variable [𝗜𝚺₁ ⪯ T]

/-- Raising the level of the relativization is provable: `𝗜𝚺₁` proves that what `Prov^n_T`
proves, `Prov^(n + 1)_T` proves.
- [Bek99, Lemma 3.1(2)] -/
theorem provable_relativizedProvability_succ_of_relativizedProvability (n : ℕ)
    {σ : ArithmeticSentence} :
    𝗜𝚺₁ ⊢ T.relativizedProvability n σ 🡒 T.relativizedProvability (n + 1) σ :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa [models_relativizedProvability_iff] using RelativizedProv.succ (T := T) (V := V)

/-- Raising the level of the relativization to any higher one is provable.
- [Bek99, Lemma 3.1(2)] -/
theorem provable_relativizedProvability_of_le {n m : ℕ} (hnm : n ≤ m) {σ : ArithmeticSentence} :
    𝗜𝚺₁ ⊢ T.relativizedProvability n σ 🡒 T.relativizedProvability m σ := by
  induction m, hnm using Nat.le_induction with
  | base => cl_prover
  | succ m _ ih =>
    have h := provable_relativizedProvability_succ_of_relativizedProvability T m (σ := σ)
    cl_prover [ih, h]

/-- Provability relativized to true $\Pi_n$ sentences is monotone in `n`, over the standard
model.
- [Bek99, §3] -/
theorem models_relativizedProvability_succ_of_models_relativizedProvability
    {σ : ArithmeticSentence} (h : ℕ↓[ℒₒᵣ] ⊧ T.relativizedProvability n σ) :
    ℕ↓[ℒₒᵣ] ⊧ T.relativizedProvability (n + 1) σ :=
  Semantics.Imp.models_imply.mp
    (models_of_provable inferInstance
      (provable_relativizedProvability_succ_of_relativizedProvability T n)) h

/-- Provability relativized to true $\Pi_n$ sentences satisfies the Hilbert–Bernays–Löb
derivability conditions.
- [Bek99, Lemma 3.1(2)] -/
instance : (T.relativizedProvability n).HBL where
  D2 := complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simp only [Semantics.Imp.models_imply, models_relativizedProvability_iff]
    exact RelativizedProv.modusPonens
  D3 := complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simp only [Semantics.Imp.models_imply, models_relativizedProvability_iff]
    exact RelativizedProv.internalize

/-- Formalized $\Sigma_{n + 1}$-completeness of `Prov^n_T`.
- [Bek99, Lemma 3.1(1)] -/
theorem relativizedProvability_formalizedCompleteOn {σ : ArithmeticSentence}
    (hσ : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 (n + 1) σ) :
    (T.relativizedProvability n).FormalizedCompleteOn σ := ⟨by
  match n with
  | 0 =>
    simpa [Theory.relativizedProvability, Provability.pr] using
      provable_sigma_one_complete (T := T) hσ.hierarchy
  | m + 1 =>
    obtain ⟨ψ, ⟨φ, hφ⟩, rfl⟩ := Bounding.PrenexHierarchy.sigma_succ_iff.mp hσ
    exact complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
      simp only [Semantics.Imp.models_imply, models_relativizedProvability_iff]
      intro h
      obtain ⟨y, hy⟩ : ∃ y : V, V ⊧/![y] ψ := by simpa [models_iff] using h
      exact RelativizedProv.of_sigma φ hφ.symm hy⟩

end FFL.FirstOrder.Arithmetic
