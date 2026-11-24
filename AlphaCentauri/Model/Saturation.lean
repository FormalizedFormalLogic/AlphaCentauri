module

public import AlphaCentauri.Model.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions
public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-! # Saturation of nonstandard models of Peano arithmetic

Coded sets, coded types and $\Sigma_n$-recursive saturation of nonstandard models of `𝗣𝗔`.
-/

@[expose] public section

namespace FFL.FirstOrder

open Arithmetic Bootstrapping
open FFL.FirstOrder.Bounding (HierarchySymbol)
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [IsNonstandard M]
  {k m n : ℕ}

namespace Arithmetic

variable {S : Set ℕ}

/-- The standard numbers satisfying a definable predicate form a coded set. -/
lemma setOf_mem_standardSystem {P : M → Prop} (hP : 𝚺ᴬ_[m + 1]-Predicate P) :
    {n : ℕ | P n} ∈ standardSystem M := by
  have : Fact (1 ≤ m + 1) := ⟨by omega⟩
  obtain ⟨d, hd⟩ := Classical.arbitrary (NonstandardElement M)
  obtain ⟨c, _, hc⟩ := finset_comprehension hP d
  use c
  ext n
  exact hc n (hd n)

/-- [Kay91, Lemma 11.1] -/
lemma mem_standardSystem_of_computablePred (hS : ComputablePred (· ∈ S)) :
    S ∈ standardSystem M := by
  have h (n : ℕ) : M ⊧/![(n : M)] (codeOfComputablePred (· ∈ S)) ↔ n ∈ S := by
    constructor
    · contrapose
      intro hn
      simpa [models_iff, Semiformula.eval_substs, Matrix.constant_eq_singleton, numeral_eq_natCast]
        using models_of_provable (M := M) inferInstance
          (codeOfComputablePred_provable_neg (T := 𝗣𝗔⁻) hS hn)
    · intro hn
      simpa [models_iff, Semiformula.eval_substs, Matrix.constant_eq_singleton, numeral_eq_natCast]
        using models_of_provable (M := M) inferInstance
          (codeOfComputablePred_provable (T := 𝗣𝗔⁻) hS hn)
  have h₁ : {n : ℕ | M ⊧/![(n : M)] (codeOfComputablePred (· ∈ S))} ∈ standardSystem M :=
    setOf_mem_standardSystem (m := 0) <|
      Bounding.definablePred_of_hierarchy (codeOfComputablePred_sigma1 (· ∈ S)) Empty.elim
  simpa [h] using h₁

/-- If for every finite subset of a coded set `S` some element is related to all its members by a
definable relation, then some element is related to all members of `S`. -/
lemma exists_forall_of_mem_standardSystem {R : M → M → Prop} (hR : 𝚺ᴬ_[m + 1]-Relation R)
    (hS : S ∈ standardSystem M) (h : ∀ s : Finset ℕ, ↑s ⊆ S → ∃ x : M, ∀ e ∈ s, R x e) :
    ∃ x : M, ∀ e ∈ S, R x e := by
  classical
  obtain ⟨c, rfl⟩ := hS
  let E := natCastProperEndExtension M
  obtain ⟨d, hd, x, hx⟩ := overspill_definablePred E 𝚺 (m + 1)
    (P := fun d ↦ ∃ x, ∀ e < d, e ∈ c → R x e) (by definability) <| by
      intro d
      obtain ⟨x, hx⟩ := h {e ∈ Finset.range d | (e : M) ∈ c} (by intro e; simp)
      use x
      intro e he hec
      obtain ⟨e, rfl⟩ := E.mem_range_of_lt he
      apply hx
      simpa using ⟨E.emb_lt_emb.mp he, hec⟩
  use x
  intro e he
  exact hx e (isNonstandardElement_iff_not_mem_range.mpr hd e) he

/-- `exists_forall_of_mem_standardSystem` for the codes of a set of semisentences. -/
lemma exists_forall_of_setOf_mem_standardSystem {Q : ArithmeticSemisentence k → Prop}
    (hQ : {e : ℕ | ∃ φ, Q φ ∧ ⌜φ⌝ = e} ∈ standardSystem M) {R : M → M → Prop}
    (hR : 𝚺ᴬ_[m + 1]-Relation R)
    (h : ∀ s : Finset (ArithmeticSemisentence k), (∀ φ ∈ s, Q φ) → ∃ x, ∀ φ ∈ s, R x ⌜φ⌝) :
    ∃ x, ∀ φ, Q φ → R x ⌜φ⌝ := by
  classical
  obtain ⟨x, hx⟩ := exists_forall_of_mem_standardSystem hR hQ <| by
    intro s hs
    choose! f hf hfe using fun e (he : e ∈ s) ↦ hs he
    obtain ⟨x, hx⟩ := h (s.image f) (by simpa using hf)
    use x
    intro e he
    have h₁ := hx _ (Finset.mem_image_of_mem f he)
    rwa [← Sentence.coe_quote_eq_quote, hfe e he] at h₁
  use x
  intro φ hφ
  rw [← Sentence.coe_quote_eq_quote]
  apply hx
  use φ

/-- The codes of the prenex $\Sigma_n$ formulas, or prenex $\Pi_n$ formulas, whose code satisfies a
definable predicate form a coded set. -/
lemma setOf_prenexHierarchy_mem_standardSystem (Γ : Polarity) (n l : ℕ) {P : M → Prop}
    (hP : 𝚺ᴬ_[m + 1]-Predicate P) : {e : ℕ | ∃ φ : ArithmeticSemisentence l,
      ℬ[<, ℒₒᵣ].PrenexHierarchy Γ n φ ∧ P ⌜φ⌝ ∧ ⌜φ⌝ = e} ∈ standardSystem M := by
  have hΓ : 𝚺ᴬ_[m + 1]-Predicate (IsPrenexHierarchy Γ n : M → Prop) :=
    (IsPrenexHierarchy.definable Γ n).of_deltaOne
  apply Set.mem_of_eq_of_mem _ <| setOf_mem_standardSystem (m := m)
    (P := fun e ↦ (ℒₒᵣ).IsSemisentence (l : M) e ∧ IsPrenexHierarchy Γ n e ∧ P e) (by definability)
  ext e
  constructor
  · rintro ⟨φ, hφ, h, rfl⟩
    simp [Sentence.coe_quote_eq_quote, h, (isPrenexHierarchy_quote_iff φ).mpr hφ]
  · rintro ⟨he, hφ, h⟩
    obtain ⟨φ, rfl⟩ := he.sound_natCast
    rw [Sentence.coe_quote_eq_quote] at hφ h
    use φ
    and_intros
    · exact (isPrenexHierarchy_quote_iff φ).mp hφ
    · exact h
    · rfl

/-- The prenex $\Sigma_n$ type, or prenex $\Pi_n$ type, of a tuple is a coded set.
- [Kay91, Lemma 12.1] -/
theorem mem_standardSystem_hierarchyType (Γ : Polarity) (n : ℕ) {l : ℕ} (a : Fin l → M) :
    {e : ℕ | ∃ φ : ArithmeticSemisentence l, ℬ[<, ℒₒᵣ].PrenexHierarchy Γ n φ ∧ M ⊧/a φ ∧
      ⌜φ⌝ = e} ∈ standardSystem M := by
  apply Set.mem_of_eq_of_mem _ <| setOf_prenexHierarchy_mem_standardSystem Γ n l (m := n + 1)
    (P := PrenexFormulaSatisfied Γ n (matrixToVec a)) (by definability)
  ext e
  apply exists_congr
  intro φ
  apply and_congr_right
  intro hφ
  rw [PrenexFormulaSatisfied.quote_iff hφ]

end Arithmetic

/-- A type of prenex $\Sigma_n$ formulas, or of prenex $\Pi_n$ formulas, over a nonstandard model
of `𝗣𝗔` is realized when its set of codes is in the standard system.
- [Kay91, Lemma 12.2] -/
theorem «Type».realized_of_mem_standardSystem (Γ : Polarity) (n : ℕ)
    {Φ : FirstOrder.Type ℒₒᵣ (Fin m) k} {b : Fin m → M}
    (hΦ : ∀ φ ∈ Φ, ℬ[<, ℒₒᵣ].PrenexHierarchy Γ n φ)
    (hs : Encodable.encode '' Φ ∈ standardSystem M) (hf : Φ.FinitelySatisfied M b) :
    Φ.Realized M b := by
  classical
  obtain ⟨c, hc⟩ := hs
  let U (σ : ArithmeticSemisentence (k + m)) : ArithmeticSemiformula (Fin m) k :=
    Rew.unbindParams ℒₒᵣ k m ▹ σ
  let w : M := matrixToVec fun i ↦
    ⌜(Fin.append (fun i ↦ #i) (fun j : Fin m ↦ &j) i : SyntacticSemiterm ℒₒᵣ k)⌝
  have hw (σ : ArithmeticSemisentence (k + m)) : subst ℒₒᵣ w ⌜σ⌝ ∈ c ↔ U σ ∈ Φ := by
    rw [← encode_unbindParams, ← mem_codedSet, hc]
    simp [U]
  have hS : {e : ℕ | ∃ σ, U σ ∈ Φ ∧ ⌜σ⌝ = e} ∈ standardSystem M := by
    apply Set.mem_of_eq_of_mem _ <| setOf_mem_standardSystem (m := 0)
      (P := fun e ↦ (ℒₒᵣ).IsSemisentence ((k + m : ℕ) : M) e ∧ subst ℒₒᵣ w e ∈ c) (by definability)
    ext e
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      rw [Set.mem_ofPred, Sentence.coe_quote_eq_quote]
      exact ⟨.quote σ, (hw σ).mpr hσ⟩
    · rintro ⟨he, hσ⟩
      obtain ⟨σ, rfl⟩ := he.sound_natCast
      rw [Sentence.coe_quote_eq_quote] at hσ
      use σ
      and_intros
      · exact (hw σ).mp hσ
      · rfl
  let env (x : M) : M := matrixToVec (Fin.append (fun i : Fin k ↦ x.[((i : ℕ) : M)]) b)
  have henv : 𝚺ᴬ_[n + 2].DefinableFunction₁ env := by
    apply matrixToVec_definable
    intro i
    induction i using Fin.addCases with
    | left i =>
      simp only [Fin.append_left]
      definability
    | right j => simp
  have hR (x : M) {σ : ArithmeticSemisentence (k + m)} (hσ : U σ ∈ Φ) :
      PrenexFormulaSatisfied Γ n (env x) ⌜σ⌝ ↔ (U σ).Eval (fun i ↦ x.[((i : ℕ) : M)]) b := by
    have : ℬ[<, ℒₒᵣ].PrenexHierarchy Γ n σ := by
      simpa [U] using (hΦ _ hσ).rew (Rew.bindParams ℒₒᵣ k m)
    rw [PrenexFormulaSatisfied.quote_iff this, ← Semiformula.eval_bindParams,
      Rew.bindParams_app_unbindParams_app]
  obtain ⟨x, hx⟩ := exists_forall_of_setOf_mem_standardSystem hS
    (R := fun x e ↦ PrenexFormulaSatisfied Γ n (env x) e)
    (HierarchySymbol.DefinableRel.comp inferInstance (henv.comp (by simp)) (by simp)) <| by
      intro s hs
      obtain ⟨a, ha⟩ := hf (s.image U) <| by simpa [Set.subset_def] using hs
      use matrixToVec a
      intro σ hσ
      rw [hR _ (hs σ hσ)]
      simpa using ha _ (Finset.mem_coe.mpr <| Finset.mem_image_of_mem U hσ)
  use fun i ↦ x.[((i : ℕ) : M)]
  intro φ hφ
  have h : U (Rew.bindParams ℒₒᵣ k m ▹ φ) = φ := by simp [U]
  have h₁ := (hR x (h.symm ▸ hφ)).mp (hx _ (h.symm ▸ hφ))
  rwa [h] at h₁

/-- A nonstandard model of `𝗣𝗔` is $\Sigma_n$-recursively saturated.
- [Kay91, Theorem 11.5] -/
theorem sigmaRecursivelySaturated_of_nonstandard (n : ℕ) :
    SigmaRecursivelySaturated M ℬ[<, ℒₒᵣ] n := by
  intro k m Φ b hΦ hr hf
  apply Type.realized_of_mem_standardSystem 𝚺 n hΦ _ hf
  exact mem_standardSystem_of_computablePred hr

end FFL.FirstOrder
