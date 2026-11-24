module

public import AlphaCentauri.Model.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions
public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-! # Saturation of nonstandard models of Peano arithmetic

The standard system of a nonstandard model of `𝗣𝗔` contains every subset of `ℕ` cut out by a
definable predicate of the model, every recursive subset of `ℕ`, and the set of codes of the prenex
$\Sigma_n$ formulas, or of the prenex $\Pi_n$ formulas, satisfied by a tuple. A type over the model
consisting of prenex $\Sigma_n$ formulas, or of prenex $\Pi_n$ formulas, whose set of codes is in
the standard system is realized, and so the model is $\Sigma_n$-recursively saturated for every
$n$.
-/

@[expose] public section

namespace FFL.FirstOrder

open Arithmetic Bootstrapping
open FFL.FirstOrder.Bounding (HierarchySymbol)
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (hM : ∃ c : M, ∀ m : ℕ, (m : M) < c)
  {k m n : ℕ}
include hM

namespace Arithmetic

variable {S : Set ℕ}

/-- The standard numbers satisfying a definable predicate form a coded set. -/
lemma setOf_mem_standardSystem {P : M → Prop} (hP : 𝚺ᴬ_[m + 1]-Predicate P) :
    {n : ℕ | P n} ∈ standardSystem M := by
  have : Fact (1 ≤ m + 1) := ⟨by omega⟩
  obtain ⟨d, hd⟩ := hM
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
    setOf_mem_standardSystem hM (m := 0) <|
      Bounding.definablePred_of_hierarchy (codeOfComputablePred_sigma1 (· ∈ S)) Empty.elim
  simpa [h] using h₁

/-- If for every finite subset of a coded set `S` some element is related to all its members by a
definable relation, then some element is related to all members of `S`. -/
lemma exists_forall_of_mem_standardSystem {R : M → M → Prop} (hR : 𝚺ᴬ_[m + 1]-Relation R)
    (hS : S ∈ standardSystem M) (h : ∀ s : Finset ℕ, ↑s ⊆ S → ∃ x : M, ∀ e ∈ s, R x e) :
    ∃ x : M, ∀ e ∈ S, R x e := by
  classical
  obtain ⟨c, rfl⟩ := hS
  let E := natCastProperEndExtension M hM
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
  apply hx e _ he
  by_contra! hde
  exact hd <| E.mem_range_of_lt (a := e + 1) <| lt_of_le_of_lt hde (by simp [E])

/-- The prenex $\Sigma_n$ type, or prenex $\Pi_n$ type, of a tuple is a coded set.
- [Kay91, Lemma 12.1] -/
theorem mem_standardSystem_hierarchyType (Γ : Polarity) (n : ℕ) {l : ℕ} (a : Fin l → M) :
    {e : ℕ | ∃ φ : ArithmeticSemisentence l, ℬ[<, ℒₒᵣ].PrenexHierarchy Γ n φ ∧ M ⊧/a φ ∧
      Encodable.encode φ = e} ∈ standardSystem M := by
  have h := setOf_mem_standardSystem hM (m := n + 1) (P := fun e ↦
    (ℒₒᵣ).IsSemisentence (l : M) e ∧ PrenexFormulaSatisfied Γ n (matrixToVec a) e)
    (by definability)
  apply Set.mem_of_eq_of_mem _ h
  ext e
  simp only [← Sentence.quote_eq_encode_nat]
  constructor
  · rintro ⟨φ, hφ, ha, rfl⟩
    simp only [Set.mem_ofPred, Sentence.coe_quote_eq_quote]
    exact ⟨.quote φ, (PrenexFormulaSatisfied.quote_iff hφ a).mpr ha⟩
  · rintro ⟨he, hs⟩
    obtain ⟨φ, rfl⟩ := he.sound_natCast
    rw [Sentence.coe_quote_eq_quote] at hs
    have hφ := (isPrenexHierarchy_quote_iff φ).mp hs.isPrenexHierarchy
    use φ
    exact ⟨hφ, (PrenexFormulaSatisfied.quote_iff hφ a).mp hs, rfl⟩

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
  let S : Set ℕ := {e | (ℒₒᵣ).IsSemisentence ((k + m : ℕ) : M) e ∧ subst ℒₒᵣ w e ∈ c}
  have hS : S ∈ standardSystem M := setOf_mem_standardSystem hM (m := 0)
    (P := fun e ↦ (ℒₒᵣ).IsSemisentence ((k + m : ℕ) : M) e ∧ subst ℒₒᵣ w e ∈ c) (by definability)
  have hmem (σ : ArithmeticSemisentence (k + m)) : (⌜σ⌝ : ℕ) ∈ S ↔ U σ ∈ Φ := by
    have h : Encodable.encode (U σ) ∈ codedSet c ↔ U σ ∈ Φ := by simp [hc]
    rw [← h, mem_codedSet, encode_unbindParams, Set.mem_ofPred, Sentence.coe_quote_eq_quote]
    exact and_iff_right (.quote σ)
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
      PrenexFormulaSatisfied Γ n (env x) ((⌜σ⌝ : ℕ) : M) ↔
        (U σ).Eval (fun i ↦ x.[((i : ℕ) : M)]) b := by
    have : ℬ[<, ℒₒᵣ].PrenexHierarchy Γ n σ := by
      simpa [U] using (hΦ _ hσ).rew (Rew.bindParams ℒₒᵣ k m)
    rw [Sentence.coe_quote_eq_quote, PrenexFormulaSatisfied.quote_iff this,
      ← Semiformula.eval_bindParams, Rew.bindParams_app_unbindParams_app]
  obtain ⟨x, hx⟩ := exists_forall_of_mem_standardSystem hM
    (R := fun x e ↦ PrenexFormulaSatisfied Γ n (env x) e)
    (HierarchySymbol.DefinableRel.comp inferInstance (henv.comp (by simp)) (by simp)) hS <| by
      intro s hs
      choose! f hf' using fun e (he : e ∈ S) ↦ he.1.sound_natCast
      obtain ⟨a, ha⟩ := hf (s.image fun e ↦ U (f e)) <| by
        intro φ hφ
        obtain ⟨e, he, rfl⟩ : ∃ e ∈ s, U (f e) = φ := by simpa using hφ
        rw [← hmem, hf' e (hs he)]
        exact hs he
      use matrixToVec a
      intro e he
      have hfe := hf' e (hs he)
      rw [show (e : M) = ((⌜f e⌝ : ℕ) : M) by rw [hfe],
        hR _ ((hmem _).mp (by rw [hfe]; exact hs he))]
      simpa using ha _ (Finset.mem_coe.mpr <| Finset.mem_image_of_mem _ he)
  use fun i ↦ x.[((i : ℕ) : M)]
  intro φ hφ
  have h : U (Rew.bindParams ℒₒᵣ k m ▹ φ) = φ := by simp [U]
  have h₁ := (hR x (h.symm ▸ hφ)).mp (hx _ ((hmem _).mpr (h.symm ▸ hφ)))
  rwa [h] at h₁

/-- A nonstandard model of `𝗣𝗔` is $\Sigma_n$-recursively saturated.
- [Kay91, Theorem 11.5] -/
theorem sigmaRecursivelySaturated_of_nonstandard (n : ℕ) :
    SigmaRecursivelySaturated M ℬ[<, ℒₒᵣ] n := by
  intro k m Φ b hΦ hr hf
  apply Type.realized_of_mem_standardSystem hM 𝚺 n hΦ _ hf
  exact mem_standardSystem_of_computablePred hM hr

end FFL.FirstOrder
