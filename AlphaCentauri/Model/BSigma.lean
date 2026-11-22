module

public import AlphaCentauri.Model.DefinableElements
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.General
import AlphaCentauri.OpenProblem

/-! # Models of $\mathsf{B}\Sigma_n$

A proper cut of a model of $\mathsf{I}\Sigma_j$ which is closed under the operations and
$\Sigma_j$-elementary satisfies $\mathsf{B}\Sigma_{j+1}$.
The elements of a model of `𝗣𝗔` below a $\Sigma_{j+1}$-definable element form such a cut, which
satisfies $\mathsf{B}\Sigma_{j+1}$ and, when some $\Sigma_{j+1}$-definable element is nonstandard,
refutes $\mathsf{I}\Sigma_{j+1}$.

A model of $\mathsf{I}\Delta_0$ with a proper end extension to a model of $\mathsf{I}\Delta_0$
satisfies $\mathsf{B}\Sigma_1$, and a countable model of $\mathsf{B}\Sigma_1 + \mathrm{Exp}$ has
such an extension. Whether the hypothesis $\mathrm{Exp}$ can be dropped is open.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Semiformula

/-! ## Elementary cuts -/

section

variable {M : Type*} [ORingStructure M]

namespace ClosedCut

variable {j : ℕ} [M↓[ℒₒᵣ] ⊧* 𝗜𝚺j] (I : ClosedCut M)

private lemma exists_bound_of_isElementary (hI : ∃ c, c ∉ I.carrier)
    (hj : IsElementary (ℬ[<, ℒₒᵣ].PrenexHierarchyLE j)
      I.endExtension.emb) {ψ : ArithmeticSemiformula ℕ 3}
    (hψ : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 j ψ) (e : ℕ → I.carrier) (a : I.carrier)
    (h : ∀ x < a, ∃ y z, ψ.Eval ![z, x, y] e) :
    ∃ b, ∀ x < a, ∃ y < b, ∃ z, ψ.Eval ![z, x, y] e := by
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺j)
  obtain ⟨c₀, hc₀⟩ := hI
  let ι : I.carrier ⊂ₑ M := { I.endExtension with
    not_surjective h := hc₀ <| by obtain ⟨x, rfl⟩ := h c₀; exact x.2 }
  have hψ' (x y z : I.carrier) :
      ψ.Eval ![z.1, x.1, y.1] (I.endExtension.emb ∘ e) ↔ ψ.Eval ![z, x, y] e := by
    simpa [Matrix.comp_vecCons''] using hj ⟨j, le_rfl, 𝚷, hψ⟩ ![z, x, y] e
  have hlt {y c : M} (hy : y ∈ I.carrier) (hc : c ∉ I.carrier) : y < c := by
    by_contra! h₁
    exact hc <| h₁.lt_or_eq.elim (I.mem_of_lt · hy) (· ▸ hy)
  let Θ : ArithmeticSemiformula ℕ 1 :=
    ((((Rew.rewriteMap Nat.succ ▹ ψ) ⇜ ![#0, #2, #1]).bexsLT #2).bexsLT #1).ballLT &0
  let g : ℕ → M := a.1 :>ₙ (Subtype.val ∘ e)
  have hΘ (c : M) : Θ.Eval ![c] g ↔
      ∀ x < a.1, ∃ y < c, ∃ z < c, ψ.Eval ![z, x, y] fun i ↦ (e i).1 := by
    simp [Θ, g, eval_rewriteMap, Matrix.comp_vecCons'']
  have h₁ {c : M} (hc : c ∉ I.carrier) : Θ.Eval ![c] g := by
    apply (hΘ c).mpr
    intro x hx
    obtain ⟨y, z, h₂⟩ := h ⟨x, I.mem_of_lt hx a.2⟩ hx
    use y
    and_intros
    · exact hlt y.2 hc
    · use z
      and_intros
      · exact hlt z.2 hc
      · exact (hψ' _ y z).mpr h₂
  obtain ⟨b, hb, h₂⟩ : ∃ b ∈ I.carrier, Θ.Eval ![b] g := by
    by_contra! h₂
    obtain ⟨c, hc, h₃⟩ := overspill ι 𝚺 j (φ := ∼Θ)
      (by simp [Θ, hψ.hierarchy]) g fun b ↦ by simpa [ι] using h₂ b.1 b.2
    have hc' : c ∉ I.carrier := fun h ↦ hc ⟨⟨c, h⟩, rfl⟩
    obtain ⟨d, rfl⟩ := eq_succ_of_pos (hlt I.zero_mem hc')
    exact absurd (h₁ fun h ↦ hc' (I.succ_mem h)) (by simpa using h₃ d (lt_add_one d))
  use ⟨b, hb⟩
  intro x hx
  obtain ⟨y, hy, z, hz, h₃⟩ := (hΘ b).mp h₂ x.1 hx
  use ⟨y, I.mem_of_lt hy hb⟩
  and_intros
  · exact hy
  · use ⟨z, I.mem_of_lt hz hb⟩
    exact (hψ' x ⟨y, _⟩ ⟨z, _⟩).mp h₃

/-- A proper cut of a model of $\mathsf{I}\Sigma_j$ which is closed under the operations and
$\Sigma_j$-elementary satisfies $\mathsf{B}\Sigma_{j+1}$.
- [HP98, Lemma IV.1.22] -/
theorem models_BSigma_succ (hI : ∃ c, c ∉ I.carrier)
    (hj : IsElementary (ℬ[<, ℒₒᵣ].PrenexHierarchyLE j) I.endExtension.emb) :
    I.carrier↓[ℒₒᵣ] ⊧* 𝗕𝚺 (j + 1) := by
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := mod_ISigma_of_le (Nat.zero_le j)
  apply Semantics.ModelsSet.union_iff.mpr
  and_intros
  · exact I.endExtension.models_ISigma0
  · apply Semantics.ModelsSet.setOf_iff.mpr
    rintro _ ⟨φ, hφ, rfl⟩
    suffices ∀ (e : ℕ → I.carrier) (a : I.carrier), (∀ x < a, ∃ y, φ.Eval ![x, y] e) →
        ∃ b, ∀ x < a, ∃ y < b, φ.Eval ![x, y] e by
      simpa [models_iff, Semiformula.eval_univCl, collectionAxiom, Semiformula.eval_ballLT,
        Semiformula.eval_bexsLT, Semiformula.eval_substs] using this
    obtain ⟨ψ, hψ, rfl⟩ := Bounding.PrenexHierarchy.sigma_succ_iff.mp hφ
    simpa using I.exists_bound_of_isElementary hI hj hψ

end ClosedCut

end

/-! ## The cut below definable elements -/

section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {j : ℕ} {M : Type} [ORingStructure M]

/-- The elements of `M` below a $\Sigma_{j+1}$-definable element.
- [HP98, Definition IV.1.32] -/
def definableCut (j : ℕ) (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] : ClosedCut M where
  carrier := {a | ∃ c ∈ sigmaDefinableElements (j + 1) M, a < c}
  succ_mem := by
    rintro a ⟨c, hc, hac⟩
    use c + 1
    and_intros
    · exact ((⟨c, hc⟩ : sigmaDefinableElements (j + 1) M) + 1).2
    · simpa using hac
  mem_of_lt := by
    rintro a b hab ⟨c, hc, hbc⟩
    use c
    and_intros
    · exact hc
    · exact hab.trans hbc
  zero_mem := ⟨1, (1 : sigmaDefinableElements (j + 1) M).2, zero_lt_one⟩
  one_mem := ⟨1 + 1, (1 + 1 : sigmaDefinableElements (j + 1) M).2, lt_add_one 1⟩
  add_mem := by
    rintro a b ⟨c, hc, hac⟩ ⟨d, hd, hbd⟩
    use c + d
    and_intros
    · exact ((⟨c, hc⟩ : sigmaDefinableElements (j + 1) M) + ⟨d, hd⟩).2
    · exact _root_.add_lt_add hac hbd
  mul_mem := by
    rintro a b ⟨c, hc, hac⟩ ⟨d, hd, hbd⟩
    use c * d
    and_intros
    · exact ((⟨c, hc⟩ : sigmaDefinableElements (j + 1) M) * ⟨d, hd⟩).2
    · exact mul_lt_mul'' hac hbd _root_.zero_le _root_.zero_le

namespace definableCut

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp]
lemma mem_iff {a : M} :
    a ∈ (definableCut j M).carrier ↔ ∃ c ∈ sigmaDefinableElements (j + 1) M, a < c := Iff.rfl

open Bootstrapping in
/-- A prenex $\Pi_m$ formula, `m < j`, with parameters from the cut and a witness in `M` has a
witness in the cut. -/
private lemma exists_witness {m : ℕ} (hm : m < j) {n : ℕ} {φ : ArithmeticSemiformula ℕ (n + 1)}
    (hφ : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 m φ) (e : Fin n → (definableCut j M).carrier)
    (f : ℕ → (definableCut j M).carrier)
    (h : ∃ x : M, φ.Eval (x :> Subtype.val ∘ e) (Subtype.val ∘ f)) :
    ∃ x ∈ (definableCut j M).carrier, φ.Eval (x :> Subtype.val ∘ e) (Subtype.val ∘ f) := by
  obtain ⟨φ, rfl⟩ := hφ
  let ψ := φ.rew (φ.val.paramSubst fun i ↦ #(Fin.castLE (by omega) i))
  let w : Fin (φ.val.fvSup + n) → (definableCut j M).carrier :=
    fun i ↦ if h : (i : ℕ) < n then e ⟨i, h⟩ else f (i - n)
  let q : ℕ := ⌜ψ.matrix.val⌝
  have hP (x : M) : PrenexSatisfied 𝚷 m (x ∷ matrixToVec (Subtype.val ∘ w)) (q : M) ↔
      φ.val.Eval (x :> Subtype.val ∘ e) (Subtype.val ∘ f) := by
    rw [Sentence.coe_quote_eq_quote, show x ∷ matrixToVec (Subtype.val ∘ w) =
      matrixToVec (x :> Subtype.val ∘ w) by simp, prenexSatisfied_quote_iff,
      Bounding.Prenex.val_rew]
    exact eval_toSemisentence (φ := φ.val) _ (fun i ↦ by cases i using Fin.cases <;> simp [w])
      fun i ↦ by
        change (x :> Subtype.val ∘ w) (Fin.succ ⟨i + n, by omega⟩) = (f i).1
        simp [w]
  have hcode {N : ℕ} (v : Fin N → (definableCut j M).carrier) :
      matrixToVec (Subtype.val ∘ v) ∈ (definableCut j M).carrier := by
    induction N with
    | zero => exact (definableCut j M).zero_mem
    | succ N ih =>
      rw [matrixToVec_succ, adjoin_def]
      apply Cut.succ_mem
      have h₁ := (Matrix.vecHead v).2
      have h₂ := ih (Matrix.vecTail v)
      unfold pair
      split_ifs <;> apply_rules [ClosedCut.add_mem, ClosedCut.mul_mem]
  obtain ⟨c, hc, hyc⟩ := hcode w
  obtain ⟨θ, hθ, hθP⟩ : ∃ θ : ArithmeticSemisentence 2, ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (m + 1) θ ∧
      ∀ e p : M, M ⊧/![e, p] θ ↔ PrenexSatisfied 𝚷 m e p := by
    cases m with
    | zero =>
      use boundedSatisfied.pi.val
      simp
    | succ m =>
      use (prenexSatisfied' 𝚷 m).val
      and_intros
      · exact (prenexSatisfied' 𝚷 m).pi_prop.mono (by omega)
      · intro e p
        simp [(PrenexSatisfied.pi_defined' m).df]
  let σ := (prenexSatisfied' 𝚺 m).val
  let ρ : ArithmeticSemiformula ℕ 2 := “y x. !σ y ↑q → ∀ p, !adjoinDef p x y → !θ p ↑q”
  let C : ArithmeticSemiformula ℕ 2 :=
    “d c. ∀ y < c, !σ y ↑q → ∃ x < d, ∀ p, !adjoinDef p x y → !θ p ↑q”
  have hρ (y x : M) : ρ.Eval ![y, x] (fun _ ↦ 0) ↔
      (PrenexSatisfied 𝚺 (m + 1) y q → PrenexSatisfied 𝚷 m (x ∷ y) q) := by
    simp [ρ, σ, hθP, (PrenexSatisfied.sigma_defined' m).df, numeral_eq_natCast]
  have hC (d : M) : C.Eval ![d, c] (fun _ ↦ 0) ↔
      ∀ y < c, PrenexSatisfied 𝚺 (m + 1) y q → ∃ x < d, PrenexSatisfied 𝚷 m (x ∷ y) q := by
    simp [C, σ, hθP, (PrenexSatisfied.sigma_defined' m).df, numeral_eq_natCast]
  have hσ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (m + 1) σ := (prenexSatisfied' 𝚺 m).sigma_prop
  have hρ' : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (m + 1) ρ := by simp [ρ, hσ, hθ]
  obtain ⟨d₀, hd₀⟩ := IBroadSigma.collection (s := m + 1)
    (Bounding.definableRel_of_hierarchy (hρ'.accum 𝚺) fun _ ↦ 0) c <| by
      intro y _
      by_cases hy : PrenexSatisfied 𝚺 (m + 1) y q
      · obtain ⟨x, hx⟩ := hy
        use x
        exact (hρ y x).mpr fun _ ↦ hx
      · use 0
        simp [hρ, hy]
  obtain ⟨d, hd, hCd, -⟩ := exists_least_mem_sigmaDefinableElements (φ := C)
    ((by simp [C, hσ, hθ] : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (m + 1) C).mono hm) (e := ![c])
    (f := fun _ ↦ 0) (Fin.forall_fin_one.mpr hc)
    (fun _ ↦ (0 : sigmaDefinableElements (j + 1) M).2) <| by
      use d₀
      apply (hC d₀).mpr
      intro y hy hS
      obtain ⟨x, hx, hR⟩ := hd₀ y hy
      use x
      and_intros
      · exact hx
      · exact (hρ y x).mp hR hS
  obtain ⟨x, hx, hPx⟩ := (hC d).mp hCd _ hyc <| by
    obtain ⟨x, hx⟩ := h
    use x
    exact (hP x).mpr hx
  use x
  and_intros
  · use d
  · exact (hP x).mp hPx

/-- [HP98, Lemma IV.1.42] -/
theorem sigmaElementary : IsElementary (ℬ[<, ℒₒᵣ].PrenexHierarchyLE j)
    (definableCut j M).endExtension.emb := by
  apply isElementary_of_tarskiVaught
  · intro n φ hφ e f
    exact (Bounding.bounded_absolute (definableCut j M).endExtension.emb hφ e f).symm
  · intro m hm n φ hφ e f h
    obtain ⟨x, hx, hφx⟩ := exists_witness hm hφ e f h
    use ⟨x, hx⟩
    exact hφx

variable {a : M} (ha : a ∈ sigmaDefinableElements (j + 1) M) (hns : ∀ m : ℕ, (m : M) < a)
include hns

/-- The cut below the definable elements satisfies $\mathsf{B}\Sigma_{j+1}$ once `M` is
nonstandard.
- [HP98, Lemma IV.1.44(1)] -/
theorem models_BSigma : (definableCut j M).carrier↓[ℒₒᵣ] ⊧* 𝗕𝚺 (j + 1) := by
  obtain ⟨b, hb⟩ := exists_bound_sigmaDefinableElements (j := j) hns
  have hI : ∃ c, c ∉ (definableCut j M).carrier := by
    use b
    rintro ⟨c, hc, hbc⟩
    exact lt_asymm hbc (hb c hc)
  exact (definableCut j M).models_BSigma_succ hI sigmaElementary

include ha in
/-- The cut below the definable elements refutes $\mathsf{I}\Sigma_{j+1}$ once one of them is
nonstandard.
- [HP98, Lemma IV.1.44(3)] -/
theorem not_models_ISigma : ¬(definableCut j M).carrier↓[ℒₒᵣ] ⊧* 𝗜𝚺 (j + 1) := by
  intro hI
  have hK {x : M} (hx : x ∈ sigmaDefinableElements (j + 1) M)
      (hxI : x ∈ (definableCut j M).carrier) :
      ⟨x, hxI⟩ ∈ sigmaDefinableElements (j + 1) (definableCut j M).carrier := by
    obtain ⟨φ, hφ, hφx⟩ := mem_sigmaDefinableElements_iff.mp hx
    obtain ⟨φ', hφ'⟩ := Bounding.Prenex.models_exists_prenex.{_, 0} (Γ' := 𝚺) hφ
    have := models_BSigma (j := j) hns
    have : M↓[ℒₒᵣ] ⊧* 𝗕𝚺 j :=
      haveI : 𝗕𝚺 j ⪯ 𝗣𝗔 := BSigma_weakerThan_Peano
      models_of_subtheory (U := 𝗣𝗔) inferInstance
    have : (definableCut j M).carrier↓[ℒₒᵣ] ⊧* 𝗕𝚺 j := mod_BSigma_of_le (Nat.le_succ j)
    have transfer (v : Fin 2 → (definableCut j M).carrier) :
        M ⊧/(Subtype.val ∘ v) φ'.sigmaInv.val ↔ _ ⊧/v φ'.sigmaInv.val :=
      IsElementary.models_iff_of_hierarchy sigmaElementary Bounding.Prenex.val_hierarchy v
    apply mem_sigmaDefinableElements_iff.mpr
    use φ'.val
    and_intros
    · exact Bounding.Prenex.val_hierarchy
    · intro z
      have h₁ (y : M) : M ⊧/![y] φ ↔ ∃ w, M ⊧/![w, y] φ'.sigmaInv.val :=
        (hφ' M ![y] Empty.elim).trans <| φ'.models_sigmaInv ![y]
      rw [Bounding.Prenex.models_sigmaInv]
      constructor
      · rintro ⟨w, hw⟩
        apply Subtype.ext
        apply (hφx z.1).mp
        apply (h₁ z.1).mpr
        use w.1
        simpa [Matrix.comp_vecCons''] using (transfer ![w, z]).mpr hw
      · rintro rfl
        obtain ⟨w, hw, hχ, -⟩ := exists_least_mem_sigmaDefinableElements
          (φ := (φ'.sigmaInv.rew Rew.emb).val) (e := ![x]) (f := fun _ ↦ 0)
          Bounding.Prenex.val_hierarchy (Fin.forall_fin_one.mpr hx)
          (fun _ ↦ (0 : sigmaDefinableElements (j + 1) M).2) <| by
            simpa [eval_emb] using (h₁ x).mp ((hφx x).mpr rfl)
        use ⟨w, w + 1, ((⟨w, hw⟩ : sigmaDefinableElements (j + 1) M) + 1).2, lt_add_one w⟩
        apply (transfer _).mp
        simpa [Matrix.comp_vecCons'', eval_emb] using hχ
  have : (definableCut j M).carrier↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (Nat.le_add_left 1 j)
  have hcast (c : ℕ) : ((c : (definableCut j M).carrier) : M) = c := by
    induction c with
    | zero => rfl
    | succ c ih => simp [Nat.cast_succ, ← ih]; rfl
  have hI' {c : M} (hc : c ∈ sigmaDefinableElements (j + 1) M) : c ∈ (definableCut j M).carrier :=
    ⟨c + 1, ((⟨c, hc⟩ : sigmaDefinableElements (j + 1) M) + 1).2, lt_add_one c⟩
  obtain ⟨b, hb⟩ := exists_bound_sigmaDefinableElements (V := (definableCut j M).carrier) (j := j)
    (a := ⟨a, hI' ha⟩) fun m ↦ by
    change ((m : (definableCut j M).carrier) : M) < a
    rw [hcast]
    exact hns m
  obtain ⟨c, hc, hbc⟩ := b.2
  exact lt_asymm hbc (hb ⟨c, hI' hc⟩ (hK hc (hI' hc)) : c < b.1)

end definableCut

end

/-! ## End extensions of models of $\mathsf{B}\Sigma_1$ -/

/-- Does every countable model of $\mathsf{B}\Sigma_1$ have a proper end extension to a model of
$\mathsf{I}\Delta_0$?
- [Kay91, Chapter 16, p. 269]
- [WP89] -/
open_problem exists_proper_endExtension_ISigma0_of_BSigma1 :=
  ∀ (M : Type) [Countable M] [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗕𝚺1],
    ∃ (N : Type) (_ : ORingStructure N) (_ : M ⊂ₑ N), N↓[ℒₒᵣ] ⊧* 𝗜𝚺₀

end FFL.FirstOrder.Arithmetic
