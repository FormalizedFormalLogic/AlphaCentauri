module

public import AlphaCentauri.Model.Cut
public import AlphaCentauri.Model.DefinableElements
public import AlphaCentauri.Model.Elementary
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.General

/-! # The cut below definable elements -/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Semiformula
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {j : ℕ} {M : Type} [ORingStructure M]

/-- The elements of `M` below a $\Sigma_{j+1}$-definable element.
- [HP98, Definition IV.1.32] -/
def definableCut (j : ℕ) (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] : Cut M where
  carrier := {a | ∃ c ∈ definableElements (j + 1) M, a < c}
  succ_mem := by
    rintro a ⟨c, hc, hac⟩
    use c + 1
    and_intros
    · exact ((⟨c, hc⟩ : definableElements (j + 1) M) + 1).2
    · simpa using hac
  mem_of_lt := by
    rintro a b hab ⟨c, hc, hbc⟩
    use c
    and_intros
    · exact hc
    · exact hab.trans hbc

namespace definableCut

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp]
lemma mem_iff {a : M} :
    a ∈ (definableCut j M).carrier ↔ ∃ c ∈ definableElements (j + 1) M, a < c := Iff.rfl

instance closed : (definableCut j M).Closed where
  zero_mem := ⟨1, (1 : definableElements (j + 1) M).2, zero_lt_one⟩
  one_mem := ⟨1 + 1, (1 + 1 : definableElements (j + 1) M).2, lt_add_one 1⟩
  add_mem := by
    rintro a b ⟨c, hc, hac⟩ ⟨d, hd, hbd⟩
    use c + d
    and_intros
    · exact ((⟨c, hc⟩ : definableElements (j + 1) M) + ⟨d, hd⟩).2
    · exact _root_.add_lt_add hac hbd
  mul_mem := by
    rintro a b ⟨c, hc, hac⟩ ⟨d, hd, hbd⟩
    use c * d
    and_intros
    · exact ((⟨c, hc⟩ : definableElements (j + 1) M) * ⟨d, hd⟩).2
    · exact mul_lt_mul'' hac hbd _root_.zero_le _root_.zero_le

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
    | zero => exact Cut.Closed.zero_mem
    | succ N ih =>
      rw [matrixToVec_succ, adjoin_def]
      apply Cut.succ_mem
      have h₁ := (Matrix.vecHead v).2
      have h₂ := ih (Matrix.vecTail v)
      unfold pair
      split_ifs <;> apply_rules [Cut.Closed.add_mem, Cut.Closed.mul_mem]
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
  obtain ⟨d, hd, hCd, -⟩ := exists_least_mem_definableElements (φ := C)
    ((by simp [C, hσ, hθ] : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (m + 1) C).mono hm) (e := ![c])
    (f := fun _ ↦ 0) (Fin.forall_fin_one.mpr hc) (fun _ ↦ (0 : definableElements (j + 1) M).2) <| by
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
theorem sigmaElementary : SigmaElementary (definableCut j M).endExtension.emb j := by
  let := (definableCut j M).endExtension
  have : (definableCut j M).carrier↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := EndExtension.models_peanoMinus (N := M)
  apply sigmaElementary_of_tarskiVaught
  · intro n φ hφ e f
    exact (absolute_of_bounded (T := 𝗣𝗔⁻) hφ _ M e f).symm
  · intro m hm n φ hφ e f h
    obtain ⟨x, hx, hφx⟩ := exists_witness hm hφ e f h
    use ⟨x, hx⟩
    exact hφx

variable {a : M} (ha : a ∈ definableElements (j + 1) M) (hns : ∀ m : ℕ, (m : M) < a)
include hns

/-- The cut below the definable elements satisfies $\mathsf{B}\Sigma_{j+1}$ once `M` is
nonstandard.
- [HP98, Lemma IV.1.44(1)] -/
theorem models_BSigma : (definableCut j M).carrier↓[ℒₒᵣ] ⊧* 𝗕𝚺 (j + 1) := by
  obtain ⟨b, hb⟩ := exists_bound_definableElements (j := j) hns
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
  have hK {x : M} (hx : x ∈ definableElements (j + 1) M) (hxI : x ∈ (definableCut j M).carrier) :
      ⟨x, hxI⟩ ∈ definableElements (j + 1) (definableCut j M).carrier := by
    obtain ⟨φ, hφ, hφx⟩ := id hx
    obtain ⟨φ', hφ'⟩ := Bounding.Prenex.models_exists_prenex.{_, 0} (Γ' := 𝚺) hφ
    have := models_BSigma (j := j) hns
    have : M↓[ℒₒᵣ] ⊧* 𝗕𝚺 j :=
      haveI : 𝗕𝚺 j ⪯ 𝗣𝗔 := BSigma_weakerThan_Peano
      models_of_subtheory (U := 𝗣𝗔) inferInstance
    have : (definableCut j M).carrier↓[ℒₒᵣ] ⊧* 𝗕𝚺 j := mod_BSigma_of_le (Nat.le_succ j)
    have transfer (v : Fin 2 → (definableCut j M).carrier) :
        M ⊧/(Subtype.val ∘ v) φ'.sigmaInv.val ↔ _ ⊧/v φ'.sigmaInv.val :=
      SigmaElementary.models_iff_of_hierarchy sigmaElementary Bounding.Prenex.val_hierarchy v
    use φ'.val
    and_intros
    · exact Bounding.Prenex.val_hierarchy
    intro z
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
      obtain ⟨w, hw, hχ, -⟩ := exists_least_mem_definableElements
        (φ := (φ'.sigmaInv.rew Rew.emb).val) (e := ![x]) (f := fun _ ↦ 0)
        Bounding.Prenex.val_hierarchy (Fin.forall_fin_one.mpr hx)
        (fun _ ↦ (0 : definableElements (j + 1) M).2) <| by
          simpa [eval_emb] using (h₁ x).mp ((hφx x).mpr rfl)
      use ⟨w, w + 1, ((⟨w, hw⟩ : definableElements (j + 1) M) + 1).2, lt_add_one w⟩
      apply (transfer _).mp
      simpa [Matrix.comp_vecCons'', eval_emb] using hχ
  have : (definableCut j M).carrier↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (Nat.le_add_left 1 j)
  have hcast (c : ℕ) : ((c : (definableCut j M).carrier) : M) = c := by
    induction c with
    | zero => rfl
    | succ c ih => simp [Nat.cast_succ, ← ih]; rfl
  have hI' {c : M} (hc : c ∈ definableElements (j + 1) M) : c ∈ (definableCut j M).carrier :=
    ⟨c + 1, ((⟨c, hc⟩ : definableElements (j + 1) M) + 1).2, lt_add_one c⟩
  obtain ⟨b, hb⟩ := exists_bound_definableElements (V := (definableCut j M).carrier) (j := j)
    (a := ⟨a, hI' ha⟩) fun m ↦ by
    change ((m : (definableCut j M).carrier) : M) < a
    rw [hcast]
    exact hns m
  obtain ⟨c, hc, hbc⟩ := b.2
  exact lt_asymm hbc (hb ⟨c, hI' hc⟩ (hK hc (hI' hc)) : c < b.1)

end definableCut

end FFL.FirstOrder.Arithmetic
