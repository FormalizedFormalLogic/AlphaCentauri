module

public import AlphaCentauri.Model.Elementary
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Pigeonhole
public import AlphaCentauri.ToFoundation.FirstOrder.Semiformula
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.General
public import Foundation.FirstOrder.Incompleteness.Second

/-!
# Definable elements

The $\Sigma_{j+1}$-definable elements of a model `M` of `𝗣𝗔` form a $\Sigma_{j+1}$-elementary
substructure, which satisfies $\mathsf{I}\Sigma_j$ and, when it contains a nonstandard element,
refutes $\mathsf{B}\Sigma_{j+1}$. The elements of `M` below a definable element form a cut, which
satisfies $\mathsf{B}\Sigma_{j+1}$ and refutes $\mathsf{I}\Sigma_{j+1}$.

- [HP98, §IV.1(d)]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Semiformula
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- The elements of `M` defined by a $\Sigma_k$ formula without parameters.
- [HP98, Definition IV.1.32] -/
def definableElements (k : ℕ) (M : Type*) [ORingStructure M] : Set M :=
  {a | ∃ φ : ArithmeticSemisentence 1, ℬ[<, ℒₒᵣ].Hierarchy 𝚺 k φ ∧ ∀ x : M, M ⊧/![x] φ ↔ x = a}

variable {j : ℕ} {M : Type} [ORingStructure M]

lemma definableElements_mono {k k' : ℕ} (h : k ≤ k') :
    definableElements k M ⊆ definableElements k' M := by
  rintro a ⟨φ, hφ, ha⟩
  exact ⟨φ, hφ.mono h, ha⟩

/-- An element defined uniquely from definable elements by a $\Sigma_k$ formula is definable. -/
lemma mem_definableElements_of_unique {k m : ℕ} (hk : 1 ≤ k)
    {ψ : ArithmeticSemisentence (m + 1)} (hψ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 k ψ) {v : Fin m → M}
    (hv : ∀ i, v i ∈ definableElements k M) {a : M} (ha : ∀ x, M ⊧/(x :> v) ψ ↔ x = a) :
    a ∈ definableElements k M := by
  induction m with
  | zero =>
    use ψ
    and_intros
    · exact hψ
    simpa [Matrix.empty_eq] using ha
  | succ m ih =>
    obtain ⟨δ, hδ, hv₀⟩ := hv 0
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
    apply ih (ψ := ∃¹ (δ ⇜ ![#0] ⋏ ψ ⇜ (#1 :> #0 :> fun i ↦ #i.succ.succ))) (v := Fin.tail v)
    · simp [hδ.rew, hψ.rew]
    · intro i
      exact hv i.succ
    · intro x
      have hw : Semiterm.val (v 0 :> x :> Fin.tail v) Empty.elim ∘
          (#1 :> #0 :> fun i ↦ #i.succ.succ : Fin (m + 2) → ArithmeticSemiterm Empty (m + 2)) =
            x :> v := by
        ext i
        cases i using Fin.cases with
        | zero => simp
        | succ i => cases i using Fin.cases <;> simp [Fin.tail]
      simp [← ha x, hv₀, hw]

/-- A $\Pi_j$ formula with parameters among the $\Sigma_{j+1}$-definable elements and a witness
has a least witness, and it is $\Sigma_{j+1}$-definable. -/
lemma exists_least_mem_definableElements [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] {n : ℕ}
    {φ : ArithmeticSemiformula ℕ (n + 1)} (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 j φ) {e : Fin n → M}
    {f : ℕ → M} (he : ∀ i, e i ∈ definableElements (j + 1) M)
    (hf : ∀ i, f i ∈ definableElements (j + 1) M) (h : ∃ x, φ.Eval (x :> e) f) :
    ∃ x ∈ definableElements (j + 1) M, φ.Eval (x :> e) f ∧ ∀ y < x, ¬φ.Eval (y :> e) f := by
  obtain ⟨x₀, hx₀⟩ := h
  obtain ⟨x, hx, hmin⟩ := InductionOnHierarchy.least_number_sigma 𝚷 j
    (P := fun x ↦ φ.Eval (x :> e) f)
    (((Bounding.definable_of_hierarchy hφ f).retractiont
      (#0 :> fun i ↦ &(e i))).of_iff fun v ↦ by
        congr! 2
        ext i
        cases i using Fin.cases <;> simp) hx₀
  let χ : ArithmeticSemiformula ℕ (n + 1) :=
    φ ⋏ (∼(φ ⇜ (#0 :> fun i ↦ #i.succ.succ))).ballLT #0
  let w : Fin (χ.fvSup + n) → M := fun i ↦ if h : (i : ℕ) < n then e ⟨i, h⟩ else f (i - n)
  have hχ (y : M) :
      M ⊧/(y :> w) (χ.toSemisentence fun i ↦ #(Fin.castLE (by omega) i)) ↔ χ.Eval (y :> e) f :=
    eval_toSemisentence (φ := χ) (v := y :> w) _
      (fun i ↦ by cases i using Fin.cases <;> simp [w]) fun i ↦ by
        change (y :> w) (Fin.succ ⟨i + n, by omega⟩) = f i
        simp [w]
  use x
  and_intros
  · apply mem_definableElements_of_unique (Nat.le_add_left 1 j)
      (ψ := χ.toSemisentence fun i ↦ #(Fin.castLE (by omega) i)) (v := w)
    · exact Bounding.Hierarchy.rew _ (by simp [χ, hφ.accum 𝚺, hφ.strict_mono 𝚷 (lt_add_one j)])
    · intro i
      simp only [w]
      split_ifs
      exacts [he _, hf _]
    · intro y
      have hv (z : M) : Semiterm.val (z :> y :> e) f ∘
          (fun i : Fin n ↦ (#i.succ.succ : ArithmeticSemiterm ℕ (n + 2))) = e := by
        ext
        simp
      suffices φ.Eval (y :> e) f ∧ (∀ z < y, ¬φ.Eval (z :> e) f) ↔ y = x by
        simpa [hχ, χ, Matrix.comp_vecCons'', hv] using this
      constructor
      · rintro ⟨h₁, h₂⟩
        rcases lt_trichotomy y x with h | h | h
        · exact absurd h₁ (hmin y h)
        · exact h
        · exact absurd hx (h₂ x h)
      · rintro rfl
        exact ⟨hx, hmin⟩
  · exact hx
  · exact hmin

namespace definableElements

variable (j M) in
instance oringStructure : ORingStructure (definableElements (j + 1) M) where
  zero := ⟨0, by use “#0 = 0”; simp⟩
  one := ⟨1, by use “#0 = 1”; simp⟩
  add a b := ⟨a.1 + b.1, mem_definableElements_of_unique (Nat.le_add_left 1 j)
    (ψ := “#0 = #1 + #2”) (v := ![a.1, b.1]) (by simp) (Fin.forall_fin_two.mpr ⟨a.2, b.2⟩)
    fun x ↦ by simp⟩
  mul a b := ⟨a.1 * b.1, mem_definableElements_of_unique (Nat.le_add_left 1 j)
    (ψ := “#0 = #1 * #2”) (v := ![a.1, b.1]) (by simp) (Fin.forall_fin_two.mpr ⟨a.2, b.2⟩)
    fun x ↦ by simp⟩
  lt a b := a.1 < b.1

variable (j M) in
/-- The inclusion of the definable elements into `M`. -/
def emb : definableElements (j + 1) M ↪ₛ[ℒₒᵣ] M where
  toFun := Subtype.val
  func' f v := by cases f <;> rfl
  rel' r _ := by cases r; exacts [congrArg Subtype.val, id]
  toFun_inj := Subtype.val_injective
  rel_inv' r _ := by cases r; exacts [Subtype.ext, id]

@[simp]
lemma emb_apply (x : definableElements (j + 1) M) : emb j M x = x.val := rfl

variable (j) in
/-- [HP98, Lemma IV.1.39] -/
theorem sigmaElementary [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] : SigmaElementary (emb j M) (j + 1) := by
  have witness {n : ℕ} {φ : ArithmeticSemiformula ℕ (n + 1)} (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 j φ)
      (e : Fin n → definableElements (j + 1) M) (f : ℕ → definableElements (j + 1) M)
      (h : ∃ x : M, φ.Eval (x :> emb j M ∘ e) (emb j M ∘ f)) :
      ∃ x, φ.Eval (emb j M x :> emb j M ∘ e) (emb j M ∘ f) := by
    obtain ⟨x, hx, h, -⟩ :=
      exists_least_mem_definableElements hφ (fun i ↦ (e i).2) (fun i ↦ (f i).2) h
    use ⟨x, hx⟩
    exact h
  apply sigmaElementary_of_tarskiVaught
  · intro n φ hφ
    exact eval_iff_of_bounded_of_witness _ (fun hψ ↦ witness (.bounded 𝚷 j _ hψ)) hφ
  · intro m hm n φ hφ
    exact witness (hφ.hierarchy.mono (by omega))

variable (j) in
/-- [HP98, Corollary IV.1.40] -/
theorem models_ISigma [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] : (definableElements (j + 1) M)↓[ℒₒᵣ] ⊧* 𝗜𝚺 j := by
  have hK : SigmaElementary (emb j M) (j + 1) := sigmaElementary j
  have : (definableElements (j + 1) M)↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
    SigmaElementary.models_peanoMinus fun hm ↦ hK (hm.trans (Nat.zero_le _))
  apply Semantics.ModelsSet.union_iff.mpr
  and_intros
  · exact this
  apply Semantics.ModelsSet.setOf_iff.mpr
  rintro _ ⟨φ, hφ, rfl⟩
  suffices ∀ v : ℕ → definableElements (j + 1) M, φ.Eval ![0] v →
      (∀ x, φ.Eval ![x] v → φ.Eval ![x + 1] v) → ∀ x, φ.Eval ![x] v by
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this
  intro v h₀ hs a
  have hM (x : definableElements (j + 1) M) : φ.Eval ![x.1] (emb j M ∘ v) ↔ φ.Eval ![x] v := by
    simpa [Matrix.comp_vecCons'', Matrix.empty_eq] using hK (by omega) hφ ![x] v
  by_contra ha
  obtain ⟨x₀, hx₀, h₁, h₂⟩ := exists_least_mem_definableElements (φ := ∼φ) (e := ![])
    (f := emb j M ∘ v) (by simpa using hφ.hierarchy) (fun i ↦ i.elim0) (fun i ↦ (v i).2) <| by
      use a.1
      simpa using (hM a).not.mpr ha
  have h₃ : ¬φ.Eval ![⟨x₀, hx₀⟩] v := by simpa [← hM] using h₁
  obtain ⟨y, rfl⟩ : ∃ y, x₀ = y + 1 := eq_succ_of_pos <| pos_iff_ne_zero.mpr <| by
    rintro rfl
    exact h₃ h₀
  have hy : y ∈ definableElements (j + 1) M :=
    mem_definableElements_of_unique (Nat.le_add_left 1 j) (ψ := “#0 + 1 = #1”) (v := ![y + 1])
      (by simp) (Fin.forall_fin_one.mpr hx₀) fun x ↦ by simp
  exact h₃ <| hs ⟨y, hy⟩ <| (hM ⟨y, hy⟩).mp <| by simpa using h₂ y (lt_add_one y)

end definableElements

section code

open Bootstrapping

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `x` is the element defined by the code `c`: `c` codes the matrix of a prenex $\Pi_j$ formula
in one variable, and `x` is the first component of the least element satisfying it. -/
def DefinesElement (j : ℕ) (c x : V) : Prop :=
  ∃ p, π₁ p = x ∧ PrenexSatisfied 𝚷 j (p ∷ 0) c ∧ ∀ q < p, ¬PrenexSatisfied 𝚷 j (q ∷ 0) c

/-- The $\Sigma_{j+1}$ definition of `DefinesElement j`. -/
noncomputable def definesElementDef : (j : ℕ) → 𝚺ᴬ_[j + 1].Semisentence 2
  | 0 => .mkSigma “c x. ∃ p, !pi₁Def x p ∧ (∃ e, !adjoinDef e p 0 ∧ !boundedSatisfied.sigma e c) ∧
      ∀ q < p, ∃ e, !adjoinDef e q 0 ∧ ¬!boundedSatisfied.pi e c”
  | j + 1 => .mkSigma “c x. ∃ p, !pi₁Def x p ∧
      (∃ e, !adjoinDef e p 0 ∧ !(prenexSatisfied' 𝚷 j).val e c) ∧
      ∀ q < p, ∃ e, !adjoinDef e q 0 ∧ ¬!(prenexSatisfied' 𝚷 j).val e c”
      (by simp [(prenexSatisfied' 𝚷 j).pi_prop.accum])

instance DefinesElement.defined : (j : ℕ) →
    𝚺ᴬ_[j + 1]-Relation (DefinesElement j : V → V → Prop) via definesElementDef j
  | 0 => .mk fun v ↦ by simp [definesElementDef, DefinesElement, eq_comm]
  | j + 1 => .mk fun v ↦ by
    simp [definesElementDef, DefinesElement, (PrenexSatisfied.pi_defined' j).df,
      eq_comm]

instance DefinesElement.definable (j : ℕ) :
    𝚺ᴬ_[j + 1]-Relation (DefinesElement j : V → V → Prop) :=
  (DefinesElement.defined j).to_definable

lemma DefinesElement.unique {c x x' : V} (h : DefinesElement j c x)
    (h' : DefinesElement j c x') : x = x' := by
  obtain ⟨p, rfl, hp, hmin⟩ := h
  obtain ⟨p', rfl, hp', hmin'⟩ := h'
  rcases lt_trichotomy p p' with h | rfl | h
  · exact absurd hp (hmin' p h)
  · rfl
  · exact absurd hp' (hmin p' h)

/-- Every $\Sigma_{j+1}$-definable element of a model of $\mathsf{I}\Sigma_{j+1}$ is defined by a
standard code. -/
lemma exists_definesElement [V↓[ℒₒᵣ] ⊧* 𝗜𝚺(j + 1)] {x : V}
    (hx : x ∈ definableElements (j + 1) V) : ∃ c : ℕ, DefinesElement j (c : V) x := by
  obtain ⟨φ, hφ, hφx⟩ := hx
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (j + 1) := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗜𝚺(j + 1))
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 j := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗜𝚺(j + 1))
  obtain ⟨φ', hφ'⟩ := Bounding.Prenex.models_exists_prenex.{_, 0} (Γ' := 𝚺) hφ
  let χ := φ'.sigmaInv
  let θ : ArithmeticSemisentence 1 := “p. ∃ y <⁺ p, ∃ w <⁺ p, !pairDef p y w ∧ !χ.val w y”
  have hθ : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 j θ := by simp [θ]
  obtain ⟨χ', hχ'⟩ := Bounding.Prenex.models_exists_prenex.{_, 0} (Γ' := 𝚺) hθ
  have hS (p : V) : PrenexSatisfied 𝚷 j (p ∷ 0) ((⌜χ'.matrix.val⌝ : ℕ) : V) ↔ V ⊧/![p] χ'.val := by
    rw [Sentence.coe_quote_eq_quote, show p ∷ 0 = matrixToVec ![p] by simp,
      prenexSatisfied_quote_iff]
  have hχ (p : V) : V ⊧/![p] χ'.val ↔ V ⊧/![π₂ p, π₁ p] χ.val := by
    rw [← hχ' V]
    simp [θ]
    grind [le_pair_left, le_pair_right, pi₁_le_self, pi₂_le_self]
  have h₁ (y : V) : V ⊧/![y] φ ↔ ∃ w, V ⊧/![w, y] χ.val :=
    (hφ' V ![y] Empty.elim).trans <| φ'.models_sigmaInv ![y]
  obtain ⟨w, hw⟩ := (h₁ x).mp <| (hφx x).mpr rfl
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 j := mod_ISigma_of_le (Nat.le_succ j)
  obtain ⟨p, hp, hmin⟩ := InductionOnHierarchy.least_number_sigma 𝚷 j
    (P := fun p ↦ V ⊧/![p] χ'.val)
    ((Bounding.definable_of_hierarchy χ'.val_hierarchy Empty.elim).of_iff fun v ↦ by
      beta_reduce; rw [← Matrix.fun_eq_vec_one]) (x := ⟪x, w⟫) (by simpa [hχ] using hw)
  use ⌜χ'.matrix.val⌝
  simp only [DefinesElement, hS]
  use p
  and_intros
  · apply (hφx _).mp
    apply (h₁ _).mpr
    use π₂ p
    exact (hχ p).mp hp
  · exact hp
  · exact hmin

/-- In a nonstandard model of $\mathsf{I}\Sigma_{j+1}$ the $\Sigma_{j+1}$-definable elements are
bounded.
- [HP98, Lemma IV.1.37] -/
theorem exists_bound_definableElements [V↓[ℒₒᵣ] ⊧* 𝗜𝚺(j + 1)] {a : V}
    (ha : ∀ m : ℕ, (m : V) < a) : ∃ b, ∀ x ∈ definableElements (j + 1) V, x < b := by
  have : Fact (1 ≤ j + 1) := ⟨Nat.le_add_left 1 j⟩
  obtain ⟨u, -, hu⟩ := finset_comprehension (m := j + 1) (Γ := 𝚺)
    (P := fun c ↦ ∃ x, DefinesElement j c x) (by definability) a
  obtain ⟨b, hb⟩ := IBroadSigma.collection (s := j) (R := fun c x ↦ c ∈ u → DefinesElement j c x)
    (by definability) a <| by
      intro c hc
      simpa [imp_iff_not_or, exists_or, hu c hc] using em' (∃ x, DefinesElement j c x)
  use b
  intro x hx
  obtain ⟨c, hc⟩ := exists_definesElement hx
  obtain ⟨y, hy, hcy⟩ := hb c (ha c)
  rwa [← (hcy <| (hu c (ha c)).mpr ⟨x, hc⟩).unique hc]

end code

/-- The definable elements refute $\mathsf{B}\Sigma_{j+1}$ once one of them is nonstandard.
- [HP98, Lemma IV.1.41] -/
theorem definableElements.not_models_BSigma [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] {a : M}
    (ha : a ∈ definableElements (j + 1) M) (hns : ∀ m : ℕ, (m : M) < a) :
    ¬(definableElements (j + 1) M)↓[ℒₒᵣ] ⊧* 𝗕𝚺 (j + 1) := by
  intro hK
  have : (definableElements (j + 1) M)↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
    models_of_subtheory (definableElements.models_ISigma j (M := M))
  have transfer {n : ℕ} {φ : ArithmeticSemisentence n} (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (j + 1) φ)
      (v : Fin n → definableElements (j + 1) M) : M ⊧/(Subtype.val ∘ v) φ ↔ _ ⊧/v φ :=
    SigmaElementary.models_iff_of_hierarchy (sigmaElementary j (M := M)) hφ v
  have hcast (c : ℕ) : ((c : definableElements (j + 1) M) : M) = c := by
    induction c with
    | zero => rfl
    | succ c ih => simp [Nat.cast_succ, ← ih]; rfl
  have h₁ (x : definableElements (j + 1) M) : ∃ c < (⟨a, ha⟩ : definableElements (j + 1) M),
      _ ⊧/![c, x] (definesElementDef j).val := by
    obtain ⟨c, hc⟩ := exists_definesElement x.2
    use c
    and_intros
    · change ((c : definableElements (j + 1) M) : M) < a
      rw [hcast]
      exact hns c
    · apply (transfer (definesElementDef j).sigma_prop ![c, x]).mp
      simpa [hcast, Matrix.comp_vecCons''] using hc
  have h₂ : ∀ x < a + 1, ∃ c < a, DefinesElement j c x := by
    simpa using (transfer (φ := “s. ∀ x < s + 1, ∃ c < s, !(definesElementDef j).val c x”)
      (by simp) ![⟨a, ha⟩]).mpr (by simpa [-Subtype.forall, -Subtype.exists] using fun x _ ↦ h₁ x)
  have : Fact (1 ≤ j + 1) := ⟨Nat.le_add_left 1 j⟩
  obtain ⟨x, -, x', -, c, -, hne, hx, hx'⟩ :=
    pigeonhole (m := j + 1) (R := fun x c ↦ DefinesElement j c x) (by definability) a h₂
  exact hne <| hx.unique hx'

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

/-- A model of `𝗣𝗔` with a nonstandard $\Sigma_1$-definable element.
- [HP98, Observation IV.1.31] -/
theorem exists_model_nonstandard_definableElement :
    ∃ (M : Type) (_ : ORingStructure M) (_ : M↓[ℒₒᵣ] ⊧* 𝗣𝗔),
      ∃ a ∈ definableElements 1 M, ∀ m : ℕ, (m : M) < a := by
  obtain ⟨φ, hφ⟩ := Bounding.Prenex.models_exists_prenex.{_, 0} (Γ := 𝚺) (s := 1) (Γ' := 𝚺)
    (φ := ∼(𝗣𝗔.consistent.val : ArithmeticSentence)) 𝗣𝗔.consistent.pi_prop.neg
  by_contra! h
  apply consistent_unprovable 𝗣𝗔
  apply Arithmetic.complete.{0}
  intro M _ _
  by_contra hM
  have h₁ : ∃ x : M, φ.sigmaInv.val.Eval ![x] Empty.elim :=
    (φ.models_sigmaInv ![]).mp <| (hφ M ![] Empty.elim).mp <| by simpa [models_iff] using hM
  obtain ⟨x, hx, h₂, -⟩ := exists_least_mem_definableElements (j := 0)
    (φ := (φ.sigmaInv.rew Rew.emb).val) (e := ![]) (f := fun _ ↦ 0) Bounding.Prenex.val_hierarchy
    (fun i ↦ i.elim0) (fun _ ↦ (0 : definableElements (0 + 1) M).2) (by simpa using h₁)
  obtain ⟨m, hm⟩ := h M _ inferInstance x hx
  obtain ⟨i, hi⟩ := eq_nat_of_le_nat hm
  rw [hi] at h₂
  have h₃ : φ.sigmaInv.val.Eval ![i] Empty.elim := by
    apply (models_iff_of_Sigma0 (V := M) φ.sigmaInv.val_deltaZero (e := ![i])).mp
    simpa using h₂
  have h₄ := (hφ ℕ ![] Empty.elim).mpr <| (φ.models_sigmaInv ![]).mpr ⟨i, h₃⟩
  have h₅ : Entailment.Inconsistent 𝗣𝗔 := by simpa using h₄
  exact Entailment.Consistent.not_inconsistent h₅

end FFL.FirstOrder.Arithmetic
