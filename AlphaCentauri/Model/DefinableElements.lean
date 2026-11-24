module

public import AlphaCentauri.Model.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Pigeonhole
public import AlphaCentauri.ToFoundation.FirstOrder.Syntax
public import AlphaCentauri.ToFoundation.FirstOrder.Hierarchy
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.General
public import Foundation.FirstOrder.Arithmetic.Induction.Equiv
public import Foundation.FirstOrder.Incompleteness.Second

/-! # Definable elements

The $\Sigma_k$-definable elements of a model of arithmetic are the elements definable without
parameters by a $\Sigma_k$ formula.

The $\Sigma_{j+1}$-definable elements of a model `M` of `𝗣𝗔` form a $\Sigma_{j+1}$-elementary
substructure, which satisfies $\mathsf{I}\Sigma_j$ and, when it contains a nonstandard element,
refutes $\mathsf{B}\Sigma_{j+1}$.

The elements of a model `M` of `𝗣𝗔` definable over a set `A` of parameters form an elementary
substructure. The elements of `M` definable without parameters embed elementarily into every model
`N` elementarily equivalent to `M`, in exactly one way, and the image consists of the elements of
`N` definable without parameters. For a complete extension `T` of `𝗣𝗔` these elements form the
prime model $K_T$ of `T`. Consequently the prime model has no proper elementary substructures and no
non-trivial automorphisms.

- [HP98, §IV.1(d)]
- [Kay91, §8.1]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic


open Semiformula
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- The elements of `M` defined by a $\Sigma_k$ formula without parameters.
- [HP98, Definition IV.1.32] -/
abbrev sigmaDefinableElements (k : ℕ) (M : Type*) [ORingStructure M] : Set M :=
  definableElementsOver (∅ : Set M) (ℬ[<, ℒₒᵣ].Hierarchy 𝚺 k)

variable {j : ℕ} {M : Type} [ORingStructure M]

lemma mem_sigmaDefinableElements_iff {k : ℕ} {a : M} : a ∈ sigmaDefinableElements k M ↔
    ∃ φ : ArithmeticSemisentence 1, ℬ[<, ℒₒᵣ].Hierarchy 𝚺 k φ ∧ ∀ x, M ⊧/![x] φ ↔ x = a :=
  mem_definableElementsOver_empty_iff (C := fun φ ↦ ℬ[<, ℒₒᵣ].Hierarchy 𝚺 k φ) fun _ _ h ↦ h.rew _

/-- An element defined uniquely from definable elements by a $\Sigma_k$ formula is definable. -/
lemma mem_sigmaDefinableElements_of_unique {k m : ℕ} (hk : 1 ≤ k)
    {ψ : ArithmeticSemisentence (m + 1)} (hψ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 k ψ) {v : Fin m → M}
    (hv : ∀ i, v i ∈ sigmaDefinableElements k M) {a : M} (ha : ∀ x, M ⊧/(x :> v) ψ ↔ x = a) :
    a ∈ sigmaDefinableElements k M := by
  induction m with
  | zero => exact mem_sigmaDefinableElements_iff.mpr ⟨ψ, hψ, by simpa [Matrix.empty_eq] using ha⟩
  | succ m ih =>
    obtain ⟨δ, hδ, hv₀⟩ := mem_sigmaDefinableElements_iff.mp (hv 0)
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

/-- The least witness of a formula with parameters is defined by a formula whose parameters are
among those of the formula, and which is $\Sigma_{j+1}$ if the formula is $\Pi_j$. -/
lemma exists_defining_formula_of_least [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] {n : ℕ} {φ : ArithmeticSemiformula ℕ (n + 1)}
    {e : Fin n → M} {f : ℕ → M} {x : M} (hx : φ.Eval (x :> e) f)
    (hmin : ∀ y < x, ¬φ.Eval (y :> e) f) :
    ∃ (m : ℕ) (ψ : ArithmeticSemisentence (m + 1)) (w : Fin m → M),
      (∀ j, ℬ[<, ℒₒᵣ].Hierarchy 𝚷 j φ → ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (j + 1) ψ) ∧
      (∀ i, (∃ k, w i = e k) ∨ ∃ k, w i = f k) ∧ ∀ y, ψ.Eval (y :> w) Empty.elim ↔ y = x := by
  let χ : ArithmeticSemiformula ℕ (n + 1) :=
    φ ⋏ (∼(φ ⇜ (#0 :> fun i ↦ #i.succ.succ))).ballLT #0
  let w : Fin (χ.fvSup + n) → M := fun i ↦ if h : (i : ℕ) < n then e ⟨i, h⟩ else f (i - n)
  have hχ (y : M) :
      M ⊧/(y :> w) (χ.toSemisentence fun i ↦ #(Fin.castLE (by omega) i)) ↔ χ.Eval (y :> e) f :=
    eval_toSemisentence (φ := χ) (v := y :> w) _
      (fun i ↦ by cases i using Fin.cases <;> simp [w]) fun i ↦ by
        change (y :> w) (Fin.succ ⟨i + n, by omega⟩) = f i
        simp [w]
  use χ.fvSup + n, χ.toSemisentence fun i ↦ #(Fin.castLE (by omega) i), w
  and_intros
  · intro j hφ
    exact Bounding.Hierarchy.rew _ (by simp [χ, hφ.accum 𝚺, hφ.strict_mono 𝚷 (lt_add_one j)])
  · intro i
    simp only [w]
    split_ifs
    exacts [.inl ⟨_, rfl⟩, .inr ⟨_, rfl⟩]
  · intro y
    have hv (z : M) : Semiterm.val (z :> y :> e) f ∘
        (fun i : Fin n ↦ (#i.succ.succ : ArithmeticSemiterm ℕ (n + 2))) = e := by
      ext
      simp
    suffices φ.Eval (y :> e) f ∧ (∀ z < y, ¬φ.Eval (z :> e) f) ↔ y = x by
      simpa [hχ, χ, Matrix.comp_vecCons'', hv] using this
    constructor
    · rintro ⟨h₁, h₂⟩
      apply le_antisymm
      · by_contra! h
        exact h₂ x h hx
      · by_contra! h
        exact hmin y h h₁
    · rintro rfl
      exact ⟨hx, hmin⟩

/-- A $\Pi_j$ formula with parameters among the $\Sigma_{j+1}$-definable elements and a witness
has a least witness, and it is $\Sigma_{j+1}$-definable. -/
lemma exists_least_mem_sigmaDefinableElements [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] {n : ℕ}
    {φ : ArithmeticSemiformula ℕ (n + 1)} (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 j φ) {e : Fin n → M}
    {f : ℕ → M} (he : ∀ i, e i ∈ sigmaDefinableElements (j + 1) M)
    (hf : ∀ i, f i ∈ sigmaDefinableElements (j + 1) M) (h : ∃ x, φ.Eval (x :> e) f) :
    ∃ x ∈ sigmaDefinableElements (j + 1) M, φ.Eval (x :> e) f ∧ ∀ y < x, ¬φ.Eval (y :> e) f := by
  obtain ⟨x₀, hx₀⟩ := h
  obtain ⟨x, hx, hmin⟩ := InductionOnHierarchy.least_number_sigma 𝚷 j
    (P := fun x ↦ φ.Eval (x :> e) f)
    (((Bounding.definable_of_hierarchy hφ f).retractiont
      (#0 :> fun i ↦ &(e i))).of_iff fun v ↦ by
        congr! 2
        ext i
        cases i using Fin.cases <;> simp) hx₀
  obtain ⟨m, ψ, w, hψ, hw, hdef⟩ := exists_defining_formula_of_least hx hmin
  use x
  and_intros
  · apply mem_sigmaDefinableElements_of_unique (Nat.le_add_left 1 j) (ψ := ψ) (v := w) (hψ j hφ)
    · intro i
      rcases hw i with ⟨k, hk⟩ | ⟨k, hk⟩
      exacts [hk ▸ he k, hk ▸ hf k]
    · exact hdef
  · exact hx
  · exact hmin

namespace sigmaDefinableElements

variable (j M) in
instance oringStructure : ORingStructure (sigmaDefinableElements (j + 1) M) where
  zero := ⟨0, mem_sigmaDefinableElements_iff.mpr ⟨“#0 = 0”, by simp, by simp⟩⟩
  one := ⟨1, mem_sigmaDefinableElements_iff.mpr ⟨“#0 = 1”, by simp, by simp⟩⟩
  add a b := ⟨a.1 + b.1, mem_sigmaDefinableElements_of_unique (Nat.le_add_left 1 j)
    (ψ := “#0 = #1 + #2”) (v := ![a.1, b.1]) (by simp) (Fin.forall_fin_two.mpr ⟨a.2, b.2⟩)
    fun x ↦ by simp⟩
  mul a b := ⟨a.1 * b.1, mem_sigmaDefinableElements_of_unique (Nat.le_add_left 1 j)
    (ψ := “#0 = #1 * #2”) (v := ![a.1, b.1]) (by simp) (Fin.forall_fin_two.mpr ⟨a.2, b.2⟩)
    fun x ↦ by simp⟩
  lt a b := a.1 < b.1

variable (j M) in
/-- The inclusion of the definable elements into `M`. -/
def emb : sigmaDefinableElements (j + 1) M ↪ₛ[ℒₒᵣ] M where
  toFun := Subtype.val
  func' f v := by cases f <;> rfl
  rel' r _ := by cases r; exacts [congrArg Subtype.val, id]
  toFun_inj := Subtype.val_injective
  rel_inv' r _ := by cases r; exacts [Subtype.ext, id]

@[simp]
lemma emb_apply (x : sigmaDefinableElements (j + 1) M) : emb j M x = x.val := rfl

variable (j) in
/-- [HP98, Lemma IV.1.39] -/
theorem sigmaElementary [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] :
    IsElementary (ℬ[<, ℒₒᵣ].PrenexHierarchyLE (j + 1)) (emb j M) := by
  have witness {n : ℕ} {φ : ArithmeticSemiformula ℕ (n + 1)} (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 j φ)
      (e : Fin n → sigmaDefinableElements (j + 1) M) (f : ℕ → sigmaDefinableElements (j + 1) M)
      (h : ∃ x : M, φ.Eval (x :> emb j M ∘ e) (emb j M ∘ f)) :
      ∃ x, φ.Eval (emb j M x :> emb j M ∘ e) (emb j M ∘ f) := by
    obtain ⟨x, hx, h, -⟩ :=
      exists_least_mem_sigmaDefinableElements hφ (fun i ↦ (e i).2) (fun i ↦ (f i).2) h
    use ⟨x, hx⟩
    exact h
  apply IsElementary.prenexHierarchyLE_of_tarskiVaught
  · apply IsElementary.bounded_of_tarskiVaught
    intro n φ hφ
    exact witness (.bounded 𝚷 j _ hφ)
  · intro m hm n φ hφ
    exact witness (hφ.hierarchy.mono (by omega))

variable (j) in
/-- [HP98, Corollary IV.1.40] -/
theorem models_ISigma [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] : (sigmaDefinableElements (j + 1) M)↓[ℒₒᵣ] ⊧* 𝗜𝚺 j := by
  have hK : IsElementary (ℬ[<, ℒₒᵣ].PrenexHierarchyLE (j + 1))
      (emb j M) := sigmaElementary j
  have : (sigmaDefinableElements (j + 1) M)↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
    IsElementary.models_peanoMinus fun hφ ↦
      hK ⟨0, Nat.zero_le _, 𝚷, Bounding.PrenexHierarchy.zero_iff_bounded.mpr hφ⟩
  apply Semantics.ModelsSet.union_iff.mpr
  and_intros
  · exact this
  · apply Semantics.ModelsSet.setOf_iff.mpr
    rintro _ ⟨φ, hφ, rfl⟩
    suffices ∀ v : ℕ → sigmaDefinableElements (j + 1) M, φ.Eval ![0] v →
        (∀ x, φ.Eval ![x] v → φ.Eval ![x + 1] v) → ∀ x, φ.Eval ![x] v by
      simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
        Matrix.constant_eq_singleton] using this
    intro v h₀ hs a
    have hM (x : sigmaDefinableElements (j + 1) M) : φ.Eval ![x.1] (emb j M ∘ v) ↔
        φ.Eval ![x] v := by
      simpa [Matrix.comp_vecCons'', Matrix.empty_eq] using hK ⟨_, by omega, _, hφ⟩ ![x] v
    by_contra ha
    obtain ⟨x₀, hx₀, h₁, h₂⟩ := exists_least_mem_sigmaDefinableElements (φ := ∼φ) (e := ![])
      (f := emb j M ∘ v) (by simpa using hφ.hierarchy) (fun i ↦ i.elim0) (fun i ↦ (v i).2) <| by
        use a.1
        simpa using (hM a).not.mpr ha
    have h₃ : ¬φ.Eval ![⟨x₀, hx₀⟩] v := by simpa [← hM] using h₁
    obtain ⟨y, rfl⟩ : ∃ y, x₀ = y + 1 := eq_succ_of_pos <| pos_iff_ne_zero.mpr <| by
      rintro rfl
      exact h₃ h₀
    have hy : y ∈ sigmaDefinableElements (j + 1) M :=
      mem_sigmaDefinableElements_of_unique (Nat.le_add_left 1 j) (ψ := “#0 + 1 = #1”)
        (v := ![y + 1])
        (by simp) (Fin.forall_fin_one.mpr hx₀) fun x ↦ by simp
    exact h₃ <| hs ⟨y, hy⟩ <| (hM ⟨y, hy⟩).mp <| by simpa using h₂ y (lt_add_one y)

end sigmaDefinableElements

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

instance DefinesElement.definable (j : ℕ) : 𝚺ᴬ_[j + 1]-Relation (DefinesElement j : V → V → Prop) :=
  (DefinesElement.defined j).to_definable

lemma DefinesElement.unique {c x x' : V} (h : DefinesElement j c x)
    (h' : DefinesElement j c x') : x = x' := by
  obtain ⟨p, rfl, hp, hmin⟩ := h
  obtain ⟨p', rfl, hp', hmin'⟩ := h'
  obtain rfl : p = p' := by
    apply le_antisymm
    · by_contra! h
      exact hmin p' h hp'
    · by_contra! h
      exact hmin' p h hp
  rfl

/-- Every $\Sigma_{j+1}$-definable element of a model of $\mathsf{I}\Sigma_{j+1}$ is defined by a
standard code. -/
lemma exists_definesElement [V↓[ℒₒᵣ] ⊧* 𝗜𝚺(j + 1)] {x : V}
    (hx : x ∈ sigmaDefinableElements (j + 1) V) : ∃ c : ℕ, DefinesElement j (c : V) x := by
  obtain ⟨φ, hφ, hφx⟩ := mem_sigmaDefinableElements_iff.mp hx
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
theorem exists_bound_sigmaDefinableElements [V↓[ℒₒᵣ] ⊧* 𝗜𝚺(j + 1)] {a : V}
    (ha : IsNonstandard a) : ∃ b, ∀ x ∈ sigmaDefinableElements (j + 1) V, x < b := by
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
  obtain ⟨y, hy, hcy⟩ := hb c (ha.natCast_lt c)
  rwa [← (hcy <| (hu c (ha.natCast_lt c)).mpr ⟨x, hc⟩).unique hc]

end code

/-- The definable elements refute $\mathsf{B}\Sigma_{j+1}$ once one of them is nonstandard.
- [HP98, Lemma IV.1.41] -/
theorem sigmaDefinableElements.not_models_BSigma [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] {a : M}
    (ha : a ∈ sigmaDefinableElements (j + 1) M) (hns : IsNonstandard a) :
    ¬(sigmaDefinableElements (j + 1) M)↓[ℒₒᵣ] ⊧* 𝗕𝚺 (j + 1) := by
  intro hK
  have : (sigmaDefinableElements (j + 1) M)↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
    models_of_subtheory (sigmaDefinableElements.models_ISigma j (M := M))
  have transfer {n : ℕ} {φ : ArithmeticSemisentence n} (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (j + 1) φ)
      (v : Fin n → sigmaDefinableElements (j + 1) M) : M ⊧/(Subtype.val ∘ v) φ ↔ _ ⊧/v φ :=
    IsElementary.models_iff_of_hierarchy (sigmaElementary j (M := M)) hφ v
  have hcast (c : ℕ) : ((c : sigmaDefinableElements (j + 1) M) : M) = c := by
    induction c with
    | zero => rfl
    | succ c ih => simp [Nat.cast_succ, ← ih]; rfl
  have h₁ (x : sigmaDefinableElements (j + 1) M) :
      ∃ c < (⟨a, ha⟩ : sigmaDefinableElements (j + 1) M),
        _ ⊧/![c, x] (definesElementDef j).val := by
    obtain ⟨c, hc⟩ := exists_definesElement x.2
    use c
    and_intros
    · change ((c : sigmaDefinableElements (j + 1) M) : M) < a
      rw [hcast]
      exact hns.natCast_lt c
    · apply (transfer (definesElementDef j).sigma_prop ![c, x]).mp
      simpa [hcast, Matrix.comp_vecCons''] using hc
  have h₂ : ∀ x < a + 1, ∃ c < a, DefinesElement j c x := by
    simpa using (transfer (φ := “s. ∀ x < s + 1, ∃ c < s, !(definesElementDef j).val c x”)
      (by simp) ![⟨a, ha⟩]).mpr (by simpa [-Subtype.forall, -Subtype.exists] using fun x _ ↦ h₁ x)
  have : Fact (1 ≤ j + 1) := ⟨Nat.le_add_left 1 j⟩
  obtain ⟨x, -, x', -, c, -, hne, hx, hx'⟩ :=
    pigeonhole (m := j + 1) (R := fun x c ↦ DefinesElement j c x) (by definability) a h₂
  exact hne <| hx.unique hx'


/-- A model of `𝗣𝗔` with a nonstandard $\Sigma_1$-definable element.
- [HP98, Observation IV.1.31] -/
theorem exists_model_nonstandard_sigmaDefinableElement :
    ∃ (M : Type) (_ : ORingStructure M) (_ : M↓[ℒₒᵣ] ⊧* 𝗣𝗔),
      ∃ a ∈ sigmaDefinableElements 1 M, IsNonstandard a := by
  obtain ⟨φ, hφ⟩ := Bounding.Prenex.models_exists_prenex.{_, 0} (Γ := 𝚺) (s := 1) (Γ' := 𝚺)
    (φ := ∼(𝗣𝗔.consistent.val : ArithmeticSentence)) 𝗣𝗔.consistent.pi_prop.neg
  by_contra! h
  simp only [IsNonstandard, not_forall, not_lt] at h
  apply consistent_unprovable 𝗣𝗔
  apply Arithmetic.complete.{0}
  intro M _ _
  by_contra hM
  have h₁ : ∃ x : M, φ.sigmaInv.val.Eval ![x] Empty.elim :=
    (φ.models_sigmaInv ![]).mp <| (hφ M ![] Empty.elim).mp <| by simpa [models_iff] using hM
  obtain ⟨x, hx, h₂, -⟩ := exists_least_mem_sigmaDefinableElements (j := 0)
    (φ := (φ.sigmaInv.rew Rew.emb).val) (e := ![]) (f := fun _ ↦ 0) Bounding.Prenex.val_hierarchy
    (fun i ↦ i.elim0) (fun _ ↦ (0 : sigmaDefinableElements (0 + 1) M).2) (by simpa using h₁)
  obtain ⟨m, hm⟩ := h M _ inferInstance x hx
  obtain ⟨i, hi⟩ := eq_nat_of_le_nat hm
  rw [hi] at h₂
  have h₃ : φ.sigmaInv.val.Eval ![i] Empty.elim := by
    apply (models_iff_of_Sigma0 (V := M) φ.sigmaInv.val_deltaZero (e := ![i])).mp
    simpa using h₂
  have h₄ := (hφ ℕ ![] Empty.elim).mpr <| (φ.models_sigmaInv ![]).mpr ⟨i, h₃⟩
  exact Entailment.Consistent.not_inconsistent (by simpa using h₄)

section over

variable {A : Set M}

lemma subset_definableClosure (A : Set M) : A ⊆ definableClosure ℒₒᵣ A := by
  intro b hb
  exact ⟨⟨“#0 = &(⟨b, hb⟩ : A)”, trivial, fun x ↦ by simp⟩⟩

/-- An element defined uniquely by a formula with parameters from `A` and from
`definableClosure ℒₒᵣ A` is definable over `A`. -/
lemma mem_definableClosure_of_unique {n : ℕ} {ψ : ArithmeticSemiformula A (n + 1)}
    {v : Fin n → M} (hv : ∀ i, v i ∈ definableClosure ℒₒᵣ A) {b : M}
    (hb : ∀ x, ψ.Eval (x :> v) Subtype.val ↔ x = b) : b ∈ definableClosure ℒₒᵣ A := by
  induction n with
  | zero => exact ⟨⟨ψ, trivial, by simpa [Matrix.empty_eq] using hb⟩⟩
  | succ n ih =>
    obtain ⟨θ, -, hθ⟩ := hv 0
    apply ih (ψ := ∃¹ (θ ⇜ ![#0] ⋏ ψ ⇜ (#1 :> #0 :> fun i ↦ #i.succ.succ))) (v := Fin.tail v)
    · intro i
      exact hv i.succ
    · intro x
      have hw : Semiterm.val (v 0 :> x :> Fin.tail v) Subtype.val ∘
          (#1 :> #0 :> fun i ↦ #i.succ.succ : Fin (n + 2) → ArithmeticSemiterm A (n + 2)) =
            x :> v := by
        ext i
        cases i using Fin.cases with
        | zero => simp
        | succ i => cases i using Fin.cases <;> simp [Fin.tail]
      simp [← hb x, hθ, hw]

namespace definableClosure

variable (A) in
instance oringStructure : ORingStructure (definableClosure ℒₒᵣ A) where
  zero := ⟨0, mem_definableClosure_of_unique (ψ := “#0 = 0”) (v := ![])
    (fun i ↦ i.elim0) fun x ↦ by simp⟩
  one := ⟨1, mem_definableClosure_of_unique (ψ := “#0 = 1”) (v := ![])
    (fun i ↦ i.elim0) fun x ↦ by simp⟩
  add a b := ⟨a.1 + b.1, mem_definableClosure_of_unique (ψ := “#0 = #1 + #2”)
    (v := ![a.1, b.1]) (Fin.forall_fin_two.mpr ⟨a.2, b.2⟩) fun x ↦ by simp⟩
  mul a b := ⟨a.1 * b.1, mem_definableClosure_of_unique (ψ := “#0 = #1 * #2”)
    (v := ![a.1, b.1]) (Fin.forall_fin_two.mpr ⟨a.2, b.2⟩) fun x ↦ by simp⟩
  lt a b := a.1 < b.1

variable (A) in
/-- The inclusion of the elements definable over `A` into `M`. -/
def emb : definableClosure ℒₒᵣ A ↪ₛ[ℒₒᵣ] M where
  toFun := Subtype.val
  func' f v := by cases f <;> rfl
  rel' r _ := by cases r; exacts [congrArg Subtype.val, id]
  toFun_inj := Subtype.val_injective
  rel_inv' r _ := by cases r; exacts [Subtype.ext, id]

@[simp]
lemma emb_apply (x : definableClosure ℒₒᵣ A) : emb A x = x.val := rfl

/-- A formula with parameters definable over `A` and a witness in a model of `𝗣𝗔` has a witness
definable over `A`. -/
lemma exists_mem_of_exists [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] {n : ℕ} (φ : ArithmeticSemiformula ℕ (n + 1))
    {e : Fin n → M} {f : ℕ → M} (he : ∀ i, e i ∈ definableClosure ℒₒᵣ A)
    (hf : ∀ i, f i ∈ definableClosure ℒₒᵣ A) (h : ∃ x, φ.Eval (x :> e) f) :
    ∃ x ∈ definableClosure ℒₒᵣ A, φ.Eval (x :> e) f := by
  obtain ⟨x₀, hx₀⟩ := h
  obtain ⟨s, hs⟩ := Bounding.exists_prenexHierarchy_eval_iff.{0} (ℬ := ℬ[<, ℒₒᵣ]) φ
  obtain ⟨ψ, hψ, hφψ⟩ := hs 𝚺 s le_rfl
  obtain ⟨x, hx, hmin⟩ := InductionOnHierarchy.least_number_sigma 𝚺 s
    (P := fun x ↦ φ.Eval (x :> e) f)
    (((Bounding.definable_of_hierarchy hψ.hierarchy f).retractiont
      (#0 :> fun i ↦ &(e i))).of_iff fun v ↦ by
        change φ.Eval (v 0 :> e) f ↔ _
        rw [hφψ M]
        congr! 2
        ext i
        cases i using Fin.cases <;> simp) hx₀
  obtain ⟨m, ψ, w, -, hw, hdef⟩ := exists_defining_formula_of_least hx hmin
  use x
  and_intros
  · apply mem_definableClosure_of_unique (v := w) (ψ := Rewriting.emb ψ)
    · intro i
      rcases hw i with ⟨k, hk⟩ | ⟨k, hk⟩
      exacts [hk ▸ he k, hk ▸ hf k]
    · simpa using hdef
  · exact hx

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

variable (A) in
/-- The elements definable over `A` form an elementary substructure of a model of `𝗣𝗔`.
- [Kay91, Theorem 8.1] -/
theorem isElementary : IsElementary (fun {_} _ ↦ True) (emb A) := by
  apply IsElementary.of_tarskiVaught
  intro n φ e f h
  obtain ⟨x, hx, hφ⟩ := exists_mem_of_exists φ (fun i ↦ (e i).2) (fun i ↦ (f i).2) h
  use ⟨x, hx⟩
  exact hφ

variable (A) in
/-- The elements definable over `A` as an elementary substructure of a model of `𝗣𝗔`.
- [Kay91, Theorem 8.1] -/
def elementarySubstructure : definableClosure ℒₒᵣ A ≼ₑ[ℒₒᵣ] M where
  emb := emb A
  isElementary := isElementary A

variable (A) in
/-- The elements definable over `A` in a model of `𝗣𝗔` form a model of `𝗣𝗔`.
- [Kay91, Theorem 8.1] -/
theorem models_PA : (definableClosure ℒₒᵣ A)↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
  IsElementary.modelsTheory (isElementary A)

end definableClosure

end over

/-! ## The prime model -/

section

open Tarski.Structure

variable {N : Type} [ORingStructure N] [M ≡ₑ[ℒₒᵣ] N]

namespace definableElements

open definableClosure

lemma existsUnique_realize (a : definableElements ℒₒᵣ M) :
    ∃! y : N, ∀ θ : ArithmeticSemisentence 1, M ⊧/![a.1] θ → N ⊧/![y] θ := by
  obtain ⟨θa, ha⟩ := mem_definableElements_iff.mp a.2
  obtain ⟨y, hy, huniq⟩ := (ElementaryEquiv.existsUnique_iff (N := N) θa).mp
    ⟨a.1, (ha _).mpr rfl, fun x ↦ (ha x).mp⟩
  use y
  and_intros
  · intro θ hθ
    obtain ⟨z, hz, -⟩ := (ElementaryEquiv.existsUnique_iff (N := N) (θa ⋏ θ)).mp
      ⟨a.1, by simpa [(ha _).mpr rfl] using hθ, fun x hx ↦
        (ha x).mp (show M ⊧/![x] θa ∧ M ⊧/![x] θ by simpa using hx).1⟩
    simp only [LogicalConnective.HomClass.map_and] at hz
    obtain rfl := huniq z hz.1
    exact hz.2
  · intro y' hy'
    exact huniq y' (hy' θa ((ha _).mpr rfl))

/-- The element of `N` realizing the type of an element of `M` definable without parameters. -/
noncomputable def primeModelMap (a : definableElements ℒₒᵣ M) : N :=
  (existsUnique_realize a).exists.choose

lemma realize_primeModelMap (a : definableElements ℒₒᵣ M)
    {θ : ArithmeticSemisentence 1} (h : M ⊧/![a.1] θ) : N ⊧/![primeModelMap a] θ :=
  (existsUnique_realize a).exists.choose_spec θ h

lemma eq_primeModelMap {a : definableElements ℒₒᵣ M} {y : N}
    (h : ∀ θ : ArithmeticSemisentence 1, M ⊧/![a.1] θ → N ⊧/![y] θ) : y = primeModelMap a :=
  (existsUnique_realize a).unique h fun _ ↦ realize_primeModelMap a

lemma evalb_primeModelMap {n : ℕ} (φ : ArithmeticSemisentence n)
    (v : Fin n → definableElements ℒₒᵣ M) :
    N ⊧/(primeModelMap ∘ v) φ ↔ M ⊧/(Subtype.val ∘ v) φ := by
  suffices h : ∀ {n : ℕ} (φ : ArithmeticSemisentence n) (v : Fin n → definableElements ℒₒᵣ M),
      M ⊧/(Subtype.val ∘ v) φ → N ⊧/(primeModelMap ∘ v) φ by
    constructor
    · intro hN
      by_contra hM
      have := h (∼φ) v (by simpa using hM)
      simp only [LogicalConnective.HomClass.map_neg] at this
      exact this hN
    · exact h φ v
  intro n φ v
  induction n with
  | zero =>
    simpa [models_iff, Matrix.empty_eq] using
      (ElementaryEquiv.models (L := ℒₒᵣ) (M₁ := M) (M₂ := N) (φ := φ)).mp
  | succ n ih =>
    intro hφ
    obtain ⟨θ, hθ⟩ := mem_definableElements_iff.mp (v 0).2
    have h₁ := ih (∀¹ ((θ ⇜ ![#0]) 🡒 φ)) (Fin.tail v) <| by
      simp only [eval_all, LogicalConnective.HomClass.map_imply, eval_substs]
      intro x hx
      obtain rfl := (hθ x).mp (by simpa [Matrix.constant_eq_singleton] using hx)
      convert hφ using 2
      ext i
      cases i using Fin.cases <;> simp [Fin.tail]
    simp only [eval_all, LogicalConnective.HomClass.map_imply, eval_substs] at h₁
    have := h₁ (primeModelMap (v 0))
      (by simpa [Matrix.constant_eq_singleton] using realize_primeModelMap (v 0) ((hθ _).mpr rfl))
    convert this using 2
    ext i
    cases i using Fin.cases <;> simp [Fin.tail]

lemma primeModelMap_mem (a : definableElements ℒₒᵣ M) :
    (primeModelMap a : N) ∈ definableElements ℒₒᵣ N := by
  obtain ⟨θ, hθ⟩ := mem_definableElements_iff.mp a.2
  obtain ⟨y, -, huniq⟩ := (ElementaryEquiv.existsUnique_iff (N := N) θ).mp
    ⟨a.1, (hθ _).mpr rfl, fun x ↦ (hθ x).mp⟩
  have ha := realize_primeModelMap (N := N) a ((hθ _).mpr rfl)
  apply mem_definableElements_iff.mpr
  use θ
  intro x
  constructor
  · intro hx
    rw [huniq x hx, huniq _ ha]
  · rintro rfl
    exact ha

lemma exists_primeModelMap_eq {b : N} (hb : b ∈ definableElements ℒₒᵣ N) :
    ∃ a : definableElements ℒₒᵣ M, primeModelMap a = b := by
  obtain ⟨θ, hθ⟩ := mem_definableElements_iff.mp hb
  obtain ⟨x, hx, huniq⟩ := (ElementaryEquiv.existsUnique_iff (M := M) (N := N) θ).mpr
    ⟨b, (hθ _).mpr rfl, fun y ↦ (hθ y).mp⟩
  have hmem : x ∈ definableElements ℒₒᵣ M := by
    apply mem_definableElements_iff.mpr
    use θ
    intro y
    exact ⟨huniq y, by rintro rfl; exact hx⟩
  use ⟨x, hmem⟩
  exact (hθ _).mp (realize_primeModelMap ⟨x, hmem⟩ hx)

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

variable (M N) in
/-- The elementary embedding of the elements of `M` definable without parameters into `N`.
- [Kay91, Theorem 8.2] -/
noncomputable def primeModelEmbedding : definableElements ℒₒᵣ M ≼ₑ[ℒₒᵣ] N where
  emb := {
    toFun := primeModelMap
    func' f v := by
      have := (evalb_primeModelMap (N := N) “#0 = !!(Semiterm.func f fun i ↦ #i.succ)”
        (Tarski.Structure.func f v :> v)).mpr <| by
          simpa [Function.comp_def] using HomClass.map_func (emb (∅ : Set M)) f v
      simpa [Matrix.comp_vecCons'', Function.comp_def] using this
    rel' r v h := by
      have := (evalb_primeModelMap (N := N) (Semiformula.rel r fun i ↦ #i) v).mpr <| by
        simpa [Function.comp_def] using HomClass.map_rel (emb (∅ : Set M)) r v h
      simpa [Function.comp_def] using this
    toFun_inj a b h := by
      have := (evalb_primeModelMap (N := N) “#0 = #1” ![a, b]).mp (by simpa using h)
      exact Subtype.ext (by simpa using this)
    rel_inv' r v h := by
      apply EmbeddingClass.map_rel_inv (emb (∅ : Set M)) r v
      have := (evalb_primeModelMap (N := N) (Semiformula.rel r fun i ↦ #i) v).mp <| by
        simpa [Function.comp_def] using h
      simpa [Function.comp_def] using this }
  isElementary := by
    have : N↓[ℒₒᵣ] ⊧* 𝗣𝗔 := (ElementaryEquiv.modelsTheory (M₁ := M) (M₂ := N)).mp inferInstance
    apply IsElementary.of_tarskiVaught
    intro n φ e f h
    obtain ⟨x, hx, hφ⟩ := exists_mem_of_exists (A := (∅ : Set N)) φ
      (fun i ↦ primeModelMap_mem (e i)) (fun i ↦ primeModelMap_mem (f i)) h
    obtain ⟨a, rfl⟩ := exists_primeModelMap_eq (M := M) hx
    use a
    exact hφ

/-- The image of `primeModelEmbedding` is the set of elements of `N` definable without parameters.
- [Kay91, Theorem 8.2] -/
theorem range_primeModelEmbedding :
    Set.range (primeModelEmbedding M N) = definableElements ℒₒᵣ N := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact primeModelMap_mem a
  · exact exists_primeModelMap_eq

/-- `primeModelEmbedding` is the only elementary embedding of the elements of `M` definable without
parameters into `N`.
- [Kay91, Theorem 8.2] -/
noncomputable instance : Unique (definableElements ℒₒᵣ M ≼ₑ[ℒₒᵣ] N) where
  default := primeModelEmbedding M N
  uniq k := by
    obtain ⟨ι, hι⟩ := k
    congr
    ext a
    apply eq_primeModelMap
    intro θ hθ
    have h₁ := isElementary (∅ : Set M) (φ := Rewriting.emb θ) trivial ![a] fun _ ↦ a
    have h₂ := hι (φ := Rewriting.emb θ) trivial ![a] fun _ ↦ a
    simp only [eval_emb, Matrix.comp_vecCons'', Matrix.empty_eq, emb_apply] at h₁ h₂
    exact h₂.mpr (h₁.mp hθ)

omit [M ≡ₑ[ℒₒᵣ] N] in
/-- The elements of `M` definable without parameters have no proper elementary substructures.
- [Kay91, Corollary 8.3] -/
theorem surjective_of_elementarySubstructure [Nonempty N]
    (f : N ≼ₑ[ℒₒᵣ] definableElements ℒₒᵣ M) : Function.Surjective f := by
  have : M ≡ₑ[ℒₒᵣ] definableElements ℒₒᵣ M :=
    (ElementaryEquiv.of_elementarySubstructure (elementarySubstructure (∅ : Set M))).symm
  have : M ≡ₑ[ℒₒᵣ] N :=
    this.trans (ElementaryEquiv.of_elementarySubstructure f).symm
  intro b
  use primeModelEmbedding M N b
  exact congrArg (fun e : definableElements ℒₒᵣ M ≼ₑ[ℒₒᵣ] definableElements ℒₒᵣ M ↦ e b)
    (Subsingleton.elim ((primeModelEmbedding M N).trans f) (ElementarySubstructureOn.refl _ _))

/-- The elements of `M` definable without parameters have no non-trivial automorphisms.
- [Kay91, Corollary 8.4] -/
theorem eq_id_of_iso (f : definableElements ℒₒᵣ M ≃ₛ[ℒₒᵣ] definableElements ℒₒᵣ M) : ⇑f = id := by
  have : M ≡ₑ[ℒₒᵣ] definableElements ℒₒᵣ M :=
    (ElementaryEquiv.of_elementarySubstructure (elementarySubstructure (∅ : Set M))).symm
  funext b
  exact congrArg (fun e : definableElements ℒₒᵣ M ≼ₑ[ℒₒᵣ] definableElements ℒₒᵣ M ↦ e b)
    (Subsingleton.elim f.toElementarySubstructure (ElementarySubstructureOn.refl _ _))

end definableElements

end

end FFL.FirstOrder.Arithmetic
