module

public import AlphaCentauri.Model.DefinableElements

/-! # The prime model

The elements of a model `M` of `𝗣𝗔` definable without parameters embed elementarily into every
model `N` elementarily equivalent to `M`, in exactly one way, and the image consists of the elements
of `N` definable without parameters. For a complete extension `T` of `𝗣𝗔` these elements form the
prime model $K_T$ of `T`.

- [Kay91, §8.1]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Semiformula Tarski.Structure

variable {M N : Type} [ORingStructure M] [ORingStructure N]

lemma mem_definableElementsOver_empty_iff {b : M} :
    b ∈ definableElementsOver (∅ : Set M) ↔
      ∃ θ : ArithmeticSemisentence 1, ∀ x, M ⊧/![x] θ ↔ x = b := by
  constructor
  · rintro ⟨m, θ, a, h⟩
    have : IsEmpty (Fin m) := ⟨fun i ↦ (a i).2⟩
    use Rew.rewriteMap (fun i ↦ isEmptyElim i) ▹ θ
    intro x
    rw [← h x, eval_rewriteMap]
    exact iff_of_eq (congrArg (fun f ↦ Eval ![x] f θ) (Subsingleton.elim _ _))
  · rintro ⟨θ, h⟩
    use 0, Rewriting.emb θ, Fin.elim0
    simpa using h

variable [M ≡ₑ[ℒₒᵣ] N]

lemma existsUnique_iff_of_elementaryEquiv (θ : ArithmeticSemisentence 1) :
    (∃! x : M, M ⊧/![x] θ) ↔ ∃! y : N, N ⊧/![y] θ := by
  simpa [models_iff, ExistsUnique, Matrix.constant_eq_singleton] using
    (ElementaryEquiv.models (L := ℒₒᵣ) (M₁ := M) (M₂ := N)
      (φ := “∃ x, !θ x ∧ ∀ y, !θ y → y = x”))

namespace definableElementsOver

lemma existsUnique_realize (a : definableElementsOver (∅ : Set M)) :
    ∃! y : N, ∀ θ : ArithmeticSemisentence 1, M ⊧/![a.1] θ → N ⊧/![y] θ := by
  obtain ⟨θa, ha⟩ := mem_definableElementsOver_empty_iff.mp a.2
  obtain ⟨y, hy, huniq⟩ := (existsUnique_iff_of_elementaryEquiv (N := N) θa).mp
    ⟨a.1, (ha a).mpr rfl, fun x hx ↦ (ha x).mp hx⟩
  use y
  constructor
  · intro θ hθ
    obtain ⟨z, hz, -⟩ := (existsUnique_iff_of_elementaryEquiv (N := N) (θa ⋏ θ)).mp
      ⟨a.1, by simpa [(ha a).mpr rfl] using hθ, fun x hx ↦ (ha x).mp <| by
        simp only [LogicalConnective.HomClass.map_and] at hx
        exact hx.1⟩
    simp only [LogicalConnective.HomClass.map_and] at hz
    rw [← huniq z hz.1]
    exact hz.2
  · intro y' hy'
    exact huniq y' (hy' θa ((ha a).mpr rfl))

/-- The element of `N` realizing the type of an element of `M` definable without parameters. -/
noncomputable def primeModelMap (a : definableElementsOver (∅ : Set M)) : N :=
  (existsUnique_realize a).exists.choose

lemma realize_primeModelMap (a : definableElementsOver (∅ : Set M))
    {θ : ArithmeticSemisentence 1} (h : M ⊧/![a.1] θ) : N ⊧/![primeModelMap a] θ :=
  (existsUnique_realize a).exists.choose_spec θ h

lemma eq_primeModelMap {a : definableElementsOver (∅ : Set M)} {y : N}
    (h : ∀ θ : ArithmeticSemisentence 1, M ⊧/![a.1] θ → N ⊧/![y] θ) : y = primeModelMap a :=
  (existsUnique_realize a).unique h fun _ ↦ realize_primeModelMap a

lemma evalb_primeModelMap {n : ℕ} (φ : ArithmeticSemisentence n)
    (v : Fin n → definableElementsOver (∅ : Set M)) :
    N ⊧/(primeModelMap ∘ v) φ ↔ M ⊧/(Subtype.val ∘ v) φ := by
  suffices h : ∀ {n : ℕ} (φ : ArithmeticSemisentence n) (v : Fin n → definableElementsOver ∅),
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
    obtain ⟨θ, hθ⟩ := mem_definableElementsOver_empty_iff.mp (v 0).2
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

lemma primeModelMap_mem (a : definableElementsOver (∅ : Set M)) :
    (primeModelMap a : N) ∈ definableElementsOver (∅ : Set N) := by
  obtain ⟨θ, hθ⟩ := mem_definableElementsOver_empty_iff.mp a.2
  obtain ⟨y, -, huniq⟩ := (existsUnique_iff_of_elementaryEquiv (N := N) θ).mp
    ⟨a.1, (hθ a).mpr rfl, fun x hx ↦ (hθ x).mp hx⟩
  have ha : N ⊧/![primeModelMap a] θ := realize_primeModelMap a ((hθ a).mpr rfl)
  apply mem_definableElementsOver_empty_iff.mpr
  use θ
  intro x
  constructor
  · intro hx
    rw [huniq x hx, huniq _ ha]
  · rintro rfl
    exact ha

lemma exists_primeModelMap_eq {b : N} (hb : b ∈ definableElementsOver (∅ : Set N)) :
    ∃ a : definableElementsOver (∅ : Set M), primeModelMap a = b := by
  obtain ⟨θ, hθ⟩ := mem_definableElementsOver_empty_iff.mp hb
  obtain ⟨x, hx, huniq⟩ := (existsUnique_iff_of_elementaryEquiv (M := M) θ).mpr
    ⟨b, (hθ b).mpr rfl, fun y hy ↦ (hθ y).mp hy⟩
  have hmem : x ∈ definableElementsOver (∅ : Set M) := by
    apply mem_definableElementsOver_empty_iff.mpr
    use θ
    intro y
    constructor
    · exact huniq y
    · rintro rfl
      exact hx
  use ⟨x, hmem⟩
  exact (hθ _).mp (realize_primeModelMap ⟨x, hmem⟩ hx)

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

variable (M N) in
/-- The elementary embedding of the elements of `M` definable without parameters into `N`.
- [Kay91, Theorem 8.2] -/
noncomputable def primeModelEmbedding :
    definableElementsOver (∅ : Set M) ≼ₑ[ℒₒᵣ] N where
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
    Set.range (primeModelEmbedding M N) = definableElementsOver (∅ : Set N) := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact primeModelMap_mem a
  · exact exists_primeModelMap_eq

/-- `primeModelEmbedding` is the only elementary embedding of the elements of `M` definable without
parameters into `N`.
- [Kay91, Theorem 8.2] -/
noncomputable instance : Unique (definableElementsOver (∅ : Set M) ≼ₑ[ℒₒᵣ] N) where
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

end definableElementsOver

end FFL.FirstOrder.Arithmetic
