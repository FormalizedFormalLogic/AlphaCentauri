module

public import Foundation.FirstOrder.Arithmetic.BoundedCollection

/-!
# The collection scheme `𝗕𝚺`

- [HP98, §I.2(a)]
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

section axioms

variable {L : Language} [L.ORing] {ξ : Type*} [DecidableEq ξ]

/-- The collection axiom for `φ`: a witness for `φ` at every `x` below `a` can be bounded by a
single `b`.
- [HP98, §I.2(a)] -/
def collectionAxiom {ξ} (φ : Semiformula L ξ 2) : Formula L ξ :=
  “∀ a, (∀ x < a, ∃ y, !φ x y) → ∃ b, ∀ x < a, ∃ y < b, !φ x y”

/-- The collection scheme for the class `Γ` of `Semiformula ℒₒᵣ ℕ 2`.
- [HP98, §I.2(a)] -/
def CollectionScheme (Γ : ArithmeticSemiformula ℕ 2 → Prop) : ArithmeticTheory :=
  { ψ | ∃ φ : ArithmeticSemiformula ℕ 2, Γ φ ∧ ψ = .univCl (collectionAxiom φ) }

/-- `𝗕𝚺 n` is `𝗣𝗔⁻` together with the collection scheme for `Hierarchy 𝚺 n`.
- [HP98, §I.2(a)] -/
abbrev BSigma (n : ℕ) : ArithmeticTheory := 𝗣𝗔⁻ ∪ CollectionScheme (Arithmetic.Hierarchy 𝚺 n)

prefix:max "𝗕𝚺 " => BSigma

notation "𝗕𝚺₁" => BSigma 1

variable {C C' : ArithmeticSemiformula ℕ 2 → Prop}

lemma CollectionScheme_subset (h : ∀ {φ : ArithmeticSemiformula ℕ 2}, C φ → C' φ) :
    CollectionScheme C ⊆ CollectionScheme C' := by
  rintro _ ⟨φ, hφ, rfl⟩; exact ⟨φ, h hφ, rfl⟩

lemma mem_CollectionScheme_of_mem {φ : ArithmeticSemiformula ℕ 2} (hφ : C φ) :
    .univCl (collectionAxiom φ) ∈ CollectionScheme C := ⟨φ, hφ, rfl⟩

lemma BSigma_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : 𝗕𝚺 s₁ ⊆ 𝗕𝚺 s₂ :=
  Set.union_subset_union_right _ (CollectionScheme_subset (fun H ↦ H.mono h))

lemma BSigma_weakerThan_of_le {s₁ s₂} (h : s₁ ≤ s₂) : 𝗕𝚺 s₁ ⪯ 𝗕𝚺 s₂ :=
  Entailment.WeakerThan.ofSubset (BSigma_subset_mono h)

instance (n : ℕ) : 𝗣𝗔⁻ ⪯ 𝗕𝚺 n := Entailment.WeakerThan.ofSubset Set.subset_union_left

instance (n : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ 𝗕𝚺 n :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

end axioms

section models

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- The reading of the collection axiom in a model of `𝗣𝗔⁻`.
- [HP98, §I.2(a)] -/
lemma models_collectionAxiom_iff (φ : ArithmeticSemiformula ℕ 2) :
    V↓[ℒₒᵣ] ⊧ .univCl (collectionAxiom φ) ↔
      ∀ f : ℕ → V, ∀ a : V, (∀ x < a, ∃ y, φ.Eval ![x, y] f) →
        ∃ b, ∀ x < a, ∃ y < b, φ.Eval ![x, y] f := by
  simp [models_iff, Semiformula.eval_univCl, collectionAxiom, Semiformula.eval_ballLT,
    Semiformula.eval_bexsLT, Semiformula.eval_substs]

end models

section BSigma_ISigma

/-- The substitution sending the two bound variables of `φ` to the outermost two bound variables
of the target semisentence, in reversed order (to match `sigma_exists_bound_witness`'s
witness-then-bound convention), and the free variables below `φ.fvSup` to the remaining bound
variables. -/
private noncomputable def paramSubst2 (φ : ArithmeticSemiformula ℕ 2) :
    Rew ℒₒᵣ ℕ 2 Empty (φ.fvSup + 2) :=
  Rew.bind ![#1, #0] fun x ↦ if h : x < φ.fvSup then #⟨x + 2, by omega⟩ else #0

/-- A `Semiformula ℒₒᵣ ℕ 2`, viewed as a semisentence whose extra bound variables are its free
variables. -/
private noncomputable def toSemisentence2 (φ : ArithmeticSemiformula ℕ 2) :
    ArithmeticSemisentence (φ.fvSup + 2) := paramSubst2 φ ▹ φ

private lemma eval_toSemisentence2 {M : Type*} [ORingStructure M]
    (φ : ArithmeticSemiformula ℕ 2) (x y : M) (f : ℕ → M) :
    M ⊧/(y :> x :> fun i : Fin φ.fvSup ↦ f i) (toSemisentence2 φ) ↔ φ.Eval ![x, y] f := by
  rw [toSemisentence2, Semiformula.eval_rew]
  have hb : (Semiterm.val (y :> x :> fun i : Fin φ.fvSup ↦ f i) (Empty.elim) ∘
      paramSubst2 φ ∘ Semiterm.bvar) = ![x, y] := by
    refine Fin.funext_two ?_ ?_ (fun i ↦ i.elim0)
    · simp [paramSubst2]
    · simp [paramSubst2]
  rw [hb]
  refine Semiformula.eval_iff_of_funEqOn φ fun z hz ↦ ?_
  have : z < φ.fvSup := Semiformula.lt_fvSup_of_fvar? hz
  simp [paramSubst2, this]

/-- Every collection axiom of `Hierarchy 𝚺 (n + 1)` is provable in `𝗜𝚺 (n + 1)`.
- [HP98, Theorem I.2.15] -/
theorem ISigma.provable_collectionAxiom_of_hierarchy (n : ℕ) {φ : ArithmeticSemiformula ℕ 2}
    (hφ : Hierarchy 𝚺 (n + 1) φ) : 𝗜𝚺 (n + 1) ⊢ .univCl (collectionAxiom φ) := by
  refine Arithmetic.complete.{0} _ _ ?_
  intro M _ hMT
  have hPA : M↓[ℒₒᵣ] ⊧* (𝗣𝗔⁻ : ArithmeticTheory) := mod_paMinus_of_ISigma (n := n + 1)
  rw [models_collectionAxiom_iff]
  intro f a h
  have hθ : Hierarchy 𝚺 (n + 1) (toSemisentence2 φ) := hφ.rew (paramSubst2 φ)
  have h' : ∀ x < a, ∃ u, M ⊧/(u :> x :> fun i : Fin φ.fvSup ↦ f i) (toSemisentence2 φ) := by
    intro x hx
    obtain ⟨y, hy⟩ := h x hx
    exact ⟨y, (eval_toSemisentence2 φ x y f).mpr hy⟩
  obtain ⟨w, hw⟩ := sigma_exists_bound_witness hθ (fun i : Fin φ.fvSup ↦ f i) a h'
  refine ⟨w + 1, fun x hx ↦ ?_⟩
  obtain ⟨u, hu, hux⟩ := hw x hx
  exact ⟨u, Arithmetic.lt_succ_iff_le.mpr hu, (eval_toSemisentence2 φ x u f).mp hux⟩

/-- `𝗕𝚺 (n + 1)` is at most as strong as `𝗜𝚺 (n + 1)`.
- [HP98, Theorem I.2.15] -/
theorem BSigma_weakerThan_ISigma (n : ℕ) : 𝗕𝚺 (n + 1) ⪯ 𝗜𝚺 (n + 1) :=
  Entailment.WeakerThan.ofAxm! (fun {σ} hσ ↦ by
    rcases hσ with hσ | ⟨φ, hφ, rfl⟩
    · exact Entailment.WeakerThan.pbl (h := inferInstance) (Entailment.by_axm hσ)
    · exact ISigma.provable_collectionAxiom_of_hierarchy n hφ)

end BSigma_ISigma

end LO.FirstOrder.Arithmetic
