module

public import Foundation.FirstOrder.Arithmetic.BoundedCollection
public import AlphaCentauri.Vorspiel.Definable
public import AlphaCentauri.Vorspiel.Fvar

/-!
# The collection schemata `𝗕𝚺` and `𝗕𝚷`

- [HP98, §I.2(a)]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

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

/-- `𝗕 Γ n` is `𝗜𝚺₀` together with the collection scheme for `Hierarchy Γ n`.
- [HP98, I.2.3] -/
abbrev CollectionOnHierarchy (Γ : Polarity) (n : ℕ) : ArithmeticTheory :=
  𝗜𝚺₀ ∪ CollectionScheme (Arithmetic.Hierarchy Γ n)

prefix:max "𝗕 " => CollectionOnHierarchy

/-- The collection scheme for `𝚺-[n]` formulas.
- [HP98, I.2.3] -/
abbrev BSigma (n : ℕ) : ArithmeticTheory := 𝗕 𝚺 n

prefix:max "𝗕𝚺 " => BSigma

notation "𝗕𝚺₁" => BSigma 1

/-- The collection scheme for `𝚷-[n]` formulas.
- [HP98, I.2.3] -/
abbrev BPi (n : ℕ) : ArithmeticTheory := 𝗕 𝚷 n

prefix:max "𝗕𝚷 " => BPi

variable {C C' : ArithmeticSemiformula ℕ 2 → Prop}

lemma CollectionScheme_subset (h : ∀ {φ : ArithmeticSemiformula ℕ 2}, C φ → C' φ) :
    CollectionScheme C ⊆ CollectionScheme C' := by
  rintro _ ⟨φ, hφ, rfl⟩; exact ⟨φ, h hφ, rfl⟩

lemma mem_CollectionScheme_of_mem {φ : ArithmeticSemiformula ℕ 2} (hφ : C φ) :
    .univCl (collectionAxiom φ) ∈ CollectionScheme C := ⟨φ, hφ, rfl⟩

variable {Γ : Polarity}

lemma CollectionOnHierarchy_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : 𝗕 Γ s₁ ⊆ 𝗕 Γ s₂ :=
  Set.union_subset_union_right _ (CollectionScheme_subset (fun H ↦ H.mono h))

lemma CollectionOnHierarchy_weakerThan_of_le {s₁ s₂} (h : s₁ ≤ s₂) : 𝗕 Γ s₁ ⪯ 𝗕 Γ s₂ :=
  WeakerThan.ofSubset (CollectionOnHierarchy_subset_mono h)

lemma CollectionOnHierarchy_subset_BSigma_succ (Γ : Polarity) (n : ℕ) : 𝗕 Γ n ⊆ 𝗕𝚺 (n + 1) :=
  Set.union_subset_union_right _ (CollectionScheme_subset (·.accum 𝚺))

lemma CollectionOnHierarchy_weakerThan_BSigma_succ (Γ : Polarity) (n : ℕ) : 𝗕 Γ n ⪯ 𝗕𝚺 (n + 1) :=
  WeakerThan.ofSubset (CollectionOnHierarchy_subset_BSigma_succ Γ n)

instance (Γ : Polarity) (n : ℕ) : 𝗜𝚺₀ ⪯ 𝗕 Γ n := WeakerThan.ofSubset Set.subset_union_left

instance (Γ : Polarity) (n : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ 𝗕 Γ n :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻ := inferInstance
  WeakerThan.trans this inferInstance

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

/-- The reading of the collection axiom at a semisentence whose extra bound variables carry the
parameters.
- [HP98, §I.2(a)] -/
lemma exists_bound_of_models_collectionAxiom {m : ℕ} {θ : ArithmeticSemisentence (m + 2)}
    (h : V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom
      (Rew.embSubsts (#1 :> #0 :> fun i : Fin m ↦ (&(i : ℕ) : ArithmeticSemiterm ℕ 2)) ▹ θ)) :
        ArithmeticSentence))
    (e : Fin m → V) (a : V) (hex : ∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) :
    ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
  set ψ : ArithmeticSemiformula ℕ 2 :=
    Rew.embSubsts (#1 :> #0 :> fun i : Fin m ↦ (&(i : ℕ) : ArithmeticSemiterm ℕ 2)) ▹ θ with hψdef
  set f : ℕ → V := fun i ↦ if hi : i < m then e ⟨i, hi⟩ else a with hf
  have heval : ∀ x y : V, ψ.Eval ![x, y] f ↔ V ⊧/(y :> x :> e) θ := by
    intro x y
    rw [hψdef]
    simp only [Semiformula.eval_embSubsts]
    refine Iff.of_eq (congrArg (fun b ↦ Semiformula.Evalb (M := V) b θ) ?_)
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ i =>
      cases i using Fin.cases with
      | zero => simp
      | succ i => simp [hf, i.isLt]
  obtain ⟨b, hb⟩ := (models_collectionAxiom_iff ψ).mp h f a
    fun x hx ↦ (hex x hx).imp fun u hu ↦ (heval x u).mpr hu
  exact ⟨b, fun x hx ↦ (hb x hx).imp fun u hu ↦ ⟨le_of_lt hu.1, (heval x u).mp hu.2⟩⟩

/-- The reading of the collection axiom at a `Γ-[s]`-definable relation.
- [HP98, §I.2(a)] -/
lemma exists_bound_of_definable {Γ : Polarity} {s : ℕ}
    (hcol : ∀ ψ : ArithmeticSemiformula ℕ 2, Hierarchy Γ s ψ →
      V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom ψ) : ArithmeticSentence))
    {R : V → V → Prop} (hR : Γ-[s].DefinableRel R) (a : V) (h : ∀ x < a, ∃ y, R x y) :
    ∃ b, ∀ x < a, ∃ y < b, R x y := by
  obtain ⟨e, ψ, hψ, hiff⟩ := exists_hierarchy_eval_iff hR
  have heval : ∀ x y : V, R x y ↔ ψ.Eval ![x, y] e := fun x y ↦ by simpa using hiff ![x, y]
  obtain ⟨b, hb⟩ := (models_collectionAxiom_iff ψ).mp (hcol ψ hψ) e a
    fun x hx ↦ (h x hx).imp fun y hy ↦ (heval x y).mp hy
  exact ⟨b, fun x hx ↦ (hb x hx).imp fun y hy ↦ ⟨hy.1, (heval x y).mpr hy.2⟩⟩

end models

section standardModel

instance models_CollectionOnHierarchy (Γ : Polarity) (n : ℕ) : ℕ↓[ℒₒᵣ] ⊧* 𝗕 Γ n := by
  refine Semantics.ModelsSet.union_iff.mpr ⟨inferInstance, Semantics.ModelsSet.setOf_iff.mpr ?_⟩
  rintro _ ⟨φ, -, rfl⟩
  rw [models_collectionAxiom_iff]
  intro f a h
  choose! g hg using h
  refine ⟨(Finset.range a).sup g + 1, ?_⟩
  intro x hx
  exact ⟨g x, Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_range.mpr hx)), hg x hx⟩

instance (Γ : Polarity) (n : ℕ) : Consistent (𝗕 Γ n) := (𝗕 Γ n).consistent_of_sound (Eq ⊥) rfl

end standardModel

section BSigma_ISigma

/-- Every collection axiom of `Hierarchy 𝚺 (n + 1)` is provable in `𝗜𝚺 (n + 1)`.
- [HP98, Lemma I.2.11] -/
theorem ISigma.provable_collectionAxiom_of_hierarchy (n : ℕ) {φ : ArithmeticSemiformula ℕ 2}
    (hφ : Hierarchy 𝚺 (n + 1) φ) : 𝗜𝚺 (n + 1) ⊢ .univCl (collectionAxiom φ) := by
  refine Arithmetic.complete.{0} _ _ ?_
  intro M _ hMT
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := n + 1)
  rw [models_collectionAxiom_iff]
  intro f a h
  obtain ⟨w, hw⟩ := sigma_exists_bound_witness (hφ.rew _) (fun i : Fin φ.fvSup ↦ f i) a <| by
    intro x hx
    obtain ⟨y, hy⟩ := h x hx
    exact ⟨y, (φ.eval_toSemisentence_two x y f).mpr hy⟩
  refine ⟨w + 1, ?_⟩
  intro x hx
  obtain ⟨u, hu, hux⟩ := hw x hx
  exact ⟨u, Arithmetic.lt_succ_iff_le.mpr hu, (φ.eval_toSemisentence_two x u f).mp hux⟩

/-- `𝗕𝚺 (n + 1)` is at most as strong as `𝗜𝚺 (n + 1)`.
- [HP98, Lemma I.2.11] -/
theorem BSigma_weakerThan_ISigma (n : ℕ) : 𝗕𝚺 (n + 1) ⪯ 𝗜𝚺 (n + 1) :=
  WeakerThan.ofAxm! <| by
    rintro σ (hσ | ⟨φ, hφ, rfl⟩)
    · exact WeakerThan.pbl (h := ISigma_weakerThan_of_le (Nat.zero_le _)) (by_axm hσ)
    · exact ISigma.provable_collectionAxiom_of_hierarchy n hφ

end BSigma_ISigma

end FFL.FirstOrder.Arithmetic
