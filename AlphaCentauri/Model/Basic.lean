module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Model
public import AlphaCentauri.ToFoundation.FirstOrder.Hierarchy
public import AlphaCentauri.ToFoundation.FirstOrder.Model.Basic
public import Foundation.FirstOrder.Arithmetic.Collection.Basic
public import Foundation.FirstOrder.Arithmetic.Definability.PrenexDefinable
public import Foundation.FirstOrder.Arithmetic.Exponential.Bit
public import Foundation.FirstOrder.Arithmetic.Induction.Equiv
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
public import Foundation.FirstOrder.Arithmetic.Schema.DeltaInduction
public import Foundation.FirstOrder.Arithmetic.Schemata
public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Absoluteness

/-! # End extensions, cuts and elementary embeddings of models of arithmetic

-/

@[expose] public section

namespace FFL.FirstOrder

universe u v w

open Semiformula Tarski.Structure Arithmetic

/-! ## End extensions -/

/-- An end extension of `ℒₒᵣ`-structures: an embedding with nothing new below its image.
- [HP98, Definition IV.1.3(2)]
- [vO99, §3.1] -/
notation:50 M " ⊆ₑ " N => EndExtension ℬ[<, ℒₒᵣ] M N

/-- A proper end extension of `ℒₒᵣ`-structures: an end extension which is not surjective.
- [HP98, Definition IV.1.14]
- [vO99, §3.2] -/
notation:50 M " ⊂ₑ " N => ProperEndExtension ℬ[<, ℒₒᵣ] M N

namespace EndExtension

section

variable {M : Type u} {N : Type v} [ORingStructure M] [ORingStructure N] (e : M ⊆ₑ N)
  (ι : M ↪ₛ[ℒₒᵣ] N)

@[simp, grind =]
lemma emb_lt_emb {x y : M} : e x < e y ↔ x < y :=
  EmbeddingClass.map_lt_map_iff e.emb

lemma mem_range_of_lt {a : M} {b : N} (h : b < e a) : b ∈ Set.range e.emb :=
  e.isInitial.initial (R := Semiformula.Operator.LT.lt) (Set.mem_singleton _) a b (by simpa using h)

/-- The end extension given by an embedding whose image is closed downward under `<`.
- [Kay91, Definition 2.6] -/
def ofInitial (hι : ∀ x y, y < ι x → y ∈ Set.range ι) : M ⊆ₑ N where
  emb := ι
  isInitial := {
    operator_iff := by
      intro R hR a b
      obtain rfl := Set.mem_singleton_iff.mp hR
      simp
    initial := by
      intro R hR a b hb
      obtain rfl := Set.mem_singleton_iff.mp hR
      exact hι a b (by simpa using hb)
  }

@[simp]
lemma ofInitial_apply (hι : ∀ x y, y < ι x → y ∈ Set.range ι) (x : M) :
    ofInitial ι hι x = ι x := rfl

include e

/-- A structure with an end extension modelling `𝗣𝗔⁻` is itself a model of `𝗣𝗔⁻`.
- [vO99, Exercise 40] -/
theorem models_peanoMinus [N↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_theory_iff.mpr <| by
  intro σ hσ
  rcases hσ
  case equal hσ =>
    have h₁ : M↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance
    exact models_theory_iff.mp h₁ _ hσ
  case addZero | addAssoc | addComm | mulZero | mulOne | mulAssoc | mulComm | distr =>
    simp [models_iff, ← e.emb_eq_emb, add_comm, add_left_comm, mul_comm, mul_left_comm, mul_add]
  case addEqOfLt =>
    suffices ∀ x y : M, x < y → ∃ z < y + 1, x + z = y by
      simpa [models_iff, Semiformula.eval_bexsLTSucc] using this
    intro x y h
    obtain ⟨z, hz, hzeq⟩ :=
      Arithmetic.add_eq_of_lt_bounded (e x) (e y) (by simpa using h)
    have h₁ : z ≤ e y := hzeq ▸ le_add_self
    obtain ⟨w, rfl⟩ : z ∈ Set.range e :=
      h₁.lt_or_eq.elim e.mem_range_of_lt fun h₂ ↦ ⟨y, h₂.symm⟩
    use w
    and_intros
    · exact e.emb_lt_emb.mp (by simpa using hz)
    · exact e.emb_injective (by simpa using hzeq)
  case zeroLe =>
    suffices ∀ x : M, 0 ≤ x by simpa [models_iff, le_iff_of_eq_of_lt, le_def] using this
    intro x
    rcases le_def.mp (Arithmetic.zero_le (e x)) with h | h
    · exact le_def.mpr <| Or.inl <| e.emb_injective (by simpa using h)
    · exact le_def.mpr <| Or.inr <| e.emb_lt_emb.mp (by simpa using h)
  case zeroLtOne =>
    suffices (0 : M) < 1 by simpa [models_iff] using this
    exact e.emb_lt_emb.mp (by simp)
  case oneLeOfZeroLt =>
    suffices ∀ x : M, 0 < x → 1 ≤ x by
      simpa [models_iff, le_iff_of_eq_of_lt, le_def] using this
    intro x h
    have h₁ : (0 : N) < e x := by simpa using e.emb_lt_emb.mpr h
    rcases le_def.mp (one_le_of_zero_lt _ h₁) with h₂ | h₂
    · exact le_def.mpr <| Or.inl <| e.emb_injective (by simpa using h₂)
    · exact le_def.mpr <| Or.inr <| e.emb_lt_emb.mp (by simpa using h₂)
  case addLtAdd =>
    suffices ∀ x y z : M, x < y → x + z < y + z by simpa [models_iff] using this
    intro x y z h
    exact e.emb_lt_emb.mp (by simpa using add_lt_add _ _ (e z) (e.emb_lt_emb.mpr h))
  case mulLtMul =>
    suffices ∀ x y z : M, x < y → 0 < z → x * z < y * z by simpa [models_iff] using this
    intro x y z h hz
    have h₁ : (0 : N) < e z := by simpa using e.emb_lt_emb.mpr hz
    exact e.emb_lt_emb.mp (by simpa using mul_lt_mul _ _ (e z) (e.emb_lt_emb.mpr h) h₁)
  case ltIrrefl =>
    suffices ∀ x : M, ¬x < x by simpa [models_iff] using this
    intro x h
    exact Arithmetic.lt_irrefl (e x) (by grind)
  case ltTrans =>
    simpa [models_iff] using fun x y z : M ↦ Arithmetic.lt_trans (e x) (e y) (e z)
  case ltTri =>
    simpa [models_iff, e.emb_eq_emb] using fun x y : M ↦ lt_tri (e x) (e y)

/-- A structure with an end extension modelling `𝗜𝚺₀` is itself a model of `𝗜𝚺₀`.
- [HP98, Remark IV.1.21(2)] -/
theorem models_ISigma0 [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := e.models_peanoMinus
  have hind {φ : ArithmeticSemiformula ℕ 1} (hφ : ℬ[<, ℒₒᵣ].Closure φ) (v : ℕ → M)
      (h0 : φ.Eval ![0] v) (hs : ∀ x, φ.Eval ![x] v → φ.Eval ![x + 1] v) (a : M) :
      φ.Eval ![a] v := by
    have h₁ : ∀ x : M, φ.Eval ![x] v ↔ φ.Eval ![e x] (e.emb ∘ v) := by
      intro x
      simpa [Matrix.comp_vecCons'', Matrix.empty_eq] using
        Bounding.bounded_absolute e.emb hφ ![x] v
    have h₂ : ∀ y : N, y < e a + 1 → φ.Eval ![y] (e.emb ∘ v) := by
      refine InductionScheme.succ_induction (C := ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0)
        ⟨(e a + 1) :>ₙ fun j ↦ e (v j),
          “#0 < &0” 🡒 (Rew.rewriteMap Nat.succ ▹ φ), by simp [hφ.hierarchy],
          by intro x; simp [Semiformula.eval_rewriteMap, Function.comp_def]⟩
        (by intro _; simpa using (h₁ 0).mp h0) ?_
      intro y ih hy
      have h₃ : y < e a := lt_of_lt_of_le (lt_add_one y) (lt_succ_iff_le.mp hy)
      obtain ⟨x, rfl⟩ := e.mem_range_of_lt h₃
      simpa using (h₁ (x + 1)).mp (hs x ((h₁ x).mpr (ih (lt_trans h₃ (lt_add_one _)))))
    exact (h₁ a).mpr (h₂ (e a) (by simp))
  simp only [Semantics.ModelsSet.union_iff, InductionScheme]
  and_intros
  · exact this
  · apply Semantics.ModelsSet.setOf_iff.mpr
    rintro _ ⟨φ, hφ, rfl⟩
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs]
      using hind (Bounding.PrenexHierarchy.zero_iff_bounded.mp hφ)

end

end EndExtension

namespace Arithmetic

/-! ## Nonstandard elements -/

section

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- `c` is nonstandard: above every natural number. -/
def IsNonstandardElement (c : M) : Prop := ∀ m : ℕ, (m : M) < c

variable (M)

/-- The nonstandard elements of `M`. -/
def NonstandardElement : Type _ :=
  {c : M // IsNonstandardElement c}

/-- `M` is nonstandard: it has a nonstandard element. -/
abbrev IsNonstandard : Prop :=
  Nonempty (NonstandardElement M)

variable {M} {c : M} (h : IsNonstandardElement c) (a : NonstandardElement M) (m : ℕ)

include h in
lemma IsNonstandardElement.natCast_lt : (m : M) < c := h m

instance : CoeOut (NonstandardElement M) M := ⟨Subtype.val⟩

lemma NonstandardElement.isNonstandardElement (c : NonstandardElement M) :
    IsNonstandardElement (c : M) := c.2

@[simp]
lemma NonstandardElement.natCast_lt : (m : M) < a := a.2 m

lemma isNonstandardElement_iff_not_mem_range :
    IsNonstandardElement c ↔ c ∉ Set.range (Nat.cast : ℕ → M) := by
  constructor
  · rintro h ⟨n, rfl⟩
    exact Arithmetic.lt_irrefl _ (h n)
  · intro h m
    by_contra! hc
    obtain ⟨n, rfl⟩ := eq_nat_of_le_nat hc
    exact h ⟨n, rfl⟩

end

/-! ## Overspill -/

section

variable (M : Type*) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] [IsNonstandard M]

/-- The natural numbers as a proper end extension of a nonstandard model. -/
def natCastProperEndExtension : ℕ ⊂ₑ M where
  emb := natCastEmbedding M
  isInitial := inferInstance
  not_surjective := by
    intro h
    obtain ⟨c, hc⟩ := Classical.arbitrary (NonstandardElement M)
    exact isNonstandardElement_iff_not_mem_range.mp hc (h c)

end

section

variable {M : Type u} {N : Type v} [ORingStructure M] [ORingStructure N] (e : M ⊂ₑ N)
  (Γ : Polarity) (m : ℕ) [N↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ m]

/-- Overspill: a formula of the induction class holding at every element of the base model holds
below some element outside it.
- [HP98, Corollary IV.1.16]
- [vO99, Lemma 3.2, Corollary 3.3] -/
theorem overspill {φ : ArithmeticSemiformula ℕ 1} (hφ : ℬ[<, ℒₒᵣ].Hierarchy Γ m φ) (f : ℕ → N)
    (h : ∀ a : M, φ.Eval ![e a] f) : ∃ c : N, c ∉ Set.range e.emb ∧ ∀ x < c, φ.Eval ![x] f := by
  have : N↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : N↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ m)
  by_contra! hc
  have h₁ : ∀ x : N, (∀ y < x, φ.Eval ![y] f) → x ∈ Set.range e.emb := by grind;
  have h₂ : ∀ x : N, (∀ y < x, φ.Eval ![y] f) → ∀ y < x + 1, φ.Eval ![y] f := by
    intro x ih y hy;
    obtain ⟨a, rfl⟩ := h₁ x ih;
    rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hy) with hy' | rfl
    · exact ih y hy'
    · exact h a
  have h₃ : ∀ x : N, ∀ y < x, φ.Eval ![y] f :=
    InductionScheme.succ_induction (C := ℬ[<, ℒₒᵣ].Hierarchy Γ m)
      ⟨f, (φ/[#0]).ballLT #0, by simp [hφ], fun x ↦ by simp [eval_ballLT]⟩
      (by simp) h₂
  apply e.not_surjective
  intro x
  exact h₁ x (h₃ x)

/-- Overspill: a definable predicate of the induction class holding at every element of the base
model holds at some element outside it.
- [HP98, Corollary IV.1.16] -/
lemma overspill_definablePred {P : N → Prop}
    (hP : Γᴬ_[m].DefinablePred P) (h : ∀ a : M, P (e a)) : ∃ c : N, c ∉ Set.range e.emb ∧ P c := by
  have : N↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : N↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ m)
  by_contra! hc
  apply e.not_surjective
  intro x
  by_contra hx
  apply hc x hx
  apply InductionOnHierarchy.succ_induction Γ m hP
  · simpa using h 0
  · intro y hy
    obtain ⟨a, rfl⟩ : y ∈ Set.range e.emb := by grind
    simpa using h (a + 1)

end

/-! ## Cuts -/

section

variable (M : Type u) [ORingStructure M]

/-- A cut of `M`: a subset closed under successor and downward closed under `<`.
- [HP98, Definition IV.1.14] -/
structure Cut where
  carrier : Set M
  succ_mem {a : M} : a ∈ carrier → a + 1 ∈ carrier
  mem_of_lt {a b : M} : a < b → b ∈ carrier → a ∈ carrier

/-- A cut closed under the operations of `ℒₒᵣ`, hence a substructure of `M`.
- [HP98, Definition IV.2.8(2)] -/
structure ClosedCut extends Cut M where
  zero_mem : (0 : M) ∈ carrier
  one_mem : (1 : M) ∈ carrier
  add_mem {a b : M} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  mul_mem {a b : M} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier

variable {M}

namespace ClosedCut

variable (I : ClosedCut M)

instance oringStructure : ORingStructure I.carrier where
  zero := ⟨0, I.zero_mem⟩
  one := ⟨1, I.one_mem⟩
  add a b := ⟨a.1 + b.1, I.add_mem a.2 b.2⟩
  mul a b := ⟨a.1 * b.1, I.mul_mem a.2 b.2⟩
  lt a b := a.1 < b.1

/-- `M` is an end extension of each of its closed cuts.
- [HP98, Definition IV.1.3(2)] -/
def endExtension : I.carrier ⊆ₑ M :=
  .ofInitial {
    toFun := Subtype.val
    func' f v := by cases f <;> rfl
    rel' r _ := by cases r; exacts [congrArg Subtype.val, id]
    toFun_inj := Subtype.val_injective
    rel_inv' r _ := by cases r; exacts [Subtype.ext, id]
  } (by
    intro a b hb
    use ⟨b, I.mem_of_lt hb a.2⟩
    rfl)

@[simp]
lemma endExtension_apply (x : I.carrier) : I.endExtension x = x.val := rfl

section

variable {N : Type v} [ORingStructure N] (ι : M ↪ₛ[ℒₒᵣ] N)
  (hι : ∀ x y, y < ι x → y ∈ Set.range ι)

/-- The image of an embedding which is closed downward under `<`, as a closed cut. -/
def ofEmbedding : ClosedCut N where
  carrier := Set.range ι
  succ_mem := by
    rintro _ ⟨x, rfl⟩
    use x + 1
    simp
  mem_of_lt := by
    rintro y _ hy ⟨x, rfl⟩
    exact hι x y hy
  zero_mem := by
    use 0
    simp
  one_mem := by
    use 1
    simp
  add_mem := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    use x + y
    simp
  mul_mem := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    use x * y
    simp

@[simp]
lemma carrier_ofEmbedding : (ofEmbedding ι hι).carrier = Set.range ι := rfl

/-- An embedding whose image is closed downward under `<` is an isomorphism onto its image. -/
def isoOfEmbedding : M ≃ₛ[ℒₒᵣ] (ofEmbedding ι hι).carrier where
  toFun x := ⟨ι x, Set.mem_range_self x⟩
  func' f w := by
    apply Subtype.ext
    cases f <;> exact HomClass.func ι _ w
  rel' r w h := by
    cases r
    · exact Subtype.ext <| congrArg ι (show w 0 = w 1 from h)
    · exact (EmbeddingClass.map_lt_map_iff ι).mpr h
  toFun_inj x y h := EmbeddingClass.map_inj ι (congrArg Subtype.val h)
  rel_inv' r w h := by
    cases r
    · exact EmbeddingClass.map_inj ι (congrArg Subtype.val h)
    · exact (EmbeddingClass.map_lt_map_iff ι).mp h
  toFun_bij := by
    and_intros
    · intro x y h
      exact EmbeddingClass.map_inj ι (congrArg Subtype.val h)
    · rintro ⟨_, x, rfl⟩
      use x

@[simp]
lemma endExtension_isoOfEmbedding (x : M) :
    (ofEmbedding ι hι).endExtension (isoOfEmbedding ι hι x) = ι x := rfl

end

end ClosedCut

variable (I : Cut M)

/-- A cut is proper when it contains `0` and omits some element.
- [HP98, Definition IV.1.14]
- [Sla04, §1.1] -/
structure Cut.Proper : Prop where
  zero_mem : (0 : M) ∈ I.carrier
  exists_not_mem : ∃ c, c ∉ I.carrier

/-- A cut definable by a $\Sigma_0$ formula with parameters is not proper.
- [HP98, Observation IV.1.15] -/
lemma Cut.not_proper_of_definable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (hI : 𝚺ᴬ₀.DefinablePred (· ∈ I.carrier)) : ¬I.Proper := by
  rintro ⟨h0, c, hc⟩
  exact hc <| ISigma0.succ_induction (P := (· ∈ I.carrier)) hI h0 (fun _ hx ↦ I.succ_mem hx) c

/-- A proper cut whose membership relation and complement are both definable by prenex $\Sigma_n$
formulas with parameters refutes $\Delta_s$ induction.
- [Sla04, §1.1] -/
lemma not_models_IDelta_of_proper_cut (n : ℕ) (hI : I.Proper)
    (hσ : PrenexDefinablePred 𝚺 n (· ∈ I.carrier))
    (hπ : PrenexDefinablePred 𝚺 n (· ∉ I.carrier)) : ¬M↓[ℒₒᵣ] ⊧* 𝗜𝚫 n := by
  intro hM
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_of_ss hM Set.subset_union_left
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (s := 0)
  have : M↓[ℒₒᵣ] ⊧* DeltaInductionScheme (ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 n) :=
    models_of_ss hM Set.subset_union_right
  obtain ⟨e₁, φ, hφ, hφe⟩ := PrenexDefinable.exists_eval_iff hσ
  obtain ⟨e₂, ψ, hψ, hψe⟩ := PrenexDefinable.exists_eval_iff hπ
  have heven : ∀ k : ℕ, 2 * k % 2 = 0 := by intro k; omega
  have hodd : ∀ k : ℕ, (2 * k + 1) % 2 ≠ 0 := by intro k; omega
  have hhalf₁ : ∀ k : ℕ, 2 * k / 2 = k := by intro k; omega
  have hhalf₂ : ∀ k : ℕ, (2 * k + 1) / 2 = k := by intro k; omega
  let e : ℕ → M := fun k ↦ if k % 2 = 0 then e₁ (k / 2) else e₂ (k / 2)
  have hφ' : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 n (Rew.rewriteMap (fun k : ℕ ↦ 2 * k) ▹ φ) :=
    hφ.rew _
  have hψ' : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 n (Rew.rewriteMap (fun k : ℕ ↦ 2 * k + 1) ▹ ψ) :=
    hψ.rew _
  have h₁ : ∀ x : M, (Rew.rewriteMap (fun k : ℕ ↦ 2 * k) ▹ φ).Eval ![x] e ↔ x ∈ I.carrier := by
    intro x
    simpa [Semiformula.eval_rewriteMap, e, heven, hhalf₁] using (hφe ![x]).symm
  have h₂ : ∀ x : M, (Rew.rewriteMap (fun k : ℕ ↦ 2 * k + 1) ▹ ψ).Eval ![x] e ↔ x ∉ I.carrier := by
    intro x
    simpa [Semiformula.eval_rewriteMap, e, hodd, hhalf₂] using (hψe ![x]).symm
  obtain ⟨h0, c, hc⟩ := hI
  have hind := (models_deltaInd_iff _ _).mp
    (Theory.models (T := DeltaInductionScheme (ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 n)) M
      (mem_DeltaInductionScheme_of_mem hφ' hψ')) e
    (by intro x; rw [h₁ x, h₂ x, not_not])
    ((h₁ 0).mpr h0) (fun x hx ↦ (h₁ (x + 1)).mpr (I.succ_mem ((h₁ x).mp hx)))
  exact hc ((h₁ c).mp (hind c))

end

/-! ## Elementary embeddings of models of arithmetic -/

section

variable {S : Type u} {M : Type v} [ORingStructure S] [ORingStructure M] {ι : S ↪ₛ[ℒₒᵣ] M}
  [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- A $\Delta_0$-elementary substructure of a model of `𝗣𝗔⁻` is a model of `𝗣𝗔⁻`.
- [HP98, Remark IV.1.21(2)] -/
theorem _root_.FFL.FirstOrder.IsElementary.models_peanoMinus
    (hι : IsElementary (fun {_} φ ↦ ℬ[<, ℒₒᵣ].Closure φ) ι) : S↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := by
  have h {Γ : Polarity} {n : ℕ} {φ : ArithmeticSemiformula ℕ n}
      (hφ : ℬ[<, ℒₒᵣ].PrenexBlock Γ φ) (hΓ : Γ = 𝚷) (e : Fin n → S) (f : ℕ → S) :
      φ.Eval (ι ∘ e) (ι ∘ f) → φ.Eval e f := by
    induction hφ with
    | bounded h =>
      exact (hι h e f).mp
    | exs => simp at hΓ
    | all _ ih =>
      simp only [eval_all]
      intro h₁ x
      exact ih rfl (x :> e) (by simpa [Matrix.comp_vecCons''] using h₁ (ι x))
  apply models_theory_iff.mpr
  intro σ hσ
  have h₁ := models_theory_iff.mp (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻) σ hσ
  simpa [models_iff] using h ((PeanoMinus.prenexBlock σ hσ).rew Rew.emb) rfl ![] (fun _ ↦ 0)
    (by simpa [models_iff] using h₁)

/-- If `S` embeds onto a $\Sigma_n$-elementary initial segment of a model `M` of `𝗣𝗔⁻`, a
$\Pi_n$ formula satisfiable in `S` with the parameter `c` is satisfiable in `M`, with the image of
`c` as parameter, below any element outside the image.
- [Kay91, Theorem 12.3] -/
theorem exists_lt_of_initialSegmentEmbedding {n : ℕ} (hι : ∀ x y, y < ι x → y ∈ Set.range ι)
    (hel : IsElementary (fun {_} φ ↦ ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n φ) ι) {b : M}
    (hb : b ∉ Set.range ι) {c : S} {θ : ArithmeticSemisentence 2}
    (hθ : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 n θ) (h : ∃ x : S, S ⊧/![x, c] θ) : ∃ x < b, M ⊧/![x, ι c] θ := by
  obtain ⟨x, hx⟩ := h
  use ι x
  and_intros
  · rcases lt_trichotomy (ι x) b with h | rfl | h
    · exact h
    · exact (hb (Set.mem_range_self x)).elim
    · exact (hb (hι x b h)).elim
  · have h₁ := hel (φ := Rewriting.emb (∼θ)) (hθ.neg.rew Rew.emb) ![x, c] (fun _ ↦ c)
    simpa [Matrix.comp_vecCons''] using h₁.not.mpr (by simpa using hx)

end

section

variable {S M : Type} [ORingStructure S] [ORingStructure M]

/-- A $\Sigma_s$-elementary embedding preserves the truth of $\Sigma_s$ and $\Pi_s$ sentences
between models of $\mathsf{B}\Sigma_s$. -/
lemma _root_.FFL.FirstOrder.IsElementary.models_iff_of_hierarchy {ι : S ↪ₛ[ℒₒᵣ] M} {s : ℕ}
    (hι : IsElementary (ℬ[<, ℒₒᵣ].PrenexHierarchyLE s) ι)
    [S↓[ℒₒᵣ] ⊧* 𝗕𝚺s] [M↓[ℒₒᵣ] ⊧* 𝗕𝚺s] {Γ : Polarity} {n : ℕ} {φ : ArithmeticSemisentence n}
    (hφ : ℬ[<, ℒₒᵣ].Hierarchy Γ s φ) (v : Fin n → S) : M ⊧/(ι ∘ v) φ ↔ S ⊧/v φ := by
  obtain ⟨φ', hφ'⟩ := Bounding.Prenex.models_exists_prenex.{_, 0} (Γ' := 𝚺) hφ
  rw [hφ' M, hφ' S]
  have := hι ⟨s, le_rfl, Γ, (φ'.rew Rew.emb).val_prenexHierarchy⟩ v (fun _ ↦ 0)
  rwa [Bounding.Prenex.val_rew, eval_emb, eval_emb] at this

end

/-! ## The standard system -/

section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The set of standard natural numbers coded by `a` under Ackermann's membership.
- [Kay91, Exercise 11.4(a)] -/
def codedSet (a : V) : Set ℕ := {n | (n : V) ∈ a}

@[simp]
lemma mem_codedSet {a : V} {n : ℕ} : n ∈ codedSet a ↔ (n : V) ∈ a := Iff.rfl

variable (V) in
/-- The standard system: the subsets of `ℕ` coded by some element of `V`.
- [Kay91, §11.1, Exercise 11.4(a)] -/
def standardSystem : Set (Set ℕ) := Set.range (codedSet (V := V))

lemma mem_standardSystem_of_finite {S : Set ℕ} (hS : S.Finite) : S ∈ standardSystem V := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    use ∅
    ext
    simp
  | @insert n S _ _ ih =>
    obtain ⟨a, rfl⟩ := ih
    use insert (n : V) a
    ext
    simp

/-- The standard system of `ℕ` is the family of finite subsets of `ℕ`.
- [Kay91, Exercise 11.1] -/
lemma standardSystem_nat : standardSystem ℕ = {S | S.Finite} := by
  ext S
  constructor
  · rintro ⟨a, rfl⟩
    apply (Set.finite_lt_nat a).subset
    intro n hn
    exact lt_of_mem (by simpa using hn)
  · apply mem_standardSystem_of_finite

end

end Arithmetic

/-! ## The standard system along end extensions -/

namespace EndExtension

variable {M N : Type*} [ORingStructure M] [ORingStructure N] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
  (e : M ⊆ₑ N)

@[simp]
lemma emb_natCast (n : ℕ) : e n = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.cast_succ, ih]

@[simp]
lemma emb_mem_emb_iff {i a : M} : e i ∈ e a ↔ i ∈ a := by
  simpa using (Bounding.HierarchySymbol.Defined.sigmaZero_absolute e.emb
    (bit_defined (V := M)) (bit_defined (V := N)) ![i, a]).symm

@[simp]
lemma codedSet_emb (a : M) : codedSet (e a) = codedSet a := by
  ext n
  simpa using e.emb_mem_emb_iff (i := (n : M)) (a := a)

end EndExtension

namespace Arithmetic

variable {M N : Type*} [ORingStructure M] [ORingStructure N] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
  (e : M ⊆ₑ N) [IsNonstandard M]

omit [IsNonstandard M] in
include e in
/-- The standard system of a model of `𝗜𝚺₁` is contained in that of an end extension which
again models `𝗜𝚺₁`.
- [Kay91, Chapter 12, p. 159] -/
lemma standardSystem_subset_of_endExtension : standardSystem M ⊆ standardSystem N := by
  rintro _ ⟨a, rfl⟩
  use e a
  exact e.codedSet_emb a

include e in
/-- A nonstandard model of `𝗜𝚺₁` and an end extension of it which again models `𝗜𝚺₁` have the same
standard system.
- [Kay91, Chapter 12, p. 159] -/
theorem standardSystem_eq_of_endExtension : standardSystem M = standardSystem N := by
  apply (standardSystem_subset_of_endExtension e).antisymm
  rintro _ ⟨a, rfl⟩
  obtain ⟨c, hc⟩ := Classical.arbitrary (NonstandardElement M)
  have h₁ : ∀ m : ℕ, (m : N) < e c := by
    intro m
    simpa using e.emb_lt_emb.mpr (hc.natCast_lt m)
  have h₂ : 0 < e c := by simpa using h₁ 0
  obtain ⟨s, hs, h₃⟩ := finset_comprehension₁ (Γ := 𝚺) (P := (· ∈ a)) (by definability) (log (e c))
  obtain ⟨x, rfl⟩ := e.mem_range_of_lt (hs.trans_le (exp_log_le_self h₂))
  use x
  ext n
  rw [← e.codedSet_emb]
  apply h₃
  have h₄ : ((n + 1 : ℕ) : N) ≤ log (e c) :=
    (exp_le_iff_le_log h₂).mp (nat_cast_exp (V := N) (n + 1) ▸ (h₁ _).le)
  exact (Nat.cast_lt.mpr n.lt_succ_self).trans_le h₄

/-- A nonstandard model of `𝗜𝚺₁` embedded onto an initial segment of a model of `𝗜𝚺₁` has the same
standard system as that model.
- [Kay91, Theorem 12.3] -/
theorem standardSystem_eq_of_initialSegmentEmbedding
    {ι : M ↪ₛ[ℒₒᵣ] N} (hι : ∀ x y, y < ι x → y ∈ Set.range ι) :
    standardSystem M = standardSystem N :=
  standardSystem_eq_of_endExtension (.ofInitial ι hι)

end Arithmetic

end FFL.FirstOrder
