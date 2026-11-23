module

public import AlphaCentauri.ToFoundation.FirstOrder.Axiomatizability
public import AlphaCentauri.ToFoundation.FirstOrder.ConstantExtension
public import AlphaCentauri.ToFoundation.FirstOrder.Hierarchy
public import Foundation.FirstOrder.LK.Completeness.CounterModel
public import Foundation.FirstOrder.LK.Soundness
public import Foundation.FirstOrder.Tarski.Eq
public import Foundation.FirstOrder.Tarski.Elementary
public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Absoluteness
public import Foundation.Vorspiel.Computability
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.DirectedInverseSystem

/-! # Elementary substructures, end extensions, types and definable elements

For a class $\Gamma$ of formulas of a language `L`, a $\Gamma$-elementary substructure of an
`L`-structure `N` is a structure `M` together with an embedding into `N` along which every formula
of $\Gamma$ takes the same truth value at elements of `M` as at their images. An elementary
substructure is a $\Gamma$-elementary substructure for every formula; a proper one is not
surjective. Models of a complete theory are elementarily equivalent. The Tarski–Vaught test reduces
elementarity for bounded formulas, and for the prenex formulas up to a level, to finding witnesses
in the substructure.

A countable elementary chain is a sequence of `L`-structures `M 0 ≼ₑ[L] M 1 ≼ₑ[L] M 2 ≼ₑ[L] ⋯`,
each an elementary substructure of the next. Composing the steps gives an elementary substructure
`M m ≼ₑ[L] M n` for every `m ≤ n`, and these form a directed system. Its union, the direct limit
of this system, is an elementary extension of every `M n`.

For a bounding `ℬ` of `L`, an end extension of `M` to `N` is an embedding of `M` into `N` whose
image is an initial segment for every bounding operator of `ℬ`. For `ℬ[<, L]` these are the end
extensions of models of arithmetic, and for `ℬ[∈, L]` those of models of set theory. Bounded
formulas are absolute along an end extension, so an end extension is a $\Delta_0$-elementary
substructure, and a $\Pi_1$-axiomatizable theory holds in `M` as soon as it holds in an end
extension of `M`.

A type over a structure `M` is a set of formulas in the free variables $\bar x$, with parameters
from `M`, that is finitely satisfied in `M`. A type over a theory `T` is a set $\Phi(\bar x)$ of
formulas such that $T + \Phi(\bar c)$ is consistent for new constants $\bar c$; it is one realized
in some model of the theory. `M` is recursively saturated when it realizes every recursive type
over it with finitely many parameters.

An element of `M` is definable over a set `A` by a class of formulas when it is the only element
satisfying some formula of the class with parameters from `A`; the definable closure of `A`
collects the elements definable over `A` by any formula.
-/

@[expose] public section

namespace FFL.FirstOrder

open Semiformula Tarski.Structure

universe u v w

/-! ## Embeddings -/

namespace Tarski.Structure.Embedding

variable {L : Language} {M : Type u} {N : Type v} {K : Type w} [Tarski.Structure L M]
  [Tarski.Structure L N] [Tarski.Structure L K]

variable (L M) in
/-- The identity embedding. -/
@[refl]
protected def refl : M ↪ₛ[L] M where
  toFun := id
  func' _ _ := rfl
  rel' _ _ h := h
  toFun_inj := Function.injective_id
  rel_inv' _ _ h := h

@[simp]
lemma refl_apply (x : M) : Embedding.refl L M x = x := rfl

/-- The composition of embeddings. -/
@[trans]
protected def trans (ι : M ↪ₛ[L] N) (κ : N ↪ₛ[L] K) : M ↪ₛ[L] K where
  toFun := κ ∘ ι
  func' f v := by simp [HomClass.func ι, HomClass.func κ, Function.comp_def]
  rel' r v h := HomClass.rel κ r _ (HomClass.rel ι r v h)
  toFun_inj := (EmbeddingClass.map_inj κ).comp (EmbeddingClass.map_inj ι)
  rel_inv' r v h := EmbeddingClass.map_rel_inv ι r v (EmbeddingClass.map_rel_inv κ r _ h)

@[simp]
lemma trans_apply (ι : M ↪ₛ[L] N) (κ : N ↪ₛ[L] K) (x : M) : ι.trans κ x = κ (ι x) := rfl

end Tarski.Structure.Embedding

/-! ## Elementary substructures -/

section

variable {L : Language} {M : Type u} {N : Type v} {K : Type w}
  [Tarski.Structure L M] [Tarski.Structure L N] [Tarski.Structure L K]

/-- `ι` is $\Gamma$-elementary: every formula of $\Gamma$ takes the same truth value at elements of
`M` as at their images.
- [Kay91, §2.2]
- [HP98, Definition IV.1.17] -/
def IsElementary (Γ : ∀ {n : ℕ}, Semiformula L ℕ n → Prop) (ι : M ↪ₛ[L] N) : Prop :=
  ∀ {n : ℕ} {φ : Semiformula L ℕ n}, Γ φ → ∀ (e : Fin n → M) (f : ℕ → M),
    φ.Eval (ι ∘ e) (ι ∘ f) ↔ φ.Eval e f

/-- The Tarski–Vaught test: an embedding is elementary as soon as every formula with parameters
from `M` and a witness in `N` has a witness in `M`.
- [Kay91, Theorem 0.5] -/
theorem IsElementary.of_tarskiVaught (ι : M ↪ₛ[L] N)
    (witness : ∀ {n : ℕ} (φ : Semiformula L ℕ (n + 1)) (e : Fin n → M) (f : ℕ → M),
      (∃ x : N, φ.Eval (x :> ι ∘ e) (ι ∘ f)) → ∃ x : M, φ.Eval (ι x :> ι ∘ e) (ι ∘ f)) :
    IsElementary (fun {_} _ ↦ True) ι := by
  intro n φ _ e f
  induction φ using Semiformula.rec' with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => exact (eval_hom_iff_of_open ι (φ := rel r v) (by simp)).symm
  | hnrel r v => exact (eval_hom_iff_of_open ι (φ := nrel r v) (by simp)).symm
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih =>
    simp only [eval_all]
    constructor
    · intro h x
      exact (ih (x :> e)).mp <| by simpa [Matrix.comp_vecCons''] using h (ι x)
    · intro h
      by_contra hn
      push Not at hn
      obtain ⟨x, hx⟩ := witness (∼φ) e f <| by simpa using hn
      exact (by simpa using hx : ¬φ.Eval (ι x :> ι ∘ e) (ι ∘ f)) <| by
        simpa [Matrix.comp_vecCons''] using (ih (x :> e)).mpr (h x)
  | hexs φ ih =>
    simp only [eval_ex]
    constructor
    · intro h
      obtain ⟨x, hx⟩ := witness φ e f h
      use x
      exact (ih (x :> e)).mp <| by simpa [Matrix.comp_vecCons''] using hx
    · rintro ⟨x, hx⟩
      use ι x
      simpa [Matrix.comp_vecCons''] using (ih (x :> e)).mpr hx

/-- An elementary embedding preserves the truth of sentences. -/
lemma IsElementary.models_iff [Nonempty M] [Nonempty N] {ι : M ↪ₛ[L] N}
    (h : IsElementary (fun {_} _ ↦ True) ι) (σ : Sentence L) : N↓[L] ⊧ σ ↔ M↓[L] ⊧ σ := by
  rw [FFL.FirstOrder.models_iff, FFL.FirstOrder.models_iff]
  simpa [Matrix.empty_eq] using h (φ := Rewriting.emb σ) trivial ![] fun _ ↦ Classical.ofNonempty

/-- An elementary embedding into a model of `T` is from a model of `T`. -/
lemma IsElementary.modelsTheory [Nonempty M] [Nonempty N] {ι : M ↪ₛ[L] N}
    (h : IsElementary (fun {_} _ ↦ True) ι) {T : Theory L} [N↓[L] ⊧* T] : M↓[L] ⊧* T :=
  ⟨fun σ hσ ↦ (h.models_iff σ).mp <| Semantics.ModelsSet.models _ hσ⟩

/-- A $\Gamma$-elementary substructure: an embedding of `M` into `N` which is $\Gamma$-elementary.
- [Kay91, §2.2] -/
structure ElementarySubstructureOn (Γ : ∀ {n : ℕ}, Semiformula L ℕ n → Prop)
    (M : Type u) (N : Type v) [Tarski.Structure L M] [Tarski.Structure L N] where
  emb : M ↪ₛ[L] N
  isElementary : IsElementary Γ emb

variable (L) in
/-- An elementary substructure.
- [Kay91, §0.1] -/
abbrev ElementarySubstructure (M : Type u) (N : Type v) [Tarski.Structure L M]
    [Tarski.Structure L N] :=
  ElementarySubstructureOn (L := L) (fun {_} _ ↦ True) M N

/-- A proper $\Gamma$-elementary substructure: a $\Gamma$-elementary substructure which is not
surjective. -/
structure ProperElementarySubstructureOn (Γ : ∀ {n : ℕ}, Semiformula L ℕ n → Prop)
    (M : Type u) (N : Type v) [Tarski.Structure L M] [Tarski.Structure L N]
    extends ElementarySubstructureOn Γ M N where
  not_surjective : ¬Function.Surjective emb

variable (L) in
/-- A proper elementary substructure. -/
abbrev ProperElementarySubstructure (M : Type u) (N : Type v) [Tarski.Structure L M]
    [Tarski.Structure L N] :=
  ProperElementarySubstructureOn (L := L) (fun {_} _ ↦ True) M N

@[inherit_doc ElementarySubstructureOn]
notation:50 M " ≼ₑ[" L "; " Γ "] " N => @ElementarySubstructureOn L Γ M N _ _

@[inherit_doc ProperElementarySubstructureOn]
notation:50 M " ≺ₑ[" L "; " Γ "] " N => @ProperElementarySubstructureOn L Γ M N _ _

@[inherit_doc]
notation:50 M " ≼ₑ[" L "] " N => ElementarySubstructure L M N

@[inherit_doc]
notation:50 M " ≺ₑ[" L "] " N => ProperElementarySubstructure L M N

variable {Γ Γ' : ∀ {n : ℕ}, Semiformula L ℕ n → Prop}

instance : CoeFun (M ≼ₑ[L; Γ] N) (fun _ ↦ M → N) := ⟨fun e ↦ e.emb⟩

instance : CoeFun (M ≺ₑ[L; Γ] N) (fun _ ↦ M → N) := ⟨fun e ↦ e.emb⟩

namespace ElementarySubstructureOn

variable (M Γ) in
/-- The identity $\Gamma$-elementary substructure. -/
@[refl]
protected def refl : M ≼ₑ[L; Γ] M where
  emb := .refl L M
  isElementary _ _ _ := Iff.rfl

@[simp]
lemma refl_apply (x : M) : ElementarySubstructureOn.refl M Γ x = x := rfl

/-- The composition of $\Gamma$-elementary substructures. -/
@[trans]
protected def trans (e₁ : M ≼ₑ[L; Γ] N) (e₂ : N ≼ₑ[L; Γ] K) : M ≼ₑ[L; Γ] K where
  emb := e₁.emb.trans e₂.emb
  isElementary hφ e f := (e₂.isElementary hφ (e₁ ∘ e) (e₁ ∘ f)).trans (e₁.isElementary hφ e f)

@[simp]
lemma trans_apply (e₁ : M ≼ₑ[L; Γ] N) (e₂ : N ≼ₑ[L; Γ] K) (x : M) :
    e₁.trans e₂ x = e₂ (e₁ x) := rfl

/-- A $\Gamma$-elementary substructure is $\Gamma'$-elementary for every $\Gamma'$ contained in
$\Gamma$. -/
def mono (e : M ≼ₑ[L; Γ] N) (h : ∀ {n : ℕ} {φ : Semiformula L ℕ n}, Γ' φ → Γ φ) :
    M ≼ₑ[L; Γ'] N where
  emb := e.emb
  isElementary hφ := e.isElementary (h hφ)

end ElementarySubstructureOn

/-- A proper $\Gamma$-elementary substructure is proper $\Gamma'$-elementary for every $\Gamma'$
contained in $\Gamma$. -/
def ProperElementarySubstructureOn.mono (e : M ≺ₑ[L; Γ] N)
    (h : ∀ {n : ℕ} {φ : Semiformula L ℕ n}, Γ' φ → Γ φ) : M ≺ₑ[L; Γ'] N where
  toElementarySubstructureOn := e.toElementarySubstructureOn.mono h
  not_surjective := e.not_surjective

def Tarski.Structure.Iso.toElementarySubstructure (f : M ≃ₛ[L] N) : M ≼ₑ[L] N where
  emb := f.toEmbedding
  isElementary := by
    apply IsElementary.of_tarskiVaught
    intro n φ e g ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := f.toFun_bij.2 x
    use a
    exact hx

lemma Tarski.Structure.ElementaryEquiv.of_elementarySubstructure [Nonempty M] [Nonempty N]
    (e : M ≼ₑ[L] N) : M ≡ₑ[L] N :=
  ⟨fun {σ} ↦ (IsElementary.models_iff e.isElementary σ).symm⟩

lemma Tarski.Structure.ElementaryEquiv.of_complete (T : Theory L) [Entailment.Complete T]
    (M : Type u) (N : Type v) [Nonempty M] [Nonempty N] [Tarski.Structure L M]
    [Tarski.Structure L N] [M↓[L] ⊧* T] [N↓[L] ⊧* T] : M ≡ₑ[L] N := by
  constructor
  intro σ
  rcases Entailment.Complete.con (𝓢 := T) σ with h | h
  · exact iff_of_true (models_of_provable inferInstance h) (models_of_provable inferInstance h)
  · have hM := models_of_provable (M := M) inferInstance h
    have hN := models_of_provable (M := N) inferInstance h
    simp only [models_iff, LogicalConnective.HomClass.map_neg] at hM hN ⊢
    exact iff_of_false hM hN

lemma Tarski.Structure.ElementaryEquiv.existsUnique_iff [Nonempty M] [Nonempty N] [L.Eq]
    [Tarski.Structure.Eq L M] [Tarski.Structure.Eq L N] [M ≡ₑ[L] N] (θ : Semisentence L 1) :
    (∃! x : M, M ⊧/![x] θ) ↔ ∃! y : N, N ⊧/![y] θ := by
  simpa [existsUnique, models_iff, ExistsUnique, Matrix.constant_eq_singleton] using
    ElementaryEquiv.models (L := L) (M₁ := M) (M₂ := N) (φ := ∃¹! θ)

end

/-! ## The Tarski–Vaught test for prenex formulas -/

section

variable {L : Language} {ℬ : Bounding L} {S : Type u} {M : Type v} [Tarski.Structure L S]
  [Tarski.Structure L M] (ι : S ↪ₛ[L] M)

lemma eval_ex_iff_of_witness {n : ℕ} {χ : Semiformula L ℕ (n + 1)} {e : Fin n → S} {f : ℕ → S}
    (witness : (∃ x : M, χ.Eval (x :> ι ∘ e) (ι ∘ f)) → ∃ x : S, χ.Eval (ι x :> ι ∘ e) (ι ∘ f))
    (h : ∀ x : S, χ.Eval (ι ∘ (x :> e)) (ι ∘ f) ↔ χ.Eval (x :> e) f) :
    (∃¹ χ).Eval (ι ∘ e) (ι ∘ f) ↔ (∃¹ χ).Eval e f := by
  simp only [eval_ex, Matrix.comp_vecCons''] at h ⊢
  constructor
  · intro h₁
    obtain ⟨x, hx⟩ := witness h₁
    use x
    exact (h x).mp hx
  · rintro ⟨x, hx⟩
    use ι x
    exact (h x).mpr hx

/-- The Tarski–Vaught test for prenex formulas: `ι` is elementary for the prenex $\Sigma_m$ and
$\Pi_m$ formulas, `m ≤ s`, when bounded formulas are absolute along `ι` and every prenex $\Pi_m$
formula, `m < s`, with parameters from `S` and a witness in `M` has a witness in `S`.
- [HP98, Lemma IV.1.19] -/
theorem IsElementary.prenexHierarchyLE_of_tarskiVaught (s : ℕ)
    (bounded : IsElementary (fun {_} φ ↦ ℬ.Closure φ) ι)
    (witness : ∀ m < s, ∀ {n : ℕ} {φ : Semiformula L ℕ (n + 1)}, ℬ.PrenexHierarchy 𝚷 m φ →
      ∀ (e : Fin n → S) (f : ℕ → S),
        (∃ x : M, φ.Eval (x :> ι ∘ e) (ι ∘ f)) → ∃ x : S, φ.Eval (ι x :> ι ∘ e) (ι ∘ f)) :
    IsElementary (ℬ.PrenexHierarchyLE s) ι := by
  suffices ∀ {Γ : Polarity} {m n : ℕ} {φ : Semiformula L ℕ n}, m ≤ s →
      ℬ.PrenexHierarchy Γ m φ → ∀ (e : Fin n → S) (f : ℕ → S),
        φ.Eval (ι ∘ e) (ι ∘ f) ↔ φ.Eval e f by
    rintro n φ ⟨m, hm, Γ, hφ⟩
    exact this hm hφ
  intro Γ m n φ hm hφ
  induction m generalizing Γ n φ with
  | zero => exact bounded (Bounding.PrenexHierarchy.zero_iff_bounded.mp hφ)
  | succ m ih =>
    intro e f
    rcases Γ
    · obtain ⟨ψ, hψ, rfl⟩ := Bounding.PrenexHierarchy.sigma_succ_iff.mp hφ
      exact eval_ex_iff_of_witness ι (witness m (by omega) hψ e f)
        fun x ↦ ih (by omega) hψ (x :> e) f
    · obtain ⟨ψ, hψ, rfl⟩ := Bounding.PrenexHierarchy.pi_succ_iff.mp hφ
      simpa using (eval_ex_iff_of_witness ι (witness m (by omega) hψ.neg e f)
        fun x ↦ ih (by omega) hψ.neg (x :> e) f).not

/-- The Tarski–Vaught test for bounded formulas: bounded formulas are absolute along `ι` as soon as
every bounded formula with parameters from `S` and a witness in `M` has a witness in `S`. -/
theorem IsElementary.bounded_of_tarskiVaught [L.LT]
    (witness : ∀ {n : ℕ} {φ : Semiformula L ℕ (n + 1)}, ℬ[<, L].Closure φ →
      ∀ (e : Fin n → S) (f : ℕ → S),
        (∃ x : M, φ.Eval (x :> ι ∘ e) (ι ∘ f)) → ∃ x : S, φ.Eval (ι x :> ι ∘ e) (ι ∘ f)) :
    IsElementary (fun {_} φ ↦ ℬ[<, L].Closure φ) ι := by
  intro n φ hφ
  exact Bounding.Closure.induction_open
    (P := fun n φ ↦ ∀ (e : Fin n → S) (f : ℕ → S), φ.Eval (ι ∘ e) (ι ∘ f) ↔ φ.Eval e f)
    (fun _ _ hφ _ _ ↦ (eval_hom_iff_of_open ι hφ).symm)
    (fun _ _ _ _ _ ihφ ihψ e f ↦ by simp [ihφ e f, ihψ e f])
    (fun _ _ _ _ _ ihφ ihψ e f ↦ by simp [ihφ e f, ihψ e f])
    (fun _ t θ hθ ih e f ↦ by
      have hχ : ℬ[<, L].Closure (“#0 < !!(Rew.bShift t)” ⋏ ∼θ) := .and (.of_open (by simp)) hθ.neg
      simpa [ball] using (eval_ex_iff_of_witness ι (witness hχ e f) fun x ↦ by
        simp [ih (x :> e) f, ← eval_hom_iff_of_open ι (φ := “#0 < !!(Rew.bShift t)”)]).not)
    (fun _ t θ hθ ih e f ↦ by
      have hχ : ℬ[<, L].Closure (“#0 < !!(Rew.bShift t)” ⋏ θ) := .and (.of_open (by simp)) hθ
      exact eval_ex_iff_of_witness ι (witness hχ e f) fun x ↦ by
        simp [ih (x :> e) f, ← eval_hom_iff_of_open ι (φ := “#0 < !!(Rew.bShift t)”)])
    hφ

end

/-! ## Elementary chains -/

section

variable (L : Language) in
/-- A countable elementary chain: a sequence of `L`-structures
`M 0 ≼ₑ[L] M 1 ≼ₑ[L] M 2 ≼ₑ[L] ⋯`.
- [Kay91, Lemma 0.6] -/
structure ElementaryChain (M : ℕ → Type u) [∀ n, Tarski.Structure L (M n)] where
  step : ∀ n, M n ≼ₑ[L] M (n + 1)

namespace ElementaryChain

variable {L : Language} {M : ℕ → Type u} [∀ n, Tarski.Structure L (M n)]
  (c : ElementaryChain L M) {k l m n : ℕ}

/-- The elementary substructure `M m ≼ₑ[L] M n` composed of the steps from `m` to `n`. -/
def map (h : m ≤ n) : M m ≼ₑ[L] M n := Nat.leRecOn h (fun e ↦ e.trans (c.step _)) (.refl _ _)

@[simp]
lemma map_self (x : M m) : c.map le_rfl x = x := by
  simp [map, Nat.leRecOn_self]

lemma map_succ (h : m ≤ n) (x : M m) : c.map (h.trans n.le_succ) x = c.step n (c.map h x) := by
  simp [map, Nat.leRecOn_succ h]

@[simp]
lemma map_map (h₁ : l ≤ m) (h₂ : m ≤ n) (x : M l) :
    c.map h₂ (c.map h₁ x) = c.map (h₁.trans h₂) x := by
  induction n, h₂ using Nat.le_induction with
  | base => simp
  | succ n h ih => rw [map_succ c h, ih, ← map_succ]

instance : DirectedSystem M fun _ _ h ↦ (c.map h).emb where
  map_self _ := c.map_self
  map_map _ _ _ := c.map_map

/-- The union of an elementary chain.
- [Kay91, Lemma 0.6] -/
abbrev Union : Type u := DirectLimit M fun _ _ h ↦ (c.map h).emb

lemma mk_eq_mk_iff {x : M m} {y : M n} (hm : m ≤ k) (hn : n ≤ k) :
    (⟦⟨m, x⟩⟧ : c.Union) = ⟦⟨n, y⟩⟧ ↔ c.map hm x = c.map hn y := by
  constructor
  · intro h
    obtain ⟨j, hmj, hnj, hj⟩ := Quotient.exact h
    apply EmbeddingClass.map_inj (c.map (le_max_left k j)).emb
    simp only [map_map]
    rw [← c.map_map hmj (le_max_right k j), ← c.map_map hnj (le_max_right k j)]
    exact congrArg _ hj
  · intro h
    rw [← DirectLimit.mk_apply m k x hm, ← DirectLimit.mk_apply n k y hn]
    exact congrArg (fun z : M k ↦ (⟦⟨k, z⟩⟧ : c.Union)) h

/-- A stage of the chain at which finitely many elements of its union all appear. -/
noncomputable def stage (v : Fin k → c.Union) : ℕ := Finset.univ.sup fun i ↦ (v i).out.1

/-- Finitely many elements of the union, as elements of a common stage. -/
noncomputable def lift (v : Fin k → c.Union) (i : Fin k) : M (c.stage v) :=
  c.map (Finset.le_sup (f := fun i ↦ (v i).out.1) (Finset.mem_univ i)) (v i).out.2

lemma mk_lift (v : Fin k → c.Union) (i : Fin k) : (⟦⟨c.stage v, c.lift v i⟩⟧ : c.Union) = v i :=
  (DirectLimit.mk_apply _ _ _ _).trans (Quotient.out_eq (v i))

noncomputable instance : Tarski.Structure L c.Union where
  func _ f v := ⟦⟨c.stage v, func f (c.lift v)⟩⟧
  rel _ r v := rel r (c.lift v)

lemma func_mk (f : L.Func k) (w : Fin k → M n) :
    func f (fun i ↦ (⟦⟨n, w i⟩⟧ : c.Union)) = ⟦⟨n, func f w⟩⟧ := by
  let v : Fin k → c.Union := fun i ↦ ⟦⟨n, w i⟩⟧
  have hs := le_max_left (c.stage v) n
  have hn := le_max_right (c.stage v) n
  change (⟦⟨c.stage v, func f (c.lift v)⟩⟧ : c.Union) = _
  rw [c.mk_eq_mk_iff hs hn, HomClass.func, HomClass.func]
  congr 1
  funext i
  exact (c.mk_eq_mk_iff hs hn).mp (c.mk_lift v i)

lemma rel_mk (r : L.Rel k) (w : Fin k → M n) :
    rel r (fun i ↦ (⟦⟨n, w i⟩⟧ : c.Union)) ↔ rel r w := by
  let v : Fin k → c.Union := fun i ↦ ⟦⟨n, w i⟩⟧
  have hs := le_max_left (c.stage v) n
  have hn := le_max_right (c.stage v) n
  change rel r (c.lift v) ↔ _
  rw [← EmbeddingClass.rel (c.map hs).emb r (c.lift v), ← EmbeddingClass.rel (c.map hn).emb r w]
  congr! 1
  funext i
  exact (c.mk_eq_mk_iff hs hn).mp (c.mk_lift v i)

/-- The embedding of `M n` into the union of the chain. -/
noncomputable def of (n : ℕ) : M n ↪ₛ[L] c.Union where
  toFun x := ⟦⟨n, x⟩⟧
  func' f v := (c.func_mk f v).symm
  rel' r v h := (c.rel_mk r v).mpr h
  toFun_inj := DirectLimit.mk_injective _ (fun _ _ _ ↦ EmbeddingClass.map_inj _) n
  rel_inv' r v h := (c.rel_mk r v).mp h

@[simp]
lemma of_map (h : m ≤ n) (x : M m) : c.of n (c.map h x) = c.of m x :=
  DirectLimit.mk_apply ..

@[simp]
lemma of_comp_map (h : m ≤ n) : c.of n ∘ c.map h = c.of m := funext (c.of_map h)

lemma exists_eq_of_le (n : ℕ) (y : c.Union) : ∃ m, ∃ _ : n ≤ m, ∃ x, y = c.of m x := by
  obtain ⟨m, x, rfl⟩ := DirectLimit.exists_eq_mk _ y
  use max n m, le_max_left n m, c.map (le_max_right n m) x
  exact (c.of_map _ x).symm

/-- The elementary chain theorem: the union of an elementary chain is an elementary extension of
each structure in the chain.
- [Kay91, Lemma 0.6] -/
theorem isElementary_of (n : ℕ) : IsElementary (fun {_} _ ↦ True) (c.of n) := by
  suffices ∀ {k} (φ : Semiformula L ℕ k) (n : ℕ) (e : Fin k → M n) (f : ℕ → M n),
      φ.Eval (c.of n ∘ e) (c.of n ∘ f) ↔ φ.Eval e f from fun {_ φ} _ ↦ this φ n
  intro k φ
  induction φ using Semiformula.rec' with
  | hverum | hfalsum => simp
  | hrel r v | hnrel r v => intro n e f; exact (eval_hom_iff_of_open (c.of n) (by simp)).symm
  | hand φ ψ ihφ ihψ | hor φ ψ ihφ ihψ => intro n e f; simp [ihφ, ihψ]
  | hall φ ih =>
    intro n e f
    simp only [eval_all]
    constructor
    · intro h x
      exact (ih n (x :> e) f).mp (by simpa [Matrix.comp_vecCons''] using h (c.of n x))
    · intro h y
      obtain ⟨m, hn, x, rfl⟩ := c.exists_eq_of_le n y
      have h₁ := ((c.map hn).isElementary (φ := ∀¹ φ) trivial e f).mpr (by simpa using h)
      simpa [Matrix.comp_vecCons'', ← Function.comp_assoc] using
        (ih m (x :> c.map hn ∘ e) (c.map hn ∘ f)).mpr (eval_all.mp h₁ x)
  | hexs φ ih =>
    intro n e f
    simp only [eval_ex]
    constructor
    · rintro ⟨y, h⟩
      obtain ⟨m, hn, x, rfl⟩ := c.exists_eq_of_le n y
      have h₁ := (ih m (x :> c.map hn ∘ e) (c.map hn ∘ f)).mp
        (by simpa [Matrix.comp_vecCons'', ← Function.comp_assoc] using h)
      simpa using ((c.map hn).isElementary (φ := ∃¹ φ) trivial e f).mp (eval_ex.mpr ⟨_, h₁⟩)
    · rintro ⟨x, h⟩
      use c.of n x
      simpa [Matrix.comp_vecCons''] using (ih n (x :> e) f).mpr h

/-- Each structure in an elementary chain is an elementary substructure of its union. -/
noncomputable def toUnion (n : ℕ) : M n ≼ₑ[L] c.Union where
  emb := c.of n
  isElementary := c.isElementary_of n

end ElementaryChain

end

/-! ## End extensions -/

section

variable {L : Language} {ℬ : Bounding L} {M : Type u} {N : Type v} {K : Type w}
  [Tarski.Structure L M] [Tarski.Structure L N] [Tarski.Structure L K] {T : Theory L}

/-- An end extension of `M` to `N` for `ℬ`: an embedding of `M` into `N` whose image is an initial
segment for every bounding operator of `ℬ`.
- [Kay91, Definition 2.6]
- [HP98, Definition IV.1.3(2)] -/
structure EndExtension (ℬ : Bounding L) (M : Type u) (N : Type v) [Tarski.Structure L M]
    [Tarski.Structure L N] where
  emb : M ↪ₛ[L] N
  isInitial : ℬ.IsInitial emb

/-- A proper end extension: an end extension which is not surjective.
- [HP98, Definition IV.1.14] -/
structure ProperEndExtension (ℬ : Bounding L) (M : Type u) (N : Type v) [Tarski.Structure L M]
    [Tarski.Structure L N] extends EndExtension ℬ M N where
  not_surjective : ¬Function.Surjective emb

@[inherit_doc]
notation:50 M " ⊆ₑ[" ℬ "] " N => EndExtension ℬ M N

@[inherit_doc]
notation:50 M " ⊂ₑ[" ℬ "] " N => ProperEndExtension ℬ M N

instance : CoeFun (M ⊆ₑ[ℬ] N) (fun _ ↦ M → N) := ⟨fun e ↦ e.emb⟩

instance : CoeFun (M ⊂ₑ[ℬ] N) (fun _ ↦ M → N) := ⟨fun e ↦ e.emb⟩

namespace EndExtension

variable (e : M ⊆ₑ[ℬ] N)

instance : ℬ.IsInitial e.emb := e.isInitial

lemma emb_injective : Function.Injective e.emb := EmbeddingClass.map_inj e.emb

@[grind =]
lemma emb_eq_emb {x y : M} : e x = e y ↔ x = y := e.emb_injective.eq_iff

variable (ℬ M) in
/-- The identity end extension. -/
@[refl]
protected def refl : M ⊆ₑ[ℬ] M where
  emb := .refl L M
  isInitial := {
    operator_iff _ _ _ := Iff.rfl
    initial _ _ b _ := ⟨b, rfl⟩
  }

@[simp]
lemma refl_apply (x : M) : EndExtension.refl ℬ M x = x := rfl

/-- The composition of end extensions. -/
@[trans]
protected def trans (e₁ : M ⊆ₑ[ℬ] N) (e₂ : N ⊆ₑ[ℬ] K) : M ⊆ₑ[ℬ] K where
  emb := e₁.emb.trans e₂.emb
  isInitial := {
    operator_iff hR a b :=
      (e₁.isInitial.operator_iff hR a b).trans (e₂.isInitial.operator_iff hR _ _)
    initial hR a c h := by
      obtain ⟨d, rfl⟩ := e₂.isInitial.initial hR (e₁ a) c h
      obtain ⟨x, rfl⟩ := e₁.isInitial.initial hR a d ((e₂.isInitial.operator_iff hR _ _).mpr h)
      use x
      rfl
  }

@[simp]
lemma trans_apply (e₁ : M ⊆ₑ[ℬ] N) (e₂ : N ⊆ₑ[ℬ] K) (x : M) : e₁.trans e₂ x = e₂ (e₁ x) :=
  rfl

/-- An end extension is a $\Delta_0$-elementary substructure.
- [Kay91, Theorem 2.7]
- [HP98, Fact IV.1.3(4)] -/
def toElementarySubstructureOn : M ≼ₑ[L; fun {_} φ ↦ ℬ.Closure φ] N where
  emb := e.emb
  isElementary hφ v f := (Bounding.bounded_absolute e.emb hφ v f).symm

include e in
/-- A theory all of whose members are $\Pi_1$ sentences holds in `M` as soon as it holds in an end
extension of `M`.
- [HP98, Remark IV.1.18, Remark IV.1.21(2)] -/
theorem models_of_Pi1 [Nonempty M] [Nonempty N] (hT : ∀ σ ∈ T, ℬ.Hierarchy 𝚷 1 σ)
    [N↓[L] ⊧* T] : M↓[L] ⊧* T := by
  apply models_theory_iff.mpr
  intro σ hσ
  have h := models_theory_iff.mp (inferInstance : N↓[L] ⊧* T) σ hσ
  simp only [models_iff] at h ⊢
  exact Bounding.pi_one_downward e.emb (hT σ hσ) ![] Empty.elim <|
    Eval.of_eq h (funext (·.elim0)) (funext (·.elim))

include e in
/-- A $\Pi_1$-axiomatizable theory holds in `M` as soon as it holds in an end extension of `M`.
- [HP98, Remark IV.1.18, Remark IV.1.21(2)] -/
theorem models_of_Pi1Axiomatizable [Nonempty M] [Nonempty N]
    (hT : Axiomatizable (ℬ.Hierarchy 𝚷 1) T) [N↓[L] ⊧* T] : M↓[L] ⊧* T := by
  obtain ⟨U, hU, hTU⟩ := hT
  have : U ⪯ T := hTU.symm.le
  have : T ⪯ U := hTU.le
  have : N↓[L] ⊧* U := models_of_subtheory ‹N↓[L] ⊧* T›
  exact models_of_subtheory (e.models_of_Pi1 hU)

end EndExtension

namespace ProperEndExtension

/-- A proper end extension followed by an end extension is proper. -/
protected def transLeft (e₁ : M ⊂ₑ[ℬ] N) (e₂ : N ⊆ₑ[ℬ] K) : M ⊂ₑ[ℬ] K where
  toEndExtension := e₁.toEndExtension.trans e₂
  not_surjective h := e₁.not_surjective <| by
    intro y
    obtain ⟨x, hx⟩ := h (e₂ y)
    use x
    exact e₂.emb_injective hx

/-- The composition of proper end extensions. -/
@[trans]
protected def trans (e₁ : M ⊂ₑ[ℬ] N) (e₂ : N ⊂ₑ[ℬ] K) : M ⊂ₑ[ℬ] K :=
  e₁.transLeft e₂.toEndExtension

end ProperEndExtension

end

/-! ## Types -/

/-- A $k$-type of `L` with parameters indexed by `ξ`: a set of formulas in `k` variables, whose
free variables are the parameters.
- [Kay91, §8.1] -/
abbrev _root_.FFL.FirstOrder.Type (L : Language) (ξ : Type*) (k : ℕ) := Set (Semiformula L ξ k)

namespace «Type»

open Semiformula

variable {L : Language} {ξ : Type*} {k : ℕ} {M : Type*} [Tarski.Structure L M]
  {Φ Ψ : FirstOrder.Type L ξ k} {b : ξ → M}

/-- The tuple `a` realizes `Φ` with the parameters read as `b`.
- [Kay91, §8.1] -/
def RealizedBy (Φ : FirstOrder.Type L ξ k) (b : ξ → M) (a : Fin k → M) : Prop :=
  ∀ φ ∈ Φ, φ.Eval a b

/-- `Φ` is realized in `M` with the parameters read as `b`.
- [Kay91, §8.1] -/
def Realized (Φ : FirstOrder.Type L ξ k) (M : Type*) [Tarski.Structure L M] (b : ξ → M) : Prop :=
  ∃ a : Fin k → M, Φ.RealizedBy b a

/-- `M` omits `Φ` with the parameters read as `b`: no tuple of `M` realizes `Φ`.
- [Kay91, §8.1] -/
def Omitted (Φ : FirstOrder.Type L ξ k) (M : Type*) [Tarski.Structure L M] (b : ξ → M) : Prop :=
  ∀ a : Fin k → M, ¬Φ.RealizedBy b a

/-- Every finite subset of `Φ` is realized in `M` with the parameters read as `b`.
- [Kay91, §11.2] -/
def FinitelySatisfied (Φ : FirstOrder.Type L ξ k) (M : Type*) [Tarski.Structure L M]
    (b : ξ → M) : Prop :=
  ∀ s : Finset (Semiformula L ξ k), ↑s ⊆ Φ → Realized (s : Set (Semiformula L ξ k)) M b

/-- `Φ` decides every formula in `M` with the parameters read as `b`: some finite subset of `Φ`
implies the formula or its negation.
- [Kay91, §11.2] -/
def IsComplete (Φ : FirstOrder.Type L ξ k) (b : ξ → M) : Prop :=
  ∀ φ : Semiformula L ξ k, ∃ s : Finset (Semiformula L ξ k), ↑s ⊆ Φ ∧
    ((∀ a, RealizedBy (s : Set (Semiformula L ξ k)) b a → φ.Eval a b) ∨
      ∀ a, RealizedBy (s : Set (Semiformula L ξ k)) b a → ¬φ.Eval a b)

lemma RealizedBy.mono {a : Fin k → M} (h : Φ.RealizedBy b a) (hΨΦ : Ψ ⊆ Φ) : Ψ.RealizedBy b a :=
  fun φ hφ ↦ h φ (hΨΦ hφ)

lemma Realized.mono (h : Φ.Realized M b) (hΨΦ : Ψ ⊆ Φ) : Ψ.Realized M b :=
  h.imp fun _ ha ↦ ha.mono hΨΦ

lemma omitted_iff_not_realized : Φ.Omitted M b ↔ ¬Φ.Realized M b := by
  simp [Omitted, Realized]

lemma Realized.finitelySatisfied (h : Φ.Realized M b) : Φ.FinitelySatisfied M b :=
  fun _ hs ↦ h.mono hs

section theory

open _root_.FFL.Entailment


variable {L : Language.{u}} {k : ℕ}

/-- `T + Φ(c̄)`: `T` together with the formulas of `Φ`, their variables filled by new constants.
- [Kay91, §8.1] -/
def _root_.FFL.FirstOrder.Theory.addType (T : Theory L) (Φ : FirstOrder.Type L Empty k) :
    Theory (L.add (Language.constant (Fin k))) :=
  T.lMap (Language.Hom.add₁ L (Language.constant (Fin k))) ∪ lift '' Φ

/-- `Φ` is a type over `T`: `T + Φ(c̄)` is consistent.
- [Kay91, §8.1] -/
def IsTypeOver (Φ : FirstOrder.Type L Empty k) (T : Theory L) : Prop :=
  Consistent (T.addType Φ)

/-- `Φ` is a complete type over `T`: `T + Φ(c̄)` is consistent and complete.
- [Kay91, §8.1] -/
def IsCompleteOver (Φ : FirstOrder.Type L Empty k) (T : Theory L) : Prop :=
  Φ.IsTypeOver T ∧ Entailment.Complete (T.addType Φ)

/-- `Φ` is a principal type over `T`: some `ψ` with `T + Φ(c̄) ⊢ ψ(c̄)` implies every formula of `Φ`
over `T`.
- [Kay91, §8.1] -/
def IsPrincipalOver (Φ : FirstOrder.Type L Empty k) (T : Theory L) : Prop :=
  ∃ ψ : Semisentence L k, T.addType Φ ⊢ lift ψ ∧ ∀ φ ∈ Φ, T ⊢ ∀¹* (ψ 🡒 φ)

/-- A type over `T` is realized in some model of `T`, and a set of formulas realized in a model of
`T` is a type over `T`.
- [Kay91, §8.1] -/
theorem isTypeOver_iff_exists_realized {T : Theory L} {Φ : FirstOrder.Type L Empty k} :
    Φ.IsTypeOver T ↔ ∃ N : Tarski.Struc.{u} L, N ⊧* T ∧ Φ.Realized N Empty.elim := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := Theory.satisfiable_iff_consistent.{u, u}.mpr h
    use N.reduct
    and_intros
    · apply Semantics.modelsSet_iff.mpr
      intro σ hσ
      exact (N.models_lMap_iff σ).mp <| Semantics.modelsSet_iff.mp hN <| Or.inl ⟨σ, hσ, rfl⟩
    · use N.cstVal
      intro φ hφ
      exact (N.models_lift_iff φ).mp <| Semantics.modelsSet_iff.mp hN <| Or.inr ⟨φ, hφ, rfl⟩
  · rintro ⟨N, hN, a, ha⟩
    apply Theory.consistent_of_satisfiable
    use strucOfTuple N a
    apply Semantics.modelsSet_iff.mpr
    rintro σ (hσ | ⟨φ, hφ, rfl⟩)
    · exact Semantics.modelsSet_iff.mp (strucOfTuple_models_lMap_image N a hN) hσ
    · exact (strucOfTuple_models_lift_iff N a φ).mpr <| ha φ hφ

/-- A set of formulas with parameters `b` is finitely satisfied in `M` if and only if, with the
parameters read as constants, it is a type over the theory of `(M, b)`.
- [Kay91, §11.2] -/
theorem isTypeOver_theory_iff_finitelySatisfied {ι : Type*} {M : Type*} [Nonempty M]
    [Tarski.Structure L M] {Φ : FirstOrder.Type L ι k} {b : ι → M} :
    IsTypeOver (liftParameters '' Φ) (Semantics.theory (strucOfTuple M b)) ↔
      Φ.FinitelySatisfied M b := by
  constructor
  · intro h s hs
    obtain ⟨N, hN, a, ha⟩ := isTypeOver_iff_exists_realized.mp h
    let σ : Sentence (L.add (Language.constant ι)) := ∃¹* ⋀(s.toList.map liftParameters)
    have hσ : ∼σ ∉ Semantics.theory (strucOfTuple M b) := by
      intro hσ
      have : Semiformula.Eval (s := N.struc) ![] Empty.elim (∼σ) := Semantics.modelsSet_iff.mp hN hσ
      simp only [σ, LogicalConnective.HomClass.map_neg, eval_exsClosure] at this
      apply this
      use a
      simpa using fun φ hφ ↦ ha (liftParameters φ) ⟨φ, hs hφ, rfl⟩
    by_contra hM
    apply hσ
    change Semiformula.Eval (s := structureOfTuple M b) ![] Empty.elim (∼σ)
    simp only [σ, LogicalConnective.HomClass.map_neg, eval_exsClosure]
    rintro ⟨a, ha⟩
    apply hM
    use a
    intro φ hφ
    have := List.map_conj₂_prop.mp ha (liftParameters φ) <|
      List.mem_map.mpr ⟨φ, by simpa using hφ, rfl⟩
    simpa using this
  · intro h
    apply consistent_compact.mpr
    intro F hF hfin
    let A : Theory ((L.add (Language.constant ι)).add (Language.constant (Fin k))) :=
      Theory.lMap (Language.Hom.add₁ (L.add (Language.constant ι)) (Language.constant (Fin k)))
        (Semantics.theory (strucOfTuple M b))
    obtain ⟨t, htΦ, htfin, ht⟩ := Set.exists_subset_image_finite_and
      (f := lift ∘ liftParameters) (s := Φ) (p := fun u ↦ F ⊆ A ∪ u) |>.mp <| by
        use F \ A
        and_intros
        · intro σ ⟨hσF, hσA⟩
          simpa [Set.image_image] using (hF hσF).resolve_left hσA
        · exact Set.Finite.sdiff hfin
        · intro σ hσ
          by_cases hσA : σ ∈ A
          · exact Or.inl hσA
          · exact Or.inr ⟨hσ, hσA⟩
    obtain ⟨a, ha⟩ := h htfin.toFinset (by simpa using htΦ)
    let _ : Tarski.Structure (L.add (Language.constant ι)) M := structureOfTuple M b
    apply Theory.consistent_of_satisfiable
    use strucOfTuple M a
    apply Semantics.modelsSet_iff.mpr
    intro σ hσ
    rcases ht hσ with hσ | ⟨φ, hφ, rfl⟩
    · exact Semantics.modelsSet_iff.mp (strucOfTuple_models_lMap_image
        (T := Semantics.theory (strucOfTuple M b)) M a ⟨fun _ h ↦ h⟩) hσ
    · apply (strucOfTuple_models_lift_iff M a (liftParameters φ)).mpr
      simpa using ha φ (by simpa using hφ)

end theory

end «Type»

/-! ## Recursive saturation -/

section

variable {L : Language} [L.Encodable]

/-- The set of codes of the formulas of `Φ` is recursive.
- [Kay91, §11.2] -/
def «Type».IsRecursive {ξ : Type*} [Encodable ξ] {k : ℕ} (Φ : FirstOrder.Type L ξ k) : Prop :=
  ComputablePred (· ∈ Encodable.encode '' Φ)

variable (M : Type*) [Tarski.Structure L M]

variable (L) in
/-- Every finitely satisfied recursive type over `M` with finitely many parameters is realized in
`M`.
- [Kay91, §11.2] -/
def RecursivelySaturated : Prop :=
  ∀ (k m : ℕ) (Φ : FirstOrder.Type L (Fin m) k) (b : Fin m → M),
    Φ.IsRecursive → Φ.FinitelySatisfied M b → Φ.Realized M b

/-- Every finitely satisfied recursive type over `M` of prenex $\Sigma_n$ formulas with finitely
many parameters is realized in `M`.
- [Kay91, §11.2] -/
def SigmaRecursivelySaturated (ℬ : Bounding L) (n : ℕ) : Prop :=
  ∀ (k m : ℕ) (Φ : FirstOrder.Type L (Fin m) k) (b : Fin m → M),
    (∀ φ ∈ Φ, ℬ.PrenexHierarchy 𝚺 n φ) → Φ.IsRecursive → Φ.FinitelySatisfied M b →
      Φ.Realized M b

end

/-! ## Definable elements -/

section

variable {L : Language} {M : Type*} [Tarski.Structure L M]

/-- A formula satisfying `C`, with parameters from `A`, which defines `a` in `M`: `a` is the only
element of `M` satisfying it. -/
structure DefiningFormula (A : Set M) (C : Semiformula L A 1 → Prop) (a : M) where
  formula : Semiformula L A 1
  formula_mem : C formula
  eval_iff : ∀ x : M, formula.Eval ![x] Subtype.val ↔ x = a

/-- The elements of `M` definable over `A` by a formula satisfying `C`.
- [Kay91, §8.1] -/
def definableElementsOver (A : Set M) (C : Semiformula L A 1 → Prop) : Set M :=
  {a | Nonempty (DefiningFormula A C a)}

variable (L) in
/-- The definable closure of `A`: the elements of `M` definable over `A`.
- [Kay91, §8.1] -/
abbrev definableClosure (A : Set M) : Set M :=
  definableElementsOver A (⊤ : Semiformula L A 1 → Prop)

variable (L M) in
/-- The elements of `M` definable without parameters. -/
abbrev definableElements : Set M := definableClosure L (∅ : Set M)

lemma definableElementsOver_mono {A : Set M} {C D : Semiformula L A 1 → Prop}
    (h : ∀ φ, C φ → D φ) : definableElementsOver A C ⊆ definableElementsOver A D := by
  rintro a ⟨φ, hφ, ha⟩
  exact ⟨φ, h φ hφ, ha⟩

end

section

variable {L : Language} {M : Type} [Tarski.Structure L M]

/-- Over no parameters, a class of formulas closed under renaming the free variables defines the
same elements by formulas as by sentences. -/
lemma mem_definableElementsOver_empty_iff {C : ∀ {ξ : Type}, Semiformula L ξ 1 → Prop}
    (hC : ∀ {ξ ζ : Type} (f : ξ → ζ) {φ : Semiformula L ξ 1}, C φ → C (Rew.rewriteMap f ▹ φ))
    {a : M} : a ∈ definableElementsOver (∅ : Set M) C ↔
      ∃ φ : Semisentence L 1, C φ ∧ ∀ x, M ⊧/![x] φ ↔ x = a := by
  constructor
  · rintro ⟨θ, hθ, h⟩
    use Rew.rewriteMap (fun i ↦ isEmptyElim i) ▹ θ
    and_intros
    · exact hC _ hθ
    · intro x
      rw [← h x, eval_rewriteMap]
      exact iff_of_eq (congrArg (fun f ↦ Eval ![x] f θ) (Subsingleton.elim _ _))
  · rintro ⟨φ, hφ, h⟩
    use Rew.rewriteMap Empty.elim ▹ φ
    · exact hC _ hφ
    · intro x
      rw [← h x, eval_rewriteMap]
      exact iff_of_eq (congrArg (fun f ↦ Eval ![x] f φ) (Subsingleton.elim _ _))

lemma mem_definableElements_iff {a : M} :
    a ∈ definableElements L M ↔ ∃ φ : Semisentence L 1, ∀ x, M ⊧/![x] φ ↔ x = a :=
  (mem_definableElementsOver_empty_iff (C := fun _ ↦ True) fun _ _ h ↦ h).trans (by simp)

end

end FFL.FirstOrder
