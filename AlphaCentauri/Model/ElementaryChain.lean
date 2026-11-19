module

public import AlphaCentauri.Model.ElementarySubstructure
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Embedding
public import Mathlib.Order.DirectedInverseSystem

/-! # Countable elementary chains

A countable elementary chain is a sequence of `ℒₒᵣ`-structures `M 0 ≼ₑ M 1 ≼ₑ M 2 ≼ₑ ⋯`, each an
elementary substructure of the next. Composing the steps gives an elementary substructure
`M m ≼ₑ M n` for every `m ≤ n`, and these form a directed system. Its union, the direct limit of
this system, is an elementary extension of every `M n`.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Semiformula Tarski.Structure

universe u

/-- A countable elementary chain: a sequence of `ℒₒᵣ`-structures `M 0 ≼ₑ M 1 ≼ₑ M 2 ≼ₑ ⋯`.
- [Kay91, Lemma 0.6] -/
structure ElementaryChain (M : ℕ → Type u) [∀ n, ORingStructure (M n)] where
  step : ∀ n, M n ≼ₑ M (n + 1)

namespace ElementaryChain

variable {M : ℕ → Type u} [∀ n, ORingStructure (M n)] (c : ElementaryChain M) {l m n : ℕ}

/-- The elementary substructure `M m ≼ₑ M n` composed of the steps from `m` to `n`. -/
def map (h : m ≤ n) : M m ≼ₑ M n := Nat.leRecOn h (fun e ↦ e.trans (c.step _)) (.refl _ _)

@[simp] lemma map_self (x : M m) : c.map le_rfl x = x := by
  simp [map, Nat.leRecOn_self]

lemma map_succ (h : m ≤ n) (x : M m) : c.map (h.trans n.le_succ) x = c.step n (c.map h x) := by
  simp [map, Nat.leRecOn_succ h]

@[simp] lemma map_map (h₁ : l ≤ m) (h₂ : m ≤ n) (x : M l) :
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

noncomputable instance : ORingStructure c.Union where
  zero := ⟦⟨0, 0⟩⟧
  one := ⟦⟨0, 1⟩⟧
  add := DirectLimit.map₂ _ _ _ (fun _ ↦ (· + ·)) fun _ _ _ _ _ ↦ HomClass.map_add _ _ _
  mul := DirectLimit.map₂ _ _ _ (fun _ ↦ (· * ·)) fun _ _ _ _ _ ↦ HomClass.map_mul _ _ _
  lt := DirectLimit.lift₂ _ _ (fun _ ↦ (· < ·)) fun _ _ _ _ _ ↦
    propext (EmbeddingClass.map_lt_map_iff _).symm

lemma mk_zero : (⟦⟨n, 0⟩⟧ : c.Union) = 0 := by
  rw [← HomClass.map_zero (c.map n.zero_le).emb, DirectLimit.mk_apply]
  rfl

lemma mk_one : (⟦⟨n, 1⟩⟧ : c.Union) = 1 := by
  rw [← HomClass.map_one (c.map n.zero_le).emb, DirectLimit.mk_apply]
  rfl

lemma mk_add (x y : M n) : (⟦⟨n, x + y⟩⟧ : c.Union) = ⟦⟨n, x⟩⟧ + ⟦⟨n, y⟩⟧ := by
  change _ = DirectLimit.map₂ _ _ _ (fun _ ↦ (· + ·)) _ ⟦⟨n, x⟩⟧ ⟦⟨n, y⟩⟧
  rw [DirectLimit.map₂_def]

lemma mk_mul (x y : M n) : (⟦⟨n, x * y⟩⟧ : c.Union) = ⟦⟨n, x⟩⟧ * ⟦⟨n, y⟩⟧ := by
  change _ = DirectLimit.map₂ _ _ _ (fun _ ↦ (· * ·)) _ ⟦⟨n, x⟩⟧ ⟦⟨n, y⟩⟧
  rw [DirectLimit.map₂_def]

lemma mk_lt_mk {x y : M n} : (⟦⟨n, x⟩⟧ : c.Union) < ⟦⟨n, y⟩⟧ ↔ x < y :=
  iff_of_eq (DirectLimit.lift₂_def ..)

lemma mk_injective : Function.Injective fun x : M n ↦ (⟦⟨n, x⟩⟧ : c.Union) :=
  DirectLimit.mk_injective _ (fun _ _ _ ↦ EmbeddingClass.map_inj _) n

/-- The embedding of `M n` into the union of the chain. -/
noncomputable def of (n : ℕ) : M n ↪ₛ[ℒₒᵣ] c.Union where
  toFun x := ⟦⟨n, x⟩⟧
  func' f v := by
    cases f
    exacts [c.mk_zero, c.mk_one, c.mk_add _ _, c.mk_mul _ _]
  rel' r v h := by
    cases r
    exacts [congrArg (fun x : M n ↦ (⟦⟨n, x⟩⟧ : c.Union)) h, c.mk_lt_mk.mpr h]
  toFun_inj := c.mk_injective
  rel_inv' r v h := by
    cases r
    exacts [c.mk_injective h, c.mk_lt_mk.mp h]

@[simp] lemma of_map (h : m ≤ n) (x : M m) : c.of n (c.map h x) = c.of m x :=
  DirectLimit.mk_apply ..

@[simp] lemma of_comp_map (h : m ≤ n) : c.of n ∘ c.map h = c.of m := funext (c.of_map h)

lemma exists_eq_of_le (n : ℕ) (y : c.Union) : ∃ m, ∃ _ : n ≤ m, ∃ x, y = c.of m x := by
  obtain ⟨m, x, rfl⟩ := DirectLimit.exists_eq_mk _ y
  use max n m, le_max_left n m, c.map (le_max_right n m) x
  exact (c.of_map _ x).symm

/-- The elementary chain theorem: the union of an elementary chain is an elementary extension of
each structure in the chain.
- [Kay91, Lemma 0.6] -/
theorem isElementary_of (n : ℕ) : IsElementary (fun {_} _ ↦ True) (c.of n) := by
  suffices ∀ {k} (φ : ArithmeticSemiformula ℕ k) (n : ℕ) (e : Fin k → M n) (f : ℕ → M n),
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
noncomputable def toUnion (n : ℕ) : M n ≼ₑ c.Union where
  emb := c.of n
  isElementary := c.isElementary_of n

end ElementaryChain

end FFL.FirstOrder.Arithmetic
