module

public import AlphaCentauri.ToFoundation.FirstOrder.ElementarySubstructure
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.DirectedInverseSystem

/-! # Countable elementary chains

A countable elementary chain is a sequence of `L`-structures `M 0 ≼ₑ[L] M 1 ≼ₑ[L] M 2 ≼ₑ[L] ⋯`,
each an elementary substructure of the next. Composing the steps gives an elementary substructure
`M m ≼ₑ[L] M n` for every `m ≤ n`, and these form a directed system. Its union, the direct limit
of this system, is an elementary extension of every `M n`.
-/

@[expose] public section

namespace FFL.FirstOrder

open Semiformula Tarski.Structure

universe u

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

end FFL.FirstOrder
