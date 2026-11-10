module

public import AlphaCentauri.InterpretabilityLogic.MaximalConsistentTheory
public import AlphaCentauri.InterpretabilityLogic.Veltman.Extension

/-!
# Completeness of $\mathbf{ILM}_0$ with respect to Veltman models

A step-by-step construction of a Veltman model satisfying the frame condition of $\mathsf{M}_0$, for
any extension of $\mathbf{IL}$ by axioms proving $\mathsf{M}_0$. One world is added at each step,
with no successors; its predecessors are the ancestors of the world it is added for along a parent
map, so the predecessors of every world form a chain. Every world is labelled by a maximal
consistent set, and the worlds added to remove deficiencies are assuring successors carrying the
promises of criticality and the boxed formulas required by $\mathsf{M}_0$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula Logic Logic.ofAxioms MaximalConsistentTheory

namespace Veltman.StepByStep

variable {α : Type*} [DecidableEq α] {𝔸 : Set (Formula α)}

/-- A world is isolated, or added for a world `a` to witness `¬(A ▷ B)`, or added for `a` as a
`≺[a]`-successor of `s`. -/
inductive Kind (α : Type*)
  | isolated
  | problem (a : ℕ) (B : Formula α)
  | deficiency (a s : ℕ)

/-- A world: its kind and maximal consistent set, its predecessors, its ancestors along the parent
map, and, for each `u`, the world supplying the boxed formulas and the criticality promises that its
`≺[u]`-successors must satisfy. -/
structure Node (𝔸 : Set (Formula α)) where
  kind : Kind α
  set : MaximalConsistentTheory (ofAxioms 𝔸)
  pre : Finset ℕ
  anc : Finset ℕ
  mu : ℕ → WithBot ℕ
  cr : ℕ → Set (Formula α)

/-- A step either witnesses `¬(A ▷ B)` at `x` or removes the deficiency of `A ▷ B` at `x` on `y`. -/
inductive Task (α : Type*)
  | problem (x : ℕ) (A B : Formula α)
  | deficiency (x y : ℕ) (A B : Formula α)

section

variable (get : ℕ → Node 𝔸)

/-- The members of `P` above `u`. -/
def above (P : Finset ℕ) (u : ℕ) : Finset ℕ := P.filter (fun t ↦ u ∈ (get t).pre)

/-- The boxed formulas of the world `r`, if any. -/
def boxes (r : WithBot ℕ) : Set (Formula α) := WithBot.recBotCoe ∅ (fun r ↦ (get r).set.boxLabel ∅) r

/-- The promises a `≺[x]`-successor of `y` must keep. -/
def label (x y : ℕ) : Set (Formula α) := (get y).cr x ∪ boxes get ((get y).mu x)

/-- The isolated world `n` labelled by `Δ`. -/
def isolatedNode (n : ℕ) (Δ : MaximalConsistentTheory (ofAxioms 𝔸)) : Node 𝔸 :=
  ⟨.isolated, Δ, ∅, {n}, fun _ ↦ ⊥, fun _ ↦ ∅⟩

/-- The world `n` of kind `k` labelled by `Δ`, given the earlier worlds. -/
noncomputable def mk (n : ℕ) (k : Kind α) (Δ : MaximalConsistentTheory (ofAxioms 𝔸)) : Node 𝔸 :=
  match k with
  | .isolated => isolatedNode n Δ
  | .problem a B =>
    ⟨.problem a B, Δ, (get a).anc, insert n (get a).anc,
      fun u ↦ if u = a then ⊥ else (above get (get a).anc u).max,
      fun u ↦ if u = a then {∼B} else ⋃ t ∈ above get (get a).anc u, (get t).cr u⟩
  | .deficiency a s =>
    ⟨.deficiency a s, Δ, (get a).anc, insert n (get (((get s).mu a).unbotD a)).anc,
      fun u ↦ if u = a then (get s).mu a else (above get (get a).anc u).max,
      fun u ↦ if u = a then (get s).cr a else ⋃ t ∈ above get (get a).anc u, (get t).cr u⟩

end

variable (Γ₀ : MaximalConsistentTheory (ofAxioms 𝔸)) (τ : ℕ → Task α)

open Classical in
/-- The world `n`, given the earlier worlds. -/
noncomputable def step (n : ℕ) (get : ℕ → Node 𝔸) : Node 𝔸 :=
  match τ n with
  | .problem x A B =>
    if h : x < n ∧ A ▷ B ∉ (get x).set then
      mk get n (.problem x B) (exists_assuringSuccessor_of_rhd_not_mem h.2).choose
    else mk get n .isolated Γ₀
  | .deficiency x y A B =>
    if h : x < n ∧ y < n ∧ x ∈ (get y).pre ∧ A ▷ B ∈ (get x).set ∧ A ∈ (get y).set ∧
        ∃ Δ, AssuringSuccessor (label get x y) (get x).set Δ ∧ B ∈ Δ ∧ □(∼B) ∈ Δ then
      mk get n (.deficiency x y) h.2.2.2.2.2.choose
    else mk get n .isolated Γ₀

/-- The worlds of the construction. -/
noncomputable def node : ℕ → Node 𝔸
  | n => step Γ₀ τ n (fun m ↦ if m < n then node m else isolatedNode 0 Γ₀)
termination_by n => n

/-- The worlds before `n`. -/
noncomputable def restr (n : ℕ) : ℕ → Node 𝔸 :=
  fun m ↦ if m < n then node Γ₀ τ m else isolatedNode 0 Γ₀

variable {Γ₀ τ}

lemma node_eq (n : ℕ) : node Γ₀ τ n = step Γ₀ τ n (restr Γ₀ τ n) := by
  rw [node];
  rfl

lemma restr_of_lt {n m : ℕ} (h : m < n) : restr Γ₀ τ n m = node Γ₀ τ m := by
  simp [restr, h]

lemma exists_mk (n : ℕ) : ∃ k Δ, node Γ₀ τ n = mk (restr Γ₀ τ n) n k Δ := by
  rw [node_eq];
  unfold step;
  split <;> split_ifs <;> exact ⟨_, _, rfl⟩

omit [DecidableEq α] in
@[simp] lemma mk_kind {get : ℕ → Node 𝔸} {n : ℕ} {k : Kind α} {Δ} : (mk get n k Δ).kind = k := by
  cases k <;> rfl

omit [DecidableEq α] in
@[simp] lemma mk_set {get : ℕ → Node 𝔸} {n : ℕ} {k : Kind α} {Δ} : (mk get n k Δ).set = Δ := by
  cases k <;> rfl

lemma node_eq_mk (n : ℕ) :
    node Γ₀ τ n = mk (restr Γ₀ τ n) n (node Γ₀ τ n).kind (node Γ₀ τ n).set := by
  obtain ⟨k, Δ, h⟩ := exists_mk (Γ₀ := Γ₀) (τ := τ) n;
  rw [h];
  simp

/-- The world `n` was added for `a`. -/
def Kind.anchor : Kind α → WithBot ℕ
  | .isolated => ⊥
  | .problem a _ => a
  | .deficiency a _ => a

lemma kind_spec (n : ℕ) :
    match (node Γ₀ τ n).kind with
    | .isolated => (node Γ₀ τ n).set = Γ₀
    | .problem a B => a < n ∧ ∃ A, τ n = .problem a A B ∧ A ▷ B ∉ (node Γ₀ τ a).set ∧
        AssuringSuccessor {∼B} (node Γ₀ τ a).set (node Γ₀ τ n).set ∧
        A ∈ (node Γ₀ τ n).set ∧ □(∼A) ∈ (node Γ₀ τ n).set
    | .deficiency a s => a < n ∧ s < n ∧ a ∈ (node Γ₀ τ s).pre ∧
        ∃ A B, τ n = .deficiency a s A B ∧ A ▷ B ∈ (node Γ₀ τ a).set ∧ A ∈ (node Γ₀ τ s).set ∧
        AssuringSuccessor (label (restr Γ₀ τ n) a s) (node Γ₀ τ a).set (node Γ₀ τ n).set ∧
        B ∈ (node Γ₀ τ n).set ∧ □(∼B) ∈ (node Γ₀ τ n).set := by
  rw [node_eq n];
  unfold step;
  rcases hτ : τ n with ⟨x, A, B⟩ | ⟨x, y, A, B⟩ <;> simp only;
  · split_ifs with h;
    · simp only [mk_kind, mk_set];
      have hx := restr_of_lt (Γ₀ := Γ₀) (τ := τ) h.1;
      have hc := (exists_assuringSuccessor_of_rhd_not_mem h.2).choose_spec;
      exact ⟨h.1, A, rfl, by simpa [hx] using h.2, by simpa only [hx] using hc.1, hc.2⟩;
    · simp [mk, isolatedNode];
  · split_ifs with h;
    · simp only [mk_kind, mk_set];
      have hx := restr_of_lt (Γ₀ := Γ₀) (τ := τ) h.1;
      have hy := restr_of_lt (Γ₀ := Γ₀) (τ := τ) h.2.1;
      have hc := h.2.2.2.2.2.choose_spec;
      exact ⟨h.1, h.2.1, by simpa [hy] using h.2.2.1, A, B, rfl, by simpa [hx] using h.2.2.2.1,
        by simpa [hy] using h.2.2.2.2.1, by simpa only [hx] using hc.1, hc.2⟩;
    · simp [mk, isolatedNode];

lemma kind_lt (n : ℕ) :
    match (node Γ₀ τ n).kind with
    | .isolated => True
    | .problem a _ => a < n
    | .deficiency a s => a < n ∧ s < n ∧ a ∈ (node Γ₀ τ s).pre := by
  have := kind_spec (Γ₀ := Γ₀) (τ := τ) n;
  split at this <;> simp_all

omit [DecidableEq α] in
lemma above_congr {get get' : ℕ → Node 𝔸} {P : Finset ℕ} {u : ℕ}
    (h : ∀ t ∈ P, get t = get' t) : above get P u = above get' P u :=
  Finset.filter_congr fun t ht ↦ by rw [h t ht]

lemma bounds (n : ℕ) :
    (∀ t ∈ (node Γ₀ τ n).anc, t ≤ n) ∧ (∀ u (r : ℕ), (node Γ₀ τ n).mu u = r → r < n) ∧
      (∀ t ∈ (node Γ₀ τ n).pre, t < n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hk := kind_lt (Γ₀ := Γ₀) (τ := τ) n;
  rw [node_eq_mk];
  generalize (node Γ₀ τ n).kind = k at hk;
  generalize (node Γ₀ τ n).set = Δ;
  cases k with
  | isolated => simp [mk, isolatedNode];
  | problem a B =>
    simp only [mk, restr_of_lt hk];
    refine ⟨?_, ?_, ?_⟩;
    · intro t ht;
      rcases Finset.mem_insert.mp ht with rfl | ht;
      · rfl;
      · exact ((ih a hk).1 t ht).trans hk.le;
    · intro u r hr;
      split_ifs at hr;
      · simp at hr;
      · have := Finset.mem_of_max hr;
        exact ((ih a hk).1 r (Finset.mem_filter.mp this).1).trans_lt hk;
    · intro t ht;
      exact ((ih a hk).1 t ht).trans_lt hk;
  | deficiency a s =>
    obtain ⟨ha, hs, -⟩ := hk;
    have hρ : ((node Γ₀ τ s).mu a).unbotD a < n := by
      induction h : (node Γ₀ τ s).mu a using WithBot.recBotCoe with
      | bot => simpa using ha;
      | coe r => simpa using ((ih s hs).2.1 a r h).trans hs;
    simp only [mk, restr_of_lt ha, restr_of_lt hs, restr_of_lt hρ];
    refine ⟨?_, ?_, ?_⟩;
    · intro t ht;
      rcases Finset.mem_insert.mp ht with rfl | ht;
      · rfl;
      · exact ((ih _ hρ).1 t ht).trans hρ.le;
    · intro u r hr;
      split_ifs at hr;
      · subst u;
        exact ((ih s hs).2.1 a r hr).trans hs;
      · have := Finset.mem_of_max hr;
        exact ((ih a ha).1 r (Finset.mem_filter.mp this).1).trans_lt ha;
    · intro t ht;
      exact ((ih a ha).1 t ht).trans_lt ha;

end Veltman.StepByStep

end FFL.InterpretabilityLogic

end
