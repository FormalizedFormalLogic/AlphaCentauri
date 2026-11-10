module

public import AlphaCentauri.InterpretabilityLogic.MaximalConsistentTheory
public import AlphaCentauri.InterpretabilityLogic.Veltman.Extension
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Data.Nat.Pairing

/-!
# Completeness of $\mathbf{ILM}_0$ with respect to Veltman models

A step-by-step construction of a Veltman model satisfying the frame condition of $\mathsf{M}_0$, for
any extension of $\mathbf{IL}$ by axioms proving $\mathsf{M}_0$. One world is added at each step,
with no successors; its predecessors are the ancestors of the world it is added for along a parent
map, so the predecessors of every world form a chain. Every world is labelled by a maximal
consistent set, and the worlds added to remove deficiencies are assuring successors carrying the
promises of criticality, the boxed formulas required by $\mathsf{M}_0$, and, for a deficiency of
`A ▷ B`, a set `ε A` of further promises fixed in advance.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula Logic Logic.ofAxioms MaximalConsistentTheory

namespace Veltman.StepByStep

variable {α : Type*} [DecidableEq α] {𝔸 : Set (Formula α)}

/-- A world is isolated, or added for a world `a` to witness `¬(A ▷ B)`, or added for `a` as a
`≺[a]`-successor of `s` to remove a deficiency of `A ▷ B`. -/
inductive Kind (α : Type*)
  | isolated
  | problem (a : ℕ) (B : Formula α)
  | deficiency (a s : ℕ) (A : Formula α)

/-- A world: its kind and maximal consistent set, its predecessors, its ancestors along the parent
map, and, for each `u`, the world supplying the boxed formulas, the criticality promises, and the
further promises that its `≺[u]`-successors must satisfy. -/
structure Node (𝔸 : Set (Formula α)) where
  kind : Kind α
  set : MaximalConsistentTheory (ofAxioms 𝔸)
  pre : Finset ℕ
  anc : Finset ℕ
  mu : ℕ → WithBot ℕ
  cr : ℕ → Set (Formula α)
  extra : ℕ → Set (Formula α)

/-- A step either witnesses `¬(A ▷ B)` at `x` or removes the deficiency of `A ▷ B` at `x` on `y`. -/
inductive Job (α : Type*)
  | problem (x : ℕ) (A B : Formula α)
  | deficiency (x y : ℕ) (A B : Formula α)

section

variable (get : ℕ → Node 𝔸)

/-- The members of `P` above `u`. -/
def above (P : Finset ℕ) (u : ℕ) : Finset ℕ := P.filter (fun t ↦ u ∈ (get t).pre)

/-- The boxed formulas of the world `r`, if any. -/
def boxes (r : WithBot ℕ) : Set (Formula α) :=
  WithBot.recBotCoe ∅ (fun r ↦ (get r).set.boxLabel ∅) r

/-- The promises a `≺[x]`-successor of `y` must keep. -/
def label (x y : ℕ) : Set (Formula α) := (get y).cr x ∪ (get y).extra x ∪ boxes get ((get y).mu x)

/-- The isolated world `n` labelled by `Δ`. -/
def isolatedNode (n : ℕ) (Δ : MaximalConsistentTheory (ofAxioms 𝔸)) : Node 𝔸 :=
  ⟨.isolated, Δ, ∅, {n}, fun _ ↦ ⊥, fun _ ↦ ∅, fun _ ↦ ∅⟩

/-- The world `n` of kind `k` labelled by `Δ`, given the earlier worlds, where a world added to
remove a deficiency of `A ▷ B` promises `ε A`. -/
noncomputable def mk (ε : Formula α → Set (Formula α)) (n : ℕ) (k : Kind α)
    (Δ : MaximalConsistentTheory (ofAxioms 𝔸)) : Node 𝔸 :=
  match k with
  | .isolated => isolatedNode n Δ
  | .problem a B =>
    ⟨.problem a B, Δ, (get a).anc, insert n (get a).anc,
      fun u ↦ if u = a then ⊥ else (above get (get a).anc u).max,
      fun u ↦ if u = a then {∼B} else ⋃ t ∈ above get (get a).anc u, (get t).cr u, fun _ ↦ ∅⟩
  | .deficiency a s A =>
    ⟨.deficiency a s A, Δ, (get a).anc, insert n (get (((get s).mu a).unbotD a)).anc,
      fun u ↦ if u = a then (get s).mu a else (above get (get a).anc u).max,
      fun u ↦ if u = a then (get s).cr a else ⋃ t ∈ above get (get a).anc u, (get t).cr u,
      fun u ↦ if u = a then (get s).extra a ∪ ε A else ∅⟩

end

variable (Γ₀ : MaximalConsistentTheory (ofAxioms 𝔸)) (ε : Formula α → Set (Formula α))
  (τ : ℕ → Job α)

open Classical in
/-- The world `n`, given the earlier worlds. -/
noncomputable def step (n : ℕ) (get : ℕ → Node 𝔸) : Node 𝔸 :=
  match τ n with
  | .problem x A B =>
    if h : x < n ∧ A ▷ B ∉ (get x).set then
      mk get ε n (.problem x B) (exists_assuringSuccessor_of_rhd_not_mem h.2).choose
    else mk get ε n .isolated Γ₀
  | .deficiency x y A B =>
    if h : x < n ∧ y < n ∧ x ∈ (get y).pre ∧ A ▷ B ∈ (get x).set ∧ A ∈ (get y).set ∧
        ∃ Δ, AssuringSuccessor (label get x y ∪ ε A) (get x).set Δ ∧ B ∈ Δ ∧ □(∼B) ∈ Δ then
      mk get ε n (.deficiency x y A) h.2.2.2.2.2.choose
    else mk get ε n .isolated Γ₀

/-- The worlds of the construction. -/
noncomputable def node : ℕ → Node 𝔸
  | n => step Γ₀ ε τ n (fun m ↦ if m < n then node m else isolatedNode 0 Γ₀)
termination_by n => n

/-- The worlds before `n`. -/
noncomputable def restr (n : ℕ) : ℕ → Node 𝔸 :=
  fun m ↦ if m < n then node Γ₀ ε τ m else isolatedNode 0 Γ₀

variable {Γ₀ ε τ}

lemma node_eq (n : ℕ) : node Γ₀ ε τ n = step Γ₀ ε τ n (restr Γ₀ ε τ n) := by
  rw [node];
  rfl

lemma restr_of_lt {n m : ℕ} (h : m < n) : restr Γ₀ ε τ n m = node Γ₀ ε τ m := by
  simp [restr, h]

lemma exists_mk (n : ℕ) : ∃ k Δ, node Γ₀ ε τ n = mk (restr Γ₀ ε τ n) ε n k Δ := by
  rw [node_eq];
  unfold step;
  split <;> split_ifs <;> exact ⟨_, _, rfl⟩

omit [DecidableEq α] in
@[simp] lemma mk_kind {get : ℕ → Node 𝔸} {n : ℕ} {k : Kind α} {Δ} : (mk get ε n k Δ).kind = k := by
  cases k <;> rfl

omit [DecidableEq α] in
@[simp] lemma mk_set {get : ℕ → Node 𝔸} {n : ℕ} {k : Kind α} {Δ} : (mk get ε n k Δ).set = Δ := by
  cases k <;> rfl

lemma node_eq_mk (n : ℕ) :
    node Γ₀ ε τ n = mk (restr Γ₀ ε τ n) ε n (node Γ₀ ε τ n).kind (node Γ₀ ε τ n).set := by
  obtain ⟨k, Δ, h⟩ := exists_mk (Γ₀ := Γ₀) (ε := ε) (τ := τ) n;
  rw [h];
  simp

/-- The world `n` was added for `a`. -/
def Kind.anchor : Kind α → WithBot ℕ
  | .isolated => ⊥
  | .problem a _ => a
  | .deficiency a _ _ => a

lemma kind_spec (n : ℕ) :
    match (node Γ₀ ε τ n).kind with
    | .isolated => (node Γ₀ ε τ n).set = Γ₀
    | .problem a B => a < n ∧ ∃ A, τ n = .problem a A B ∧ A ▷ B ∉ (node Γ₀ ε τ a).set ∧
        AssuringSuccessor {∼B} (node Γ₀ ε τ a).set (node Γ₀ ε τ n).set ∧
        A ∈ (node Γ₀ ε τ n).set ∧ □(∼A) ∈ (node Γ₀ ε τ n).set
    | .deficiency a s A => a < n ∧ s < n ∧ a ∈ (node Γ₀ ε τ s).pre ∧
        ∃ B, τ n = .deficiency a s A B ∧ A ▷ B ∈ (node Γ₀ ε τ a).set ∧ A ∈ (node Γ₀ ε τ s).set ∧
        AssuringSuccessor (label (restr Γ₀ ε τ n) a s ∪ ε A) (node Γ₀ ε τ a).set
          (node Γ₀ ε τ n).set ∧
        B ∈ (node Γ₀ ε τ n).set ∧ □(∼B) ∈ (node Γ₀ ε τ n).set := by
  rw [node_eq n];
  unfold step;
  rcases hτ : τ n with ⟨x, A, B⟩ | ⟨x, y, A, B⟩ <;> simp only;
  · split_ifs with h;
    · simp only [mk_kind, mk_set];
      have hx := restr_of_lt (Γ₀ := Γ₀) (ε := ε) (τ := τ) h.1;
      have hc := (exists_assuringSuccessor_of_rhd_not_mem h.2).choose_spec;
      exact ⟨h.1, A, rfl, by simpa [hx] using h.2, by simpa only [hx] using hc.1, hc.2⟩;
    · simp [mk, isolatedNode];
  · split_ifs with h;
    · simp only [mk_kind, mk_set];
      have hx := restr_of_lt (Γ₀ := Γ₀) (ε := ε) (τ := τ) h.1;
      have hy := restr_of_lt (Γ₀ := Γ₀) (ε := ε) (τ := τ) h.2.1;
      have hc := h.2.2.2.2.2.choose_spec;
      exact ⟨h.1, h.2.1, by simpa [hy] using h.2.2.1, B, rfl, by simpa [hx] using h.2.2.2.1,
        by simpa [hy] using h.2.2.2.2.1, by simpa only [hx] using hc.1, hc.2⟩;
    · simp [mk, isolatedNode];

lemma kind_lt (n : ℕ) :
    match (node Γ₀ ε τ n).kind with
    | .isolated => True
    | .problem a _ => a < n
    | .deficiency a s _ => a < n ∧ s < n ∧ a ∈ (node Γ₀ ε τ s).pre := by
  have := kind_spec (Γ₀ := Γ₀) (ε := ε) (τ := τ) n;
  split at this <;> simp_all

omit [DecidableEq α] in
lemma above_congr {get get' : ℕ → Node 𝔸} {P : Finset ℕ} {u : ℕ}
    (h : ∀ t ∈ P, get t = get' t) : above get P u = above get' P u :=
  Finset.filter_congr fun t ht ↦ by rw [h t ht]

lemma node_bounds (n : ℕ) :
    (∀ t ∈ (node Γ₀ ε τ n).anc, t ≤ n) ∧ (∀ u (r : ℕ), (node Γ₀ ε τ n).mu u = r → r < n) ∧
      (∀ t ∈ (node Γ₀ ε τ n).pre, t < n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hk := kind_lt (Γ₀ := Γ₀) (ε := ε) (τ := τ) n;
  rw [node_eq_mk];
  generalize (node Γ₀ ε τ n).kind = k at hk;
  generalize (node Γ₀ ε τ n).set = Δ;
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
    have hρ : ((node Γ₀ ε τ s).mu a).unbotD a < n := by
      induction h : (node Γ₀ ε τ s).mu a using WithBot.recBotCoe with
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

section

local notation "𝒩" => node Γ₀ ε τ

lemma anc_le {n t : ℕ} (h : t ∈ (𝒩 n).anc) : t ≤ n := (node_bounds n).1 t h

lemma mu_lt {n u r : ℕ} (h : (𝒩 n).mu u = r) : r < n := (node_bounds n).2.1 u r h

lemma pre_lt {n t : ℕ} (h : t ∈ (𝒩 n).pre) : t < n := (node_bounds n).2.2 t h

lemma above_restr {n a u : ℕ} (ha : a < n) :
    above (restr Γ₀ ε τ n) (𝒩 a).anc u = above 𝒩 (𝒩 a).anc u :=
  above_congr fun _ ht ↦ restr_of_lt ((anc_le ht).trans_lt ha)

lemma biUnion_restr {n a u : ℕ} (ha : a < n) :
    ⋃ t ∈ above (restr Γ₀ ε τ n) (𝒩 a).anc u, (restr Γ₀ ε τ n t).cr u =
      ⋃ t ∈ above 𝒩 (𝒩 a).anc u, (𝒩 t).cr u := by
  rw [above_restr ha];
  refine Set.iUnion₂_congr fun t ht ↦ ?_;
  rw [restr_of_lt ((anc_le (Finset.mem_filter.mp ht).1).trans_lt ha)];

lemma unbotD_mu_lt {n a s : ℕ} (ha : a < n) (hs : s < n) : ((𝒩 s).mu a).unbotD a < n := by
  induction hm : (𝒩 s).mu a using WithBot.recBotCoe with
  | bot => simpa using ha;
  | coe r => simpa using (mu_lt hm).trans hs;

lemma fields_isolated {n : ℕ} (h : (𝒩 n).kind = .isolated) :
    (𝒩 n).pre = ∅ ∧ (𝒩 n).anc = {n} ∧ (∀ u, (𝒩 n).mu u = ⊥) ∧ (∀ u, (𝒩 n).cr u = ∅) ∧
      (∀ u, (𝒩 n).extra u = ∅) := by
  rw [node_eq_mk n, h];
  simp [mk, isolatedNode];

lemma fields_problem {n a : ℕ} {B : Formula α} (h : (𝒩 n).kind = .problem a B) :
    (𝒩 n).pre = (𝒩 a).anc ∧ (𝒩 n).anc = insert n (𝒩 a).anc ∧
      (∀ u, (𝒩 n).mu u = if u = a then ⊥ else (above 𝒩 (𝒩 a).anc u).max) ∧
      (∀ u, (𝒩 n).cr u = if u = a then {∼B} else ⋃ t ∈ above 𝒩 (𝒩 a).anc u, (𝒩 t).cr u) ∧
      (∀ u, (𝒩 n).extra u = ∅) := by
  have ha : a < n := by simpa [h] using kind_lt (Γ₀ := Γ₀) (ε := ε) (τ := τ) n;
  rw [node_eq_mk n, h];
  refine ⟨?_, ?_, fun u ↦ ?_, fun u ↦ ?_, fun u ↦ ?_⟩;
  · simp only [mk, restr_of_lt ha];
  · simp only [mk, restr_of_lt ha];
  · simp only [mk, restr_of_lt ha, above_restr ha];
  · simp only [mk, restr_of_lt ha, biUnion_restr ha];
  · rfl;

lemma fields_deficiency {n a s : ℕ} {A : Formula α} (h : (𝒩 n).kind = .deficiency a s A) :
    (𝒩 n).pre = (𝒩 a).anc ∧ (𝒩 n).anc = insert n (𝒩 (((𝒩 s).mu a).unbotD a)).anc ∧
      (∀ u, (𝒩 n).mu u = if u = a then (𝒩 s).mu a else (above 𝒩 (𝒩 a).anc u).max) ∧
      (∀ u, (𝒩 n).cr u = if u = a then (𝒩 s).cr a else ⋃ t ∈ above 𝒩 (𝒩 a).anc u, (𝒩 t).cr u) ∧
      (∀ u, (𝒩 n).extra u = if u = a then (𝒩 s).extra a ∪ ε A else ∅) := by
  obtain ⟨ha, hs, -⟩ : a < n ∧ s < n ∧ _ := by
    simpa [h] using kind_lt (Γ₀ := Γ₀) (ε := ε) (τ := τ) n;
  have hρ := unbotD_mu_lt (Γ₀ := Γ₀) (ε := ε) (τ := τ) ha hs;
  rw [node_eq_mk n, h];
  refine ⟨?_, ?_, fun u ↦ ?_, fun u ↦ ?_, fun u ↦ ?_⟩;
  · simp only [mk, restr_of_lt ha];
  · simp only [mk, restr_of_lt hs, restr_of_lt hρ];
  · simp only [mk, restr_of_lt ha, restr_of_lt hs, above_restr ha];
  · simp only [mk, restr_of_lt ha, restr_of_lt hs, biUnion_restr ha];
  · simp only [mk, restr_of_lt hs];

lemma label_restr {n a s : ℕ} {A : Formula α} (h : (𝒩 n).kind = .deficiency a s A) :
    label (restr Γ₀ ε τ n) a s = label 𝒩 a s := by
  obtain ⟨-, hs, -⟩ : a < n ∧ s < n ∧ _ := by
    simpa [h] using kind_lt (Γ₀ := Γ₀) (ε := ε) (τ := τ) n;
  unfold label boxes;
  rw [restr_of_lt hs];
  induction hm : (𝒩 s).mu a using WithBot.recBotCoe with
  | bot => rfl;
  | coe r => simp [restr_of_lt ((mu_lt hm).trans hs)];

/-- The parent of the world `n`. -/
noncomputable def parent (n : ℕ) : ℕ :=
  match (𝒩 n).kind with
  | .isolated => n
  | .problem a _ => a
  | .deficiency a s _ => ((𝒩 s).mu a).unbotD a

lemma mem_anc_self (n : ℕ) : n ∈ (𝒩 n).anc := by
  rcases hk : (𝒩 n).kind with _ | ⟨a, B⟩ | ⟨a, s, A⟩;
  · simp [(fields_isolated hk).2.1];
  · simp [(fields_problem hk).2.1];
  · simp [(fields_deficiency hk).2.1];

lemma anc_eq_insert {n : ℕ} (h : (𝒩 n).kind ≠ .isolated) :
    (𝒩 n).anc = insert n (𝒩 (parent (Γ₀ := Γ₀) (ε := ε) (τ := τ) n)).anc ∧
      parent (Γ₀ := Γ₀) (ε := ε) (τ := τ) n < n := by
  unfold parent;
  rcases hk : (𝒩 n).kind with _ | ⟨a, B⟩ | ⟨a, s, A⟩;
  · exact absurd hk h;
  · exact ⟨(fields_problem hk).2.1, by simpa [hk] using kind_lt (Γ₀ := Γ₀) (ε := ε) (τ := τ) n⟩;
  · refine ⟨(fields_deficiency hk).2.1, ?_⟩;
    obtain ⟨ha, hs, -⟩ : a < n ∧ s < n ∧ _ := by
      simpa [hk] using kind_lt (Γ₀ := Γ₀) (ε := ε) (τ := τ) n;
    exact unbotD_mu_lt ha hs;

lemma anc_subset {n m : ℕ} (h : m ∈ (𝒩 n).anc) : (𝒩 m).anc ⊆ (𝒩 n).anc := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hk : (𝒩 n).kind = .isolated;
  · obtain rfl : m = n := by simpa [(fields_isolated hk).2.1] using h;
    rfl;
  · obtain ⟨he, hlt⟩ := anc_eq_insert hk;
    rw [he] at h ⊢;
    rcases Finset.mem_insert.mp h with rfl | h;
    · rw [← he];
    · exact (ih _ hlt h).trans (Finset.subset_insert _ _);

/-- The ancestors of a world form a chain. -/
lemma mem_anc_of_le {n p q : ℕ} (hp : p ∈ (𝒩 n).anc) (hq : q ∈ (𝒩 n).anc) (hpq : p ≤ q) :
    p ∈ (𝒩 q).anc := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hk : (𝒩 n).kind = .isolated;
  · obtain rfl : q = n := by simpa [(fields_isolated hk).2.1] using hq;
    exact hp;
  · obtain ⟨he, hlt⟩ := anc_eq_insert hk;
    rw [he] at hq;
    rcases Finset.mem_insert.mp hq with rfl | hq;
    · exact hp;
    · have hq' := anc_le hq;
      rw [he] at hp;
      rcases Finset.mem_insert.mp hp with rfl | hp;
      · omega;
      · exact ih _ hlt hp hq;

lemma pre_anc_mu (x : ℕ) :
    (∀ t ∈ (𝒩 x).pre, t ∈ (𝒩 x).anc) ∧
      ∀ w (r : ℕ), w ∈ (𝒩 x).pre → (𝒩 x).mu w = r → w ∈ (𝒩 r).pre ∧ r ∈ (𝒩 x).anc := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  rcases hk : (𝒩 x).kind with _ | ⟨a, B⟩ | ⟨a, s, A⟩;
  · simp [(fields_isolated hk).1];
  · obtain ⟨hp, he, hm, -⟩ := fields_problem hk;
    rw [hp, he];
    refine ⟨fun t ht ↦ Finset.mem_insert_of_mem ht, fun w r hw hr ↦ ?_⟩;
    rw [hm] at hr;
    split_ifs at hr;
    · simp at hr;
    · have := Finset.mem_filter.mp (Finset.mem_of_max hr);
      exact ⟨this.2, Finset.mem_insert_of_mem this.1⟩;
  · obtain ⟨hp, he, hm, -⟩ := fields_deficiency hk;
    obtain ⟨ha, hs, has⟩ : a < x ∧ s < x ∧ a ∈ (𝒩 s).pre := by
      simpa [hk] using kind_lt (Γ₀ := Γ₀) (ε := ε) (τ := τ) x;
    have hsub : (𝒩 a).anc ⊆ (𝒩 (((𝒩 s).mu a).unbotD a)).anc := by
      induction hr : (𝒩 s).mu a using WithBot.recBotCoe with
      | bot => simp;
      | coe r =>
        obtain ⟨h₁, -⟩ := (ih s hs).2 a r has hr;
        simpa using anc_subset ((ih r ((mu_lt hr).trans hs)).1 a h₁);
    rw [hp, he];
    refine ⟨fun t ht ↦ Finset.mem_insert_of_mem (hsub ht), fun w r hw hr ↦ ?_⟩;
    rw [hm] at hr;
    split_ifs at hr with hwa;
    · subst w;
      refine ⟨((ih s hs).2 a r has hr).1, Finset.mem_insert_of_mem ?_⟩;
      simpa [hr] using mem_anc_self (Γ₀ := Γ₀) (ε := ε) (τ := τ) r;
    · have := Finset.mem_filter.mp (Finset.mem_of_max hr);
      exact ⟨this.2, Finset.mem_insert_of_mem (hsub this.1)⟩;

lemma pre_subset_anc {x t : ℕ} (h : t ∈ (𝒩 x).pre) : t ∈ (𝒩 x).anc := (pre_anc_mu x).1 t h

lemma mu_spec {x w r : ℕ} (hw : w ∈ (𝒩 x).pre) (hr : (𝒩 x).mu w = r) :
    w ∈ (𝒩 r).pre ∧ r ∈ (𝒩 x).anc := (pre_anc_mu x).2 w r hw hr

lemma pre_eq_anc_anchor {x t : ℕ} (h : t ∈ (𝒩 x).pre) :
    ∃ a : ℕ, (𝒩 x).kind.anchor = a ∧ (𝒩 x).pre = (𝒩 a).anc := by
  rcases hk : (𝒩 x).kind with _ | ⟨a, B⟩ | ⟨a, s, A⟩;
  · simp [(fields_isolated hk).1] at h;
  · exact ⟨a, rfl, (fields_problem hk).1⟩;
  · exact ⟨a, rfl, (fields_deficiency hk).1⟩;

lemma anc_subset_pre {x y : ℕ} (h : y ∈ (𝒩 x).pre) : (𝒩 y).anc ⊆ (𝒩 x).pre := by
  obtain ⟨a, -, he⟩ := pre_eq_anc_anchor h;
  rw [he] at h ⊢;
  exact anc_subset h

lemma pre_trans {x y z : ℕ} (h₁ : x ∈ (𝒩 y).pre) (h₂ : y ∈ (𝒩 z).pre) : x ∈ (𝒩 z).pre :=
  anc_subset_pre h₂ (pre_subset_anc h₁)

lemma lt_of_mem_pre_of_anchor {x u a : ℕ} (hu : u ∈ (𝒩 x).pre) (ha : (𝒩 x).kind.anchor = a) :
    u ≤ a := by
  obtain ⟨a', ha', he⟩ := pre_eq_anc_anchor hu;
  obtain rfl : a' = a := by simpa [ha] using ha'.symm;
  rw [he] at hu;
  exact anc_le hu

lemma mu_of_anchor_ne {x w : ℕ} (h : (𝒩 x).kind.anchor ≠ w) :
    (𝒩 x).mu w = (above 𝒩 (𝒩 x).pre w).max := by
  rcases hk : (𝒩 x).kind with _ | ⟨a, B⟩ | ⟨a, s, A⟩;
  · simp [(fields_isolated hk).1, (fields_isolated hk).2.2.1, above];
  · have hwa : w ≠ a := by rintro rfl; simp [hk, Kind.anchor] at h;
    rw [(fields_problem hk).2.2.1, (fields_problem hk).1];
    simp [hwa];
  · have hwa : w ≠ a := by rintro rfl; simp [hk, Kind.anchor] at h;
    rw [(fields_deficiency hk).2.2.1, (fields_deficiency hk).1];
    simp [hwa];

lemma cr_of_anchor_ne {x w : ℕ} (h : (𝒩 x).kind.anchor ≠ w) :
    (𝒩 x).cr w = ⋃ t ∈ above 𝒩 (𝒩 x).pre w, (𝒩 t).cr w := by
  rcases hk : (𝒩 x).kind with _ | ⟨a, B⟩ | ⟨a, s, A⟩;
  · simp [(fields_isolated hk).1, (fields_isolated hk).2.2.2.1, above];
  · have hwa : w ≠ a := by rintro rfl; simp [hk, Kind.anchor] at h;
    rw [(fields_problem hk).2.2.2.1, (fields_problem hk).1];
    simp [hwa];
  · have hwa : w ≠ a := by rintro rfl; simp [hk, Kind.anchor] at h;
    rw [(fields_deficiency hk).2.2.2.1, (fields_deficiency hk).1];
    simp [hwa];

lemma extra_of_anchor_ne {x w : ℕ} (h : (𝒩 x).kind.anchor ≠ w) : (𝒩 x).extra w = ∅ := by
  rcases hk : (𝒩 x).kind with _ | ⟨a, B⟩ | ⟨a, s, A⟩;
  · exact (fields_isolated hk).2.2.2.2 w;
  · exact (fields_problem hk).2.2.2.2 w;
  · have hwa : w ≠ a := by rintro rfl; simp [hk, Kind.anchor] at h;
    rw [(fields_deficiency hk).2.2.2.2];
    simp [hwa];

lemma exists_mu_of_mem_above {x w u : ℕ} (h : (𝒩 x).kind.anchor ≠ w) (hu : u ∈ (𝒩 x).pre)
    (hw : w ∈ (𝒩 u).pre) : ∃ r : ℕ, (𝒩 x).mu w = r ∧ u ∈ (𝒩 r).anc ∧ r ∈ (𝒩 x).pre := by
  have hmem : u ∈ above 𝒩 (𝒩 x).pre w := Finset.mem_filter.mpr ⟨hu, hw⟩;
  obtain ⟨r, hr⟩ := Finset.max_of_nonempty ⟨u, hmem⟩;
  have hr' := Finset.mem_of_max hr;
  have hur : u ≤ r := by
    have := Finset.le_max hmem;
    rw [hr] at this;
    exact WithBot.coe_le_coe.mp this;
  obtain ⟨a, -, he⟩ := pre_eq_anc_anchor hu;
  have hrx := (Finset.mem_filter.mp hr').1;
  refine ⟨r, (mu_of_anchor_ne h).trans hr, ?_, hrx⟩;
  rw [he] at hu hrx;
  exact mem_anc_of_le hu hrx hur

/-- One step of `≺[w]`: along `≺` above `w`, or from the seed of a world added for `w`. -/
def Step (w t t' : ℕ) : Prop :=
  (w ∈ (𝒩 t).pre ∧ t ∈ (𝒩 t').pre) ∨ ∃ A, (𝒩 t').kind = .deficiency w t A

lemma exists_mu_of_reflTransGen {w u y y' : ℕ} (hw : w ∈ (𝒩 u).pre) (hu : u ∈ (𝒩 y).pre)
    (h : Relation.ReflTransGen (Step (Γ₀ := Γ₀) (ε := ε) (τ := τ) w) y y') :
    ∃ r : ℕ, (𝒩 y').mu w = r ∧ u ∈ (𝒩 r).anc := by
  have hne {x : ℕ} {t : ℕ} (ht : t ∈ (𝒩 x).pre) (hwt : w < t) : (𝒩 x).kind.anchor ≠ w := by
    intro ha;
    have := lt_of_mem_pre_of_anchor ht ha;
    omega;
  induction h with
  | refl =>
    obtain ⟨r, hr, hur, -⟩ := exists_mu_of_mem_above (hne hu (pre_lt hw)) hu hw;
    exact ⟨r, hr, hur⟩;
  | @tail t t' _ hs ih =>
    obtain ⟨r, hr, hur⟩ := ih;
    rcases hs with ⟨hwt, htt'⟩ | ⟨B, hd⟩;
    · have hut : u ∈ (𝒩 t).anc := anc_subset (mu_spec hwt hr).2 hur;
      obtain ⟨r', hr', hur', -⟩ := exists_mu_of_mem_above (hne htt' (pre_lt hwt))
        (anc_subset_pre htt' hut) hw;
      exact ⟨r', hr', hur'⟩;
    · refine ⟨r, ?_, hur⟩;
      rw [(fields_deficiency hd).2.2.1];
      simpa using hr;

lemma anchor_ne_of_mem_pre {x t w : ℕ} (ht : t ∈ (𝒩 x).pre) (hwt : w < t) :
    (𝒩 x).kind.anchor ≠ w := by
  intro ha;
  have := lt_of_mem_pre_of_anchor ht ha;
  omega

lemma cr_subset_of_step {w t t' : ℕ} (h : Step (Γ₀ := Γ₀) (ε := ε) (τ := τ) w t t') :
    (𝒩 t).cr w ⊆ (𝒩 t').cr w := by
  rcases h with ⟨hwt, htt'⟩ | ⟨B, hd⟩;
  · rw [cr_of_anchor_ne (anchor_ne_of_mem_pre htt' (pre_lt hwt))];
    exact Set.subset_biUnion_of_mem (u := fun t ↦ (𝒩 t).cr w)
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨htt', hwt⟩));
  · rw [(fields_deficiency hd).2.2.2.1];
    simp

lemma cr_subset_of_reflTransGen {w t t' : ℕ}
    (h : Relation.ReflTransGen (Step (Γ₀ := Γ₀) (ε := ε) (τ := τ) w) t t') :
    (𝒩 t).cr w ⊆ (𝒩 t').cr w := by
  induction h with
  | refl => rfl;
  | tail _ hs ih => exact ih.trans (cr_subset_of_step hs);

omit [DecidableEq α] in
private lemma biUnion_eq_of_forall {P : Finset ℕ} {f : ℕ → Set (Formula α)} {t₀ : ℕ} (h₀ : t₀ ∈ P)
    (h : ∀ t ∈ P, f t = f t₀) : ⋃ t ∈ P, f t = f t₀ := by
  apply subset_antisymm;
  · exact Set.iUnion₂_subset fun t ht ↦ (h t ht).le;
  · exact Set.subset_biUnion_of_mem (u := f) (Finset.mem_coe.mpr h₀);

variable (Γ₀ ε τ) in
private def CrConst (n : ℕ) : Prop :=
  ∀ t u, u ∈ (𝒩 t).pre → u ∈ (𝒩 n).pre → t ∈ (𝒩 n).anc → (𝒩 t).cr u = (𝒩 n).cr u

variable (Γ₀ ε τ) in
private def CrMu (n : ℕ) : Prop :=
  ∀ u (r : ℕ), u ∈ (𝒩 n).pre → (𝒩 n).mu u = r → (𝒩 n).cr u = (𝒩 r).cr u

variable (Γ₀ ε τ) in
private def CrGap (n : ℕ) : Prop :=
  ∀ u a, u ∈ (𝒩 a).anc → u ≠ a → (∀ t ∈ (𝒩 a).anc, u ∉ (𝒩 t).pre) → a ∈ (𝒩 n).anc →
    u ∈ (𝒩 n).pre → (𝒩 n).cr u = ∅

variable (Γ₀ ε τ) in
private def CrInvariant (n : ℕ) : Prop := CrConst Γ₀ ε τ n ∧ CrMu Γ₀ ε τ n ∧ CrGap Γ₀ ε τ n

private lemma biUnion_cr_eq_of_lt {n a u t₀ : ℕ}
    (ih : ∀ m < n, CrInvariant Γ₀ ε τ m) (ha : a < n)
    (h₀ : t₀ ∈ above 𝒩 (𝒩 a).anc u) :
    ⋃ t ∈ above 𝒩 (𝒩 a).anc u, (𝒩 t).cr u = (𝒩 t₀).cr u := by
  apply biUnion_eq_of_forall h₀;
  intro t ht;
  obtain ⟨ht₁, ht₂⟩ := Finset.mem_filter.mp ht;
  obtain ⟨h₀₁, h₀₂⟩ := Finset.mem_filter.mp h₀;
  rcases le_total t t₀ with hle | hle;
  · exact (ih t₀ ((anc_le h₀₁).trans_lt ha)).1 t u ht₂ h₀₂ (mem_anc_of_le ht₁ h₀₁ hle);
  · exact ((ih t ((anc_le ht₁).trans_lt ha)).1 t₀ u h₀₂ ht₂ (mem_anc_of_le h₀₁ ht₁ hle)).symm;

private lemma cr_const_problem {n a t u : ℕ} {B : Formula α}
    (ih : ∀ m < n, CrInvariant Γ₀ ε τ m)
    (hk : (𝒩 n).kind = .problem a B) (htρ : t ∈ (𝒩 a).anc) (hut : u ∈ (𝒩 t).pre) :
    (𝒩 t).cr u = (𝒩 n).cr u := by
  have ha : a < n := by simpa [hk] using kind_lt (Γ₀ := Γ₀) (ε := ε) (τ := τ) n;
  have hua : u ≠ a := by
    rintro rfl;
    have := anc_le htρ;
    have := pre_lt hut;
    omega;
  rw [(fields_problem hk).2.2.2.1, ite_eq_right hua,
    biUnion_cr_eq_of_lt ih ha (Finset.mem_filter.mpr ⟨htρ, hut⟩)]

private lemma cr_const_deficiency_coe {n a s r t u : ℕ}
    (ih : ∀ m < n, CrInvariant Γ₀ ε τ m)
    (ha : a < n) (hs : s < n) (has : a ∈ (𝒩 s).pre) (hr : (𝒩 s).mu a = r)
    (htρ : t ∈ (𝒩 r).anc) (hut : u ∈ (𝒩 t).pre) (hun : u ∈ (𝒩 a).anc) :
    (𝒩 t).cr u = if u = a then (𝒩 s).cr a else ⋃ t ∈ above 𝒩 (𝒩 a).anc u, (𝒩 t).cr u := by
  have hrs := mu_lt hr;
  obtain ⟨har, -⟩ := mu_spec has hr;
  by_cases hua : u = a;
  · subst u;
    rw [ite_eq_left rfl, (ih s hs).2.1 a r has hr];
    exact (ih r (hrs.trans hs)).1 t a hut har htρ;
  · rw [ite_eq_right hua];
    have haρ : a ∈ (𝒩 r).anc := pre_subset_anc har;
    rcases le_or_gt t a with hta | hta;
    · rw [biUnion_cr_eq_of_lt ih ha (Finset.mem_filter.mpr ⟨mem_anc_of_le htρ haρ hta, hut⟩)];
    · have hat : a ∈ (𝒩 t).anc := mem_anc_of_le haρ htρ hta.le;
      have htn : t < n := (anc_le htρ).trans_lt (hrs.trans hs);
      by_cases hne : (above 𝒩 (𝒩 a).anc u).Nonempty;
      · obtain ⟨t'', ht''⟩ := hne;
        rw [biUnion_cr_eq_of_lt ih ha ht''];
        obtain ⟨ht''₁, ht''₂⟩ := Finset.mem_filter.mp ht'';
        exact ((ih t htn).1 t'' u ht''₂ hut (anc_subset hat ht''₁)).symm;
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne];
        simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty];
        refine (ih t htn).2.2 u a hun hua ?_ hat hut;
        intro t' ht' hut';
        exact hne ⟨t', Finset.mem_filter.mpr ⟨ht', hut'⟩⟩;

private lemma cr_const_deficiency {n a s t u : ℕ} {A : Formula α}
    (ih : ∀ m < n, CrInvariant Γ₀ ε τ m)
    (hk : (𝒩 n).kind = .deficiency a s A) (htρ : t ∈ (𝒩 (((𝒩 s).mu a).unbotD a)).anc)
    (hut : u ∈ (𝒩 t).pre) (hun : u ∈ (𝒩 n).pre) : (𝒩 t).cr u = (𝒩 n).cr u := by
  obtain ⟨ha, hs, has⟩ : a < n ∧ s < n ∧ a ∈ (𝒩 s).pre := by
    simpa [hk] using kind_lt (Γ₀ := Γ₀) (ε := ε) (τ := τ) n;
  rw [(fields_deficiency hk).2.2.2.1];
  induction hr : (𝒩 s).mu a using WithBot.recBotCoe with
  | bot =>
    rw [hr] at htρ;
    simp only [WithBot.unbotD_bot] at htρ;
    have hua : u ≠ a := by
      rintro rfl;
      have := anc_le htρ;
      have := pre_lt hut;
      omega;
    rw [ite_eq_right hua, biUnion_cr_eq_of_lt ih ha (Finset.mem_filter.mpr ⟨htρ, hut⟩)];
  | coe r =>
    rw [hr] at htρ;
    simp only [WithBot.unbotD_coe] at htρ;
    exact cr_const_deficiency_coe ih ha hs has hr htρ hut (by rwa [(fields_deficiency hk).1] at hun)

private lemma cr_const_step {n : ℕ} (ih : ∀ m < n, CrInvariant Γ₀ ε τ m) : CrConst Γ₀ ε τ n := by
  intro t u hut hun htn;
  by_cases htn' : t = n;
  · rw [htn'];
  have hk : (𝒩 n).kind ≠ .isolated := by
    intro hk;
    simp [(fields_isolated hk).1] at hun;
  obtain ⟨he, -⟩ := anc_eq_insert hk;
  rw [he] at htn;
  have htρ := (Finset.mem_insert.mp htn).resolve_left htn';
  rcases hk' : (𝒩 n).kind with _ | ⟨a, B⟩ | ⟨a, s, A⟩;
  · exact absurd hk' hk;
  · exact cr_const_problem ih hk' (by simpa [parent, hk'] using htρ) hut;
  · exact cr_const_deficiency ih hk' (by simpa [parent, hk'] using htρ) hut hun;

private lemma cr_mu_anchor {n u r : ℕ} (ih : ∀ m < n, CrInvariant Γ₀ ε τ m)
    (hau : (𝒩 n).kind.anchor = u) (hr : (𝒩 n).mu u = r) : (𝒩 n).cr u = (𝒩 r).cr u := by
  rcases hk : (𝒩 n).kind with _ | ⟨a, B⟩ | ⟨a, s, A⟩ <;> rw [hk] at hau <;>
    simp only [Kind.anchor] at hau;
  · simp at hau;
  · obtain rfl : u = a := (WithBot.coe_injective hau).symm;
    rw [(fields_problem hk).2.2.1] at hr;
    simp at hr;
  · obtain rfl : u = a := (WithBot.coe_injective hau).symm;
    obtain ⟨-, hs, hus⟩ : u < n ∧ s < n ∧ u ∈ (𝒩 s).pre := by
      simpa [hk] using kind_lt (Γ₀ := Γ₀) (ε := ε) (τ := τ) n;
    rw [(fields_deficiency hk).2.2.1] at hr;
    simp only at hr;
    rw [(fields_deficiency hk).2.2.2.1];
    simp only;
    exact (ih s hs).2.1 u r hus hr;

private lemma cr_mu_step {n : ℕ} (ih : ∀ m < n, CrInvariant Γ₀ ε τ m) : CrMu Γ₀ ε τ n := by
  intro u r hun hr;
  by_cases hau : (𝒩 n).kind.anchor = u;
  · exact cr_mu_anchor ih hau hr;
  · rw [mu_of_anchor_ne hau] at hr;
    have hrm := Finset.mem_of_max hr;
    obtain ⟨hr₁, hr₂⟩ := Finset.mem_filter.mp hrm;
    rw [cr_of_anchor_ne hau];
    apply biUnion_eq_of_forall hrm;
    intro t ht;
    obtain ⟨ht₁, ht₂⟩ := Finset.mem_filter.mp ht;
    have htr : t ≤ r := by
      have := Finset.le_max ht;
      rw [hr] at this;
      exact WithBot.coe_le_coe.mp this;
    obtain ⟨a, -, he⟩ := pre_eq_anc_anchor hun;
    rw [he] at ht₁ hr₁;
    exact (ih r (pre_lt (he ▸ hr₁))).1 t u ht₂ hr₂ (mem_anc_of_le ht₁ hr₁ htr);

private lemma cr_gap_anchor {n u a : ℕ} (ih : ∀ m < n, CrInvariant Γ₀ ε τ m)
    (hua : u ∈ (𝒩 a).anc) (hne : u ≠ a) (hgap : ∀ t ∈ (𝒩 a).anc, u ∉ (𝒩 t).pre)
    (haρ : a ∈ (𝒩 (parent (Γ₀ := Γ₀) (ε := ε) (τ := τ) n)).anc) (hau : (𝒩 n).kind.anchor = u) :
    (𝒩 n).cr u = ∅ := by
  have hlt : u < a := lt_of_le_of_ne (anc_le hua) hne;
  rcases hk' : (𝒩 n).kind with _ | ⟨b, B⟩ | ⟨b, s, A⟩ <;> rw [hk'] at hau <;>
    simp only [Kind.anchor] at hau;
  · simp at hau;
  · obtain rfl : u = b := (WithBot.coe_injective hau).symm;
    have := anc_le (by simpa [parent, hk'] using haρ);
    omega;
  · obtain rfl : u = b := (WithBot.coe_injective hau).symm;
    obtain ⟨-, hs, hus⟩ : u < n ∧ s < n ∧ u ∈ (𝒩 s).pre := by
      simpa [hk'] using kind_lt (Γ₀ := Γ₀) (ε := ε) (τ := τ) n;
    rw [(fields_deficiency hk').2.2.2.1];
    simp only;
    have haρ' : a ∈ (𝒩 (((𝒩 s).mu u).unbotD u)).anc := by simpa [parent, hk'] using haρ;
    induction hr : (𝒩 s).mu u using WithBot.recBotCoe with
    | bot =>
      rw [hr] at haρ';
      have := anc_le (by simpa using haρ');
      omega;
    | coe r =>
      rw [hr] at haρ';
      simp only [WithBot.unbotD_coe] at haρ';
      obtain ⟨hur, -⟩ := mu_spec hus hr;
      have hra : a ≠ r := by
        rintro rfl;
        exact hgap a (mem_anc_self a) hur;
      rw [(ih s hs).2.1 u r hus hr];
      exact (ih r ((mu_lt hr).trans hs)).2.2 u a hua hne hgap haρ' hur;

private lemma cr_gap_of_anchor_ne {n u a : ℕ} (ih : ∀ m < n, CrInvariant Γ₀ ε τ m)
    (hua : u ∈ (𝒩 a).anc) (hne : u ≠ a) (hgap : ∀ t ∈ (𝒩 a).anc, u ∉ (𝒩 t).pre)
    (han : a ∈ (𝒩 n).anc) (hau : (𝒩 n).kind.anchor ≠ u) : (𝒩 n).cr u = ∅ := by
  rw [cr_of_anchor_ne hau];
  apply Set.subset_empty_iff.mp;
  refine Set.iUnion₂_subset fun t ht ↦ ?_;
  obtain ⟨ht₁, ht₂⟩ := Finset.mem_filter.mp ht;
  have hta : a < t := by
    rcases lt_trichotomy t a with h | rfl | h;
    · exact absurd ht₂ (hgap t (mem_anc_of_le (pre_subset_anc ht₁) han h.le));
    · exact absurd ht₂ (hgap t (mem_anc_self t));
    · exact h;
  exact ((ih t (pre_lt ht₁)).2.2 u a hua hne hgap
    (mem_anc_of_le han (pre_subset_anc ht₁) hta.le) ht₂).le;

private lemma cr_gap_step {n : ℕ} (ih : ∀ m < n, CrInvariant Γ₀ ε τ m) : CrGap Γ₀ ε τ n := by
  intro u a hua hne hgap han hun;
  have hka : a ≠ n := by
    rintro rfl;
    exact hgap _ han hun;
  have hk : (𝒩 n).kind ≠ .isolated := by
    intro hk;
    simp [(fields_isolated hk).1] at hun;
  obtain ⟨he, -⟩ := anc_eq_insert hk;
  have haρ : a ∈ (𝒩 (parent (Γ₀ := Γ₀) (ε := ε) (τ := τ) n)).anc := by
    rw [he] at han;
    exact (Finset.mem_insert.mp han).resolve_left hka;
  by_cases hau : (𝒩 n).kind.anchor = u;
  · exact cr_gap_anchor ih hua hne hgap haρ hau;
  · exact cr_gap_of_anchor_ne ih hua hne hgap han hau;

/-- The criticality promises are constant along the ancestors above a world. -/
lemma cr_invariants (n : ℕ) :
    (∀ t u, u ∈ (𝒩 t).pre → u ∈ (𝒩 n).pre → t ∈ (𝒩 n).anc → (𝒩 t).cr u = (𝒩 n).cr u) ∧
    (∀ u (r : ℕ), u ∈ (𝒩 n).pre → (𝒩 n).mu u = r → (𝒩 n).cr u = (𝒩 r).cr u) ∧
    (∀ u a, u ∈ (𝒩 a).anc → u ≠ a → (∀ t ∈ (𝒩 a).anc, u ∉ (𝒩 t).pre) → a ∈ (𝒩 n).anc →
      u ∈ (𝒩 n).pre → (𝒩 n).cr u = ∅) := by
  induction n using Nat.strong_induction_on with
  | _ n ih => exact ⟨cr_const_step ih, cr_mu_step ih, cr_gap_step ih⟩

lemma cr_eq_of_mem_anc {t m u : ℕ} (hut : u ∈ (𝒩 t).pre) (hum : u ∈ (𝒩 m).pre)
    (htm : t ∈ (𝒩 m).anc) : (𝒩 t).cr u = (𝒩 m).cr u := (cr_invariants m).1 t u hut hum htm

lemma cr_eq_of_mu {x u r : ℕ} (hux : u ∈ (𝒩 x).pre) (hr : (𝒩 x).mu u = r) :
    (𝒩 x).cr u = (𝒩 r).cr u := (cr_invariants x).2.1 u r hux hr

lemma biUnion_cr_eq {x u t₀ : ℕ} (h₀ : t₀ ∈ above 𝒩 (𝒩 x).pre u) :
    ⋃ t ∈ above 𝒩 (𝒩 x).pre u, (𝒩 t).cr u = (𝒩 t₀).cr u := by
  apply biUnion_eq_of_forall h₀;
  intro t ht;
  obtain ⟨ht₁, ht₂⟩ := Finset.mem_filter.mp ht;
  obtain ⟨h₀₁, h₀₂⟩ := Finset.mem_filter.mp h₀;
  obtain ⟨a, -, he⟩ := pre_eq_anc_anchor ht₁;
  rw [he] at ht₁ h₀₁;
  rcases le_total t t₀ with hle | hle;
  · exact cr_eq_of_mem_anc ht₂ h₀₂ (mem_anc_of_le ht₁ h₀₁ hle);
  · exact (cr_eq_of_mem_anc h₀₂ ht₂ (mem_anc_of_le h₀₁ ht₁ hle)).symm;

lemma label_restr_of_lt {n x y : ℕ} (hy : y < n) : label (restr Γ₀ ε τ n) x y = label 𝒩 x y := by
  unfold label boxes;
  rw [restr_of_lt hy];
  induction hm : (𝒩 y).mu x using WithBot.recBotCoe with
  | bot => rfl;
  | coe r => simp [restr_of_lt ((mu_lt hm).trans hy)];

/-! ### Maximal consistent sets along the construction -/

lemma assuring_anchor_problem {n a : ℕ} {B : Formula α} (h : (𝒩 n).kind = .problem a B) :
    AssuringSuccessor {∼B} (𝒩 a).set (𝒩 n).set := by
  have := kind_spec (Γ₀ := Γ₀) (ε := ε) (τ := τ) n;
  rw [h] at this;
  obtain ⟨-, A, -, -, h, -⟩ := this;
  exact h

lemma assuring_anchor_deficiency {n a s : ℕ} {A : Formula α}
    (h : (𝒩 n).kind = .deficiency a s A) :
    AssuringSuccessor (label 𝒩 a s ∪ ε A) (𝒩 a).set (𝒩 n).set := by
  have := kind_spec (Γ₀ := Γ₀) (ε := ε) (τ := τ) n;
  rw [h] at this;
  obtain ⟨-, -, -, B, -, -, -, h', -⟩ := this;
  rwa [label_restr h] at h'

lemma box_mem_of_parent {n : ℕ} {C : Formula α} (hk : (𝒩 n).kind ≠ .isolated)
    (hC : □C ∈ (𝒩 (parent (Γ₀ := Γ₀) (ε := ε) (τ := τ) n)).set) : □C ∈ (𝒩 n).set := by
  unfold parent at hC;
  rcases hk' : (𝒩 n).kind with _ | ⟨a, B⟩ | ⟨a, s, A⟩;
  · exact absurd hk' hk;
  · simp only [hk'] at hC;
    exact ((assuring_anchor_problem hk').mono (Set.empty_subset _)).box_mem_of_box_mem hC |>.2;
  · simp only [hk'] at hC;
    have h := assuring_anchor_deficiency hk';
    induction hr : (𝒩 s).mu a using WithBot.recBotCoe with
    | bot =>
      rw [hr] at hC;
      exact (h.mono (Set.empty_subset _)).box_mem_of_box_mem (by simpa using hC) |>.2;
    | coe r =>
      rw [hr] at hC;
      simp only [WithBot.unbotD_coe] at hC;
      have h₁ : □(∼∼C) ∈ (𝒩 n).set := by
        apply h.subset;
        left;
        right;
        simp only [boxes, hr, WithBot.recBotCoe_coe];
        exact ⟨∼C, mem_antecedents_empty_iff.mpr (mem_of_imp (box_mono dni) hC), rfl⟩;
      exact mem_of_imp (box_mono Entailment.dne) h₁;

lemma box_mem_of_mem_anc {n p : ℕ} {C : Formula α} (hp : p ∈ (𝒩 n).anc) (hC : □C ∈ (𝒩 p).set) :
    □C ∈ (𝒩 n).set := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hk : (𝒩 n).kind = .isolated;
  · obtain rfl : p = n := by simpa [(fields_isolated hk).2.1] using hp;
    exact hC;
  · obtain ⟨he, hlt⟩ := anc_eq_insert hk;
    rw [he] at hp;
    rcases Finset.mem_insert.mp hp with rfl | hp;
    · exact hC;
    · exact box_mem_of_parent hk (ih _ hlt hp);

lemma assuring_anchor {n a : ℕ} (ha : (𝒩 n).kind.anchor = a) :
    AssuringSuccessor ∅ (𝒩 a).set (𝒩 n).set := by
  rcases hk : (𝒩 n).kind with _ | ⟨b, B⟩ | ⟨b, s, A⟩ <;> rw [hk] at ha <;>
    simp only [Kind.anchor] at ha;
  · simp at ha;
  · obtain rfl : b = a := WithBot.coe_injective ha;
    exact (assuring_anchor_problem hk).mono (Set.empty_subset _);
  · obtain rfl : b = a := WithBot.coe_injective ha;
    exact (assuring_anchor_deficiency hk).mono (Set.empty_subset _);

lemma successor_of_mem_pre {n u : ℕ} (hu : u ∈ (𝒩 n).pre) :
    AssuringSuccessor ∅ (𝒩 u).set (𝒩 n).set := by
  obtain ⟨a, ha, he⟩ := pre_eq_anc_anchor hu;
  rw [he] at hu;
  intro A hA;
  exact (assuring_anchor ha).box_mem_of_box_mem
    (box_mem_of_mem_anc hu (mem_antecedents_empty_iff.mp hA))

lemma assuring_cr {n u : ℕ} (hu : u ∈ (𝒩 n).pre) :
    AssuringSuccessor ((𝒩 n).cr u) (𝒩 u).set (𝒩 n).set := by
  induction n using Nat.strong_induction_on generalizing u with
  | _ n ih =>
  by_cases hau : (𝒩 n).kind.anchor = u;
  · rcases hk : (𝒩 n).kind with _ | ⟨b, B⟩ | ⟨b, s, A⟩ <;> rw [hk] at hau <;>
      simp only [Kind.anchor] at hau;
    · simp at hau;
    · obtain rfl : u = b := (WithBot.coe_injective hau).symm;
      rw [(fields_problem hk).2.2.2.1];
      simpa using assuring_anchor_problem hk;
    · obtain rfl : u = b := (WithBot.coe_injective hau).symm;
      rw [(fields_deficiency hk).2.2.2.1];
      simpa using (assuring_anchor_deficiency hk).mono fun _ h ↦ .inl (.inl (.inl h));
  · rw [cr_of_anchor_ne hau];
    by_cases hne : (above 𝒩 (𝒩 n).pre u).Nonempty;
    · obtain ⟨t₀, h₀⟩ := hne;
      rw [biUnion_cr_eq h₀];
      obtain ⟨h₀₁, h₀₂⟩ := Finset.mem_filter.mp h₀;
      exact (ih t₀ (pre_lt h₀₁) h₀₂).trans_successor (successor_of_mem_pre h₀₁);
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne];
      simpa using successor_of_mem_pre hu;

variable (hM₀ : ∀ {A B C : Formula α}, ofAxioms 𝔸 ⊢ Axioms.M₀ A B C)

include hM₀ in
lemma assuring_label {x u : ℕ} (hu : u ∈ (𝒩 x).pre) :
    AssuringSuccessor (label 𝒩 u x) (𝒩 u).set (𝒩 x).set := by
  by_cases hau : (𝒩 x).kind.anchor = u;
  · rcases hk : (𝒩 x).kind with _ | ⟨b, B⟩ | ⟨b, s, A⟩ <;> rw [hk] at hau <;>
      simp only [Kind.anchor] at hau;
    · simp at hau;
    · obtain rfl : u = b := (WithBot.coe_injective hau).symm;
      unfold label;
      rw [(fields_problem hk).2.2.2.1, (fields_problem hk).2.2.2.2, (fields_problem hk).2.2.1];
      simpa [boxes] using assuring_anchor_problem hk;
    · obtain rfl : u = b := (WithBot.coe_injective hau).symm;
      unfold label;
      rw [(fields_deficiency hk).2.2.2.1, (fields_deficiency hk).2.2.2.2,
        (fields_deficiency hk).2.2.1];
      apply (assuring_anchor_deficiency hk).mono;
      intro _ h;
      simp only [label, Set.mem_union, ite_true] at h ⊢;
      tauto;
  · unfold label;
    rw [extra_of_anchor_ne hau, Set.union_empty];
    induction hr : (𝒩 x).mu u using WithBot.recBotCoe with
    | bot => simpa [boxes] using assuring_cr hu;
    | coe r =>
      have hm := Finset.mem_of_max ((mu_of_anchor_ne hau).symm.trans hr);
      obtain ⟨hr₁, hr₂⟩ := Finset.mem_filter.mp hm;
      simp only [boxes, WithBot.recBotCoe_coe];
      rw [cr_eq_of_mu hu hr];
      exact AssuringSuccessor.union_boxLabel_of_axiomM₀ hM₀ (assuring_cr hr₂)
        (successor_of_mem_pre hr₁)

omit hM₀

/-! ### Depth -/

/-- The formulas of a task belong to `Ω`. -/
def Job.Mem (Ω : Finset (Formula α)) : Job α → Prop
  | .problem _ A B => A ∈ Ω ∧ B ∈ Ω
  | .deficiency _ _ A B => A ∈ Ω ∧ B ∈ Ω

variable (Γ₀ ε τ) in
open Classical in
/-- The formulas `C` of `Ω` with `□∼C` at `n`. -/
noncomputable def boxedNeg (Ω : Finset (Formula α)) (n : ℕ) : Finset (Formula α) :=
  Ω.filter (fun C ↦ □(∼C) ∈ (𝒩 n).set)

lemma boxedNeg_ssubset {Ω : Finset (Formula α)} (hτ : ∀ n, (τ n).Mem Ω) {n u : ℕ}
    (hu : u ∈ (𝒩 n).pre) : boxedNeg Γ₀ ε τ Ω u ⊂ boxedNeg Γ₀ ε τ Ω n := by
  classical
  obtain ⟨a, ha, he⟩ := pre_eq_anc_anchor hu;
  rw [he] at hu;
  have h₁ : boxedNeg Γ₀ ε τ Ω u ⊆ boxedNeg Γ₀ ε τ Ω a := by
    intro C hC;
    obtain ⟨hC₁, hC₂⟩ := Finset.mem_filter.mp hC;
    exact Finset.mem_filter.mpr ⟨hC₁, box_mem_of_mem_anc hu hC₂⟩;
  have h₂ : boxedNeg Γ₀ ε τ Ω a ⊆ boxedNeg Γ₀ ε τ Ω n := by
    intro C hC;
    obtain ⟨hC₁, hC₂⟩ := Finset.mem_filter.mp hC;
    exact Finset.mem_filter.mpr ⟨hC₁, ((assuring_anchor ha).box_mem_of_box_mem hC₂).2⟩;
  refine (Finset.ssubset_iff_of_subset (h₁.trans h₂)).mpr ?_;
  have := kind_spec (Γ₀ := Γ₀) (ε := ε) (τ := τ) n;
  rcases hk : (𝒩 n).kind with _ | ⟨b, B⟩ | ⟨b, s, A⟩ <;> rw [hk] at this ha <;>
    simp only [Kind.anchor] at ha;
  · simp at ha;
  · obtain rfl : b = a := WithBot.coe_injective ha;
    obtain ⟨-, A, hτn, hAB, -, -, hA⟩ := this;
    have hΩ : A ∈ Ω := by
      have := hτ n;
      rw [hτn] at this;
      exact this.1;
    refine ⟨A, Finset.mem_filter.mpr ⟨hΩ, hA⟩, fun hm ↦ ?_⟩;
    apply hAB;
    exact mem_of_imp (C_trans (box_mono (show ofAxioms 𝔸 ⊢ ∼A 🡒 A 🡒 B by cl_prover)) axiomJ1)
      (Finset.mem_filter.mp (h₁ hm)).2;
  · obtain rfl : b = a := WithBot.coe_injective ha;
    obtain ⟨-, -, hbs, B, hτn, hAB, hA, -, -, hB⟩ := this;
    have hΩ : B ∈ Ω := by
      have := hτ n;
      rw [hτn] at this;
      exact this.2;
    refine ⟨B, Finset.mem_filter.mpr ⟨hΩ, hB⟩, fun hm ↦ ?_⟩;
    have h₃ : □(∼B) ∈ (𝒩 b).set := (Finset.mem_filter.mp (h₁ hm)).2;
    have h₄ : □(∼A) ∈ (𝒩 b).set := mem_of_imp₂ box_neg_of_rhd hAB h₃;
    exact not_mem_of_neg_mem ((successor_of_mem_pre hbs).box_mem_of_box_mem h₄).1 hA;

/-! ### The model -/

variable (Γ₀ ε τ) in
/-- The model of the construction. -/
noncomputable def model : Model ℕ α where
  Rel' x y := x ∈ (node Γ₀ ε τ y).pre
  S' w x y := w ∈ (node Γ₀ ε τ x).pre ∧ w ∈ (node Γ₀ ε τ y).pre ∧
    Relation.ReflTransGen (Step (Γ₀ := Γ₀) (ε := ε) (τ := τ) w) x y
  Val' x a := #a ∈ (node Γ₀ ε τ x).set

lemma model_isIL {Ω : Finset (Formula α)} (hτ : ∀ n, (τ n).Mem Ω) : (model Γ₀ ε τ).IsIL where
  trans _ _ _ h₁ h₂ := pre_trans h₁ h₂
  cwf := by
    classical
    refine Subrelation.wf ?_ (InvImage.wf
      (fun x ↦ Ω.card - (boxedNeg Γ₀ ε τ Ω x).card) wellFounded_lt);
    intro x y h;
    have h₁ := Finset.card_lt_card (boxedNeg_ssubset hτ h);
    have h₂ : (boxedNeg Γ₀ ε τ Ω x).card ≤ Ω.card :=
      Finset.card_le_card (Finset.filter_subset _ Ω);
    simp only [InvImage];
    omega
  rel_of_s_left h := h.1
  rel_of_s_right h := h.2.1
  s_refl h := ⟨h, h, .refl⟩
  s_trans h₁ h₂ := ⟨h₁.1, h₂.2.1, h₁.2.2.trans h₂.2.2⟩
  s_of_rel h₁ h₂ := ⟨h₁, pre_trans h₁ h₂, .single (.inl ⟨h₁, h₂⟩)⟩

instance model_hasM₀ : (model Γ₀ ε τ).HasM₀ where
  rel_of_rel_rel_s_rel {w x y z u} hwx hxy hyz hzu := by
    obtain ⟨r, hr, hxr⟩ := exists_mu_of_reflTransGen hwx hxy hyz.2.2;
    exact anc_subset_pre hzu (anc_subset (mu_spec hyz.2.1 hr).2 hxr)

/-! ### The truth lemma -/

lemma node_zero : (𝒩 0).set = Γ₀ := by
  have := kind_spec (Γ₀ := Γ₀) (ε := ε) (τ := τ) 0;
  rcases hk : (𝒩 0).kind with _ | ⟨a, B⟩ | ⟨a, s, A⟩ <;> rw [hk] at this;
  · exact this;
  · exact absurd this.1 (Nat.not_lt_zero _);
  · exact absurd this.1 (Nat.not_lt_zero _);

lemma kind_of_problem {n x : ℕ} {A B : Formula α} (hτn : τ n = .problem x A B) (hx : x < n)
    (h : A ▷ B ∉ (𝒩 x).set) : (𝒩 n).kind = .problem x B := by
  rw [node_eq n];
  unfold step;
  rw [hτn];
  simp only;
  split_ifs with hc;
  · simp;
  · exact absurd ⟨hx, by rwa [restr_of_lt hx]⟩ hc;

variable (hε : ∀ {S : Set (Formula α)} {Γ Δ : MaximalConsistentTheory (ofAxioms 𝔸)}
  {A B : Formula α}, AssuringSuccessor S Γ Δ → A ▷ B ∈ Γ → A ∈ Δ →
    ∃ Θ, AssuringSuccessor (S ∪ ε A) Γ Θ ∧ B ∈ Θ ∧ □(∼B) ∈ Θ)

include hM₀ hε in
lemma kind_of_deficiency {n x y : ℕ} {A B : Formula α} (hτn : τ n = .deficiency x y A B)
    (hx : x < n) (hy : y < n) (hxy : x ∈ (𝒩 y).pre) (hAB : A ▷ B ∈ (𝒩 x).set)
    (hA : A ∈ (𝒩 y).set) : (𝒩 n).kind = .deficiency x y A := by
  rw [node_eq n];
  unfold step;
  rw [hτn];
  simp only;
  split_ifs with hc;
  · simp;
  · apply absurd _ hc;
    rw [restr_of_lt hx, restr_of_lt hy, label_restr_of_lt hy];
    exact ⟨hx, hy, hxy, hAB, hA, hε (assuring_label hM₀ hxy) hAB hA⟩;

private lemma exists_problem_child {Ω : Finset (Formula α)}
    (hfair : ∀ t : Job α, t.Mem Ω → ∀ N, ∃ n, N < n ∧ τ n = t) {x : ℕ} {A B : Formula α}
    (hΩ : A ∈ Ω ∧ B ∈ Ω) (h : A ▷ B ∉ (𝒩 x).set) :
    ∃ n, x ∈ (𝒩 n).pre ∧ A ∈ (𝒩 n).set ∧ (𝒩 n).cr x = {∼B} := by
  obtain ⟨n, hxn, hτn⟩ := hfair (.problem x A B) hΩ x;
  have hk := kind_of_problem hτn hxn h;
  have hs := kind_spec (Γ₀ := Γ₀) (ε := ε) (τ := τ) n;
  rw [hk] at hs;
  obtain ⟨-, A', hτ', -, -, hA', -⟩ := hs;
  obtain rfl : A' = A := by
    rw [hτn] at hτ';
    injection hτ' with _ h;
    exact h.symm;
  refine ⟨n, ?_, hA', ?_⟩;
  · rw [(fields_problem hk).1];
    exact mem_anc_self x;
  · rw [(fields_problem hk).2.2.2.1];
    simp;

include hM₀ hε in
private lemma exists_deficiency_child {Ω : Finset (Formula α)}
    (hfair : ∀ t : Job α, t.Mem Ω → ∀ N, ∃ n, N < n ∧ τ n = t) {x y : ℕ} {A B : Formula α}
    (hΩ : A ∈ Ω ∧ B ∈ Ω) (hxy : x ∈ (𝒩 y).pre) (h : A ▷ B ∈ (𝒩 x).set) (hy : A ∈ (𝒩 y).set) :
    ∃ n, x ∈ (𝒩 n).pre ∧ Step (Γ₀ := Γ₀) (ε := ε) (τ := τ) x y n ∧ B ∈ (𝒩 n).set := by
  obtain ⟨n, hn, hτn⟩ := hfair (.deficiency x y A B) hΩ (max x y);
  have hk := kind_of_deficiency hM₀ hε hτn (by omega) (by omega) hxy h hy;
  have hs := kind_spec (Γ₀ := Γ₀) (ε := ε) (τ := τ) n;
  rw [hk] at hs;
  obtain ⟨-, -, -, B', hτ', -, -, -, hB', -⟩ := hs;
  obtain rfl : B' = B := by
    rw [hτn] at hτ';
    injection hτ' with _ _ _ h;
    exact h.symm;
  refine ⟨n, ?_, .inr ⟨A, hk⟩, hB'⟩;
  rw [(fields_deficiency hk).1];
  exact mem_anc_self x;

include hM₀ hε in
lemma truthlemma {Ω : Finset (Formula α)}
    (hfair : ∀ t : Job α, t.Mem Ω → ∀ N, ∃ n, N < n ∧ τ n = t) (hbot : ⊥ ∈ Ω)
    {C : Formula α} (hC : ∀ D ∈ C.subformulas, D ∈ Ω ∧ ∼D ∈ Ω) (x : ℕ) :
    Model.World.Forces (model Γ₀ ε τ) x C ↔ C ∈ (𝒩 x).set := by
  induction C generalizing x with
  | atom a => rfl;
  | falsum => exact ⟨False.elim, fun h ↦ (bot_not_mem h).elim⟩;
  | imp A B ihA ihB =>
    have hA := ihA (fun D hD ↦ hC D (by simp [subformulas, hD]));
    have hB := ihB (fun D hD ↦ hC D (by simp [subformulas, hD]));
    rw [imp_mem_iff, ← hA, ← hB];
    rfl;
  | box A ih =>
    have hA := ih (fun D hD ↦ hC D (by simp [subformulas, hD]));
    constructor;
    · intro h;
      by_contra hn;
      have hn' : ∼A ▷ ⊥ ∉ (𝒩 x).set := fun h₁ ↦
        hn <| mem_of_imp (C_trans rhd_bot (box_mono Entailment.dne)) h₁;
      obtain ⟨n, hxn, hA', -⟩ :=
        exists_problem_child hfair ⟨(hC A (by simp [subformulas])).2, hbot⟩ hn';
      exact not_mem_of_neg_mem hA' <| (hA n).mp (h n hxn);
    · intro h y hxy;
      exact (hA y).mpr ((successor_of_mem_pre hxy).box_mem_of_box_mem h).1;
  | rhd A B ihA ihB =>
    have hA := ihA (fun D hD ↦ hC D (by simp [subformulas, hD]));
    have hB := ihB (fun D hD ↦ hC D (by simp [subformulas, hD]));
    have hΩ : A ∈ Ω ∧ B ∈ Ω :=
      ⟨(hC A (by simp [subformulas])).1, (hC B (by simp [subformulas])).1⟩;
    constructor;
    · intro h;
      by_contra hn;
      obtain ⟨n, hxn, hA', hcr⟩ := exists_problem_child hfair hΩ hn;
      obtain ⟨z, ⟨-, hxz, hnz⟩, hz⟩ := h n hxn ((hA n).mpr hA');
      have h₁ : ∼B ∈ (𝒩 z).cr x := cr_subset_of_reflTransGen hnz (by simp [hcr]);
      exact not_mem_of_neg_mem ((assuring_cr hxz).subset h₁) ((hB z).mp hz);
    · intro h y hxy hy;
      obtain ⟨n, hxn, hs, hBn⟩ := exists_deficiency_child hM₀ hε hfair hΩ hxy h ((hA y).mp hy);
      exact ⟨n, ⟨hxy, hxn, .single hs⟩, (hB n).mpr hBn⟩;

end

/-! ### Enumerating the jobs -/

/-- The jobs with formulas from `l`, each appearing infinitely often. -/
noncomputable def enumJob (l : List (Formula α)) (n : ℕ) : Job α :=
  match Encodable.decode (α := Bool × ℕ × ℕ × ℕ × ℕ) n.unpair.1 with
  | some (true, x, _, i, j) => .problem x (l.getD i ⊥) (l.getD j ⊥)
  | some (false, x, y, i, j) => .deficiency x y (l.getD i ⊥) (l.getD j ⊥)
  | none => .problem 0 ⊥ ⊥

private lemma getD_mem {Ω : Finset (Formula α)} (hbot : ⊥ ∈ Ω) (i : ℕ) : Ω.toList.getD i ⊥ ∈ Ω := by
  by_cases hi : i < Ω.toList.length;
  · rw [List.getD_eq_getElem _ _ hi];
    exact Finset.mem_toList.mp (List.getElem_mem hi);
  · rw [List.getD_eq_default _ _ (not_lt.mp hi)];
    exact hbot;

private lemma exists_getD {Ω : Finset (Formula α)} {A : Formula α} (hA : A ∈ Ω) :
    ∃ i, Ω.toList.getD i ⊥ = A := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (Finset.mem_toList.mpr hA);
  exact ⟨i, List.getD_eq_getElem _ _ hi⟩

lemma enumJob_mem {Ω : Finset (Formula α)} (hbot : ⊥ ∈ Ω) (n : ℕ) : (enumJob Ω.toList n).Mem Ω := by
  unfold enumJob;
  split <;> first | exact ⟨getD_mem hbot _, getD_mem hbot _⟩ | exact ⟨hbot, hbot⟩

lemma enumJob_fair {Ω : Finset (Formula α)} (t : Job α) (ht : t.Mem Ω) (N : ℕ) :
    ∃ n, N < n ∧ enumJob Ω.toList n = t := by
  have key (c : Bool × ℕ × ℕ × ℕ × ℕ) : ∃ n, N < n ∧
      Encodable.decode (α := Bool × ℕ × ℕ × ℕ × ℕ) n.unpair.1 = some c := by
    refine ⟨Nat.pair (Encodable.encode c) (N + 1), ?_, ?_⟩;
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.right_le_pair _ _);
    · rw [Nat.unpair_pair];
      exact Encodable.encodek c;
  rcases t with ⟨x, A, B⟩ | ⟨x, y, A, B⟩;
  · obtain ⟨i, hi⟩ := exists_getD ht.1;
    obtain ⟨j, hj⟩ := exists_getD ht.2;
    obtain ⟨n, hn, hd⟩ := key (true, x, 0, i, j);
    exact ⟨n, hn, by unfold enumJob; rw [hd]; simp only [hi, hj]⟩;
  · obtain ⟨i, hi⟩ := exists_getD ht.1;
    obtain ⟨j, hj⟩ := exists_getD ht.2;
    obtain ⟨n, hn, hd⟩ := key (false, x, y, i, j);
    exact ⟨n, hn, by unfold enumJob; rw [hd]; simp only [hi, hj]⟩;

/-- The subformulas of `A`, their negations, and `⊥`. -/
def jobFormulas (A : Formula α) : Finset (Formula α) :=
  A.subformulas ∪ A.subformulas.image (∼·) ∪ {⊥}

lemma bot_mem_jobFormulas {A : Formula α} : ⊥ ∈ jobFormulas A := by simp [jobFormulas]

variable (hM₀ : ∀ {A B C : Formula α}, ofAxioms 𝔸 ⊢ Axioms.M₀ A B C)
  {ε : Formula α → Set (Formula α)}
  (hε : ∀ {S : Set (Formula α)} {Γ Δ : MaximalConsistentTheory (ofAxioms 𝔸)} {A B : Formula α},
    AssuringSuccessor S Γ Δ → A ▷ B ∈ Γ → A ∈ Δ →
      ∃ Θ, AssuringSuccessor (S ∪ ε A) Γ Θ ∧ B ∈ Θ ∧ □(∼B) ∈ Θ)

include hM₀ hε in
/-- A formula not provable in `ofAxioms 𝔸` fails at the world `0` of the model of the construction
for some initial maximal consistent set. -/
lemma exists_not_forces {A : Formula α} (hA : ¬ofAxioms 𝔸 ⊢ A) :
    ∃ Γ₀ : MaximalConsistentTheory (ofAxioms 𝔸),
      ¬Model.World.Forces (model Γ₀ ε (enumJob (jobFormulas A).toList)) 0 A := by
  classical
  have hX : ({∼A} : Set (Formula α)) *⊬[ofAxioms 𝔸] ⊥ := by
    intro h₁;
    apply hA;
    have h₂ : ofAxioms 𝔸 ⊢ ∼A 🡒 ⊥ := Context.emptyPrf <| Context.deduct <| by simpa using h₁;
    cl_prover [h₂];
  obtain ⟨Γ₀, hΓ₀⟩ := MaximalConsistentTheory.exists_superset hX;
  use Γ₀;
  have hΩ (D : Formula α) (hD : D ∈ A.subformulas) : D ∈ jobFormulas A ∧ ∼D ∈ jobFormulas A := by
    refine ⟨by simp [jobFormulas, hD], ?_⟩;
    simp only [jobFormulas, Finset.mem_union, Finset.mem_image];
    exact .inl (.inr ⟨D, hD, rfl⟩);
  rw [truthlemma hM₀ hε enumJob_fair bot_mem_jobFormulas hΩ 0, node_zero];
  exact MaximalConsistentTheory.not_mem_of_neg_mem (hΓ₀ rfl)

end Veltman.StepByStep

/-! ### Completeness -/

namespace Logic.ILM₀

open Veltman Veltman.StepByStep

variable {α : Type*} {A : Formula α}

/-- - [GJ08, Theorem 6.1] -/
theorem complete
    (h : ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α), [M.IsIL] → [M.HasM₀] → M ⊧ A) :
    𝐈𝐋𝐌₀ ⊢ A := by
  classical
  by_contra hA;
  obtain ⟨Γ₀, hΓ₀⟩ := exists_not_forces (ε := fun _ ↦ ∅) axiomM₀
    (fun h hAB hA ↦ by simpa using h.exists_of_rhd_mem hAB hA) hA;
  have := model_isIL (Γ₀ := Γ₀) (ε := fun _ ↦ ∅)
    (enumJob_mem (bot_mem_jobFormulas (A := A)));
  exact hΓ₀ (h _ 0)

end Logic.ILM₀

end FFL.InterpretabilityLogic

end
