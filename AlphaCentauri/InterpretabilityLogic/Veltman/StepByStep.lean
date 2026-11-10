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

section

local notation "𝒩" => node Γ₀ τ

lemma anc_le {n t : ℕ} (h : t ∈ (𝒩 n).anc) : t ≤ n := (bounds n).1 t h

lemma mu_lt {n u r : ℕ} (h : (𝒩 n).mu u = r) : r < n := (bounds n).2.1 u r h

lemma pre_lt {n t : ℕ} (h : t ∈ (𝒩 n).pre) : t < n := (bounds n).2.2 t h

lemma above_restr {n a u : ℕ} (ha : a < n) :
    above (restr Γ₀ τ n) (𝒩 a).anc u = above 𝒩 (𝒩 a).anc u :=
  above_congr fun _ ht ↦ restr_of_lt ((anc_le ht).trans_lt ha)

lemma biUnion_restr {n a u : ℕ} (ha : a < n) :
    ⋃ t ∈ above (restr Γ₀ τ n) (𝒩 a).anc u, (restr Γ₀ τ n t).cr u =
      ⋃ t ∈ above 𝒩 (𝒩 a).anc u, (𝒩 t).cr u := by
  rw [above_restr ha];
  refine Set.iUnion₂_congr fun t ht ↦ ?_;
  rw [restr_of_lt ((anc_le (Finset.mem_filter.mp ht).1).trans_lt ha)];

lemma unbotD_mu_lt {n a s : ℕ} (ha : a < n) (hs : s < n) : ((𝒩 s).mu a).unbotD a < n := by
  induction hm : (𝒩 s).mu a using WithBot.recBotCoe with
  | bot => simpa using ha;
  | coe r => simpa using (mu_lt hm).trans hs;

lemma fields_isolated {n : ℕ} (h : (𝒩 n).kind = .isolated) :
    (𝒩 n).pre = ∅ ∧ (𝒩 n).anc = {n} ∧ (∀ u, (𝒩 n).mu u = ⊥) ∧ (∀ u, (𝒩 n).cr u = ∅) := by
  rw [node_eq_mk n, h];
  simp [mk, isolatedNode];

lemma fields_problem {n a : ℕ} {B : Formula α} (h : (𝒩 n).kind = .problem a B) :
    (𝒩 n).pre = (𝒩 a).anc ∧ (𝒩 n).anc = insert n (𝒩 a).anc ∧
      (∀ u, (𝒩 n).mu u = if u = a then ⊥ else (above 𝒩 (𝒩 a).anc u).max) ∧
      (∀ u, (𝒩 n).cr u = if u = a then {∼B} else ⋃ t ∈ above 𝒩 (𝒩 a).anc u, (𝒩 t).cr u) := by
  have ha : a < n := by simpa [h] using kind_lt (Γ₀ := Γ₀) (τ := τ) n;
  rw [node_eq_mk n, h];
  refine ⟨?_, ?_, fun u ↦ ?_, fun u ↦ ?_⟩;
  · simp only [mk, restr_of_lt ha];
  · simp only [mk, restr_of_lt ha];
  · simp only [mk, restr_of_lt ha, above_restr ha];
  · simp only [mk, restr_of_lt ha, biUnion_restr ha];

lemma fields_deficiency {n a s : ℕ} (h : (𝒩 n).kind = .deficiency a s) :
    (𝒩 n).pre = (𝒩 a).anc ∧ (𝒩 n).anc = insert n (𝒩 (((𝒩 s).mu a).unbotD a)).anc ∧
      (∀ u, (𝒩 n).mu u = if u = a then (𝒩 s).mu a else (above 𝒩 (𝒩 a).anc u).max) ∧
      (∀ u, (𝒩 n).cr u = if u = a then (𝒩 s).cr a else ⋃ t ∈ above 𝒩 (𝒩 a).anc u, (𝒩 t).cr u) := by
  obtain ⟨ha, hs, -⟩ : a < n ∧ s < n ∧ _ := by simpa [h] using kind_lt (Γ₀ := Γ₀) (τ := τ) n;
  have hρ := unbotD_mu_lt (Γ₀ := Γ₀) (τ := τ) ha hs;
  rw [node_eq_mk n, h];
  refine ⟨?_, ?_, fun u ↦ ?_, fun u ↦ ?_⟩;
  · simp only [mk, restr_of_lt ha];
  · simp only [mk, restr_of_lt hs, restr_of_lt hρ];
  · simp only [mk, restr_of_lt ha, restr_of_lt hs, above_restr ha];
  · simp only [mk, restr_of_lt ha, restr_of_lt hs, biUnion_restr ha];

lemma label_restr {n a s : ℕ} (h : (𝒩 n).kind = .deficiency a s) :
    label (restr Γ₀ τ n) a s = label 𝒩 a s := by
  obtain ⟨-, hs, -⟩ : a < n ∧ s < n ∧ _ := by simpa [h] using kind_lt (Γ₀ := Γ₀) (τ := τ) n;
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
  | .deficiency a s => ((𝒩 s).mu a).unbotD a

lemma mem_anc_self (n : ℕ) : n ∈ (𝒩 n).anc := by
  rcases hk : (𝒩 n).kind with _ | ⟨a, B⟩ | ⟨a, s⟩;
  · simp [(fields_isolated hk).2.1];
  · simp [(fields_problem hk).2.1];
  · simp [(fields_deficiency hk).2.1];

lemma anc_eq_insert {n : ℕ} (h : (𝒩 n).kind ≠ .isolated) :
    (𝒩 n).anc = insert n (𝒩 (parent (Γ₀ := Γ₀) (τ := τ) n)).anc ∧
      parent (Γ₀ := Γ₀) (τ := τ) n < n := by
  unfold parent;
  rcases hk : (𝒩 n).kind with _ | ⟨a, B⟩ | ⟨a, s⟩;
  · exact absurd hk h;
  · exact ⟨(fields_problem hk).2.1, by simpa [hk] using kind_lt (Γ₀ := Γ₀) (τ := τ) n⟩;
  · refine ⟨(fields_deficiency hk).2.1, ?_⟩;
    obtain ⟨ha, hs, -⟩ : a < n ∧ s < n ∧ _ := by simpa [hk] using kind_lt (Γ₀ := Γ₀) (τ := τ) n;
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
  rcases hk : (𝒩 x).kind with _ | ⟨a, B⟩ | ⟨a, s⟩;
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
      simpa [hk] using kind_lt (Γ₀ := Γ₀) (τ := τ) x;
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
      simpa [hr] using mem_anc_self (Γ₀ := Γ₀) (τ := τ) r;
    · have := Finset.mem_filter.mp (Finset.mem_of_max hr);
      exact ⟨this.2, Finset.mem_insert_of_mem (hsub this.1)⟩;

lemma pre_subset_anc {x t : ℕ} (h : t ∈ (𝒩 x).pre) : t ∈ (𝒩 x).anc := (pre_anc_mu x).1 t h

lemma mu_spec {x w r : ℕ} (hw : w ∈ (𝒩 x).pre) (hr : (𝒩 x).mu w = r) :
    w ∈ (𝒩 r).pre ∧ r ∈ (𝒩 x).anc := (pre_anc_mu x).2 w r hw hr

lemma pre_eq_anc_anchor {x t : ℕ} (h : t ∈ (𝒩 x).pre) :
    ∃ a : ℕ, (𝒩 x).kind.anchor = a ∧ (𝒩 x).pre = (𝒩 a).anc := by
  rcases hk : (𝒩 x).kind with _ | ⟨a, B⟩ | ⟨a, s⟩;
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
  rcases hk : (𝒩 x).kind with _ | ⟨a, B⟩ | ⟨a, s⟩;
  · simp [(fields_isolated hk).1, (fields_isolated hk).2.2.1, above];
  · have hwa : w ≠ a := by rintro rfl; simp [hk, Kind.anchor] at h;
    rw [(fields_problem hk).2.2.1, (fields_problem hk).1];
    simp [hwa];
  · have hwa : w ≠ a := by rintro rfl; simp [hk, Kind.anchor] at h;
    rw [(fields_deficiency hk).2.2.1, (fields_deficiency hk).1];
    simp [hwa];

lemma cr_of_anchor_ne {x w : ℕ} (h : (𝒩 x).kind.anchor ≠ w) :
    (𝒩 x).cr w = ⋃ t ∈ above 𝒩 (𝒩 x).pre w, (𝒩 t).cr w := by
  rcases hk : (𝒩 x).kind with _ | ⟨a, B⟩ | ⟨a, s⟩;
  · simp [(fields_isolated hk).1, (fields_isolated hk).2.2.2, above];
  · have hwa : w ≠ a := by rintro rfl; simp [hk, Kind.anchor] at h;
    rw [(fields_problem hk).2.2.2, (fields_problem hk).1];
    simp [hwa];
  · have hwa : w ≠ a := by rintro rfl; simp [hk, Kind.anchor] at h;
    rw [(fields_deficiency hk).2.2.2, (fields_deficiency hk).1];
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
  (w ∈ (𝒩 t).pre ∧ t ∈ (𝒩 t').pre) ∨ (𝒩 t').kind = .deficiency w t

lemma exists_mu_of_reflTransGen {w u y y' : ℕ} (hw : w ∈ (𝒩 u).pre) (hu : u ∈ (𝒩 y).pre)
    (h : Relation.ReflTransGen (Step (Γ₀ := Γ₀) (τ := τ) w) y y') :
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
    rcases hs with ⟨hwt, htt'⟩ | hd;
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

lemma cr_subset_of_step {w t t' : ℕ} (h : Step (Γ₀ := Γ₀) (τ := τ) w t t') :
    (𝒩 t).cr w ⊆ (𝒩 t').cr w := by
  rcases h with ⟨hwt, htt'⟩ | hd;
  · rw [cr_of_anchor_ne (anchor_ne_of_mem_pre htt' (pre_lt hwt))];
    exact Set.subset_biUnion_of_mem (u := fun t ↦ (𝒩 t).cr w)
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨htt', hwt⟩));
  · rw [(fields_deficiency hd).2.2.2];
    simp

lemma cr_subset_of_reflTransGen {w t t' : ℕ}
    (h : Relation.ReflTransGen (Step (Γ₀ := Γ₀) (τ := τ) w) t t') : (𝒩 t).cr w ⊆ (𝒩 t').cr w := by
  induction h with
  | refl => rfl;
  | tail _ hs ih => exact ih.trans (cr_subset_of_step hs);

omit [DecidableEq α] in
private lemma biUnion_eq_of_forall {P : Finset ℕ} {f : ℕ → Set (Formula α)} {t₀ : ℕ} (h₀ : t₀ ∈ P)
    (h : ∀ t ∈ P, f t = f t₀) : ⋃ t ∈ P, f t = f t₀ := by
  apply subset_antisymm;
  · exact Set.iUnion₂_subset fun t ht ↦ (h t ht).le;
  · exact Set.subset_biUnion_of_mem (u := f) (Finset.mem_coe.mpr h₀);

/-- The criticality promises are constant along the ancestors above a world. -/
lemma cr_aux (n : ℕ) :
    (∀ t u, u ∈ (𝒩 t).pre → u ∈ (𝒩 n).pre → t ∈ (𝒩 n).anc → (𝒩 t).cr u = (𝒩 n).cr u) ∧
    (∀ u (r : ℕ), u ∈ (𝒩 n).pre → (𝒩 n).mu u = r → (𝒩 n).cr u = (𝒩 r).cr u) ∧
    (∀ u a, u ∈ (𝒩 a).anc → u ≠ a → (∀ t ∈ (𝒩 a).anc, u ∉ (𝒩 t).pre) → a ∈ (𝒩 n).anc →
      u ∈ (𝒩 n).pre → (𝒩 n).cr u = ∅) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hom {a u t₀ : ℕ} (ha : a < n) (h₀ : t₀ ∈ above 𝒩 (𝒩 a).anc u) :
      ⋃ t ∈ above 𝒩 (𝒩 a).anc u, (𝒩 t).cr u = (𝒩 t₀).cr u := by
    apply biUnion_eq_of_forall h₀;
    intro t ht;
    obtain ⟨ht₁, ht₂⟩ := Finset.mem_filter.mp ht;
    obtain ⟨h₀₁, h₀₂⟩ := Finset.mem_filter.mp h₀;
    rcases le_total t t₀ with hle | hle;
    · exact (ih t₀ ((anc_le h₀₁).trans_lt ha)).1 t u ht₂ h₀₂ (mem_anc_of_le ht₁ h₀₁ hle);
    · exact ((ih t ((anc_le ht₁).trans_lt ha)).1 t₀ u h₀₂ ht₂ (mem_anc_of_le h₀₁ ht₁ hle)).symm;
  refine ⟨?_, ?_, ?_⟩;
  · intro t u hut hun htn;
    by_cases htn' : t = n;
    · rw [htn'];
    have hk : (𝒩 n).kind ≠ .isolated := by
      intro hk;
      simp [(fields_isolated hk).1] at hun;
    obtain ⟨he, hlt⟩ := anc_eq_insert hk;
    rw [he] at htn;
    have htρ := (Finset.mem_insert.mp htn).resolve_left htn';
    rcases hk' : (𝒩 n).kind with _ | ⟨a, B⟩ | ⟨a, s⟩;
    · exact absurd hk' hk;
    · obtain ⟨hp, -, -, hc⟩ := fields_problem hk';
      have ha : a < n := by simpa [hk'] using kind_lt (Γ₀ := Γ₀) (τ := τ) n;
      have htρ' : t ∈ (𝒩 a).anc := by simpa [parent, hk'] using htρ;
      have hua : u ≠ a := by
        rintro rfl;
        have := anc_le htρ';
        have := pre_lt hut;
        omega;
      rw [hc, if_neg hua, hom ha (Finset.mem_filter.mpr ⟨htρ', hut⟩)];
    · obtain ⟨hp, -, -, hc⟩ := fields_deficiency hk';
      obtain ⟨ha, hs, has⟩ : a < n ∧ s < n ∧ a ∈ (𝒩 s).pre := by
        simpa [hk'] using kind_lt (Γ₀ := Γ₀) (τ := τ) n;
      have htρ' : t ∈ (𝒩 (((𝒩 s).mu a).unbotD a)).anc := by simpa [parent, hk'] using htρ;
      rw [hc];
      induction hr : (𝒩 s).mu a using WithBot.recBotCoe with
      | bot =>
        rw [hr] at htρ';
        simp only [WithBot.unbotD_bot] at htρ';
        have hua : u ≠ a := by
          rintro rfl;
          have := anc_le htρ';
          have := pre_lt hut;
          omega;
        rw [if_neg hua, hom ha (Finset.mem_filter.mpr ⟨htρ', hut⟩)];
      | coe r =>
        rw [hr] at htρ';
        simp only [WithBot.unbotD_coe] at htρ';
        have hrs := mu_lt hr;
        obtain ⟨har, -⟩ := mu_spec has hr;
        by_cases hua : u = a;
        · subst u;
          rw [if_pos rfl, (ih s hs).2.1 a r has hr];
          exact (ih r (hrs.trans hs)).1 t a hut har htρ';
        · rw [if_neg hua];
          have haρ : a ∈ (𝒩 r).anc := pre_subset_anc har;
          rcases le_or_gt t a with hta | hta;
          · rw [hom ha (Finset.mem_filter.mpr ⟨mem_anc_of_le htρ' haρ hta, hut⟩)];
          · have hat : a ∈ (𝒩 t).anc := mem_anc_of_le haρ htρ' hta.le;
            have htn₁ : t < n := ((anc_le htρ').trans_lt (hrs.trans hs));
            by_cases hne : (above 𝒩 (𝒩 a).anc u).Nonempty;
            · obtain ⟨t'', ht''⟩ := hne;
              rw [hom ha ht''];
              obtain ⟨ht''₁, ht''₂⟩ := Finset.mem_filter.mp ht'';
              exact ((ih t htn₁).1 t'' u ht''₂ hut (anc_subset hat ht''₁)).symm;
            · rw [Finset.not_nonempty_iff_eq_empty.mp hne];
              simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty];
              have hua' : u ∈ (𝒩 a).anc := by rwa [hp] at hun;
              refine (ih t htn₁).2.2 u a hua' hua ?_ hat hut;
              intro t' ht' hut';
              exact hne ⟨t', Finset.mem_filter.mpr ⟨ht', hut'⟩⟩;
  · intro u r hun hr;
    by_cases hau : (𝒩 n).kind.anchor = u;
    · rcases hk : (𝒩 n).kind with _ | ⟨a, B⟩ | ⟨a, s⟩ <;> rw [hk] at hau <;>
        simp only [Kind.anchor] at hau;
      · simp at hau;
      · obtain rfl : u = a := (WithBot.coe_injective hau).symm;
        rw [(fields_problem hk).2.2.1] at hr;
        simp at hr;
      · obtain rfl : u = a := (WithBot.coe_injective hau).symm;
        obtain ⟨-, hs, hus⟩ : u < n ∧ s < n ∧ u ∈ (𝒩 s).pre := by
          simpa [hk] using kind_lt (Γ₀ := Γ₀) (τ := τ) n;
        rw [(fields_deficiency hk).2.2.1] at hr;
        simp only at hr;
        rw [(fields_deficiency hk).2.2.2];
        simp only;
        exact (ih s hs).2.1 u r hus hr;
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
  · intro u a hua hne hgap han hun;
    have hka : a ≠ n := by
      rintro rfl;
      exact hgap _ han hun;
    have hk : (𝒩 n).kind ≠ .isolated := by
      intro hk;
      simp [(fields_isolated hk).1] at hun;
    obtain ⟨he, hlt⟩ := anc_eq_insert hk;
    have haρ : a ∈ (𝒩 (parent (Γ₀ := Γ₀) (τ := τ) n)).anc := by
      rw [he] at han;
      exact (Finset.mem_insert.mp han).resolve_left hka;
    have hlt_ua : u < a := lt_of_le_of_ne (anc_le hua) hne;
    by_cases hau : (𝒩 n).kind.anchor = u;
    · rcases hk' : (𝒩 n).kind with _ | ⟨b, B⟩ | ⟨b, s⟩ <;> rw [hk'] at hau <;>
        simp only [Kind.anchor] at hau;
      · simp at hau;
      · obtain rfl : u = b := (WithBot.coe_injective hau).symm;
        have := anc_le (by simpa [parent, hk'] using haρ);
        omega;
      · obtain rfl : u = b := (WithBot.coe_injective hau).symm;
        obtain ⟨-, hs, hus⟩ : u < n ∧ s < n ∧ u ∈ (𝒩 s).pre := by
          simpa [hk'] using kind_lt (Γ₀ := Γ₀) (τ := τ) n;
        rw [(fields_deficiency hk').2.2.2];
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
    · rw [cr_of_anchor_ne hau];
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

lemma cr_eq_of_mem_anc {t m u : ℕ} (hut : u ∈ (𝒩 t).pre) (hum : u ∈ (𝒩 m).pre)
    (htm : t ∈ (𝒩 m).anc) : (𝒩 t).cr u = (𝒩 m).cr u := (cr_aux m).1 t u hut hum htm

lemma cr_eq_of_mu {x u r : ℕ} (hux : u ∈ (𝒩 x).pre) (hr : (𝒩 x).mu u = r) :
    (𝒩 x).cr u = (𝒩 r).cr u := (cr_aux x).2.1 u r hux hr

end

end Veltman.StepByStep

end FFL.InterpretabilityLogic

end
