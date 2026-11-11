module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.ElementaryArithmetic.Bit
public import Foundation.FirstOrder.Arithmetic.HFS.Seq

/-!
# Hereditary finite sets in models of $\mathsf{EA}$

The file `Foundation/FirstOrder/Arithmetic/HFS/Basic.lean` on hereditary finite set theory in
models of $\mathsf{I}\Sigma_1$, ported to models of $\mathsf{EA}$: union, intersection, product,
domain, range, mappings and restriction of bit-coded sets. Comprehension is available for
$\Delta_0$ predicates only, so the Skolem and replacement principles carry an explicit bound on
the values.

- [HP98, §I.1(b)]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic
namespace ElementaryArithmetic

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

@[simp] lemma susbset_insert (x a : V) : a ⊆ insert x a := by intro z hz; simp [hz]

@[simp] lemma bitRemove_susbset (x a : V) : bitRemove x a ⊆ a := by intro z; simp

lemma lt_of_mem_dom {x y m : V} (h : ⟪x, y⟫ ∈ m) : x < m := lt_of_le_of_lt (by simp) (lt_of_mem h)

lemma lt_of_mem_rng {x y m : V} (h : ⟪x, y⟫ ∈ m) : y < m := lt_of_le_of_lt (by simp) (lt_of_mem h)

lemma insert_subset_insert_of_subset {a b : V} (x : V) (h : a ⊆ b) : insert x a ⊆ insert x b := by
  intro z hz
  rcases mem_bitInsert_iff.mp hz with (rfl | hz)
  · simp
  · simp [h hz]

@[simp] lemma under_subset_under_of_le {i j : V} : under i ⊆ under j ↔ i ≤ j :=
  ⟨by intro h; by_contra hij
      have : j < i := by simpa using hij
      simpa using h (mem_under_iff.mpr this),
   by intro hij x
      simp only [mem_under_iff]
      intro hx
      exact lt_of_lt_of_le hx hij⟩

lemma sUnion_exists_unique (s : V) :
    ∃! u : V, ∀ x, (x ∈ u ↔ ∃ t ∈ s, x ∈ t) := by
  have : 𝚺ᴬ₀-Predicate fun x ↦ ∃ t ∈ s, x ∈ t := by definability
  exact finite_comprehension! this
    ⟨s, fun i ↦ by
      rintro ⟨t, ht, hi⟩; exact lt_trans (lt_of_mem hi) (lt_of_mem ht)⟩

noncomputable def sUnion (s : V) : V := Classical.choose! (sUnion_exists_unique s)

scoped macro_rules
  | `(⋃ʰᶠ $s) => `(sUnion $s)

@[simp] lemma mem_sUnion_iff {a b : V} : a ∈ ⋃ʰᶠ b ↔ ∃ c ∈ b, a ∈ c :=
  Classical.choose!_spec (sUnion_exists_unique b) a

@[simp] lemma sUnion_empty : (⋃ʰᶠ ∅ : V) = ∅ := mem_ext (by simp)

lemma sUnion_lt_of_pos {a : V} (ha : 0 < a) : ⋃ʰᶠ a < a :=
  lt_of_lt_log ha <| by
    suffices ∀ i x, x ∈ a → i ∈ x → i < log a by simpa
    intro i x hx hi
    exact lt_of_lt_of_le (lt_of_mem hi) (le_log_of_mem hx)

@[simp] lemma sUnion_le (a : V) : ⋃ʰᶠ a ≤ a := by
  rcases Arithmetic.zero_le a with (rfl | pos)
  · simp [←emptyset_def]
  · exact le_of_lt (sUnion_lt_of_pos pos)

lemma sUnion_graph {u s : V} : u = ⋃ʰᶠ s ↔ ∀ x < u + s, (x ∈ u ↔ ∃ t ∈ s, x ∈ t) :=
  ⟨by rintro rfl; simp, by
    intro h; apply mem_ext
    intro x
    suffices x ∈ u ↔ ∃ c ∈ s, x ∈ c by simpa
    constructor
    · intro hx
      exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp)) |>.mp hx
    · rintro ⟨c, hc, hx⟩
      exact h x (lt_of_lt_of_le (lt_trans (lt_of_mem hx) (lt_of_mem hc)) (by simp))
        |>.mpr ⟨c, hc, hx⟩⟩

instance sUnion_defined : 𝚺ᴬ₀-Function₁[V] sUnion via sUnionDef :=
  .mk fun v ↦ by simp [sUnionDef, sUnion_graph]

instance sUnion_definable : 𝚺ᴬ₀-Function₁[V] sUnion := sUnion_defined.to_definable

instance sUnion_definable' (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₁[V] sUnion :=
  sUnion_definable.of_zero

noncomputable def union (a b : V) : V := ⋃ʰᶠ {a, b}

noncomputable scoped instance : Union V := ⟨union⟩

@[simp] lemma mem_cup_iff {a b c : V} : a ∈ b ∪ c ↔ a ∈ b ∨ a ∈ c := by simp [Union.union, union]

private lemma union_graph {u s t : V} : u = s ∪ t ↔ ∀ x < u + s + t, (x ∈ u ↔ x ∈ s ∨ x ∈ t) :=
  ⟨by rintro rfl; simp, by
    intro h; apply mem_ext
    intro x
    suffices x ∈ u ↔ x ∈ s ∨ x ∈ t by simpa
    constructor
    · intro hx; exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp [add_assoc])) |>.mp hx
    · rintro (hx | hx)
      · exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp )) |>.mpr (Or.inl hx)
      · exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp )) |>.mpr (Or.inr hx)⟩

instance union_defined : 𝚺ᴬ₀-Function₂[V] (· ∪ ·) via unionDef := .mk fun v ↦ by
  simp [unionDef, union_graph]

instance union_definable : 𝚺ᴬ₀-Function₂[V] (· ∪ ·) := union_defined.to_definable

instance union_definable' (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₂[V] (· ∪ ·) :=
  union_definable.of_zero

lemma insert_eq_union_singleton (a s : V) : insert a s = {a} ∪ s := mem_ext (fun x ↦ by simp)

@[simp] lemma union_polybound (a b : V) : a ∪ b ≤ 2 * (a + b) := by
  suffices ∀ i, i ∈ a ∨ i ∈ b → i < log (2 * (a + b) + 1) from
    le_iff_lt_succ.mpr <| lt_of_lt_log (by simp) <| by simpa
  rintro i (hi | hi)
  · calc
      i ≤ log (a + b) := le_trans (le_log_of_mem hi) (log_monotone (by simp))
      _ < log (2 * (a + b)) := by
        simp [log_two_mul_of_pos (show 0 < a + b from by simp [pos_of_nonempty hi])]
      _ ≤ log (2 * (a + b) + 1) := log_monotone (by simp)
  · calc
      i ≤ log (a + b) := le_trans (le_log_of_mem hi) (log_monotone (by simp))
      _ < log (2 * (a + b)) := by
        simp [log_two_mul_of_pos (show 0 < a + b from by simp [pos_of_nonempty hi])]
      _ ≤ log (2 * (a + b) + 1) := log_monotone (by simp)

instance : Bounded₂ ((· ∪ ·) : V → V → V) := ⟨‘x y. 2 * (x + y)’, fun _ ↦ by simp⟩

@[simp] lemma union_succ_union_left (a b : V) : a ⊆ a ∪ b := by intro x hx; simp [hx]

@[simp] lemma union_succ_union_right (a b : V) : b ⊆ a ∪ b := by intro x hx; simp [hx]

@[simp] lemma union_succ_union_union_left (a b c : V) : a ⊆ a ∪ b ∪ c := by intro x hx; simp [hx]

@[simp] lemma union_succ_union_union_right (a b c : V) : b ⊆ a ∪ b ∪ c := by intro x hx; simp [hx]

@[simp] lemma union_empty_eq_right (a : V) : a ∪ ∅ = a := mem_ext <| by simp

@[simp] lemma union_empty_eq_left (a : V) : ∅ ∪ a = a := mem_ext <| by simp

lemma sInter_exists_unique (s : V) :
    ∃! u : V, ∀ x, (x ∈ u ↔ s ≠ ∅ ∧ ∀ t ∈ s, x ∈ t) := by
  have : 𝚺ᴬ₀-Predicate fun x ↦ s ≠ ∅ ∧ ∀ t ∈ s, x ∈ t := by definability
  exact finite_comprehension! this
    ⟨s, fun i ↦ by
      rintro ⟨hs, h⟩
      have : log s ∈ s := log_mem_of_pos <| pos_iff_ne_zero.mpr hs
      exact _root_.trans (lt_of_mem <| h (log s) this) (lt_of_mem this)⟩

noncomputable def sInter (s : V) : V := Classical.choose! (sInter_exists_unique s)

scoped macro_rules
  | `(⋂ʰᶠ $s) => `(sInter $s)

lemma mem_sInter_iff {x s : V} : x ∈ ⋂ʰᶠ s ↔ s ≠ ∅ ∧ ∀ t ∈ s, x ∈ t :=
  Classical.choose!_spec (sInter_exists_unique s) x

@[simp] lemma mem_sInter_iff_empty : ⋂ʰᶠ (∅ : V) = ∅ := mem_ext (by simp [mem_sInter_iff])

lemma mem_sInter_iff_of_pos {x s : V} (h : s ≠ ∅) : x ∈ ⋂ʰᶠ s ↔ ∀ t ∈ s, x ∈ t := by
  simp [mem_sInter_iff, h]

noncomputable def inter (a b : V) : V := ⋂ʰᶠ {a, b}

noncomputable scoped instance : Inter V := ⟨inter⟩

@[simp] lemma mem_inter_iff {a b c : V} : a ∈ b ∩ c ↔ a ∈ b ∧ a ∈ c := by
  simp [Inter.inter, inter, mem_sInter_iff_of_pos (s := {b, c}) (nonempty_iff.mpr ⟨b, by simp⟩)]

lemma inter_comm (a b : V) : a ∩ b = b ∩ a := mem_ext (by simp [and_comm])

lemma inter_eq_self_of_subset {a b : V} (h : a ⊆ b) :
  a ∩ b = a := mem_ext (by simpa using fun i hi↦ h hi)

lemma product_exists_unique (a b : V) :
    ∃! u : V, ∀ x, (x ∈ u ↔ ∃ y ∈ a, ∃ z ∈ b, x = ⟪y, z⟫) := by
  have : 𝚺ᴬ₀-Predicate fun x ↦ ∃ y ∈ a, ∃ z ∈ b, x = ⟪y, z⟫ := by definability
  exact finite_comprehension! this
    ⟨⟪log a, log b⟫ + 1, fun i ↦ by
      rintro ⟨y, hy, z, hz, rfl⟩
      simpa [lt_succ_iff_le]
      using pair_le_pair (le_log_of_mem hy) (le_log_of_mem hz)⟩

noncomputable def product (a b : V) : V := Classical.choose! (product_exists_unique a b)

scoped macro_rules
  | `($a ×ʰᶠ $b) => `(product $a $b)

lemma mem_product_iff {x a b : V} : x ∈ a ×ʰᶠ b ↔ ∃ y ∈ a, ∃ z ∈ b, x = ⟪y, z⟫ :=
  Classical.choose!_spec (product_exists_unique a b) x

lemma mem_product_iff' {x a b : V} : x ∈ a ×ʰᶠ b ↔ π₁ x ∈ a ∧ π₂ x ∈ b := by
  suffices (∃ y ∈ a, ∃ z ∈ b, x = ⟪y, z⟫) ↔ π₁ x ∈ a ∧ π₂ x ∈ b by simpa [mem_product_iff]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩; simp [*]
  · rintro ⟨h₁, h₂⟩; exact ⟨π₁ x, h₁, π₂ x, h₂, by simp⟩

@[simp] lemma pair_mem_product_iff {x y a b : V} : ⟪x, y⟫ ∈ a ×ʰᶠ b ↔ x ∈ a ∧ y ∈ b := by
  simp [mem_product_iff']

private lemma product_graph {u a b : V} : u = a ×ʰᶠ b ↔
    ∀ x < u + (a + b + 1) ^ 2, (x ∈ u ↔ ∃ y ∈ a, ∃ z ∈ b, x = ⟪y, z⟫) :=
  ⟨by rintro rfl x _; simp [mem_product_iff], by
    intro h
    apply mem_ext; intro x
    suffices x ∈ u ↔ ∃ y ∈ a, ∃ z ∈ b, x = ⟪y, z⟫ by simpa [mem_product_iff]
    constructor
    · intro hx; exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp)) |>.mp hx
    · rintro ⟨y, hy, z, hz, rfl⟩
      exact h ⟪y, z⟫ (lt_of_lt_of_le (pair_lt_pair (lt_of_mem hy) (lt_of_mem hz))
        (le_trans (pair_polybound a b) <| by simp)) |>.mpr ⟨y, hy, z, hz, rfl⟩⟩

instance product_defined : 𝚺ᴬ₀-Function₂[V] (· ×ʰᶠ ·) via productDef := .mk fun v ↦ by
  simp [productDef, product_graph]

instance product_definable : 𝚺ᴬ₀-Function₂[V] (· ×ʰᶠ ·) := product_defined.to_definable

instance product_definable' (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₂[V] (· ×ʰᶠ ·) :=
  product_definable.of_zero

@[simp] lemma zero_product {b : V} : ∅ ×ʰᶠ b = ∅ := by
  refine mem_ext (fun i ↦ ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩) <;> simp_all [mem_product_iff]

@[simp] lemma product_zero {a : V} : a ×ʰᶠ ∅ = ∅ := by
  refine mem_ext (fun i ↦ ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩) <;> simp_all [mem_product_iff]

lemma domain_exists_unique (s : V) :
    ∃! d : V, ∀ x, x ∈ d ↔ ∃ y, ⟪x, y⟫ ∈ s := by
  have : 𝚺ᴬ₀-Predicate fun x ↦ ∃ y, ⟪x, y⟫ ∈ s :=
    Bounding.HierarchySymbol.DefinablePred.of_iff (Q := fun x ↦ ∃ y < s, ⟪x, y⟫ ∈ s)
      (by definability)
      (fun x ↦ ⟨by rintro ⟨y, hy⟩; exact ⟨y, lt_of_le_of_lt (le_pair_right x y) (lt_of_mem hy), hy⟩,
                by rintro ⟨y, _, hy⟩; exact ⟨y, hy⟩⟩)
  exact finite_comprehension!
    this
    (⟨s, fun x ↦ by rintro ⟨y, hy⟩; exact lt_of_le_of_lt (le_pair_left x y) (lt_of_mem hy)⟩)

noncomputable def domain (s : V) : V := Classical.choose! (domain_exists_unique s)

lemma mem_domain_iff {x s : V} : x ∈ domain s ↔ ∃ y, ⟪x, y⟫ ∈ s :=
  Classical.choose!_spec (domain_exists_unique s) x

private lemma domain_graph {u s : V} : u = domain s ↔
    ∀ x < u + s, (x ∈ u ↔ ∃ y < s, ∃ z ∈ s, z = ⟪x, y⟫) := by
  constructor
  · rintro rfl x _
    suffices (∃ y, ⟪x, y⟫ ∈ s) ↔ ∃ y < s, ⟪x, y⟫ ∈ s by simpa [mem_domain_iff]
    exact ⟨by rintro ⟨y, hy⟩; exact ⟨y, lt_of_le_of_lt (le_pair_right x y) (lt_of_mem hy), hy⟩, by
      rintro ⟨y, _, hy⟩; exact ⟨y, hy⟩⟩
  · intro h; apply mem_ext; intro x
    suffices x ∈ u ↔ ∃ y, ⟪x, y⟫ ∈ s by simpa [mem_domain_iff]
    constructor
    · intro hx
      rcases h x (lt_of_lt_of_le (lt_of_mem hx) (by simp)) |>.mp hx with ⟨y, _, _, hy, rfl⟩
      exact ⟨y, hy⟩
    · rintro ⟨y, hy⟩
      exact h x (lt_of_lt_of_le (lt_of_le_of_lt (le_pair_left x y) (lt_of_mem hy)) (by simp))
        |>.mpr ⟨y, lt_of_le_of_lt (le_pair_right x y) (lt_of_mem hy), _, hy, rfl⟩

instance domain_defined : 𝚺ᴬ₀-Function₁[V] domain via domainDef :=
  .mk fun v ↦ by simp [domainDef, domain_graph]

instance domain_definable : 𝚺ᴬ₀-Function₁[V] domain := domain_defined.to_definable

instance domain_definable' (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₁[V] domain :=
  domain_definable.of_zero

@[simp] lemma domain_empty : domain (∅ : V) = ∅ := mem_ext (by simp [mem_domain_iff])

@[simp] lemma domain_union (a b : V) : domain (a ∪ b) = domain a ∪ domain b := mem_ext (by
  suffices ∀ i, (∃ y, ⟪i, y⟫ ∈ a ∨ ⟪i, y⟫ ∈ b) ↔
      (∃ y, ⟪i, y⟫ ∈ a) ∨ ∃ y, ⟪i, y⟫ ∈ b by simpa [mem_domain_iff]
  intro x; constructor
  · rintro ⟨y, (hy | hy)⟩
    · left; exact ⟨y, hy⟩
    · right; exact ⟨y, hy⟩
  · rintro (⟨y, hy⟩ | ⟨y, hy⟩)
    · exact ⟨y, Or.inl hy⟩
    · exact ⟨y, Or.inr hy⟩)

@[simp] lemma domain_singleton (x y : V) : (domain {⟪x, y⟫} : V) = {x} :=
  mem_ext (by simp [mem_domain_iff])

@[simp] lemma domain_insert (x y s : V) : domain (insert ⟪x, y⟫ s) = insert x (domain s) := by
  simp [insert_eq_union_singleton]

@[simp] lemma domain_bound (s : V) : domain s ≤ 2 * s := le_iff_lt_succ.mpr
  <| lt_of_lt_log (by simp) (by
    simp only [mem_domain_iff, forall_exists_index]
    intro i x hix
    exact lt_of_le_of_lt (le_trans (le_pair_left i x) (le_log_of_mem hix))
      (by simp [log_two_mul_add_one_of_pos (pos_of_nonempty hix)]))

instance : Bounded₁ (domain : V → V) := ⟨‘x. 2 * x’, fun _ ↦ by simp⟩

lemma mem_domain_of_pair_mem {x y s : V} (h : ⟪x, y⟫ ∈ s) : x ∈ domain s :=
  mem_domain_iff.mpr ⟨y, h⟩

lemma domain_subset_domain_of_subset {s t : V} (h : s ⊆ t) : domain s ⊆ domain t := by
  intro x hx
  rcases mem_domain_iff.mp hx with ⟨y, hy⟩
  exact mem_domain_iff.mpr ⟨y, h hy⟩

@[simp] lemma domain_eq_empty_iff_eq_empty {s : V} : domain s = ∅ ↔ s = ∅ :=
  ⟨by simp only [isempty_iff, mem_domain_iff, not_exists]
      intro h x hx
      exact h (π₁ x) (π₂ x) (by simpa using hx), by rintro rfl; simp⟩

/-! ### Range -/

lemma range_exists_unique (s : V) :
    ∃! r : V, ∀ y, y ∈ r ↔ ∃ x, ⟪x, y⟫ ∈ s := by
  have : 𝚺ᴬ₀-Predicate fun y ↦ ∃ x, ⟪x, y⟫ ∈ s :=
    Bounding.HierarchySymbol.DefinablePred.of_iff (Q := fun y ↦ ∃ x < s, ⟪x, y⟫ ∈ s)
      (by definability)
      (fun y ↦ ⟨by rintro ⟨x, hy⟩; exact ⟨x, lt_of_le_of_lt (le_pair_left x y) (lt_of_mem hy), hy⟩,
                by rintro ⟨y, _, hy⟩; exact ⟨y, hy⟩⟩)
  exact finite_comprehension!
    this
    (⟨s, fun y ↦ by rintro ⟨x, hx⟩; exact lt_of_le_of_lt (le_pair_right x y) (lt_of_mem hx)⟩)

noncomputable def range (s : V) : V := Classical.choose! (range_exists_unique s)

lemma mem_range_iff {y s : V} : y ∈ range s ↔ ∃ x, ⟪x, y⟫ ∈ s :=
  Classical.choose!_spec (range_exists_unique s) y

private lemma range_graph {s' s : V} : s' = range s ↔
    ∀ y < s' + s, (y ∈ s' ↔ ∃ x < s, ∃ z ∈ s, z = ⟪x, y⟫) :=
  ⟨by rintro rfl y _
      suffices (∃ x, ⟪x, y⟫ ∈ s) ↔ ∃ x < s, ⟪x, y⟫ ∈ s by simpa [mem_range_iff]
      exact ⟨by rintro ⟨x, hx⟩; exact ⟨x, lt_of_mem_dom hx, hx⟩,
        by rintro ⟨y, _, hy⟩; exact ⟨y, hy⟩⟩,
   by intro h
      apply mem_ext
      intro y
      suffices y ∈ s' ↔ ∃ x, ⟪x, y⟫ ∈ s by simpa [mem_range_iff]
      constructor
      · intro hy
        rcases h y (lt_of_lt_of_le (lt_of_mem hy) (by simp)) |>.mp hy with ⟨y, _, _, hy, rfl⟩
        exact ⟨y, hy⟩
      · rintro ⟨x, hx⟩
        exact h y (lt_of_lt_of_le (lt_of_mem_rng hx) (by simp))
          |>.mpr ⟨x, lt_of_mem_dom hx, _, hx, rfl⟩⟩

instance range_defined : 𝚺ᴬ₀-Function₁[V] range via rangeDef :=
  .mk fun v ↦ by simp [rangeDef, range_graph]

instance range_definable : 𝚺ᴬ₀-Function₁[V] range := range_defined.to_definable

instance range_definable' (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₁[V] range :=
  range_definable.of_zero

@[simp] lemma range_empty : range (∅ : V) = ∅ := mem_ext (by simp [mem_range_iff])

@[simp] lemma range_bound (s : V) : range s ≤ 2 * s := le_iff_lt_succ.mpr
  <| lt_of_lt_log (by simp) (by
    simp only [mem_range_iff, forall_exists_index]
    intro i x hix
    exact lt_of_le_of_lt (le_trans (le_pair_right x i) (le_log_of_mem hix))
      (by simp [log_two_mul_add_one_of_pos (pos_of_nonempty hix)]))

instance : Bounded₁ (range : V → V) := ⟨‘x. 2 * x’, fun _ ↦ by simp⟩

/-! ### Disjoint -/

def Disjoint (s t : V) : Prop := s ∩ t = ∅

lemma Disjoint.iff {s t : V} : Disjoint s t ↔ ∀ x, x ∉ s ∨ x ∉ t := by
  simp [Disjoint, isempty_iff, imp_iff_not_or]

lemma Disjoint.not_of_mem {s t x : V} (hs : x ∈ s) (ht : x ∈ t) : ¬Disjoint s t := by
  simpa [Disjoint.iff, not_or] using ⟨x, hs, ht⟩

lemma Disjoint.symm {s t : V} (h : Disjoint s t) : Disjoint t s := by
  simpa [Disjoint, inter_comm t s] using h

@[simp] lemma Disjoint.singleton_iff {a s : V} : Disjoint ({a} : V) s ↔ a ∉ s := by
  simp [Disjoint, isempty_iff]

/-! ### Mapping -/

def IsMapping (m : V) : Prop := ∀ x ∈ domain m, ∃! y, ⟪x, y⟫ ∈ m

private lemma isMapping_iff {m : V} :
    IsMapping m ↔ ∃ d ≤ 2 * m, d = domain m ∧ ∀ x ∈ d, ∃ y < m,
      ⟪x, y⟫ ∈ m ∧ ∀ y' < m, ⟪x, y'⟫ ∈ m → y' = y :=
  ⟨by intro hm
      exact ⟨domain m, by simp, rfl, fun x hx ↦ by
        rcases hm x hx with ⟨y, hy, uniq⟩
        exact ⟨y, lt_of_mem_rng hy, hy, fun y' _ h' ↦ uniq y' h'⟩⟩,
   by rintro ⟨_, _, rfl, h⟩ x hx
      rcases h x hx with ⟨y, _, hxy, h⟩
      exact ExistsUnique.intro y hxy (fun y' hxy' ↦ h y' (lt_of_mem_rng hxy') hxy')⟩

instance isMapping_defined : 𝚺ᴬ₀-Predicate[V] IsMapping via isMappingDef := .mk <| by
  intro v; simp [isMappingDef, isMapping_iff]

instance isMapping_definable : 𝚺ᴬ₀-Predicate[V] IsMapping :=
  isMapping_defined.to_definable

instance isMapping_definable'
    (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) : ℌ-Predicate[V] IsMapping :=
  isMapping_definable.of_zero

lemma IsMapping.get_exists_uniq {m : V} (h : IsMapping m) {x : V} (hx : x ∈ domain m) :
    ∃! y, ⟪x, y⟫ ∈ m := h x hx

noncomputable def IsMapping.get {m : V} (h : IsMapping m) {x : V} (hx : x ∈ domain m) : V :=
  Classical.choose! (IsMapping.get_exists_uniq h hx)

@[simp] lemma IsMapping.get_mem {m : V} (h : IsMapping m) {x : V} (hx : x ∈ domain m) :
    ⟪x, h.get hx⟫ ∈ m := Classical.choose!_spec (IsMapping.get_exists_uniq h hx)

lemma IsMapping.get_uniq {m : V} (h : IsMapping m) {x y : V} (hx : x ∈ domain m)
    (hy : ⟪x, y⟫ ∈ m) : y = h.get hx :=
    (h x hx).unique hy (by simp)

@[simp] lemma IsMapping.empty : IsMapping (∅ : V) := by intro x; simp

lemma IsMapping.union_of_disjoint_domain {m₁ m₂ : V}
    (h₁ : IsMapping m₁) (h₂ : IsMapping m₂)
    (disjoint : Disjoint (domain m₁) (domain m₂)) : IsMapping (m₁ ∪ m₂) := by
  intro x
  suffices x ∈ domain m₁ ∨ x ∈ domain m₂ → ∃! y, ⟪x, y⟫ ∈ m₁ ∨ ⟪x, y⟫ ∈ m₂ by simpa
  rintro (hx | hx)
  · exact ExistsUnique.intro (h₁.get hx) (by simp) (by
      intro y
      rintro (hy | hy)
      · exact h₁.get_uniq hx hy
      · by_contra; exact Disjoint.not_of_mem hx (mem_domain_of_pair_mem hy) disjoint)
  · exact ExistsUnique.intro (h₂.get hx) (by simp) (by
      intro y
      rintro (hy | hy)
      · by_contra; exact Disjoint.not_of_mem hx (mem_domain_of_pair_mem hy) disjoint.symm
      · exact h₂.get_uniq hx hy)

@[simp] lemma IsMapping.singleton (x y : V) : IsMapping ({⟪x, y⟫} : V) := by
  intro x; simp only [domain_singleton, mem_singleton_iff, pair_ext_iff]
  rintro rfl; exact ExistsUnique.intro y (by simp) (by rintro _ ⟨_, rfl⟩; simp)

lemma IsMapping.insert {x y m : V}
    (h : IsMapping m) (disjoint : x ∉ domain m) : IsMapping (insert ⟪x, y⟫ m) := by
  simpa [insert_eq_union_singleton]
  using IsMapping.union_of_disjoint_domain (by simp) h (by simpa)

lemma IsMapping.of_subset {m m' : V} (h : IsMapping m) (ss : m' ⊆ m) : IsMapping m' := by
  intro x hx
  rcases mem_domain_iff.mp hx with ⟨y, hy⟩
  have : ∃! y, ⟪x, y⟫ ∈ m := h x (domain_subset_domain_of_subset ss hx)
  exact ExistsUnique.intro y hy (fun y' hy' ↦ this.unique (ss hy') (ss hy))

lemma IsMapping.uniq {m x y₁ y₂ : V} (h : IsMapping m) :
    ⟪x, y₁⟫ ∈ m → ⟪x, y₂⟫ ∈ m → y₁ = y₂ := fun h₁ h₂ ↦
  h x (mem_domain_iff.mpr ⟨y₁, h₁⟩) |>.unique h₁ h₂

/-! #### Properties of mappings -/

def IsMapping.Injective (m : V) : Prop := ∀ x x' y, ⟪x, y⟫ ∈ m → ⟪x', y⟫ ∈ m → x = x'

/-- An equivalent formulation of injectivity in which all quantifiers are bounded. -/
lemma IsMapping.injective_iff_bounded {m : V} :
    IsMapping.Injective m ↔
    ∀ x < m, ∀ x_1 < m, ∀ x_2 < m, ⟪x, x_2⟫ ∈ m → ⟪x_1, x_2⟫ ∈ m → x = x_1 := by
  constructor <;> intro h
  · aesop
  · intro x x' y hxy hx'y
    have hxlt : x < m := lt_of_le_of_lt (le_pair_left x y) (lt_of_mem hxy)
    have hx'lt : x' < m := lt_of_le_of_lt (le_pair_left x' y) (lt_of_mem hx'y)
    have hylt : y < m := lt_of_le_of_lt (le_pair_right x y) (lt_of_mem hxy)
    exact h x hxlt x' hx'lt y hylt hxy hx'y

instance IsMapping.injective_defined :
    𝚺ᴬ₀-Predicate[V] IsMapping.Injective via IsMapping.injectiveDef :=
  .mk fun v ↦ by simp [IsMapping.injectiveDef, injective_iff_bounded]

instance IsMapping.injective_definable : 𝚺ᴬ₀-Predicate[V] IsMapping.Injective :=
  injective_defined.to_definable

instance IsMapping.injective_definable' (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Predicate[V] IsMapping.Injective :=
  injective_definable.of_zero

@[simp] lemma IsMapping.injective_empty : IsMapping.Injective (∅ : V) := by intro x x' y; simp

def IsMapping.Surjective (m : V) : Prop := ∀ y ∈ range m, ∃ x, ⟪x, y⟫ ∈ m

/-- An equivalent formulation of surjectivity in which all quantifiers are bounded. -/
lemma IsMapping.surjective_iff_bounded {m : V} :
    IsMapping.Surjective m ↔
    ∀ y < m, y ∈ range m → ∃ x < m, ⟪x, y⟫ ∈ m := by
  constructor <;> intro h
  · intro y _ hy
    obtain ⟨x, hx⟩ := h y hy
    have hxlt : x < m := lt_of_le_of_lt (le_pair_left x y) (lt_of_mem hx)
    exact ⟨x, hxlt, hx⟩
  · intro y hy
    have hylt : y < m :=
      lt_of_le_of_lt (le_pair_right _ y) (lt_of_mem (Classical.choose_spec (mem_range_iff.mp hy)))
    obtain ⟨x, _, hx⟩ := h y hylt hy
    exact ⟨x, hx⟩

instance IsMapping.surjective_defined :
    𝚺ᴬ₀-Predicate[V] IsMapping.Surjective via IsMapping.surjectiveDef :=
  .mk fun v ↦ by simp [IsMapping.surjectiveDef, surjective_iff_bounded]

instance IsMapping.surjective_definable : 𝚺ᴬ₀-Predicate[V] IsMapping.Surjective :=
  IsMapping.surjective_defined.to_definable

instance IsMapping.surjective_definable' (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Predicate[V] IsMapping.Surjective :=
  IsMapping.surjective_definable.of_zero

@[simp] lemma IsMapping.surjective_empty : IsMapping.Surjective (∅ : V) := by intro y; simp

/-! ### Restriction of mapping -/

lemma restr_exists_unique (f s : V) :
    ∃! g : V, ∀ x, (x ∈ g ↔ x ∈ f ∧ π₁ x ∈ s) := by
  have : 𝚺ᴬ₀-Predicate fun x ↦ x ∈ f ∧ π₁ x ∈ s := by definability
  exact finite_comprehension! this
    ⟨f, fun i ↦ by rintro ⟨hi, _⟩; exact lt_of_mem hi⟩

noncomputable def restr (f s : V) : V := Classical.choose! (restr_exists_unique f s)

scoped macro_rules
  | `($f ↾ $s) => `(restr $f $s)

lemma mem_restr_iff {x f s : V} : x ∈ f ↾ s ↔ x ∈ f ∧ π₁ x ∈ s :=
  Classical.choose!_spec (restr_exists_unique f s) x

@[simp] lemma pair_mem_restr_iff {x y f s : V} :
    ⟪x, y⟫ ∈ f ↾ s ↔ ⟪x, y⟫ ∈ f ∧ x ∈ s := by simp [mem_restr_iff]

@[simp] lemma restr_empty (f : V) : f ↾ ∅ = ∅ := mem_ext (by simp [mem_restr_iff])

@[simp] lemma restr_subset_self (f s : V) : f ↾ s ⊆ f := fun _ hx ↦ (mem_restr_iff.mp hx).1

@[simp] lemma restr_le_self (f s : V) : f ↾ s ≤ f := le_of_subset (by simp)

lemma IsMapping.restr {m : V} (h : IsMapping m) (s : V) : IsMapping (m ↾ s) := h.of_subset (by simp)

lemma domain_restr (f s : V) : domain (f ↾ s) = domain f ∩ s :=
  mem_ext (by simp [mem_domain_iff, pair_mem_restr_iff, exists_and_right, mem_inter_iff])

lemma domain_restr_of_subset_domain {f s : V} (h : s ⊆ domain f) : domain (f ↾ s) = s := by
  simp [domain_restr, inter_comm, inter_eq_self_of_subset h]

def IsMapping.IsFunction (f : V) : Prop := IsMapping f ∧ f ⊆ domain f ×ʰᶠ range f

set_option linter.flexible false in
instance IsMapping.isFunction_defined :
    𝚺ᴬ₀-Predicate[V] IsMapping.IsFunction via IsMapping.isFunctionDef :=
  .mk fun v ↦ by
    simp [IsMapping.isFunctionDef]
    constructor <;> intro h
    · apply And.intro h.1
      intro p hpmem
      have hplt : p < v 0 := lt_of_mem hpmem
      obtain ⟨x, hxlt, y, hylt, rfl⟩ := h.2 p hplt hpmem
      apply mem_product_iff.mpr
      have hxmem : x ∈ domain (v 0) := mem_domain_iff.mpr ⟨y, hpmem⟩
      have hymem : y ∈ range (v 0) := mem_range_iff.mpr ⟨x, hpmem⟩
      exact ⟨x, hxmem, y, hymem, rfl⟩
    · apply And.intro h.1
      intro p hplt hpmem
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_product_iff.mp (h.2 hpmem)
      have hxlt : x < v 0 := lt_of_le_of_lt (le_pair_left x y) hplt
      have hylt : y < v 0 := lt_of_le_of_lt (le_pair_right x y) hplt
      exact ⟨x, hxlt, y, hylt, rfl⟩

instance IsMapping.isFunction_definable : 𝚺ᴬ₀-Predicate[V] IsMapping.IsFunction :=
  IsMapping.isFunction_defined.to_definable

instance IsMapping.isFunction_definable' (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Predicate[V] IsMapping.IsFunction :=
  IsMapping.isFunction_definable.of_zero

/-- Induction on $\Delta_0$ predicates along insertion of an element. -/
@[elab_as_elim]
theorem insert_induction {P : V → Prop} (hP : 𝚺ᴬ₀-Predicate P)
    (hempty : P ∅) (hinsert : ∀ a s, a ∉ s → P s → P (insert a s)) : ∀ s, P s := by
  intro s
  induction s using ISigma0.order_induction
  · exact hP
  case ind s IH =>
    rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
    · exact hempty
    · simpa [insert_remove hx] using
        hinsert x (bitRemove x s) (by simp) (IH _ (bitRemove_lt_of_mem hx))

noncomputable def fstIdx (p : V) : V := π₁ (p - 1)

@[simp] lemma fstIdx_le_self (p : V) : fstIdx p ≤ p :=
  le_trans (by simp [fstIdx]) (show p - 1 ≤ p by simp)

instance fstIdx_defined : 𝚺ᴬ₀-Function₁[V] fstIdx via fstIdxDef := .mk <| by
  intro v; simp [fstIdxDef, fstIdx]

instance fstIdx_definable : 𝚺ᴬ₀-Function₁[V] fstIdx := fstIdx_defined.to_definable

instance fstIdx_definable' (Γ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    Γ-Function₁[V] fstIdx := fstIdx_definable.of_zero

noncomputable def sndIdx (p : V) : V := π₂ (p - 1)

@[simp] lemma sndIdx_le_self (p : V) : sndIdx p ≤ p :=
  le_trans (by simp [sndIdx]) (show p - 1 ≤ p by simp)

instance sndIdx_defined : 𝚺ᴬ₀-Function₁[V] sndIdx via sndIdxDef :=
  .mk fun v ↦ by simp [sndIdxDef, sndIdx]

instance sndIdx_definable : 𝚺ᴬ₀-Function₁[V] sndIdx := sndIdx_defined.to_definable

instance sndIdx_definable' (Γ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    Γ-Function₁[V] sndIdx := sndIdx_definable.of_zero

end ElementaryArithmetic
end FFL.FirstOrder.Arithmetic
