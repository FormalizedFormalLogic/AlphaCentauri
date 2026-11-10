module

public import Foundation.FirstOrder.Arithmetic.EA.Basic
public import Foundation.FirstOrder.Arithmetic.Exponential.Bit

/-!
# Exponentiation and bit-coded finite sets in models of $\mathsf{EA}$

In a model of $\mathsf{EA}$ the $\Delta_0$-definable graph of exponentiation is total, so
`Exp.exp`, the binary length and logarithm, and the coding of finite sets by binary expansion
(`i ∈ a` iff the `i`-th bit of `a` is one) behave as they do in models of $\mathsf{I}\Sigma_1$.
Comprehension holds for $\Delta_0$ predicates on bounded domains. The instances are scoped to
`ElementaryArithmetic`, and are read by Foundation's formulas `expDef`, `bitDef`, `insertDef`,
`bitSubsetDef` and `underDef`.

- [HP98, §I.1(b)]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

section exponential

noncomputable scoped instance : Exp V := ⟨fun a ↦ Classical.choose! (exponential_exists_unique a)⟩

lemma exponential_exp (a : V) : Exponential a (Exp.exp a) :=
  Classical.choose!_spec (exponential_exists_unique a)

lemma exponential_graph {a b : V} : a = Exp.exp b ↔ Exponential b a :=
  Classical.choose!_eq_iff_right _

instance exp_defined_deltaZero : 𝚺ᴬ₀-Function₁[V] Exp.exp via expDef := .mk fun v ↦ by
  simp [expDef, exponential_graph]

instance exp_definable_deltaZero : 𝚺ᴬ₀-Function₁ (Exp.exp : V → V) :=
  exp_defined_deltaZero.to_definable

lemma exp_of_exponential {a b : V} (h : Exponential a b) : Exp.exp a = b :=
  Eq.symm <| exponential_graph.mpr h

lemma exp_inj : Function.Injective (Exp.exp : V → V) := fun a _ H ↦
  (exponential_exp a).inj (exponential_graph.mp H)

@[simp] lemma exp_zero : Exp.exp (0 : V) = 1 := exp_of_exponential (by simp)

@[simp] lemma exp_one : Exp.exp (1 : V) = 2 := exp_of_exponential (by simp)

lemma exp_succ (a : V) : Exp.exp (a + 1) = 2 * Exp.exp a :=
  exp_of_exponential <| Exponential.exponential_succ_mul_two.mpr <| exponential_exp a

lemma exp_even (a : V) : Exp.exp (2 * a) = (Exp.exp a) ^ 2 :=
  exp_of_exponential <| Exponential.exponential_even_sq.mpr <| exponential_exp a

@[simp] lemma lt_exp (a : V) : a < Exp.exp a := (exponential_exp a).lt

@[simp] lemma exp_pos (a : V) : 0 < Exp.exp a := (exponential_exp a).range_pos

@[simp] lemma one_le_exp (a : V) : 1 ≤ Exp.exp a := pos_iff_one_le.mp (by simp)

@[simp] lemma exp_pow2 (a : V) : Pow2 (Exp.exp a) := (exponential_exp a).range_pow2

@[simp] lemma exp_monotone {a b : V} : Exp.exp a < Exp.exp b ↔ a < b :=
  Iff.symm <| Exponential.monotone_iff (exponential_exp a) (exponential_exp b)

@[simp] lemma exp_monotone_le {a b : V} : Exp.exp a ≤ Exp.exp b ↔ a ≤ b :=
  Iff.symm <| Exponential.monotone_le_iff (exponential_exp a) (exponential_exp b)

lemma exp_add (a b : V) : Exp.exp (a + b) = Exp.exp a * Exp.exp b :=
  exp_of_exponential (Exponential.add_mul (exponential_exp a) (exponential_exp b))

@[simp] lemma log_exponential (a : V) : log (Exp.exp a) = a :=
  (exponential_exp a).log_eq_of_exp

lemma exp_log_le_self {a : V} (pos : 0 < a) : Exp.exp (log a) ≤ a := by
  obtain ⟨_, _, H, _⟩ := log_pos pos
  rcases H.uniq (exponential_exp (log a))
  assumption

lemma lt_two_mul_exponential_log {a : V} (pos : 0 < a) : a < 2 * Exp.exp (log a) := by
  obtain ⟨_, _, H, _⟩ := log_pos pos
  rcases H.uniq (exponential_exp (log a))
  assumption

@[simp] lemma length_exponential (a : V) : ‖Exp.exp a‖ = a + 1 := by
  simp [length_of_pos (exp_pos a)]

lemma exp_le_iff_le_log {i a : V} (pos : 0 < a) : Exp.exp i ≤ a ↔ i ≤ log a :=
  ⟨by intro h; simpa using log_monotone h,
    fun h ↦ le_trans (exp_monotone_le.mpr h) (exp_log_le_self pos)⟩

end exponential

section mem

/-- `i ∈ a` states that the `i`-th bit of `a` is one. -/
def Bit (i a : V) : Prop := LenBit (Exp.exp i) a

scoped instance : Membership V V := ⟨fun a i ↦ Bit i a⟩

set_option linter.flexible false in
instance bit_defined : 𝚺ᴬ₀-Relation[V] (· ∈ ·) via bitDef := .mk fun v ↦ by
  simp [bitDef]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨by simp [h.le], h⟩⟩

instance mem_definable : 𝚺ᴬ₀-Relation[V] (· ∈ ·) := bit_defined.to_definable

instance mem_definable' (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Relation[V] (· ∈ ·) := mem_definable.of_zero

instance mem_definable'' (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Relation[V] Membership.mem := by
  simpa using (mem_definable' ℌ).retraction ![1, 0]

lemma mem_iff_bit {i a : V} : i ∈ a ↔ Bit i a := iff_of_eq rfl

lemma exp_le_of_mem {i a : V} (h : i ∈ a) : Exp.exp i ≤ a := LenBit.le h

lemma lt_of_mem {i a : V} (h : i ∈ a) : i < a := lt_of_lt_of_le (lt_exp i) (exp_le_of_mem h)

lemma not_mem_of_lt_exp {i a : V} (h : a < Exp.exp i) : i ∉ a := fun H ↦ by
  have := lt_of_le_of_lt (exp_le_of_mem H) h; simp at this

@[definability]
lemma _root_.FFL.FirstOrder.Bounding.HierarchySymbol.Definable.arithmetic_ball_mem_zero
    {Γ} {k : ℕ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction f) (h : Γᴬ_[0].Definable (fun w ↦ P (w ·.succ) (w 0))) :
    Γᴬ_[0].Definable (fun v ↦ ∀ x ∈ f v, P v x) := by
  have : Γᴬ_[0].Definable (fun v ↦ ∀ x < f v, x ∈ f v → P v x) := by
    apply Bounding.HierarchySymbol.Definable.arithmetic_ball_blt hf
    apply Bounding.HierarchySymbol.Definable.imp
    · exact Bounding.HierarchySymbol.Definable.arithmetic_bounded_comp₂_zero
        (R := (· ∈ ·)) (.var 0) (hf.retraction Fin.succ)
    · exact h
  exact this.of_iff <| by
    intro v; exact ⟨fun h x _ hxv ↦ h x hxv, fun h x hx ↦ h x (lt_of_mem hx) hx⟩

@[definability]
lemma _root_.FFL.FirstOrder.Bounding.HierarchySymbol.Definable.arithmetic_bexs_mem_zero
    {Γ} {k : ℕ} {P : (Fin k → V) → V → Prop} {f : (Fin k → V) → V}
    (hf : DefinableBoundedFunction f) (h : Γᴬ_[0].Definable (fun w ↦ P (w ·.succ) (w 0))) :
    Γᴬ_[0].Definable (fun v ↦ ∃ x ∈ f v, P v x) := by
  have : Γᴬ_[0].Definable (fun v ↦ ∃ x < f v, x ∈ f v ∧ P v x) := by
    apply Bounding.HierarchySymbol.Definable.arithmetic_bexs_blt hf
    apply Bounding.HierarchySymbol.Definable.and
    · exact Bounding.HierarchySymbol.Definable.arithmetic_bounded_comp₂_zero
        (R := (· ∈ ·)) (.var 0) (hf.retraction Fin.succ)
    · exact h
  exact this.of_iff <| by
    intro v; exact ⟨by rintro ⟨x, hx, hxv⟩; exact ⟨x, lt_of_mem hx, hx, hxv⟩,
      by rintro ⟨x, _, hx, hxv⟩; exact ⟨x, hx, hxv⟩⟩

scoped instance : Tarski.Structure.Mem ℒₒᵣ V :=
  ⟨by intro a b; simp [Semiformula.Operator.val, operator_mem_def, bit_defined.iff]⟩

@[simp] lemma eval_ballIn {ξ : Type*} {n : ℕ} {t : ArithmeticSemiterm ξ n}
    {φ : ArithmeticSemiformula ξ (n + 1)} {bv : Fin n → V} {fv : ξ → V} :
    (ballIn t φ).Eval (M := V) bv fv ↔ ∀ x ∈ t.val bv fv, φ.Eval (x :> bv) fv := by
  suffices
    (∀ x < t.val bv fv, x ∈ t.val bv fv → φ.Eval (x :> bv) fv) ↔
    ∀ x ∈ t.val bv fv, φ.Eval (x :> bv) fv by simpa [ballIn]
  constructor
  · intro h x hx; exact h x (lt_of_mem hx) hx
  · intro h x _ hx; exact h x hx

@[simp] lemma eval_bexsIn {ξ : Type*} {n : ℕ} {t : ArithmeticSemiterm ξ n}
    {φ : ArithmeticSemiformula ξ (n + 1)} {bv : Fin n → V} {fv : ξ → V} :
    (bexsIn t φ).Eval (M := V) bv fv ↔ ∃ x ∈ t.val bv fv, φ.Eval (x :> bv) fv := by
  suffices
    (∃ x < t.val bv fv, x ∈ t.val bv fv ∧ φ.Eval (x :> bv) fv) ↔
    ∃ x ∈ t.val bv fv, φ.Eval (x :> bv) fv by simpa [bexsIn]
  constructor
  · rintro ⟨x, _, hx, h⟩; exact ⟨x, hx, h⟩
  · rintro ⟨x, hx, h⟩; exact ⟨x, lt_of_mem hx, hx, h⟩

instance memRel_defined : 𝚺ᴬ₀-Relation₃ (fun r x y : V ↦ ⟪x, y⟫ ∈ r) via memRel :=
  .mk fun v ↦ by simp [memRel]

instance memRel₃_defined : 𝚺ᴬ₀-Relation₄ (fun r x y z : V ↦ ⟪x, y, z⟫ ∈ r) via memRel₃ :=
  .mk fun v ↦ by simp [memRel₃]

@[simp] lemma eval_memRel {x y r : V} : memRelOpr.val ![r, x, y] ↔ ⟪x, y⟫ ∈ r := by
  unfold Semiformula.Operator.val
  simp [memRelOpr]

@[simp] lemma eval_memRel₃ {x y z r : V} : memRel₃Opr.val ![r, x, y, z] ↔ ⟪x, y, z⟫ ∈ r := by
  unfold Semiformula.Operator.val
  simp [memRel₃Opr]

lemma mem_iff_mul_exp_add_exp_add {i a : V} :
    i ∈ a ↔ ∃ k, ∃ r < Exp.exp i, a = k * Exp.exp (i + 1) + Exp.exp i + r := by
  simpa [mem_iff_bit, exp_succ] using! lenbit_iff_add_mul (exp_pow2 i) (a := a)

lemma not_mem_iff_mul_exp_add {i a : V} :
    i ∉ a ↔ ∃ k, ∃ r < Exp.exp i, a = k * Exp.exp (i + 1) + r := by
  simpa [mem_iff_bit, exp_succ] using! not_lenbit_iff_add_mul (exp_pow2 i) (a := a)

end mem

section finiteSet

scoped instance : EmptyCollection V := ⟨0⟩

omit [V↓[ℒₒᵣ] ⊧* 𝗘𝗔] in
lemma emptyset_def : (∅ : V) = 0 := rfl

@[simp] lemma not_mem_empty (i : V) : i ∉ (∅ : V) := by simp [emptyset_def, mem_iff_bit, Bit]

@[simp] lemma not_mem_zero (i : V) : i ∉ (0 : V) := by simp [mem_iff_bit, Bit]

noncomputable scoped instance : Singleton V V := ⟨fun a ↦ Exp.exp a⟩

lemma singleton_def (a : V) : {a} = Exp.exp a := rfl

@[simp] lemma singleton_injective (a b : V) : ({a} : V) = {b} ↔ a = b :=
  ⟨fun h ↦ by simpa [singleton_def] using congr_arg log h, by rintro rfl; rfl⟩

open Classical in
/-- `bitInsert i a` adds `i` to the set `a`. -/
noncomputable def bitInsert (i a : V) : V := if i ∈ a then a else a + Exp.exp i

open Classical in
/-- `bitRemove i a` removes `i` from the set `a`. -/
noncomputable def bitRemove (i a : V) : V := if i ∈ a then a - Exp.exp i else a

noncomputable scoped instance : Insert V V := ⟨bitInsert⟩

lemma insert_eq {i a : V} : insert i a = bitInsert i a := rfl

lemma singleton_eq_insert (i : V) : ({i} : V) = insert i ∅ := by
  simp [singleton_def, insert, bitInsert, emptyset_def]

scoped instance : LawfulSingleton V V where
  insert_empty_eq := fun x ↦ Eq.symm <| singleton_eq_insert x

@[simp] lemma mem_bitInsert_iff {i j a : V} : i ∈ insert j a ↔ i = j ∨ i ∈ a := by
  by_cases h : j ∈ a <;> simp [h, insert_eq, bitInsert]
  · by_cases e : i = j <;> simp [h, e]
  · simpa [exp_inj.eq_iff] using!
      lenbit_add_pow2_iff_of_not_lenbit (exp_pow2 i) (exp_pow2 j) h

@[simp] lemma mem_bitRemove_iff {i j a : V} : i ∈ bitRemove j a ↔ i ≠ j ∧ i ∈ a := by
  by_cases h : j ∈ a
  · simpa [h, bitRemove, exp_inj.eq_iff] using!
      lenbit_sub_pow2_iff_of_lenbit (exp_pow2 i) (exp_pow2 j) h
  · simp only [bitRemove, h, ↓reduceIte, ne_eq, iff_and_self]
    rintro _ rfl; contradiction

lemma not_mem_bitRemove_self (i a : V) : i ∉ bitRemove i a := by simp

lemma insert_graph (b i a : V) :
    b = insert i a ↔ (i ∈ a ∧ b = a) ∨ (i ∉ a ∧ ∃ e ≤ b, e = Exp.exp i ∧ b = a + e) :=
  ⟨by rintro rfl; by_cases hi : i ∈ a <;> simp [hi, insert, bitInsert],
   by by_cases hi : i ∈ a <;> simp only [hi, true_and, not_true_eq_false, false_and,
        or_false, insert, bitInsert, ↓reduceIte, imp_self,
        not_false_eq_true, true_and, false_or, forall_exists_index, and_imp]
      rintro x _ rfl rfl; rfl⟩

instance insert_defined : 𝚺ᴬ₀-Function₂[V] insert via insertDef :=
  .mk fun v ↦ by simp [insertDef, insert_graph, exp_defined_deltaZero.iff]

instance insert_definable : 𝚺ᴬ₀-Function₂[V] insert := insert_defined.to_definable

instance insert_definable' (Γ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    Γ-Function₂[V] insert := insert_definable.of_zero

open Classical in
lemma insert_le_of_le_of_le {i j a b : V} (hij : i ≤ j) (hab : a ≤ b) :
    insert i a ≤ b + Exp.exp j := by
  suffices (if i ∈ a then a else a + Exp.exp i) ≤ b + Exp.exp j by simpa [insert, bitInsert]
  by_cases hi : i ∈ a
  · simpa [hi] using le_trans hab (by simp)
  · simpa [hi] using add_le_add hab (exp_monotone_le.mpr hij)

lemma one_eq_singleton : (1 : V) = {∅} := by
  simp [singleton_eq_insert, insert, bitInsert, emptyset_def]

@[simp] lemma mem_singleton_iff {i j : V} : i ∈ ({j} : V) ↔ i = j := by
  simp [singleton_eq_insert, -insert_empty_eq]

lemma bitRemove_lt_of_mem {i a : V} (h : i ∈ a) : bitRemove i a < a := by
  simp [h, bitRemove, tsub_lt_iff_left (exp_le_of_mem h)]

lemma pos_of_nonempty {i a : V} (h : i ∈ a) : 0 < a := by
  by_contra A
  rcases show a = 0 by simpa using A
  simp_all

@[simp] lemma mem_insert (i a : V) : i ∈ insert i a := by simp

lemma insert_eq_self_of_mem {i a : V} (h : i ∈ a) : insert i a = a := by
  simp [insert_eq, bitInsert, h]

lemma log_mem_of_pos {a : V} (h : 0 < a) : log a ∈ a :=
  mem_iff_mul_exp_add_exp_add.mpr
    ⟨0, a - Exp.exp (log a),
      (tsub_lt_iff_left (exp_log_le_self h)).mpr
        (by rw [← two_mul]; exact lt_two_mul_exponential_log h),
      by simpa using Eq.symm <| add_tsub_self_of_le (exp_log_le_self h)⟩

lemma le_log_of_mem {i a : V} (h : i ∈ a) : i ≤ log a :=
  (exp_le_iff_le_log (pos_of_nonempty h)).mp (exp_le_of_mem h)

lemma succ_mem_iff_mem_div_two {i a : V} : i + 1 ∈ a ↔ i ∈ a / 2 := by
  simp [mem_iff_bit, Bit, LenBit.iff_rem, exp_succ, Arithmetic.div_mul]

lemma lt_length_of_mem {i a : V} (h : i ∈ a) : i < ‖a‖ := by
  simpa [length_of_pos (pos_of_nonempty h), ← le_iff_lt_succ] using le_log_of_mem h

lemma lt_exp_iff {a i : V} : a < Exp.exp i ↔ ∀ j ∈ a, j < i :=
  ⟨fun h j hj ↦ exp_monotone.mp <| lt_of_le_of_lt (exp_le_of_mem hj) h,
   by suffices Exp.exp i ≤ a → ∃ x ∈ a, i ≤ x by contrapose; simpa
      intro h
      have pos : 0 < a := lt_of_lt_of_le (by simp) h
      exact ⟨log a, log_mem_of_pos pos, (exp_le_iff_le_log pos).mp h⟩⟩

scoped instance : HasSubset V := ⟨fun a b ↦ ∀ ⦃i⦄, i ∈ a → i ∈ b⟩

instance bitSubset_defined : 𝚺ᴬ₀-Relation[V] Subset via bitSubsetDef := .mk fun v ↦ by
  simpa [bitSubsetDef, bit_defined.iff]
    using ⟨by intro h x hx; exact h x (lt_of_mem hx) hx, by intro h x _ hx; exact h hx⟩

instance bitSubset_definable : 𝚺ᴬ₀-Relation[V] Subset := bitSubset_defined.to_definable₀

instance bitSubset_definable' (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Relation[V] Subset := bitSubset_defined.to_definable₀

lemma subset_iff {a b : V} : a ⊆ b ↔ (∀ x ∈ a, x ∈ b) := by simp [HasSubset.Subset]

@[refl, simp] lemma subset_refl (a : V) : a ⊆ a := by intro x; simp

@[trans] lemma subset_trans {a b c : V} (hab : a ⊆ b) (hbc : b ⊆ c) : a ⊆ c := by
  intro x hx; exact hbc (hab hx)

lemma mem_exp_add_succ_sub_one (i j : V) : i ∈ Exp.exp (i + j + 1) - 1 := by
  have : Exp.exp (i + j + 1) - 1 =
      (Exp.exp j - 1) * Exp.exp (i + 1) + Exp.exp i + (Exp.exp i - 1) := calc
    Exp.exp (i + j + 1) - 1 = Exp.exp j * Exp.exp (i + 1) - 1 := by
      simp [exp_add, ← mul_assoc, mul_comm]
    _ = Exp.exp j * Exp.exp (i + 1) - Exp.exp (i + 1) + Exp.exp (i + 1) - 1 := by
      rw [sub_add_self_of_le]; exact le_mul_of_pos_left (exp_pos j)
    _ = (Exp.exp j - 1) * Exp.exp (i + 1) + Exp.exp (i + 1) - 1 := by simp [sub_mul]
    _ = (Exp.exp j - 1) * Exp.exp (i + 1) + (Exp.exp i + Exp.exp i) - 1 := by
      simp [← two_mul, ← exp_succ i]
    _ = (Exp.exp j - 1) * Exp.exp (i + 1) + (Exp.exp i + Exp.exp i - 1) := by
      rw [add_tsub_assoc_of_le]; simp [← two_mul, ← pos_iff_one_le]
    _ = (Exp.exp j - 1) * Exp.exp (i + 1) + Exp.exp i + (Exp.exp i - 1) := by
      simp [add_assoc, add_tsub_assoc_of_le]
  exact mem_iff_mul_exp_add_exp_add.mpr
    ⟨Exp.exp j - 1, Exp.exp i - 1, (tsub_lt_iff_left (by simp)).mpr <| by simp, this⟩

/-- `under a` is the set `{0, 1, …, a - 1}`. -/
noncomputable def under (a : V) : V := Exp.exp a - 1

@[simp] lemma le_under (a : V) : a ≤ under a :=
  le_iff_lt_succ.mpr (by
    simp [under, show Exp.exp a - 1 + 1 = Exp.exp a from sub_add_self_of_le (by simp)])

@[simp] lemma mem_under_iff {i j : V} : i ∈ under j ↔ i < j := by
  constructor
  · intro h
    have : Exp.exp i < Exp.exp j := calc
      Exp.exp i ≤ Exp.exp j - 1 := exp_le_of_mem h
      _ < Exp.exp j := pred_lt_self_of_pos (exp_pos j)
    exact exp_monotone.mp this
  · intro lt
    have : j = i + (j - (i + 1)) + 1 := calc
      j = i + (j - i) := by rw [add_tsub_self_of_le (le_of_lt lt)]
      _ = i + (j - i - 1 + 1) := by
        rw [sub_add_self_of_le <| le_tsub_of_add_le_left <| lt_iff_succ_le.mp lt]
      _ = i + (j - (i + 1)) + 1 := by simp [add_assoc, ← Arithmetic.sub_sub]
    rw [this]; exact mem_exp_add_succ_sub_one i _

lemma not_mem_under_self (i : V) : i ∉ under i := by simp

private lemma under_graph (x y : V) : y = under x ↔ y + 1 = Exp.exp x := by
  constructor
  · rintro rfl; simp [under, sub_add_self_of_le]
  · intro h
    have := congr_arg (· - 1) h
    simpa [under] using this

instance under_defined : 𝚺ᴬ₀-Function₁[V] under via underDef :=
  .mk fun v ↦ by simp [underDef, under_graph, exp_defined_deltaZero.iff]

instance under_definable : 𝚺ᴬ₀-Function₁[V] under := under_defined.to_definable

instance under_definable' (Γ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]) :
    Γ-Function₁[V] under := under_definable.of_zero

lemma eq_zero_of_subset_zero {a : V} : a ⊆ 0 → a = 0 := by
  intro h; by_contra A
  have : log a ∈ (0 : V) := h (log_mem_of_pos (pos_iff_ne_zero.mpr A))
  simp_all

lemma subset_div_two {a b : V} : a ⊆ b → a / 2 ⊆ b / 2 := by
  intro ss i hi
  exact succ_mem_iff_mem_div_two.mp <| ss <| succ_mem_iff_mem_div_two.mpr hi

lemma zero_mem_iff {a : V} : 0 ∉ a ↔ 2 ∣ a := by simp [mem_iff_bit, Bit, LenBit]

@[simp] lemma zero_not_mem (a : V) : 0 ∉ 2 * a := by simp [mem_iff_bit, Bit, LenBit]

@[simp] lemma zero_mem_double_add_one (a : V) : 0 ∈ 2 * a + 1 := by
  simp [mem_iff_bit, Bit, LenBit, ← mod_eq_zero_iff_dvd]

@[simp] lemma succ_mem_two_mul_iff {i a : V} : i + 1 ∈ 2 * a ↔ i ∈ a := by
  simp [mem_iff_bit, Bit, LenBit, exp_succ, div_cancel_left]

@[simp] lemma succ_mem_two_mul_succ_iff {i a : V} : i + 1 ∈ 2 * a + 1 ↔ i ∈ a := by
  simp [mem_iff_bit, Bit, LenBit, exp_succ, Arithmetic.div_mul]

private lemma le_of_subset_of_le {c : V} : ∀ b a : V, a ≤ c → a ⊆ b → a ≤ b := by
  intro b
  induction b using sigma0_polynomial_induction
  · definability
  case zero =>
    intro a _ h
    simp [eq_zero_of_subset_zero h]
  case even b _ IH =>
    intro a hac h
    have IH : a / 2 ≤ b := IH _ (le_trans (by simp) hac) (by simpa using subset_div_two h)
    have : 2 * (a / 2) = a :=
      mul_div_self_of_dvd.mpr (zero_mem_iff.mp <| by intro ha; have : 0 ∈ 2 * b := h ha; simp_all)
    simpa [this] using mul_le_mul_left (a := 2) IH
  case odd b IH =>
    intro a hac h
    have IH : a / 2 ≤ b := IH _ (le_trans (by simp) hac)
      (by simpa [div_mul_add' b 2 one_lt_two] using subset_div_two h)
    exact le_trans (le_two_mul_div_two_add_one a) (by simpa using IH)

/-- - [HP98, Theorem I.1.37] -/
lemma le_of_subset {a b : V} (h : a ⊆ b) : a ≤ b := le_of_subset_of_le (c := a) b a le_rfl h

lemma mem_ext {a b : V} (h : ∀ i, i ∈ a ↔ i ∈ b) : a = b :=
  le_antisymm (le_of_subset fun i hi ↦ (h i).mp hi) (le_of_subset fun i hi ↦ (h i).mpr hi)

lemma mem_ext_iff {a b : V} : a = b ↔ ∀ i, i ∈ a ↔ i ∈ b := ⟨by rintro rfl; simp, mem_ext⟩

lemma nonempty_of_pos {a : V} (h : 0 < a) : ∃ i, i ∈ a := ⟨log a, log_mem_of_pos h⟩

lemma eq_empty_or_nonempty (a : V) : a = ∅ ∨ ∃ i, i ∈ a := by
  rcases Arithmetic.zero_le a with (rfl | pos)
  · simp [emptyset_def]
  · exact Or.inr <| nonempty_of_pos pos

lemma nonempty_iff {s : V} : s ≠ ∅ ↔ ∃ x, x ∈ s := by
  rcases eq_empty_or_nonempty s with (rfl | hy)
  · simp
  · simpa [show s ≠ ∅ from by rintro rfl; simp_all]

lemma isempty_iff {s : V} : s = ∅ ↔ ∀ x, x ∉ s := by
  simpa using not_iff_not.mpr (nonempty_iff (s := s))

@[simp] lemma empty_subset (s : V) : ∅ ⊆ s := by intro x; simp

lemma lt_of_lt_log {a b : V} (pos : 0 < b) (h : ∀ i ∈ a, i < log b) : a < b := by
  rcases Arithmetic.zero_le a with (rfl | apos)
  · exact pos
  by_contra A
  exact not_lt_of_ge (log_monotone <| show b ≤ a by simpa using A) (h (log a) (log_mem_of_pos apos))

@[simp] lemma under_inj {i j : V} : under i = under j ↔ i = j := ⟨fun h ↦ by
  by_contra ne
  wlog lt : i < j
  · exact this (Eq.symm h) (Ne.symm ne) (lt_of_le_of_ne (by simpa using lt) (Ne.symm ne))
  have : i ∉ under i := by simp
  have : i ∈ under i := by rw [h]; simp [mem_under_iff, lt]
  contradiction, by rintro rfl; simp⟩

@[simp] lemma under_zero : under (0 : V) = ∅ := mem_ext (by simp [mem_under_iff])

@[simp] lemma under_succ (i : V) : under (i + 1) = insert i (under i) :=
  mem_ext (by simp [mem_under_iff, lt_succ_iff_le, le_iff_eq_or_lt])

lemma insert_remove {i a : V} (h : i ∈ a) : insert i (bitRemove i a) = a := mem_ext <| by
  suffices ∀ j, j = i ∨ j ≠ i ∧ j ∈ a ↔ j ∈ a by simpa
  intro j
  constructor
  · rintro (rfl | ⟨_, hj⟩) <;> assumption
  · intro hj; simp [hj, eq_or_ne j i]

end finiteSet

section comprehension

variable {P : V → Prop}

/-- Comprehension for a $\Delta_0$ predicate on `{0, …, a - 1}`.
- [HP98, Theorem I.1.36] -/
theorem finset_comprehension (hP : 𝚺ᴬ₀.DefinablePred P) (a : V) :
    ∃ s < Exp.exp a, ∀ i < a, i ∈ s ↔ P i := by
  have hs : ∀ i < a, P i → i ∈ under a := fun i hi _ ↦ by simpa [mem_under_iff] using hi
  have : 𝚺ᴬ₀.DefinablePred (fun s : V ↦ ∀ i < a, P i → i ∈ s) := by
    apply Bounding.HierarchySymbol.Definable.arithmetic_ball_blt
    · simp
    apply Bounding.HierarchySymbol.Definable.imp
    · simpa using Bounding.HierarchySymbol.Definable.arithmetic_bounded_comp₁ (by definability)
    · simpa using Bounding.HierarchySymbol.Definable.arithmetic_bounded_comp₂
        (by definability) (by definability)
  obtain ⟨t, ht, t_minimal⟩ := ISigma0.least_number this hs
  have t_le_s : t ≤ under a := not_lt.mp fun lt ↦ t_minimal _ lt hs
  have : ∀ i < a, i ∈ t → P i := by
    intro i _ hit
    by_contra Hi
    exact t_minimal (bitRemove i t) (bitRemove_lt_of_mem hit) fun j hj Hj ↦
      mem_bitRemove_iff.mpr ⟨by rintro rfl; exact Hi Hj, ht j hj Hj⟩
  use t
  and_intros
  · exact lt_of_le_of_lt t_le_s (pred_lt_self_of_pos (by simp))
  · intro i hi
    exact ⟨this i hi, ht i hi⟩

theorem finset_comprehension! (hP : 𝚺ᴬ₀.DefinablePred P) (a : V) :
    ∃! s, s < Exp.exp a ∧ ∀ i < a, i ∈ s ↔ P i := by
  obtain ⟨s, hs, Hs⟩ := finset_comprehension hP a
  apply ExistsUnique.intro s ⟨hs, Hs⟩
  rintro t ⟨ht, Ht⟩
  apply mem_ext
  intro i
  constructor
  · intro hi
    have hin : i < a := exp_monotone.mp (lt_of_le_of_lt (exp_le_of_mem hi) ht)
    exact (Hs i hin).mpr ((Ht i hin).mp hi)
  · intro hi
    have hin : i < a := exp_monotone.mp (lt_of_le_of_lt (exp_le_of_mem hi) hs)
    exact (Ht i hin).mpr ((Hs i hin).mp hi)

theorem finite_comprehension! (hP : 𝚺ᴬ₀.DefinablePred P) (fin : ∃ m, ∀ i, P i → i < m) :
    ∃! s : V, ∀ i, i ∈ s ↔ P i := by
  obtain ⟨m, hm⟩ := fin
  obtain ⟨s, hs, Hs⟩ := finset_comprehension hP m
  have H : ∀ i, i ∈ s ↔ P i := fun i ↦
    ⟨fun h ↦ (Hs i (exp_monotone.mp (lt_of_le_of_lt (exp_le_of_mem h) hs))).mp h,
      fun h ↦ (Hs i (hm i h)).mpr h⟩
  apply ExistsUnique.intro s H
  intro s' H'
  apply mem_ext
  intro i
  simp [H, H']

/-- The set given by `finite_comprehension!` lies below `Exp.exp m` for a bound `m` of `P`. -/
theorem finite_comprehension!_bound {m : V} (hP : 𝚺ᴬ₀.DefinablePred P)
    (hm : ∀ i, P i → i < m) :
    Classical.choose! (finite_comprehension! hP ⟨m, hm⟩) < Exp.exp m :=
  lt_of_lt_log (exp_pos m) fun i himem ↦ (log_exponential m).symm ▸
    hm i ((Classical.choose!_spec (finite_comprehension! hP ⟨m, hm⟩) i).mp himem)

end comprehension

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic
