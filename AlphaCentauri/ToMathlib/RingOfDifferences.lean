module

public import Mathlib.Algebra.Order.Ring.Cone
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# The ring of differences of an ordered commutative semiring

For a linearly ordered commutative semiring `M` with `CanonicallyOrderedAdd`, `RingOfDifferences M`
is the ring of formal differences `a - b` of elements of `M`. It is a linearly ordered commutative
ring in which `M` embeds as the non-negative elements.
-/

@[expose] public section

universe u

/-- The ring of formal differences `a - b` of elements of an ordered commutative semiring `M`. -/
def RingOfDifferences (M : Type u) [CommSemiring M] [LinearOrder M] [IsStrictOrderedRing M]
    [CanonicallyOrderedAdd M] : Type u :=
  Quotient (⟨fun x y : M × M ↦ x.1 + y.2 = y.1 + x.2, ⟨fun _ ↦ rfl, fun h ↦ h.symm,
    fun h₁ h₂ ↦ by linear_combination h₁ + h₂⟩⟩ : Setoid (M × M))

namespace RingOfDifferences

variable {M : Type u} [CommSemiring M] [LinearOrder M] [IsStrictOrderedRing M]
  [CanonicallyOrderedAdd M]

/-- The class of `(a, b)`, that is, `a - b`. -/
def mk (a b : M) : RingOfDifferences M := Quotient.mk _ (a, b)

lemma mk_eq_mk {a b c d : M} : mk a b = mk c d ↔ a + d = c + b := Quotient.eq

@[elab_as_elim]
lemma ind {motive : RingOfDifferences M → Prop} (h : ∀ a b, motive (mk a b))
    (x : RingOfDifferences M) : motive x :=
  Quotient.ind (fun ⟨a, b⟩ ↦ h a b) x

instance : Zero (RingOfDifferences M) := ⟨mk 0 0⟩

instance : One (RingOfDifferences M) := ⟨mk 1 0⟩

instance : Add (RingOfDifferences M) :=
  ⟨Quotient.map₂ (fun x y ↦ (x.1 + y.1, x.2 + y.2)) fun _ _ hx _ _ hy ↦ by
    change _ + _ = _ + _ at hx hy ⊢
    linear_combination hx + hy⟩

instance : Neg (RingOfDifferences M) :=
  ⟨Quotient.map (fun x ↦ (x.2, x.1)) fun _ _ hx ↦ by
    change _ + _ = _ + _ at hx ⊢
    linear_combination hx.symm⟩

instance : Mul (RingOfDifferences M) :=
  ⟨Quotient.map₂ (fun x y ↦ (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1))
    fun x x' hx y y' hy ↦ by
      change _ + _ = _ + _ at hx hy ⊢
      linear_combination y.1 * hx - y.2 * hx + x'.1 * hy - x'.2 * hy⟩

lemma mk_add (a b c d : M) : mk a b + mk c d = mk (a + c) (b + d) := rfl

lemma mk_mul (a b c d : M) : mk a b * mk c d = mk (a * c + b * d) (a * d + b * c) := rfl

lemma mk_neg (a b : M) : -mk a b = mk b a := rfl

lemma zero_def : (0 : RingOfDifferences M) = mk 0 0 := rfl

lemma one_def : (1 : RingOfDifferences M) = mk 1 0 := rfl

local macro "diff_ring" : tactic =>
  `(tactic| (simp only [zero_def, one_def, mk_add, mk_mul, mk_neg, mk_eq_mk]; ring))

instance : CommRing (RingOfDifferences M) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  mul := (· * ·)
  one := 1
  sub a b := a + -b
  nsmul := nsmulRec
  npow := npowRec
  zsmul := zsmulRec
  add_assoc x y z := by
    induction x using ind; induction y using ind; induction z using ind; diff_ring
  zero_add x := by induction x using ind; diff_ring
  add_zero x := by induction x using ind; diff_ring
  add_comm x y := by induction x using ind; induction y using ind; diff_ring
  neg_add_cancel x := by induction x using ind; diff_ring
  mul_assoc x y z := by
    induction x using ind; induction y using ind; induction z using ind; diff_ring
  one_mul x := by induction x using ind; diff_ring
  mul_one x := by induction x using ind; diff_ring
  zero_mul x := by induction x using ind; diff_ring
  mul_zero x := by induction x using ind; diff_ring
  left_distrib x y z := by
    induction x using ind; induction y using ind; induction z using ind; diff_ring
  right_distrib x y z := by
    induction x using ind; induction y using ind; induction z using ind; diff_ring
  mul_comm x y := by induction x using ind; induction y using ind; diff_ring

/-- The embedding `M → RingOfDifferences M`, `a ↦ a - 0`. -/
def of : M →+* RingOfDifferences M where
  toFun a := mk a 0
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by change mk (a + b) 0 = mk a 0 + mk b 0; diff_ring
  map_mul' a b := by change mk (a * b) 0 = mk a 0 * mk b 0; diff_ring

lemma of_def (a : M) : of a = mk a 0 := rfl

lemma mk_eq_sub (a b : M) : mk a b = of a - of b := by
  simp only [of_def, sub_eq_add_neg]; diff_ring

lemma of_injective : Function.Injective (of : M →+* RingOfDifferences M) := fun a b h ↦ by
  simpa [of_def, mk_eq_mk] using h

@[simp] lemma of_inj {a b : M} : of a = of b ↔ a = b := of_injective.eq_iff

lemma exists_eq_sub (x : RingOfDifferences M) : ∃ a b : M, x = of a - of b := by
  induction x using ind with
  | h a b =>
    use a, b
    exact mk_eq_sub a b

/-- The cone of non-negative elements: the image of `M`. -/
def cone : RingCone (RingOfDifferences M) where
  carrier := Set.range of
  add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add of a b⟩
  zero_mem' := ⟨0, map_zero of⟩
  mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, map_mul of a b⟩
  one_mem' := ⟨1, map_one of⟩
  eq_zero_of_mem_of_neg_mem' := by
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    simp only [of_def, mk_neg, mk_eq_mk, zero_add] at hb
    obtain rfl := (add_eq_zero.1 hb).2
    exact map_zero of

instance : HasMemOrNegMem (cone (M := M)) where
  mem_or_neg_mem x := by
    induction x using ind with
    | h a b =>
    rcases le_total a b with h | h
    · obtain ⟨c, rfl⟩ := exists_add_of_le h
      exact Or.inr ⟨c, by simp only [of_def, mk_neg, mk_eq_mk]; ring⟩
    · obtain ⟨c, rfl⟩ := exists_add_of_le h
      exact Or.inl ⟨c, by simp only [of_def, mk_eq_mk]; ring⟩

noncomputable instance : LinearOrder (RingOfDifferences M) :=
  letI := Classical.decPred (· ∈ cone (M := M))
  LinearOrder.mkOfAddGroupCone cone

lemma le_iff {x y : RingOfDifferences M} : x ≤ y ↔ y - x ∈ cone := Iff.rfl

lemma nonneg_iff {x : RingOfDifferences M} : 0 ≤ x ↔ ∃ a, of a = x := by
  rw [le_iff, sub_zero]
  exact Iff.rfl

@[simp] lemma of_nonneg (a : M) : 0 ≤ of a := nonneg_iff.2 ⟨a, rfl⟩

@[simp] lemma of_le_of {a b : M} : of a ≤ of b ↔ a ≤ b := by
  rw [le_iff, ← mk_eq_sub, le_iff_exists_add']
  change (∃ c, mk c 0 = mk b a) ↔ _
  simp [mk_eq_mk, eq_comm]

@[simp] lemma of_lt_of {a b : M} : of a < of b ↔ a < b := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, of_le_of, of_le_of]

instance : IsOrderedRing (RingOfDifferences M) := IsOrderedRing.mkOfCone cone

instance : Nontrivial (RingOfDifferences M) :=
  ⟨⟨0, 1, fun h ↦ zero_ne_one (α := M) <| of_injective <|
    (map_zero of).trans (h.trans (map_one of).symm)⟩⟩

instance : IsStrictOrderedRing (RingOfDifferences M) :=
  .of_mul_pos fun x y hx hy ↦ by
    obtain ⟨a, rfl⟩ := nonneg_iff.1 hx.le
    obtain ⟨b, rfl⟩ := nonneg_iff.1 hy.le
    rw [← map_zero of, of_lt_of] at hx hy
    rw [← map_mul, ← map_zero of, of_lt_of]
    exact mul_pos hx hy

lemma one_le_of_pos (h : ∀ x : M, 0 < x → 1 ≤ x) {x : RingOfDifferences M} (hx : 0 < x) :
    1 ≤ x := by
  obtain ⟨a, rfl⟩ := nonneg_iff.1 hx.le
  rw [← map_zero of, of_lt_of] at hx
  rw [← map_one of, of_le_of]
  exact h a hx

/-- A positive part of a difference. -/
noncomputable def posPart (x : RingOfDifferences M) : M := (exists_eq_sub x).choose

/-- A negative part of a difference. -/
noncomputable def negPart (x : RingOfDifferences M) : M := (exists_eq_sub x).choose_spec.choose

lemma posPart_sub_negPart (x : RingOfDifferences M) : of (posPart x) - of (negPart x) = x :=
  (exists_eq_sub x).choose_spec.choose_spec.symm

/-- Every difference of absolute value below `B` is a difference of two elements below a fixed
`b : M`. -/
lemma exists_forall_abs_lt_exists_sub (B : RingOfDifferences M) :
    ∃ b : M, ∀ y, |y| < B → ∃ p q : M, of p - of q = y ∧ p < b ∧ q < b := by
  obtain ⟨b, hb⟩ := nonneg_iff.1 (add_nonneg (abs_nonneg B) zero_le_one)
  use b
  intro y hy
  replace hy : |y| < of b := hb ▸ hy.trans_le ((le_abs_self B).trans (by simp))
  have hb : 0 < b := of_lt_of.1 <| by simpa using (abs_nonneg y).trans_lt hy
  rcases le_total 0 y with h | h
  · obtain ⟨p, rfl⟩ := nonneg_iff.1 h
    rw [abs_of_nonneg h, of_lt_of] at hy
    use p, 0
    exact ⟨by simp, hy, hb⟩
  · obtain ⟨q, hq⟩ := nonneg_iff.1 (neg_nonneg.2 h)
    rw [abs_of_nonpos h, ← hq, of_lt_of] at hy
    use 0, q
    exact ⟨by simp [hq], hb, hy⟩

end RingOfDifferences
