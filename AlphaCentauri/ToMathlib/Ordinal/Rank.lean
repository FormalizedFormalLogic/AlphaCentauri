module

public import Mathlib.SetTheory.Ordinal.Rank

/-!
# Order type of a well-founded relation

For a well-founded relation `r`, `WellFounded.orderType r` is its order type: the least
ordinal above every `WellFounded.rank r a`.
-/

@[expose] public section

namespace WellFounded

variable {α : Type*} (r : α → α → Prop) [WellFounded r]

lemma rank_le_of_forall {a : α} {o : Ordinal} (h : ∀ b, r b a → rank r b < o) : rank r a ≤ o := by
  rw [rank_eq]
  exact Ordinal.iSup_le fun b => Order.succ_le_of_lt (h b b.2)

/-- The order type of `r`, the least ordinal above every `rank r a`. -/
noncomputable def orderType : Ordinal := ⨆ a : α, Order.succ (rank r a)

lemma orderType_le_of_forall {o : Ordinal} (h : ∀ a, rank r a < o) : orderType r ≤ o :=
  Ordinal.iSup_le fun a => Order.succ_le_of_lt (h a)

end WellFounded
