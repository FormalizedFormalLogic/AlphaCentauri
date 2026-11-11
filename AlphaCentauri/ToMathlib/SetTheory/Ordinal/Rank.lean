module

public import Mathlib.SetTheory.Ordinal.Rank

/-!
# Bounding the rank of a well-founded relation

For a well-founded relation `r`, `WellFounded.rank r a` is at most `o` as soon as every `b` with
`r b a` has rank below `o`.
-/

@[expose] public section

namespace WellFounded

variable {α : Type*} (r : α → α → Prop) [WellFounded r]

lemma rank_le_of_forall {a : α} {o : Ordinal} (h : ∀ b, r b a → rank r b < o) : rank r a ≤ o := by
  rw [rank_eq]
  exact Ordinal.iSup_le fun b => Order.succ_le_of_lt (h b b.2)

/-- The order type of `r`, the least ordinal above every `rank r a`. -/
noncomputable def orderType : Ordinal := ⨆ a : α, Order.succ (rank r a)

end WellFounded
