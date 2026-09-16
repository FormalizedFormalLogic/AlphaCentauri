module

public import Mathlib.SetTheory.Ordinal.Notation
public import Mathlib.SetTheory.Ordinal.Veblen
public import AlphaCentauri.ToMathlib.Ordinal.Rank

/-!
# ε₀-completeness of CNF notations

Mathlib's `Mathlib/SetTheory/Ordinal/Notation.lean` proves that `ONote.repr` is an embedding
`NONote ↪ ε₀` but does not prove surjectivity onto ordinals `< ε₀`. This file supplies that
surjectivity, and transfers the result to any `ℕ`-order obtained by pulling the `NONote` order
back along a bijection. A concrete computable bijection (`natCode`) is constructed from a
structural `Encodable ONote` instance.
-/

@[expose] public section

namespace ONote

open Ordinal ONote IsWellFounded
open scoped Ordinal

/-- Every ordinal `< ε₀` is `repr` of some normal-form `ONote`. -/
theorem exists_NF_repr_eq (o : Ordinal) (hε : o < ε₀) : ∃ x : ONote, x.NF ∧ x.repr = o := by
  induction o using WellFoundedLT.induction with
  | _ o IH =>
    obtain rfl | ho := eq_or_ne o 0
    · exact ⟨0, NF.zero, repr_zero⟩
    · set e := log ω o with he
      have hee : e < o := by
        have h1 : ω ^ e ≤ o := opow_log_le_self ω ho
        have h2 : e ≤ ω ^ e := (isNormal_opow one_lt_omega0).strictMono.le_apply
        rcases lt_or_eq_of_le (h2.trans h1) with h | h
        · exact h
        · exact absurd (epsilon_zero_le_of_omega0_opow_le (h ▸ h1)) hε.not_ge
      obtain ⟨eN, heNF, heRepr⟩ := IH e hee (hee.trans hε)
      set r := o % ω ^ e with hr
      have hre : r < o := mod_opow_log_lt_self ω ho
      obtain ⟨rN, hrNF, hrRepr⟩ := IH r hre (hre.trans hε)
      have hcpos : 0 < o / ω ^ e := div_opow_log_pos ω ho
      have hclt : o / ω ^ e < ω := div_opow_log_lt o one_lt_omega0
      obtain ⟨m, hm⟩ := lt_omega0.1 hclt
      have hmpos : 0 < m := by rw [hm] at hcpos; exact_mod_cast hcpos
      have hωe : ω ^ e ≠ 0 := (opow_pos e omega0_pos).ne'
      refine ⟨oadd eN ⟨m, hmpos⟩ rN, NF.oadd heNF _ (NF.below_of_lt' ?_ hrNF), ?_⟩
      · rw [hrRepr, heRepr]
        exact mod_lt _ hωe
      · have hval : repr (oadd eN ⟨m, hmpos⟩ rN) = ω ^ repr eN * (m : Ordinal) + repr rN := by
          simp [repr]
        rw [hval, heRepr, hrRepr, hr, ← hm]
        exact div_add_mod o (ω ^ e)

/-- `ε₀` is a limit ordinal. -/
private lemma isSuccLimit_epsilon0 : Order.IsSuccLimit ε₀ := by
  have h := isSuccLimit_opow_left isSuccLimit_omega0 (epsilon_pos 0).ne'
  rwa [omega0_opow_epsilon] at h

/-- Every normal-form `ONote` represents an ordinal `< ε₀`. -/
theorem NF.repr_lt_epsilon0 {x : ONote} (h : x.NF) : x.repr < ε₀ := by
  induction x with
  | zero => exact epsilon_pos 0
  | oadd e n a IHe IHa =>
    have hee : e.repr < ε₀ := IHe h.fst
    have hbelow : a.repr < ω ^ e.repr := h.snd'.repr_lt
    have hsucc : Order.succ e.repr < ε₀ := isSuccLimit_epsilon0.succ_lt hee
    have key : (ONote.oadd e n a).repr < ω ^ Order.succ e.repr := by
      rw [opow_succ]
      have h1 : (ONote.oadd e n a).repr = ω ^ e.repr * ((n : ℕ) : Ordinal) + a.repr := by simp
      rw [h1]
      calc ω ^ e.repr * ((n : ℕ) : Ordinal) + a.repr
          < ω ^ e.repr * ((n : ℕ) : Ordinal) + ω ^ e.repr := (add_lt_add_iff_left _).2 hbelow
        _ = ω ^ e.repr * (((n : ℕ) : Ordinal) + 1) := by rw [mul_add, mul_one]
        _ ≤ ω ^ e.repr * ω := by
            gcongr
            rw [← Nat.cast_one, ← Nat.cast_add]
            exact (natCast_lt_omega0 _).le
    exact key.trans (((opow_lt_opow_iff_right one_lt_omega0).2 hsucc).trans_eq
      (omega0_opow_epsilon 0))

/-- The range of `NONote.repr` is exactly the ordinals `< ε₀`. -/
theorem range_NONote_repr : Set.range NONote.repr = Set.Iio ε₀ := by
  ext o
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2.repr_lt_epsilon0
  · intro ho
    obtain ⟨x, hx, hxo⟩ := exists_NF_repr_eq o ho
    exact ⟨⟨x, hx⟩, hxo⟩

/-! ## Transfer to an `ℕ`-order: `ε₀ ≤ orderType` of any pullback of the `NONote` order -/

section Pullback

variable (e : ℕ ≃ NONote)

/-- The `NONote` order pulled back to `ℕ` along a coding `e`. -/
def ltPull (a b : ℕ) : Prop := e a < e b

instance ltPull_wf : IsWellFounded ℕ (ltPull e) :=
  ⟨InvImage.wf e NONote.lt_wf⟩

/-- The `≺`-rank of `n` in the pullback order is the ordinal `NONote.repr (e n)`. -/
lemma rank_ltPull_eq_repr (n : ℕ) : rank (ltPull e) n = NONote.repr (e n) := by
  refine IsWellFounded.induction (ltPull e) n
    (motive := fun k => rank (ltPull e) k = NONote.repr (e k)) ?_
  intro n IH
  refine le_antisymm (rank_le_of_forall (ltPull e) fun m hm => (IH m hm).trans_lt hm) ?_
  by_contra! hlt
  have hlt' : rank (ltPull e) n < ε₀ := hlt.trans (e n).2.repr_lt_epsilon0
  obtain ⟨x, hxNF, hxo⟩ := exists_NF_repr_eq (rank (ltPull e) n) hlt'
  set m₀ := e.symm (@NONote.mk x hxNF) with hm₀
  have he : NONote.repr (e m₀) = rank (ltPull e) n := by
    rw [hm₀, Equiv.apply_symm_apply]; exact hxo
  have hrel : ltPull e m₀ n := by
    change NONote.repr (e m₀) < NONote.repr (e n)
    rw [he]; exact hlt
  have := rank_lt_of_rel hrel
  rw [IH m₀ hrel, he] at this
  exact lt_irrefl _ this

/-- For any coding `e : ℕ ≃ NONote`, the pullback order on `ℕ` has order type at least `ε₀`. -/
theorem epsilon0_le_orderType_ltPull : ε₀ ≤ orderType (ltPull e) := by
  by_contra! hlt
  obtain ⟨x, hxNF, hxo⟩ := exists_NF_repr_eq (orderType (ltPull e)) hlt
  set n₀ := e.symm (@NONote.mk x hxNF) with hn₀
  have he : rank (ltPull e) n₀ = orderType (ltPull e) := by
    rw [rank_ltPull_eq_repr, hn₀, Equiv.apply_symm_apply]; exact hxo
  have hle : Order.succ (rank (ltPull e) n₀) ≤ orderType (ltPull e) :=
    Ordinal.le_iSup (fun n => Order.succ (rank (ltPull e) n)) n₀
  rw [he] at hle
  exact (Order.lt_succ _).not_ge hle

end Pullback

/-! ## A concrete coding `ℕ ≃ NONote` -/

/-- Structural encoding `ONote → ℕ`. -/
def encodeONote : ONote → ℕ
  | ONote.zero => 0
  | ONote.oadd e n a =>
      Nat.pair (encodeONote e) (Nat.pair ((n : ℕ) - 1) (encodeONote a)) + 1

/-- Structural decoding `ℕ → ONote`, a left inverse of `encodeONote`. -/
def decodeONote : ℕ → ONote
  | 0 => ONote.zero
  | (m + 1) =>
      ONote.oadd (decodeONote (Nat.unpair m).1)
        ⟨(Nat.unpair (Nat.unpair m).2).1 + 1, Nat.succ_pos _⟩
        (decodeONote (Nat.unpair (Nat.unpair m).2).2)
  decreasing_by
    · exact Nat.lt_succ_of_le (Nat.unpair_left_le m)
    · exact Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le m))

lemma decodeONote_encodeONote : ∀ x : ONote, decodeONote (encodeONote x) = x
  | ONote.zero => by simp only [encodeONote, decodeONote]
  | ONote.oadd e n a => by
      rw [encodeONote, decodeONote]
      simp only [Nat.unpair_pair, decodeONote_encodeONote e, decodeONote_encodeONote a]
      congr 1
      apply Subtype.ext
      change (n : ℕ) - 1 + 1 = (n : ℕ)
      exact Nat.succ_pred_eq_of_pos n.pos

instance : Encodable ONote :=
  Encodable.ofLeftInverse encodeONote decodeONote decodeONote_encodeONote

instance : Infinite NONote :=
  Infinite.of_injective NONote.ofNat (by
    intro m n h
    simpa [NONote.repr, NONote.ofNat] using congrArg NONote.repr h)

instance : Encodable NONote :=
  inferInstanceAs (Encodable {o : ONote // o.NF})

instance : Denumerable NONote :=
  Denumerable.ofEncodableOfInfinite NONote

/-- A computable coding of `ℕ` by CNF notations, built from the structural `Encodable ONote`. -/
def natCode : ℕ ≃ NONote := (Denumerable.eqv NONote).symm

/-- The pullback order on `ℕ` along `natCode` has order type at least `ε₀`. -/
theorem epsilon0_le_orderType_natCode : ε₀ ≤ orderType (ltPull natCode) :=
  epsilon0_le_orderType_ltPull natCode

end ONote
