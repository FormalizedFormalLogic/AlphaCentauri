module

public import AlphaCentauri.ToMathlib.SetTheory.Ordinal.Notation.Epsilon0

/-!
# A concrete coding of Cantor normal forms by natural numbers

A structural `Encodable ONote` instance, enumerating the normal forms in increasing order of their
code, gives a bijection `natCode : ℕ ≃ NONote`.
-/

@[expose] public section

namespace ONote

open Ordinal ONote WellFounded
open scoped Ordinal

/-! ## A concrete coding `ℕ ≃ NONote` -/

/-- Structural encoding `ONote → ℕ`. -/
def encodeONote : ONote → ℕ
  | ONote.zero => 0
  | ONote.oadd e n a =>
      Nat.pair (encodeONote e) (Nat.pair ((n : ℕ) - 1) (encodeONote a)) + 1

/-- Structural decoding `ℕ → ONote`. -/
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

/-- A coding of `ℕ` by normal-form notations, in increasing order of the structural code. -/
noncomputable def natCode : ℕ ≃ NONote :=
  letI : DecidablePred (· ∈ Set.range (Encodable.encode : NONote → ℕ)) :=
    Encodable.decidableRangeEncode NONote
  letI : Infinite (Set.range (Encodable.encode : NONote → ℕ)) :=
    Infinite.of_injective _ (Equiv.ofInjective _ Encodable.encode_injective).injective
  (Nat.Subtype.orderIsoOfNat (Set.range (Encodable.encode : NONote → ℕ))).toEquiv.trans
    (Encodable.equivRangeEncode NONote).symm

theorem epsilon0_le_orderType_natCode : ε₀ ≤ orderType (ltPull natCode) :=
  epsilon0_le_orderType_ltPull natCode

end ONote
