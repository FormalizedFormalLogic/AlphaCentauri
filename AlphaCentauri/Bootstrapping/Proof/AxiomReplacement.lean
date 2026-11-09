module

public import AlphaCentauri.Bootstrapping.Proof.InductionAxiom
public import AlphaCentauri.Bootstrapping.Proof.PeanoMinusAxiom
public import AlphaCentauri.ToFoundation.Provable
public import Foundation.FirstOrder.Arithmetic.EA.Basic

/-!
# Replacing the axioms of $\mathsf{I}\Sigma_n$ and $\mathsf{EA}$ by false blocks

Every axiom `p` of the internal $\mathsf{I}\Sigma_n$ or $\mathsf{EA}$ has a replacement `q` such
that `p` follows in pure logic from the negation of `q`. For $n \le k$, in a model of
$\mathsf{I}\Sigma^+_{k+1}$, the negation of a replacement is a block of existential quantifiers over
a closed matrix in `IsReadable k 3` all of whose instances are false.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open Arithmetic (numeral substNumerals)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {k D : ℕ}

/-- The instance by the numerals of `v` of the code of `∃y ρ(y, x⃗)`, with `ρ` a prenex
$\Pi_{s+1}$ formula and $s \le k$, is a false block when `ρ(b, v)` fails for every `b`. -/
lemma isFalseBlock_substNumerals_exs {s m : ℕ} (hs : s ≤ k)
    (ρ : ℬ[<, ℒₒᵣ].Prenex 𝚷 (s + 1) Empty (m + 1)) (v : Fin m → V)
    (h : ∀ b : V, ¬V ⊧/(b :> v) ρ.val) :
    IsFalseBlock k D (substNumerals (⌜∃¹ ρ.val⌝ : V) v) := by
  set w : V := matrixToVec fun i ↦ numeral (v i)
  have hw : IsSemitermVec ℒₒᵣ (m : V) 0 w :=
    SemitermVec.isSemitermVec (V := V) (L := ℒₒᵣ) (k := m) (n := 0)
      fun i ↦ Arithmetic.typedNumeral (v i)
  have hr : IsSemiformula ℒₒᵣ (m + 1 : V) (⌜ρ.val⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) ρ.val
  have hq : IsSemitermVec ℒₒᵣ (m + 1 : V) 1 (qVec ℒₒᵣ w) := by simpa using hw.qVec
  have hlevel : IsAtomLevel k 𝚷 (s + 1) := by
    rcases hs.lt_or_eq with hs | rfl
    · exact .inl hs
    · exact .inr ⟨rfl, rfl⟩
  have hshift : termShiftVec ℒₒᵣ (m : V) w = w := by
    apply nth_ext' (m : V) (len_termShiftVec hw.isUTerm) hw.lh
    intro i hi
    obtain ⟨j, rfl⟩ := eq_nat_of_lt_nat hi
    have hj : j < m := by exact_mod_cast hi
    have e := matrixToVec_nth (fun i : Fin m ↦ numeral (v i)) ⟨j, hj⟩
    rw [nth_termShiftVec hw.isUTerm hi, e, Arithmetic.numeral_shift]
  use 1, subst ℒₒᵣ (qVec ℒₒᵣ w) ⌜ρ.val⌝
  and_intros
  · rw [substNumerals, Sentence.quote_ex, substs_ex hr.isUFormula, ← zero_add (1 : V),
      qqExss_succ, qqExss_zero]
  · exact hr.subst hq
  · rw [shift_substs hr hq, Semisentence.shift_quote, termShift_qVec hw, hshift]
  · intro p
    rw [ρ.val_piInv, Sentence.quote_all, substs_all (Sentence.quote_isUFormula _)]
    simp [qqAll, qqExs]
  · exact .subst hq hr <| .of_isPrenexAtom
      ⟨𝚷, s + 1, hlevel, (isPrenexHierarchy_quote_iff ρ.val).mpr ⟨ρ, rfl⟩⟩
  · intro u hu hT
    obtain ⟨u₀, u', rfl, hu₀, hu'⟩ := IsSemitermVec.exists_cons (V := V) (m := 0) (w := u)
      (by simpa using hu)
    obtain rfl : u' = 0 := by simpa using hu'.lh
    rw [show (u₀ ∷ (0 : V)) = ?[u₀] from rfl, ← substs1, substs1_subst_qVec hw hr hu₀,
      ReadableTruth.subst_quote_iff hlevel ρ (n := m + 1)
        (by simpa using IsSemitermVec.cons_iff.mpr ⟨hu₀, hw⟩)] at hT
    apply h (termVal 0 u₀)
    convert hT using 2
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simp [w]

/-- `q` is the replacement of the axiom `p` of `𝗜𝚺 n`: an axiom of $\mathsf{PA}^-$ is its own
replacement, and an induction axiom is replaced by the prenex form of the induction axiom of the
matrix it is built from. -/
def IsAxiomReplacement (n : ℕ) (p q : V) : Prop :=
  Derivable (∅ : Theory ℒₒᵣ) (insert (neg ℒₒᵣ q) ({p} : V)) ∧
    ((p ∈ (𝗣𝗔⁻ : ArithmeticTheory).Δ₁Class ∧ q = p) ∨
      ∃ m ≤ p, ∃ Z ≤ p, IsInductionMatrix n m Z ∧ q = prenexInductionAxiom m Z)

instance IsAxiomReplacement.definable (n : ℕ) :
    𝚺ᴬ₁-Relation (IsAxiomReplacement n : V → V → Prop) := by
  unfold IsAxiomReplacement
  definability

theorem exists_isAxiomReplacement {n : ℕ} {p : V} (hp : p ∈ (𝗜𝚺n).Δ₁Class) :
    ∃ q, IsAxiomReplacement n p q := by
  rcases InductionOnPrenexHierarchy.mem_Δ₁Class_iff.mp hp with h | h
  · exact ⟨p, derivable_of_mem_peanoMinus_Δ₁Class h, Or.inl ⟨h, rfl⟩⟩
  · obtain ⟨m, hm, Z, hZ, hM, hd⟩ := exists_derivable_prenexInductionAxiom h
    exact ⟨_, hd, Or.inr ⟨m, hm, Z, hZ, hM, rfl⟩⟩

theorem IsAxiomReplacement.isFalseBlock {n k : ℕ} [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺(k + 1)] (hn : n ≤ k)
    {p q : V} (h : IsAxiomReplacement n p q) : IsFalseBlock k 3 (neg ℒₒᵣ q) := by
  rcases h.2 with ⟨hp, rfl⟩ | ⟨m, -, Z, -, hM, rfl⟩
  · exact isFalseBlock_neg_of_mem_peanoMinus_Δ₁Class hp k 3
  · exact hM.isFalseBlock_neg_prenexInductionAxiom hn

private lemma isFalseBlock_neg_quote_expAxiom : IsFalseBlock k D (neg ℒₒᵣ (⌜expAxiom⌝ : V)) := by
  let E : ArithmeticSemisentence 2 :=
    (Rew.subst ![#1, #0] : Rew ℒₒᵣ Empty 2 Empty 2) ▹
      (exponentialDef.val : ArithmeticSemisentence 2)
  have hE : ℬ[<, ℒₒᵣ].Closure (∼E) := by
    rw [← Bounding.Hierarchy.zero_iff_bounded (Γ := 𝚺)]
    simp [E]
  let ρ : ℬ[<, ℒₒᵣ].Prenex 𝚷 1 Empty 1 := (⟨⟨∼E, hE⟩⟩ : ℬ[<, ℒₒᵣ].Prenex 𝚺 0 Empty 2).pi
  have hρ : ρ.val = ∀¹ ∼E := Bounding.Prenex.val_pi
  have e : ∼expAxiom = ∃¹ ρ.val := by
    rw [hρ]
    simp [expAxiom, E]
  have h := isFalseBlock_substNumerals_exs (k := k) (D := D) (Nat.zero_le k) ρ ![] fun (b : V) ↦ by
    obtain ⟨y, hy⟩ := ElementaryArithmetic.exponential_total b
    rw [hρ]
    simpa [E] using ⟨y, hy⟩
  rwa [substNumerals_quote_of_isEmpty, ← e, quote_neg_sentence] at h

/-- Every axiom `p` of the internal `T` has a replacement `q`, chosen by a $\Sigma_1$ relation, such
that `p` follows in pure logic from the negation of `q` and the negation of `q` is a false block. -/
def AdmitsFalseBlockReplacement (T : ArithmeticTheory) [T.Δ₁] (V : Type*) [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : ℕ) : Prop :=
  ∃ R : V → V → Prop, (𝚺ᴬ₁-Relation R) ∧ (∀ p ∈ T.Δ₁Class, ∃ q, R p q) ∧
    ∀ p q, R p q →
      Derivable (∅ : Theory ℒₒᵣ) (insert (neg ℒₒᵣ q) ({p} : V)) ∧ IsFalseBlock k 3 (neg ℒₒᵣ q)

lemma admitsFalseBlockReplacement_ISigma {n : ℕ} [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺(k + 1)] (hn : n ≤ k) :
    AdmitsFalseBlockReplacement (𝗜𝚺 n) V k := by
  use IsAxiomReplacement n
  and_intros
  · infer_instance
  · intro p hp
    exact exists_isAxiomReplacement hp
  · intro p q h
    exact ⟨h.1, h.isFalseBlock hn⟩

lemma admitsFalseBlockReplacement_ElementaryArithmetic [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺(k + 1)] :
    AdmitsFalseBlockReplacement 𝗘𝗔 V k := by
  use fun p q ↦ IsAxiomReplacement 0 p q ∨ (p = ⌜expAxiom⌝ ∧ q = p)
  and_intros
  · definability
  · intro p hp
    rcases Theory.Δ₁Class.mem_union.mp hp with hp | hp
    · obtain ⟨q, hq⟩ := exists_isAxiomReplacement hp
      use q
      exact .inl hq
    · use p
      right
      simpa [Theory.Δ₁Class, Sentence.quote_eq_encode, numeral_eq_natCast] using hp
  · rintro p q (h | ⟨rfl, rfl⟩)
    · exact ⟨h.1, h.isFalseBlock (Nat.zero_le k)⟩
    · have hf : IsFormula ℒₒᵣ (⌜expAxiom⌝ : V) := Sentence.quote_isSemiformula₀ expAxiom
      exact ⟨Derivable.em (by simp [hf]) (⌜expAxiom⌝ : V) (by simp) (by simp),
        isFalseBlock_neg_quote_expAxiom⟩

end FFL.FirstOrder.Arithmetic.Bootstrapping
