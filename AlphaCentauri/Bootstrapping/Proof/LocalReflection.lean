module

public import AlphaCentauri.Bootstrapping.Proof.InductionAxiom
public import AlphaCentauri.Bootstrapping.Proof.Soundness
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Provable
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions
public import Foundation.FirstOrder.Arithmetic.EA.Basic
public import Foundation.FirstOrder.Incompleteness.Consistency
public import Foundation.FirstOrder.Incompleteness.Definability

/-!
# False-block replacements of the axioms and uniform reflection

In a model of $\mathsf{I}\Sigma_1$, the negation of the code of each axiom of $\mathsf{PA}^-$ is a
block of existential quantifiers over a $\Delta_0$ matrix all of whose instances are false.

Every axiom `p` of the internal $\mathsf{I}\Sigma_n$ or $\mathsf{EA}$ has a replacement `q` such
that `p` follows in pure logic from the negation of `q`. For $n \le k$, in a model of
$\mathsf{I}\Sigma^+_{k+1}$, the negation of a replacement is a block of existential quantifiers over
a closed matrix in `IsReadable k 3` all of whose instances are false.

In a model of $\mathsf{I}\Sigma_{k+1}$, a prenex $\Pi_{k+3}$ formula holds of any parameters for
whose numerals the internal $\mathsf{I}\Sigma_n$, for $n \le k$, or the internal $\mathsf{EA}$
proves it. In particular, the internal $\mathsf{I}\Sigma_n$ is consistent.

## References

- [HP98, Corollary I.4.34]
- [Bek05, Theorem 7]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

section PeanoMinusAxiom

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma mem_peanoMinus_Δ₁Class_iff (p : V) :
    p ∈ (𝗣𝗔⁻ : ArithmeticTheory).Δ₁Class ↔ ∃ σ ∈ 𝗣𝗔⁻, p = (⌜σ⌝ : V) := by
  change V ⊧/![p] (Theory.Δ₁.ofList PeanoMinus.finite.toFinset.toList).ch.val ↔ _
  rw [satisfies_ofList_ch]
  simp

section falseBlock

/-- The negation of the code of a universal closure of a $\Delta_0$ formula that is true in `V`
is a block of existential quantifiers whose instances are all false. -/
private lemma isFalseBlock_neg_quote_allClosure {k D m : ℕ} {θ : ArithmeticSemisentence m}
    (hθ : ℬ[<, ℒₒᵣ].Closure θ) (hn : ∀ ψ, θ ≠ ∀¹ ψ)
    (hσ : V↓[ℒₒᵣ] ⊧ (∀¹* θ : ArithmeticSentence)) :
    IsFalseBlock k D (neg ℒₒᵣ (⌜∀¹* θ⌝ : V)) := by
  have hb : IsBounded (⌜∼θ⌝ : V) := (isBounded_quote_iff _).mpr hθ.neg
  refine ⟨m, ⌜∼θ⌝, ?_, ?_, ?_, quote_neg_ne_exs hn, ?_, ?_⟩
  · rw [quote_allClosure_sentence, neg_qqAlls (Sentence.quote_isUFormula θ), quote_neg_sentence]
  · exact Sentence.quote_isSemiformula _
  · exact Semisentence.shift_quote _
  · exact .of_isPrenexAtom (IsPrenexAtMost.of_isBounded hb).isPrenexAtom
  · intro w hw
    have := ReadableTruth.subst_quote_iff (V := V) (k := k) (D := D) (Γ := 𝚺) (s := 0)
      (.of_le (Nat.zero_le k)) ⟨⟨∼θ, hθ.neg⟩⟩ hw
    have e : ((⟨⟨∼θ, hθ.neg⟩⟩ : ℬ[<, ℒₒᵣ].Prenex 𝚺 0 Empty m) : ArithmeticSemisentence m) = ∼θ :=
      rfl
    rw [e] at this
    rw [this]
    simp only [models_iff, Semiformula.eval_allClosure] at hσ
    simpa using hσ _

end falseBlock

section classification

private lemma exists_allClosure_closure_of_peanoMinus {σ : ArithmeticSentence} (h : σ ∈ 𝗣𝗔⁻) :
    ∃ m, ∃ θ : ArithmeticSemisentence m, σ = ∀¹* θ ∧ ℬ[<, ℒₒᵣ].Closure θ ∧ ∀ ψ, θ ≠ ∀¹ ψ := by
  rcases h with ⟨φ, hφ⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  · rcases hφ with _ | _ | _ | @⟨k, f⟩ | @⟨k, r⟩
    all_goals
      first
      | refine ⟨k + k, _, rfl, ?_, ?_⟩
      | refine ⟨3, _, rfl, ?_, ?_⟩
      | refine ⟨2, _, rfl, ?_, ?_⟩
      | refine ⟨1, _, rfl, ?_, ?_⟩
    all_goals first
      | (rw [← Bounding.Hierarchy.zero_iff_bounded (Γ := 𝚺)]
         simp [Semiformula.Operator.operator, Semiformula.Operator.Eq.eq])
      | (intro ψ h; cases h)
  all_goals
    first
    | refine ⟨3, _, rfl, ?_, ?_⟩
    | refine ⟨2, _, rfl, ?_, ?_⟩
    | refine ⟨1, _, rfl, ?_, ?_⟩
    | refine ⟨0, _, rfl, ?_, ?_⟩
  all_goals first
    | (rw [← Bounding.Hierarchy.zero_iff_bounded (Γ := 𝚺)]
       simp [Semiformula.Operator.operator, Semiformula.Operator.Eq.eq,
         Semiformula.Operator.LT.lt, Semiformula.Operator.LE.sentence_eq])
    | (intro ψ h; cases h)

end classification

section peanoMinus

private lemma isFalseBlock_neg_quote_of_mem_peanoMinus {σ : ArithmeticSentence}
    (h : σ ∈ 𝗣𝗔⁻) (k D : ℕ) : IsFalseBlock k D (neg ℒₒᵣ (⌜σ⌝ : V)) := by
  obtain ⟨m, θ, rfl, hθ, hn⟩ := exists_allClosure_closure_of_peanoMinus h
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (s := 1)
  exact isFalseBlock_neg_quote_allClosure hθ hn (Semantics.ModelsSet.models _ h)

lemma isFalseBlock_neg_of_mem_peanoMinus_Δ₁Class {p : V}
    (hp : p ∈ (𝗣𝗔⁻ : ArithmeticTheory).Δ₁Class) (k D : ℕ) : IsFalseBlock k D (neg ℒₒᵣ p) := by
  obtain ⟨σ, hσ, rfl⟩ := (mem_peanoMinus_Δ₁Class_iff p).mp hp
  exact isFalseBlock_neg_quote_of_mem_peanoMinus hσ k D

lemma derivable_of_mem_peanoMinus_Δ₁Class {p : V} (hp : p ∈ (𝗣𝗔⁻ : ArithmeticTheory).Δ₁Class) :
    Derivable (∅ : Theory ℒₒᵣ) (insert (neg ℒₒᵣ p) ({p} : V)) := by
  obtain ⟨σ, -, rfl⟩ := (mem_peanoMinus_Δ₁Class_iff p).mp hp
  have hf : IsFormula ℒₒᵣ (⌜σ⌝ : V) := Sentence.quote_isSemiformula₀ σ
  exact Derivable.em (by simp [hf]) (⌜σ⌝ : V) (by simp) (by simp)

end peanoMinus

end PeanoMinusAxiom

section AxiomReplacement

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

end AxiomReplacement

section LocalReflection

open Arithmetic (substNumerals)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {k n : ℕ} {T : ArithmeticTheory} [T.Δ₁]

/-- Below any code `d` there is a set of false blocks, closed under the shift, that contains the
negation of a replacement of each axiom of `T` below `d`. -/
private lemma exists_falseBlock_set (hT : AdmitsFalseBlockReplacement T V k) (d : V) :
    ∃ a : V, IsFormulaSet ℒₒᵣ a ∧ setShift ℒₒᵣ a = a ∧ (∀ e ∈ a, IsFalseBlock k 3 e) ∧
      ∀ p ≤ d, p ∈ T.Δ₁Class →
        ∃ q, neg ℒₒᵣ q ∈ a ∧ Derivable (∅ : Theory ℒₒᵣ) (insert (neg ℒₒᵣ q) ({p} : V)) := by
  obtain ⟨R, hRdef, hRex, hR⟩ := hT
  obtain ⟨s, hs, hsP⟩ := finset_comprehension₁ (Γ := 𝚺) (P := fun p : V ↦ p ∈ T.Δ₁Class)
    (by definability) (d + 1)
  have hsd : ∀ x ∈ s, x ≤ d ∧ x ∈ T.Δ₁Class := by
    intro x hx
    have hx' : x < d + 1 := exp_monotone.mp (lt_of_le_of_lt (exp_le_of_mem hx) hs)
    exact ⟨lt_succ_iff_le.mp hx', (hsP x hx').mp hx⟩
  obtain ⟨F, hF, rfl, hFR⟩ := sigmaOne_skolem
    (R := fun x y : V ↦ ∃ q, y = neg ℒₒᵣ q ∧ R x q) (by definability)
    (s := s) fun x hx ↦ by
      obtain ⟨q, hq⟩ := hRex x (hsd x hx).2
      exact ⟨_, q, rfl, hq⟩
  have hmem : ∀ e ∈ range F, IsFalseBlock k 3 e := by
    intro e he
    obtain ⟨x, hx⟩ := mem_range_iff.mp he
    obtain ⟨q, rfl, hq⟩ := hFR x e hx
    exact (hR x q hq).2
  use range F
  and_intros
  · intro e he
    exact (hmem e he).isFormula
  · apply mem_ext
    intro y
    rw [mem_setShift_iff]
    exact ⟨fun ⟨x, hx, hy⟩ ↦ by rwa [hy, (hmem x hx).shift_eq], fun hy ↦
      ⟨y, hy, ((hmem y hy).shift_eq).symm⟩⟩
  · exact hmem
  · intro p hp hpT
    obtain ⟨y, hy⟩ := mem_domain_iff.mp ((hsP p (lt_succ_iff_le.mpr hp)).mpr hpT)
    obtain ⟨q, rfl, hq⟩ := hFR p y hy
    use q
    exact ⟨mem_range_iff.mpr ⟨p, hy⟩, (hR p q hq).1⟩

/-- In a model of $\mathsf{I}\Sigma^+_{k+1}$, a prenex $\Pi_{k+3}$ formula holds of
`v` if the internal `T`, each of whose axioms has a replacement by a false block, proves its
instance by the numerals of `v`.
- [HP98, Corollary I.4.34]
- [Bek05, Theorem 7] -/
theorem models_of_provable_substNumerals [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺(k + 1)]
    (hT : AdmitsFalseBlockReplacement T V k) {m : ℕ} {φ : ArithmeticSemisentence m}
    (hφ : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (k + 3) φ) (v : Fin m → V)
    (h : Provable T (substNumerals (⌜φ⌝ : V) v)) : V ⊧/v φ := by
  by_contra hV
  obtain ⟨ψ, hψ, rfl⟩ := Bounding.PrenexHierarchy.pi_succ_iff.mp hφ
  obtain ⟨ρ', hρ', rfl⟩ := Bounding.PrenexHierarchy.sigma_succ_iff.mp hψ
  obtain ⟨ρ, rfl⟩ := hρ'
  rw [Semiformula.eval_all] at hV
  obtain ⟨a, ha⟩ := not_forall.mp hV
  rw [Semiformula.eval_ex, not_exists] at ha
  obtain ⟨d, hd⟩ := provable_substNumerals_of_provable_substNumerals_all (∃¹ ρ.val) h a
  obtain ⟨A, hA, hAs, hAfb, hAax⟩ := exists_falseBlock_set hT d
  refine not_derivable_of_isFalseBlock (E := fstIdx d ∪ A) (k := k) (D := 3) ?_
    (Derivation.derivable_union_of_replacement hA hAs hAax hd.2)
  intro e he
  rcases mem_cup_iff.mp he with he | he
  · rw [hd.1, mem_singleton_iff] at he
    exact he ▸ isFalseBlock_substNumerals_exs le_rfl ρ (a :> v) ha
  · exact hAfb e he

/-- In a model of $\mathsf{I}\Sigma^+_{k+1}$, the internal $\mathsf{I}\Sigma_n$ is consistent for
$n \le k$.
- [HP98, Corollary I.4.34] -/
lemma consistent_ISigma [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺(k + 1)] (hn : n ≤ k) :
    (𝗜𝚺 n).Consistent V := by
  intro h
  let π : ArithmeticSentence := (Bounding.Prenex.falsum : ℬ[<, ℒₒᵣ].Prenex 𝚷 (k + 3) Empty 0).val
  have hπ : Provable 𝗜𝚺n (⌜π⌝ : V) := by
    apply Derivable.toProvable
    apply Derivable.cut (^⊥ : V)
    · apply Derivable.wk (s' := insert (^⊥ : V) ∅) (by simp)
      · exact insert_subset_insert_of_subset _ (by simp)
      · have := h.toDerivable
        rwa [Sentence.quote_falsum] at this
    · exact Derivable.verum (by simp) (by simp)
  have := models_of_provable_substNumerals (admitsFalseBlockReplacement_ISigma hn) (φ := π)
    ⟨_, rfl⟩ (![] : Fin 0 → V) (by rwa [substNumerals_quote_of_isEmpty])
  simpa using (Bounding.Prenex.models_falsum ![]).mp this

end LocalReflection

end FFL.FirstOrder.Arithmetic.Bootstrapping
