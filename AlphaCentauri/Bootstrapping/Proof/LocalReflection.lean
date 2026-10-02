module

public import AlphaCentauri.Bootstrapping.Proof.AxiomReplacement
public import AlphaCentauri.Bootstrapping.Proof.ReadableSoundness
public import AlphaCentauri.ToFoundation.Provable

/-!
# Local reflection in a model of $\mathsf{I}\Sigma_{k+1}$

In a model of $\mathsf{I}\Sigma_{k+1}$, a prenex $\Pi_{k+3}$ sentence that the internal
$\mathsf{I}\Sigma_n$, for $n \le k$, proves, holds.

## References

- [HP98, Corollary I.4.34]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open Arithmetic (numeral numeral_semiterm substNumeral)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {k n : ℕ}

/-- For $n \le k$, below any code `d` there is a set of false blocks, closed under the shift, that
contains the negation of a replacement of each axiom of $\mathsf{I}\Sigma_n$ below `d`. -/
theorem exists_falseBlock_set [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺(k + 1)] (hn : n ≤ k) (d : V) :
    ∃ a : V, IsFormulaSet ℒₒᵣ a ∧ setShift ℒₒᵣ a = a ∧ (∀ e ∈ a, IsFalseBlock k 3 e) ∧
      ∀ p ≤ d, p ∈ (𝗜𝚺 n).Δ₁Class →
        ∃ q, neg ℒₒᵣ q ∈ a ∧ Derivable (∅ : Theory ℒₒᵣ) (insert (neg ℒₒᵣ q) ({p} : V)) := by
  obtain ⟨s, hs, hsP⟩ := finset_comprehension₁ (Γ := 𝚺) (P := fun p : V ↦ p ∈ (𝗜𝚺 n).Δ₁Class)
    (by definability) (d + 1)
  have hsd : ∀ x ∈ s, x ≤ d ∧ x ∈ (𝗜𝚺 n).Δ₁Class := by
    intro x hx
    have hx' : x < d + 1 := exp_monotone.mp (lt_of_le_of_lt (exp_le_of_mem hx) hs)
    exact ⟨lt_succ_iff_le.mp hx', (hsP x hx').mp hx⟩
  obtain ⟨F, hF, rfl, hFR⟩ := sigmaOne_skolem
    (R := fun x y : V ↦ ∃ q, y = neg ℒₒᵣ q ∧ IsAxiomReplacement n x q) (by definability)
    (s := s) fun x hx ↦ by
      obtain ⟨q, hq⟩ := exists_isAxiomReplacement (n := n) (hsd x hx).2
      exact ⟨_, q, rfl, hq⟩
  have hmem : ∀ e ∈ range F, IsFalseBlock k 3 e := by
    intro e he
    obtain ⟨x, hx⟩ := mem_range_iff.mp he
    obtain ⟨q, rfl, hq⟩ := hFR x e hx
    exact hq.isFalseBlock hn
  refine ⟨range F, fun e he ↦ (hmem e he).isFormula, ?_, hmem, ?_⟩
  · apply mem_ext
    intro y
    rw [mem_setShift_iff]
    exact ⟨fun ⟨x, hx, hy⟩ ↦ by rwa [hy, (hmem x hx).shift_eq], fun hy ↦
      ⟨y, hy, ((hmem y hy).shift_eq).symm⟩⟩
  · intro p hp hpT
    obtain ⟨y, hy⟩ := mem_domain_iff.mp ((hsP p (lt_succ_iff_le.mpr hp)).mpr hpT)
    obtain ⟨q, rfl, hq⟩ := hFR p y hy
    exact ⟨q, mem_range_iff.mpr ⟨p, hy⟩, hq.1⟩

private lemma not_readableTruth_subst_subst_qVec (ρ : ℬ[<, ℒₒᵣ].Prenex 𝚷 (k + 1) Empty 2) (a : V)
    (h : ∀ b : V, ¬V ⊧/![b, a] ρ.val) {w : V} (hw : IsSemitermVec ℒₒᵣ 1 0 w) :
    ¬ReadableTruth k 3 (subst ℒₒᵣ w (subst ℒₒᵣ (qVec ℒₒᵣ (?[numeral a] : V)) ⌜ρ.val⌝)) := by
  intro hT
  have ha : IsSemitermVec ℒₒᵣ 1 0 (?[numeral a] : V) := by simp
  have hr : IsSemiformula ℒₒᵣ (1 + 1) (⌜ρ.val⌝ : V) := by
    simpa [one_add_one_eq_two] using Sentence.quote_isSemiformula (V := V) ρ.val
  obtain ⟨w₀, w', rfl, hw₀, hw'⟩ := IsSemitermVec.exists_cons (V := V) (m := 0) (w := w)
    (by simpa using hw)
  obtain rfl : w' = 0 := by simpa using hw'.lh
  have hu : IsSemitermVec ℒₒᵣ 2 0 (w₀ ∷ (?[numeral a] : V)) := by
    simpa [one_add_one_eq_two] using IsSemitermVec.cons_iff.mpr ⟨hw₀, ha⟩
  rw [show (w₀ ∷ (0 : V)) = ?[w₀] from rfl, ← substs1, substs1_subst_qVec ha hr hw₀,
    ReadableTruth.subst_quote_iff (Γ := 𝚷) (s := k + 1) (.inr ⟨rfl, rfl⟩) ρ (n := 2)
      (by simpa using hu)] at hT
  apply h (termVal 0 w₀)
  convert hT using 2
  funext i
  match i with
  | 0 => simp
  | 1 => simp

/-- The instance by the numeral of `a` of a code `∃y ρ(x, y)`, with `ρ` a prenex $\Pi_{k+1}$
formula, is a false block when `ρ(a, b)` fails for all `b`. -/
lemma isFalseBlock_substNumeral_exs (ρ : ℬ[<, ℒₒᵣ].Prenex 𝚷 (k + 1) Empty 2) (a : V)
    (h : ∀ b : V, ¬V ⊧/![b, a] ρ.val) :
    IsFalseBlock k 3 (substNumeral (⌜∃¹ ρ.val⌝ : V) a) := by
  have hr : IsSemiformula ℒₒᵣ 2 (⌜ρ.val⌝ : V) := Sentence.quote_isSemiformula ρ.val
  have hw : IsSemitermVec ℒₒᵣ 2 1 (qVec ℒₒᵣ (?[numeral a] : V)) := by
    simpa [one_add_one_eq_two] using
      (show IsSemitermVec ℒₒᵣ 1 0 (?[numeral a] : V) by simp).qVec
  have hne : ∀ p : V, subst ℒₒᵣ (qVec ℒₒᵣ (?[numeral a] : V)) ⌜ρ.val⌝ ≠ ^∃ p := by
    intro p
    rw [ρ.val_piInv, Sentence.quote_all, substs_all (Sentence.quote_isUFormula _)]
    simp [qqAll, qqExs]
  have e : substNumeral (⌜∃¹ ρ.val⌝ : V) a =
      qqExss (subst ℒₒᵣ (qVec ℒₒᵣ (?[numeral a] : V)) ⌜ρ.val⌝) 1 := by
    rw [substNumeral, Sentence.quote_ex, substs_ex hr.isUFormula, ← zero_add (1 : V), qqExss_succ,
      qqExss_zero]
  have hs : shift ℒₒᵣ (subst ℒₒᵣ (qVec ℒₒᵣ (?[numeral a] : V)) ⌜ρ.val⌝) =
      subst ℒₒᵣ (qVec ℒₒᵣ (?[numeral a] : V)) ⌜ρ.val⌝ := by
    rw [shift_substs hr hw, Semisentence.shift_quote]
    congr 1
    simp [qVec]
  rw [e]
  exact ⟨1, _, rfl, hr.subst hw, hs,
    hne, .subst hw hr (Or.inr <| Or.inr <| (isPrenexHierarchy_quote_iff ρ.val).mpr ⟨ρ, rfl⟩),
    fun _ hw' ↦ not_readableTruth_subst_subst_qVec ρ a h hw'⟩

/-- In a model of $\mathsf{I}\Sigma^+_{k+1}$, a prenex $\Pi_{k+3}$ sentence that
$\mathsf{I}\Sigma_n$ proves internally, for $1 \le k$ and $n \le k$, holds.
- [HP98, Corollary I.4.34] -/
theorem models_of_provable_prenexPi [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺(k + 1)] (hk : 1 ≤ k) (hn : n ≤ k)
    {π : ArithmeticSentence} (hπ : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (k + 3) π)
    (h : Provable 𝗜𝚺n (⌜π⌝ : V)) : V↓[ℒₒᵣ] ⊧ π := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺2 := mod_IBroadSigma_of_le (s₁ := 2) (s₂ := k + 1) (by omega)
  by_contra hV
  obtain ⟨ψ, hψ, rfl⟩ := Bounding.PrenexHierarchy.pi_succ_iff.mp hπ
  obtain ⟨ρ', hρ', rfl⟩ := Bounding.PrenexHierarchy.sigma_succ_iff.mp hψ
  obtain ⟨ρ, rfl⟩ := hρ'
  rw [models_iff, Semiformula.eval_all] at hV
  obtain ⟨a, ha⟩ := not_forall.mp hV
  rw [Semiformula.eval_ex, not_exists] at ha
  have hp : Provable 𝗜𝚺n (substNumeral (⌜∃¹ ρ.val⌝ : V) a) :=
    provable_substNumeral_of_provable_quote_all (∃¹ ρ.val) h a
  obtain ⟨d, hd⟩ := hp
  obtain ⟨A, hA, hAs, hAfb, hAax⟩ := exists_falseBlock_set hn d
  refine not_derivable_of_isFalseBlock (E := fstIdx d ∪ A) (k := k) (D := 3) ?_
    (Derivation.derivable_union_of_replacement hA hAs hAax hd.2)
  intro e he
  rcases mem_cup_iff.mp he with he | he
  · rw [hd.1, mem_singleton_iff] at he
    exact he ▸ isFalseBlock_substNumeral_exs ρ a ha
  · exact hAfb e he

end FFL.FirstOrder.Arithmetic.Bootstrapping
