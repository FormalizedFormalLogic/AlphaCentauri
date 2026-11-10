module

public import AlphaCentauri.InterpretabilityLogic.MaximalConsistentSet
public import AlphaCentauri.InterpretabilityLogic.Veltman.Extension
public import Mathlib.Data.Set.Finite.List

/-!
# The model on ranked sets

Critical solutions and their ranks, a finite Veltman model satisfying the frame condition of
$\mathsf{W}$ whose worlds are maximal consistent subsets of an adequate set indexed by finite
sequences of ranked labels, and the truth lemma for it, for every extension of $\mathbf{IL}$ by
axioms proving $\mathsf{W}$. For $\mathbf{ILW}$ itself this gives completeness with respect to
finite Veltman models satisfying the frame condition of $\mathsf{W}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

namespace Logic.ofAxioms

variable {α : Type*} {𝔸 : Set (Formula α)} {X : Set (Formula α)} {A B C : Formula α}

lemma rhd_trans (h₁ : X *⊢[ofAxioms 𝔸] A ▷ B) (h₂ : X *⊢[ofAxioms 𝔸] B ▷ C) :
    X *⊢[ofAxioms 𝔸] A ▷ C :=
  Context.of axiomJ2 ⨀ K_intro h₁ h₂

lemma or_rhd (h₁ : X *⊢[ofAxioms 𝔸] A ▷ C) (h₂ : X *⊢[ofAxioms 𝔸] B ▷ C) :
    X *⊢[ofAxioms 𝔸] (A ⋎ B) ▷ C :=
  Context.of axiomJ3 ⨀ K_intro h₁ h₂

end Logic.ofAxioms

variable {α : Type*} [DecidableEq α]

namespace MaximalConsistentSet

open Logic Logic.ofAxioms

variable {L : Logic α} {Φ : Finset (Formula α)} {Γ Δ : MaximalConsistentSet L Φ}
  {Y Z₁ Z₂ Z₁' Z₂' : Finset (Formula α × Formula α)} {p : Formula α × Formula α}
  {C D E F : Formula α}

/-- The pairs `(B, C)` of formulas in `Φ` with `B ▷ C ∈ Γ` and `B ▷ E ∉ Γ`. -/
noncomputable def rhdPairs (Γ : MaximalConsistentSet L Φ) (E : Formula α) :
    Finset (Formula α × Formula α) :=
  (Φ ×ˢ Φ).filter fun p ↦ p.1 ▷ p.2 ∈ Γ ∧ p.1 ▷ E ∉ Γ

lemma rhd_mem_of_mem_rhdPairs (hp : p ∈ Γ.rhdPairs E) : p.1 ▷ p.2 ∈ Γ :=
  (Finset.mem_filter.mp hp).2.1

lemma rhd_not_mem_of_mem_rhdPairs (hp : p ∈ Γ.rhdPairs E) : p.1 ▷ E ∉ Γ :=
  (Finset.mem_filter.mp hp).2.2

/-- `Δ` is an `E`-critical successor of `Γ` containing `C`, with `□∼B ∈ Δ` for `(B, _) ∈ Z₁` and
`B ∉ Δ` for `(B, _) ∈ Z₂`.

- [dJV99, Definition 11]
-/
structure CriticalSolution (E C : Formula α) (Z₁ Z₂ : Finset (Formula α × Formula α))
    (Γ Δ : MaximalConsistentSet L Φ) : Prop extends CriticalSuccessor E Γ Δ where
  mem : C ∈ Δ
  box_neg_mem_of_mem : ∀ p ∈ Z₁, □(∼p.1) ∈ Δ
  not_mem_of_mem : ∀ p ∈ Z₂, p.1 ∉ Δ

lemma CriticalSolution.mono (h : CriticalSolution E C Z₁ Z₂ Γ Δ) (h₁ : Z₁' ⊆ Z₁)
    (h₂ : Z₂' ⊆ Z₂) : CriticalSolution E C Z₁' Z₂' Γ Δ :=
  ⟨h.toCriticalSuccessor, h.mem, fun p hp ↦ h.box_neg_mem_of_mem p (h₁ hp),
    fun p hp ↦ h.not_mem_of_mem p (h₂ hp)⟩

/-- `r` assigns to each pair `(B, C)` in `Y` a number below `|Y|` such that `C` has an `E`-critical
solution with `□∼B'` for the pairs `(B', C')` in `Y` of rank at least that of `(B, C)` and blocking
the antecedents of the pairs of greater rank.

- [dJV99, Theorem 13]
-/
def IsRank (Γ : MaximalConsistentSet L Φ) (E : Formula α) (Y : Finset (Formula α × Formula α))
    (r : Formula α × Formula α → ℕ) : Prop :=
  ∀ p ∈ Y, r p < Y.card ∧
    ∃ Δ, CriticalSolution E p.2 (Y.filter (r p ≤ r ·)) (Y.filter (r p < r ·)) Γ Δ

/-- A rank on `Γ.rhdPairs E`, if there is one. -/
noncomputable def rank (Γ : MaximalConsistentSet L Φ) (E : Formula α) :
    Formula α × Formula α → ℕ :=
  Classical.epsilon (Γ.IsRank E (Γ.rhdPairs E))

section

variable {𝔸 : Set (Formula α)} {Γ : MaximalConsistentSet (ofAxioms 𝔸) Φ}

lemma provable_rhd_or_of_inconsistent (h : (Γ.criticalSet F C ∪ {∼D}) *⊢[ofAxioms 𝔸] ⊥) :
    Γ.literals *⊢[ofAxioms 𝔸] C ▷ (D ⋎ F) := by
  rw [Set.union_singleton] at h;
  have h₁ : ({A | □A ∈ Γ} ∪ (□·) '' {A | □A ∈ Γ}) *⊢[ofAxioms 𝔸]
      C ⋏ □(∼C) 🡒 (Γ.rhdDisj F ⋎ ∼□(∼Γ.rhdDisj F)) ⋎ D := by
    have hD : Γ.criticalSet F C *⊢[ofAxioms 𝔸] D := Context.of Entailment.dne ⨀ Context.deduct h;
    have := Context.deduct <| Context.deduct <| Context.deduct <| Context.deduct hD;
    cl_prover [this];
  have h₂ : Γ.literals *⊢[ofAxioms 𝔸] □(C ⋏ □(∼C) 🡒 (Γ.rhdDisj F ⋎ ◇Γ.rhdDisj F) ⋎ D) := by
    apply Context.weakening _ (box_of_provable h₁);
    rintro _ ⟨A, hA, rfl⟩;
    exact mem_literals hA;
  have h₃ : Γ.literals *⊢[ofAxioms 𝔸] Γ.rhdDisj F ▷ F := by
    apply fdisj_rhd;
    intro G hG;
    exact Context.by_axm <| mem_literals (Finset.mem_filter.mp hG).2;
  apply rhd_trans (Context.of rhd_and_box_neg);
  apply rhd_trans (Context.of axiomJ1 ⨀ h₂);
  apply or_rhd (h₂ := Context.of <| rhd_of_provable or₁);
  apply rhd_trans (Context.of or_dia_rhd);
  exact rhd_trans h₃ (Context.of <| rhd_of_provable or₂);

variable [Adequate Φ]

lemma box_neg_not_mem_of_mem_rhdPairs (hE : IsRhdOperand Φ E) (hp : p ∈ Γ.rhdPairs E) :
    □(∼p.1) ∉ Γ := by
  intro h;
  apply rhd_not_mem_of_mem_rhdPairs hp;
  apply (mem_iff_provable <| Adequate.rhd_mem
    (.of_rhd_left <| mem_of_mem <| rhd_mem_of_mem_rhdPairs hp) hE).mpr;
  have h₁ : ofAxioms 𝔸 ⊢ □(∼p.1) 🡒 p.1 ▷ E := C_trans (box_mono <| by cl_prover) axiomJ1;
  exact Context.of h₁ ⨀ Context.by_axm (mem_literals h);

/-- Either `C` has an `E`-critical solution, or `Γ` proves that `C` interprets the disjunction of
the formulas `◇B` for `(B, _) ∈ Z₁`, the formulas `B` for `(B, _) ∈ Z₂`, and `E`. -/
lemma exists_criticalSolution_or_provable (hE : IsRhdOperand Φ E) (hp : p ∈ Γ.rhdPairs E)
    (hZ₁ : Z₁ ⊆ Γ.rhdPairs E) :
    (∃ Δ, CriticalSolution E p.2 Z₁ Z₂ Γ Δ) ∨
      Γ.literals *⊢[ofAxioms 𝔸]
        p.2 ▷ (((Z₁.image fun q ↦ ◇q.1).disj ⋎ (Z₂.image Prod.fst).disj) ⋎ E) := by
  by_cases hc : (Γ.criticalSet E p.2 ∪
      {∼((Z₁.image fun q ↦ ◇q.1).disj ⋎ (Z₂.image Prod.fst).disj)}) *⊢[ofAxioms 𝔸] ⊥;
  · exact .inr <| provable_rhd_or_of_inconsistent hc;
  have hpΓ := rhd_mem_of_mem_rhdPairs hp;
  have hs : □(∼p.2) ∉ Γ := by
    intro h;
    apply box_neg_not_mem_of_mem_rhdPairs hE hp;
    apply (mem_iff_provable <| Adequate.box_neg_mem <| .of_rhd_left <| mem_of_mem hpΓ).mpr;
    exact Context.of box_neg_of_rhd ⨀ Context.by_axm (mem_literals hpΓ) ⨀
      Context.by_axm (mem_literals h);
  obtain ⟨Δ, hΔ, hCΔ, hX⟩ :=
    exists_criticalSuccessor_of_consistent_union (.of_rhd_right <| mem_of_mem hpΓ) hc hs;
  have hD : ({∼((Z₁.image fun q ↦ ◇q.1).disj ⋎ (Z₂.image Prod.fst).disj)} : Set (Formula α))
      *⊢[ofAxioms 𝔸] ∼((Z₁.image fun q ↦ ◇q.1).disj ⋎ (Z₂.image Prod.fst).disj) :=
    Context.by_axm rfl;
  refine .inl ⟨Δ, .mk hΔ hCΔ ?_ ?_⟩
  · intro q hq;
    have hqΓ := rhd_mem_of_mem_rhdPairs (hZ₁ hq);
    apply mem_of_provable hX (Adequate.box_neg_mem <| .of_rhd_left <| mem_of_mem hqΓ);
    have h₁ : ofAxioms 𝔸 ⊢ ∼□(∼q.1) 🡒 (Z₁.image fun q ↦ ◇q.1).disj :=
      right_Fdisj_intro _ (Finset.mem_image_of_mem (fun q ↦ ◇q.1) hq);
    have h₂ := Context.of (Γ := {∼((Z₁.image fun q ↦ ◇q.1).disj ⋎ (Z₂.image Prod.fst).disj)}) h₁;
    cl_prover [hD, h₂];
  · intro q hq;
    apply not_mem_of_provable_neg hX;
    have h₁ : ofAxioms 𝔸 ⊢ q.1 🡒 (Z₂.image Prod.fst).disj :=
      right_Fdisj_intro _ (Finset.mem_image_of_mem Prod.fst hq);
    have h₂ := Context.of (Γ := {∼((Z₁.image fun q ↦ ◇q.1).disj ⋎ (Z₂.image Prod.fst).disj)}) h₁;
    cl_prover [hD, h₂];

omit [Adequate Φ] in
lemma provable_dia_disj_erase {X : Finset (Formula α × Formula α)} :
    ofAxioms 𝔸 ⊢ (X.image fun q ↦ ◇q.1).disj 🡒 ◇p.1 ⋎ ((X.erase p).image fun q ↦ ◇q.1).disj := by
  apply left_Fdisj_intro;
  intro G hG;
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hG;
  by_cases hqp : q = p;
  · subst hqp;
    exact or₁;
  · exact C_trans (right_Fdisj_intro _ <|
      Finset.mem_image_of_mem (fun q ↦ ◇q.1) <| Finset.mem_erase.mpr ⟨hqp, hq⟩) or₂;

variable (hW : ∀ {A B : Formula α}, ofAxioms 𝔸 ⊢ Axioms.W A B)
include hW

/-- For a nonempty set `Y` of pairs in `Γ.rhdPairs E`, some nonempty `X ⊆ Y` consists of pairs
`(B, C)` such that `C` has an `E`-critical solution with `□∼B'` for all `(B', C') ∈ Y` and blocking
the antecedents of the pairs in `Y \ X`.

- [dJV99, Lemma 12]
-/
lemma exists_criticalSolution (hE : IsRhdOperand Φ E) (hY : Y ⊆ Γ.rhdPairs E)
    (hne : Y.Nonempty) :
    ∃ X ⊆ Y, X.Nonempty ∧ ∀ p ∈ X, ∃ Δ, CriticalSolution E p.2 Y (Y \ X) Γ Δ := by
  by_contra! hc;
  suffices h : ∀ X ⊆ Y, (∀ q ∈ Y \ X, Γ.literals *⊢[ofAxioms 𝔸]
      q.1 ▷ ((X.image fun q ↦ ◇q.1).disj ⋎ E)) → False from
    h Y subset_rfl (by simp);
  intro X;
  induction X using Finset.strongInduction with
  | H X ih =>
    intro hXY hP;
    rcases X.eq_empty_or_nonempty with rfl | hX;
    · obtain ⟨q, hq⟩ := hne;
      have hqΓ := rhd_mem_of_mem_rhdPairs (hY hq);
      have h₁ := hP q (by simpa using hq);
      apply rhd_not_mem_of_mem_rhdPairs (hY hq);
      apply (mem_iff_provable <| Adequate.rhd_mem (.of_rhd_left <| mem_of_mem hqΓ) hE).mpr;
      have h₂ : ofAxioms 𝔸 ⊢ ⊥ ⋎ E 🡒 E := by cl_prover;
      exact Context.of (rhd_mono_right <| by simpa using h₂) ⨀ h₁;
    obtain ⟨p, hp, hbad⟩ := hc X hXY hX;
    obtain ⟨Δ, hΔ⟩ | h₁ := exists_criticalSolution_or_provable (Z₂ := Y \ X) hE (hY (hXY hp)) hY;
    · exact hbad Δ hΔ;
    have h₂ : Γ.literals *⊢[ofAxioms 𝔸]
        (Y.image fun q ↦ ◇q.1).disj ▷ ((X.image fun q ↦ ◇q.1).disj ⋎ E) := by
      apply fdisj_rhd;
      intro G hG;
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hG;
      by_cases hqX : q ∈ X;
      · exact Context.of <| rhd_of_provable <|
          C_trans (right_Fdisj_intro _ <| Finset.mem_image_of_mem (fun q ↦ ◇q.1) hqX) or₁;
      · exact rhd_trans (Context.of axiomJ5) (hP q <| Finset.mem_sdiff.mpr ⟨hq, hqX⟩);
    have h₃ : Γ.literals *⊢[ofAxioms 𝔸]
        ((Y \ X).image Prod.fst).disj ▷ ((X.image fun q ↦ ◇q.1).disj ⋎ E) := by
      apply fdisj_rhd;
      intro G hG;
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hG;
      exact hP q hq;
    have h₄ : Γ.literals *⊢[ofAxioms 𝔸] p.1 ▷ ((X.image fun q ↦ ◇q.1).disj ⋎ E) :=
      rhd_trans (Context.by_axm <| mem_literals <| rhd_mem_of_mem_rhdPairs (hY (hXY hp))) <|
        rhd_trans h₁ <| or_rhd (or_rhd h₂ h₃) (Context.of <| rhd_of_provable or₂);
    have hd : ofAxioms 𝔸 ⊢ ◇p.1 🡒 ∼□(∼p.1) := C_id;
    have he := provable_dia_disj_erase (𝔸 := 𝔸) (X := X) (p := p);
    have h₅ : Γ.literals *⊢[ofAxioms 𝔸] p.1 ▷ (((X.erase p).image fun q ↦ ◇q.1).disj ⋎ E) := by
      have h₆ : ofAxioms 𝔸 ⊢ ((X.image fun q ↦ ◇q.1).disj ⋎ E) ⋏ □(∼p.1) 🡒
          ((X.erase p).image fun q ↦ ◇q.1).disj ⋎ E := by
        cl_prover [hd, he];
      exact Context.of (rhd_mono_right h₆) ⨀ (Context.of hW ⨀ h₄);
    have h₆ : Γ.literals *⊢[ofAxioms 𝔸] ((X.image fun q ↦ ◇q.1).disj ⋎ E) ▷
        (((X.erase p).image fun q ↦ ◇q.1).disj ⋎ E) := by
      have h₇ : ofAxioms 𝔸 ⊢ (X.image fun q ↦ ◇q.1).disj ⋎ E 🡒
          ◇p.1 ⋎ (((X.erase p).image fun q ↦ ◇q.1).disj ⋎ E) := by
        cl_prover [he];
      exact rhd_trans (Context.of <| rhd_of_provable h₇) <|
        or_rhd (rhd_trans (Context.of axiomJ5) h₅) (Context.of rhd_refl);
    apply ih (X.erase p) (Finset.erase_ssubset hp) ((Finset.erase_subset _ _).trans hXY);
    intro q hq;
    by_cases hqp : q = p;
    · subst hqp;
      exact h₅;
    · apply rhd_trans (hP q _) h₆;
      simp only [Finset.mem_sdiff, Finset.mem_erase, not_and] at hq ⊢;
      exact ⟨hq.1, fun h ↦ hq.2 hqp h⟩;

lemma exists_isRank (hE : IsRhdOperand Φ E) :
    ∀ Y ⊆ Γ.rhdPairs E, ∃ r, Γ.IsRank E Y r := by
  intro Y;
  induction Y using Finset.strongInduction with
  | H Y ih =>
    intro hY;
    rcases Y.eq_empty_or_nonempty with rfl | hne;
    · exact ⟨fun _ ↦ 0, by simp [IsRank]⟩
    obtain ⟨X, hXY, hX, hsol⟩ := exists_criticalSolution hW hE hY hne;
    obtain ⟨r, hr⟩ := ih (Y \ X) (Finset.sdiff_ssubset hXY hX) (Finset.sdiff_subset.trans hY);
    refine ⟨fun q ↦ if q ∈ X then 0 else r q + 1, ?_⟩
    intro p hp
    by_cases hpX : p ∈ X
    · obtain ⟨Δ, hΔ⟩ := hsol p hpX
      simp only [hpX, ite_true]
      refine ⟨hne.card_pos, Δ, hΔ.mono (Finset.filter_subset _ _) ?_⟩
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_sdiff] at hq ⊢
      split_ifs at hq with h
      · omega
      · exact ⟨hq.1, h⟩
    · obtain ⟨hlt, Δ, hΔ⟩ := hr p (Finset.mem_sdiff.mpr ⟨hp, hpX⟩)
      simp only [hpX, ite_false]
      refine ⟨?_, Δ, hΔ.mono ?_ ?_⟩
      · have := Finset.card_sdiff_add_card_eq_card hXY
        have := hX.card_pos
        omega
      all_goals
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_sdiff] at hq ⊢
        split_ifs at hq with h
        · omega
        · exact ⟨⟨hq.1, h⟩, by omega⟩

lemma isRank_rank (hE : IsRhdOperand Φ E) : Γ.IsRank E (Γ.rhdPairs E) (Γ.rank E) :=
  Classical.epsilon_spec <| exists_isRank hW hE _ subset_rfl

lemma rank_lt (hE : IsRhdOperand Φ E) (hp : p ∈ Γ.rhdPairs E) :
    Γ.rank E p < (Φ ×ˢ Φ).card :=
  ((isRank_rank hW hE p hp).1).trans_le <| Finset.card_le_card <| Finset.filter_subset _ _

end

end MaximalConsistentSet

namespace Veltman

open MaximalConsistentSet

variable {L : Logic α} {Φ : Finset (Formula α)}

/-- A maximal consistent subset of `Φ` together with a finite sequence of pairs of an antecedent or
consequent of a `▷`-formula in `Φ` and a number at most `|Φ × Φ|`, no longer than the number of
`□`-formulas in the set.

- [dJV99, Theorem 13]
-/
structure RankedSet (L : Logic α) (Φ : Finset (Formula α)) where
  set : MaximalConsistentSet L Φ
  seq : List (Formula α × ℕ)
  isRhdOperand_of_mem_seq : ∀ p ∈ seq, IsRhdOperand Φ p.1
  le_of_mem_seq : ∀ p ∈ seq, p.2 ≤ (Φ ×ˢ Φ).card
  length_seq_le : seq.length ≤ set.prebox.card

namespace RankedSet

variable {x y z w : RankedSet L Φ} {E F : Formula α} {i j k : ℕ}

lemma ext {x y : RankedSet L Φ} (h₁ : x.set = y.set) (h₂ : x.seq = y.seq) : x = y := by
  cases x; cases y; simp_all;

instance [Adequate Φ] : Finite (RankedSet L Φ) := by
  let T : Finset (Formula α × ℕ) := Φ ×ˢ Finset.range ((Φ ×ˢ Φ).card + 1);
  have : Finite {l : List T // l.length ≤ Φ.card} := (List.finite_length_le _ _).to_subtype;
  have hc (Γ : MaximalConsistentSet L Φ) : Γ.prebox.card ≤ Φ.card :=
    Finset.card_le_card_of_injOn (□·) (fun _ hA ↦ mem_of_mem (mem_prebox.mp hA))
      fun _ _ _ _ h ↦ box_inj.mp h;
  have hT (x : RankedSet L Φ) (p) (hp : p ∈ x.seq) : p ∈ T := by
    simp only [T, Finset.mem_product, Finset.mem_range];
    exact ⟨(x.isRhdOperand_of_mem_seq p hp).mem, Nat.lt_succ_of_le (x.le_of_mem_seq p hp)⟩;
  apply Finite.of_injective (β := MaximalConsistentSet L Φ × {l : List T // l.length ≤ Φ.card})
    fun x ↦ (x.set, ⟨x.seq.pmap Subtype.mk (hT x), by
      simpa using x.length_seq_le.trans (hc x.set)⟩);
  intro x y h;
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h;
  apply ext h.1;
  simpa [List.map_pmap] using congrArg (List.map Subtype.val) h.2;

omit [DecidableEq α] in
lemma eq_of_append_singleton_prefix {s l : List (Formula α × ℕ)} {a b : Formula α × ℕ}
    (ha : s ++ [a] <+: l) (hb : s ++ [b] <+: l) : a = b := by
  have h := (List.prefix_of_prefix_length_le ha hb (by simp)).eq_of_length (by simp);
  simpa using h;

/-- `y` extends `x` by the label `(E, k)`: the set of `y` is an `E`-critical successor of the set
of `x` containing `□∼B` for every pair `(B, C)` in `x.set.rhdPairs E` of rank at least `k`, and
not containing `B` if the rank is greater than `k`, or at least `k` and `y` extends `x` by more
than one label.

- [dJV99, Theorem 13]
-/
structure RelWith (x y : RankedSet L Φ) (E : Formula α) (k : ℕ) : Prop where
  append_prefix : x.seq ++ [(E, k)] <+: y.seq
  criticalSuccessor : CriticalSuccessor E x.set y.set
  box_neg_mem : ∀ p ∈ x.set.rhdPairs E, k ≤ x.set.rank E p → □(∼p.1) ∈ y.set
  not_mem : ∀ p ∈ x.set.rhdPairs E, k < x.set.rank E p → p.1 ∉ y.set
  not_mem_of_length_lt : x.seq.length + 1 < y.seq.length →
    ∀ p ∈ x.set.rhdPairs E, k ≤ x.set.rank E p → p.1 ∉ y.set

/-- `y` extends `x` by some label. -/
def Rel (x y : RankedSet L Φ) : Prop := ∃ E k, x.RelWith y E k

lemma Rel.isPrefix (h : x.Rel y) : x.seq <+: y.seq := by
  obtain ⟨E, k, h⟩ := h;
  exact (List.prefix_append _ _).trans h.append_prefix

lemma Rel.length_lt (h : x.Rel y) : x.seq.length < y.seq.length := by
  obtain ⟨E, k, h⟩ := h;
  have := h.append_prefix.length_le;
  simp only [List.length_append, List.length_singleton] at this;
  omega

lemma Rel.successor (h : x.Rel y) : Successor x.set y.set := by
  obtain ⟨E, k, h⟩ := h;
  exact h.criticalSuccessor.toSuccessor

lemma Rel.irrefl : ¬x.Rel x := fun h ↦ h.successor.irrefl

lemma Rel.relWith (h : x.Rel y) (hp : x.seq ++ [(E, k)] <+: y.seq) : x.RelWith y E k := by
  obtain ⟨F, i, h⟩ := h;
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj <| eq_of_append_singleton_prefix hp h.append_prefix;
  exact h

/-- The set `Δ` indexed by the sequence of `x` followed by `(E, k)`. -/
def extend (x : RankedSet L Φ) (E : Formula α) (k : ℕ) (hE : IsRhdOperand Φ E)
    (hk : k ≤ (Φ ×ˢ Φ).card) (Δ : MaximalConsistentSet L Φ) (h : Successor x.set Δ) :
    RankedSet L Φ :=
  ⟨Δ, x.seq ++ [(E, k)], fun p hp ↦ by
      rcases List.mem_append.mp hp with hp | hp;
      · exact x.isRhdOperand_of_mem_seq p hp;
      · obtain rfl := List.mem_singleton.mp hp;
        exact hE,
    fun p hp ↦ by
      rcases List.mem_append.mp hp with hp | hp;
      · exact x.le_of_mem_seq p hp;
      · obtain rfl := List.mem_singleton.mp hp;
        exact hk,
    by simpa using Nat.succ_le_of_lt <| x.length_seq_le.trans_lt <|
      Finset.card_lt_card h.prebox_ssubset⟩

lemma rel_extend {hE : IsRhdOperand Φ E} {hk : k ≤ (Φ ×ˢ Φ).card} {Δ : MaximalConsistentSet L Φ}
    (h : CriticalSuccessor E x.set Δ)
    (h₁ : ∀ p ∈ x.set.rhdPairs E, k ≤ x.set.rank E p → □(∼p.1) ∈ Δ)
    (h₂ : ∀ p ∈ x.set.rhdPairs E, k < x.set.rank E p → p.1 ∉ Δ) :
    x.Rel (x.extend E k hE hk Δ h.toSuccessor) :=
  ⟨E, k, List.prefix_refl _, h, h₁, h₂, fun h ↦ by simp [extend] at h⟩

variable [Entailment.Cl L]

lemma Rel.trans (h₁ : x.Rel y) (h₂ : y.Rel z) : x.Rel z := by
  obtain ⟨E, k, h₁⟩ := h₁
  exact ⟨E, k, h₁.append_prefix.trans h₂.isPrefix,
    h₁.criticalSuccessor.trans_successor h₂.successor,
    fun p hp hk ↦ h₂.successor.box_mem_of_box_mem (h₁.box_neg_mem p hp hk),
    fun p hp hk ↦ h₂.successor.not_mem_of_box_neg_mem (h₁.box_neg_mem p hp hk.le),
    fun _ p hp hk ↦ h₂.successor.not_mem_of_box_neg_mem (h₁.box_neg_mem p hp hk)⟩

end RankedSet

open RankedSet

/-- The model on ranked sets in which `S w x y` holds if `x` and `y` extend `w`, and either `x = y`,
`y` extends `x`, or `x` and `y` extend `w` by labels `(E, i)` and `(E, j)` with `j < i`, or with
`j = i` and `x` extending `w` by exactly one label.

- [dJV99, Theorem 13]
-/
def rankedCountermodel (𝔸 : Set (Formula α)) (Φ : Finset (Formula α))
    [Nonempty (RankedSet (Logic.ofAxioms 𝔸) Φ)] :
    Model (RankedSet (Logic.ofAxioms 𝔸) Φ) α where
  Rel' := RankedSet.Rel
  S' w x y := w.Rel x ∧ w.Rel y ∧ (x = y ∨ x.Rel y ∨ ∃ E i j, w.seq ++ [(E, i)] <+: x.seq ∧
    w.seq ++ [(E, j)] <+: y.seq ∧ (j < i ∨ j = i ∧ x.seq.length = w.seq.length + 1))
  Val' x a := #a ∈ x.set

namespace rankedCountermodel

open Model Model.World

variable {𝔸 : Set (Formula α)} [Nonempty (RankedSet (Logic.ofAxioms 𝔸) Φ)]

instance : IsTrans _ (rankedCountermodel 𝔸 Φ).Rel :=
  ⟨fun _ _ _ h₁ h₂ ↦ Rel.trans (L := Logic.ofAxioms 𝔸) h₁ h₂⟩

instance : Std.Irrefl (rankedCountermodel 𝔸 Φ).Rel :=
  ⟨fun _ h ↦ Rel.irrefl (L := Logic.ofAxioms 𝔸) h⟩

instance [Adequate Φ] : (rankedCountermodel 𝔸 Φ).IsIL where
  rel_of_s_left h := h.1
  rel_of_s_right h := h.2.1
  s_refl h := ⟨h, h, .inl rfl⟩
  s_trans {w x y z} h₁ h₂ := by
    obtain ⟨hwx, hwy, h₁⟩ := h₁
    obtain ⟨-, hwz, h₂⟩ := h₂
    refine ⟨hwx, hwz, ?_⟩
    rcases h₁ with rfl | hxy | ⟨E, i, j, hx, hy, hij⟩
    · exact h₂
    · rcases h₂ with rfl | hyz | ⟨F, j', k, hy, hz, hjk⟩
      · exact .inr <| .inl hxy
      · exact .inr <| .inl <| hxy.trans hyz
      · obtain ⟨E, i, hx⟩ := hwx
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj <|
          eq_of_append_singleton_prefix (hx.append_prefix.trans hxy.isPrefix) hy
        have h₁ := hx.append_prefix.length_le
        have h₂ := hxy.length_lt
        simp only [List.length_append, List.length_singleton] at h₁
        exact .inr <| .inr ⟨E, i, k, hx.append_prefix, hz, by omega⟩
    · refine .inr <| .inr ?_
      rcases h₂ with rfl | hyz | ⟨F, j', k, hy', hz, hjk⟩
      · exact ⟨E, i, j, hx, hy, hij⟩
      · exact ⟨E, i, j, hx, hy.trans hyz.isPrefix, hij⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj <| eq_of_append_singleton_prefix hy hy'
        exact ⟨E, i, k, hx, hz, by omega⟩
  s_of_rel h₁ h₂ := ⟨h₁, h₁.trans h₂, .inr <| .inl h₂⟩

instance [Adequate Φ] : (rankedCountermodel 𝔸 Φ).HasW := HasW.of_finite <| by
  intro w x y hxy hyx;
  obtain ⟨-, hwx, h⟩ := hyx;
  rcases h with rfl | hyx | ⟨E, i, j, hy, hx, hij⟩;
  · exact Rel.irrefl (L := Logic.ofAxioms 𝔸) hxy;
  · exact Rel.irrefl (L := Logic.ofAxioms 𝔸) <| hxy.trans hyx;
  · obtain ⟨-, rfl⟩ := Prod.mk.inj <|
      eq_of_append_singleton_prefix hy (hx.trans (Rel.isPrefix (L := Logic.ofAxioms 𝔸) hxy));
    have h₁ := hx.length_le;
    have h₂ := Rel.length_lt (L := Logic.ofAxioms 𝔸) hxy;
    simp only [List.length_append, List.length_singleton] at h₁;
    omega;

variable [Adequate Φ] (hW : ∀ {A B : Formula α}, Logic.ofAxioms 𝔸 ⊢ Axioms.W A B)
include hW

lemma exists_rel_of_mem_rhdPairs {x : (rankedCountermodel 𝔸 Φ).World} {E : Formula α}
    {p : Formula α × Formula α} (hE : IsRhdOperand Φ E) (hp : p ∈ x.set.rhdPairs E) :
    ∃ y, RankedSet.Rel x y ∧ y.seq = x.seq ++ [(E, x.set.rank E p)] ∧ p.2 ∈ y.set := by
  obtain ⟨-, Δ, hΔ⟩ := isRank_rank hW hE p hp;
  refine ⟨x.extend E (x.set.rank E p) hE (rank_lt hW hE hp).le Δ hΔ.toSuccessor, ?_, rfl, hΔ.mem⟩
  exact x.rel_extend hΔ.toCriticalSuccessor
    (fun q hq hk ↦ hΔ.box_neg_mem_of_mem q (Finset.mem_filter.mpr ⟨hq, hk⟩))
    (fun q hq hk ↦ hΔ.not_mem_of_mem q (Finset.mem_filter.mpr ⟨hq, hk⟩))

/-- - [dJV99, Theorem 13] -/
lemma truthlemma {x : (rankedCountermodel 𝔸 Φ).World} {A : Formula α} (hA : A ∈ Φ) :
    x ⊩ A ↔ A ∈ x.set := by
  induction A generalizing x with
  | atom a => rfl;
  | falsum => exact ⟨False.elim, fun h ↦ bot_not_mem h⟩;
  | imp A B ihA ihB =>
    have hA' := Adequate.imp_left hA;
    have hB' := Adequate.imp_right hA;
    rw [imp_mem_iff hA hA' hB', ← ihA hA', ← ihB hB'];
    rfl;
  | box A ih =>
    have hA' := Adequate.box hA;
    constructor;
    · intro h;
      by_contra hn;
      obtain ⟨Δ, hΔ, hc⟩ := exists_successor_of_box_not_mem hA hn;
      have hcrit := hΔ.criticalSuccessor_bot Logic.ofAxioms.rhd_bot;
      have hr {p} (hp : p ∈ x.set.rhdPairs ⊥) : x.set.rank ⊥ p < (Φ ×ˢ Φ).card :=
        rank_lt hW .bot hp;
      have hxy := x.rel_extend (k := (Φ ×ˢ Φ).card) (hE := .bot) (hk := le_rfl) hcrit
        (fun p hp hk ↦ absurd (hr hp) (by omega)) (fun p hp hk ↦ absurd (hr hp) (by omega));
      exact not_mem_of_provable_neg hc (Context.by_axm rfl) <| (ih hA').mp <| h _ hxy;
    · intro h y Rxy;
      exact (ih hA').mpr <| Rxy.successor.mem_of_box_mem h;
  | rhd B C ihB ihC =>
    have hB := Adequate.rhd_left hA;
    have hC := Adequate.rhd_right hA;
    have hB' : IsRhdOperand Φ B := .of_rhd_left hA;
    have hC' : IsRhdOperand Φ C := .of_rhd_right hA;
    constructor;
    · intro h;
      by_contra hn;
      have hp : (B, B) ∈ x.set.rhdPairs C := Finset.mem_filter.mpr ⟨by simp [hB],
        (mem_iff_provable (Adequate.rhd_mem hB' hB')).mpr <|
          Context.of Logic.ofAxioms.rhd_refl, hn⟩;
      obtain ⟨y, hxy, hy, hBy⟩ := exists_rel_of_mem_rhdPairs hW hC' hp;
      obtain ⟨v, hS, hv⟩ := h y hxy <| (ihB hB).mpr hBy;
      have hy' : x.seq ++ [(C, x.set.rank C (B, B))] <+: y.seq := hy ▸ List.prefix_refl _;
      have hlabel : ∃ j, x.seq ++ [(C, j)] <+: v.seq := by
        rcases hS.2.2 with rfl | hyv | ⟨E, i, j, hyE, hv, -⟩
        · exact ⟨_, hy'⟩
        · exact ⟨_, hy'.trans hyv.isPrefix⟩
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj <| eq_of_append_singleton_prefix hy' hyE
          exact ⟨j, hv⟩
      obtain ⟨j, hj⟩ := hlabel;
      have hCC : C ▷ C ∈ x.set :=
        (mem_iff_provable (Adequate.rhd_mem hC' hC')).mpr <| Context.of Logic.ofAxioms.rhd_refl;
      exact (hS.2.1.relWith hj).criticalSuccessor.not_mem hCC <| (ihC hC).mp hv;
    · intro h u Rxu hu;
      replace hu := (ihB hB).mp hu;
      obtain ⟨E, k, hxu⟩ := Rxu;
      have hE : IsRhdOperand Φ E :=
        u.isRhdOperand_of_mem_seq (E, k) <| hxu.append_prefix.subset (by simp);
      have hp : (B, C) ∈ x.set.rhdPairs E := Finset.mem_filter.mpr
        ⟨by simp [hB, hC], h, fun h' ↦ hxu.criticalSuccessor.not_mem h' hu⟩;
      obtain ⟨v, hxv, hv, hCv⟩ := exists_rel_of_mem_rhdPairs hW hE hp;
      refine ⟨v, ⟨⟨E, k, hxu⟩, hxv, .inr <| .inr ⟨E, k, x.set.rank E (B, C), hxu.append_prefix,
        hv ▸ List.prefix_refl _, ?_⟩⟩, (ihC hC).mpr hCv⟩
      have hl := hxu.append_prefix.length_le
      simp only [List.length_append, List.length_singleton] at hl
      rcases lt_trichotomy (x.set.rank E (B, C)) k with hlt | rfl | hlt
      · exact .inl hlt
      · by_contra hn
        exact hxu.not_mem_of_length_lt (by simp at hn; omega) _ hp le_rfl hu
      · exact (hxu.not_mem _ hp hlt hu).elim

end rankedCountermodel

end Veltman

/-! ### Completeness -/

namespace Logic.ofAxioms

open Veltman Veltman.Model.World MaximalConsistentSet

variable {𝔸 : Set (Formula α)} {Φ : Finset (Formula α)} {A : Formula α}

instance [Entailment.Consistent (ofAxioms 𝔸)] : Nonempty (RankedSet (ofAxioms 𝔸) Φ) := by
  obtain ⟨Γ, -⟩ := exists_consistent_union (Φ := Φ) (L := ofAxioms 𝔸) (X := ∅) <| by
    intro h;
    exact Entailment.Consistent.not_inconsistent (𝓢 := ofAxioms 𝔸) fun _ ↦
      efq ⨀ Context.emptyPrf h;
  exact ⟨⟨Γ, [], by simp, by simp, by simp⟩⟩

/-- If an extension `ofAxioms 𝔸` of $\mathbf{IL}$ proving $\mathsf{W}$ does not prove `A`, then `A`
fails at some world of the ranked countermodel over the adequate closure of `{A}`.

- [dJV99, Theorem 13]
-/
lemma not_models_rankedCountermodel [Entailment.Consistent (ofAxioms 𝔸)]
    (hW : ∀ {A B : Formula α}, ofAxioms 𝔸 ⊢ Axioms.W A B) (h : ofAxioms 𝔸 ⊬ A) :
    ¬rankedCountermodel 𝔸 (adequateClosure {A}) ⊧ A := by
  intro hM;
  have hX : ({∼A} : Set (Formula α)) *⊬[ofAxioms 𝔸] ⊥ := by
    intro h₁;
    apply h;
    have h₂ : ofAxioms 𝔸 ⊢ ∼A 🡒 ⊥ := Context.emptyPrf <| Context.deduct <| by simpa using h₁;
    cl_prover [h₂];
  obtain ⟨Γ, hΓ⟩ := exists_consistent_union (Φ := adequateClosure {A}) hX;
  have hA : A ∈ adequateClosure {A} := adequateClosure.subset (by simp);
  exact not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
    (rankedCountermodel.truthlemma hW hA).mp <| hM ⟨Γ, [], by simp, by simp, by simp⟩

end Logic.ofAxioms

namespace Logic.ILW

open Veltman

variable {α : Type} {A : Formula α}

/-- - [dJV99, Theorem 13] -/
theorem complete
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsIL] → [M.HasW] → M ⊧ A) :
    𝐈𝐋𝐖 ⊢ A := by
  classical
  by_contra hA;
  exact Logic.ofAxioms.not_models_rankedCountermodel (fun {_ _} ↦ ILW.axiomW) hA <|
    h (rankedCountermodel _ (adequateClosure {A}))

end Logic.ILW

end FFL.InterpretabilityLogic

end
