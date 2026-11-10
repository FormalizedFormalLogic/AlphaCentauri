module

public import AlphaCentauri.InterpretabilityLogic.Veltman.IndexedSetModel
public import AlphaCentauri.InterpretabilityLogic.Veltman.Extension

/-!
# The model on branches of indexed sets

$\mathbf{ILP}$-adequate sets, a finite tree-shaped Veltman model whose worlds are branches of
indexed sets, and its truth lemma for every extension of $\mathbf{IL}$ by axioms proving
$\mathbf{P}$. For $\mathbf{ILP}$ itself this gives completeness with respect to finite Veltman
models satisfying the frame condition of $\mathbf{P}$ (de Jongh–Veltman).
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula MaximalConsistentSet

variable {α : Type*} [DecidableEq α]

/-! ### $\mathbf{ILP}$-adequate sets -/

/-- `Φ` is adequate and contains `□(A ▷ B)` for each `A ▷ B ∈ Φ`.

- [dJV90, Definition 5.1]
-/
class ILPAdequate (Φ : Finset (Formula α)) : Prop extends Adequate Φ where
  box_rhd_mem {A B : Formula α} : A ▷ B ∈ Φ → □(A ▷ B) ∈ Φ

/-- `Φ` together with `□A` for every `A ∈ Φ`. -/
def boxClosure (Φ : Finset (Formula α)) : Finset (Formula α) := Φ ∪ Φ.image (□·)

namespace boxClosure

variable {Φ : Finset (Formula α)} {A B : Formula α}

lemma subset : Φ ⊆ boxClosure Φ := Finset.subset_union_left

private lemma mem_iff : A ∈ boxClosure Φ ↔ A ∈ Φ ∨ ∃ B ∈ Φ, □B = A := by
  simp [boxClosure];

private lemma rhd_mem (h : A ▷ B ∈ boxClosure Φ) : A ▷ B ∈ Φ := by
  rcases mem_iff.mp h with h | ⟨_, _, h⟩;
  · exact h;
  · simp at h;

private lemma isRhdOperand (h : IsRhdOperand (boxClosure Φ) A) : IsRhdOperand Φ A := by
  obtain ⟨B, h | h⟩ := h;
  · exact .of_rhd_left (rhd_mem h);
  · exact .of_rhd_right (rhd_mem h);

instance [Adequate Φ] : ILPAdequate (boxClosure Φ) where
  imp_left h := by
    rcases mem_iff.mp h with h | ⟨_, _, h⟩;
    · exact subset <| Adequate.imp_left h;
    · simp at h;
  imp_right h := by
    rcases mem_iff.mp h with h | ⟨_, _, h⟩;
    · exact subset <| Adequate.imp_right h;
    · simp at h;
  box h := by
    rcases mem_iff.mp h with h | ⟨_, h₁, h⟩;
    · exact subset <| Adequate.box h;
    · obtain rfl := box_inj.mp h;
      exact subset h₁;
  rhd_left h := subset <| Adequate.rhd_left (rhd_mem h)
  rhd_right h := subset <| Adequate.rhd_right (rhd_mem h)
  bot_rhd_bot := subset Adequate.bot_rhd_bot
  rhd_mem hA hB := subset <| Adequate.rhd_mem (isRhdOperand hA) (isRhdOperand hB)
  box_neg_mem hA := subset <| Adequate.box_neg_mem (isRhdOperand hA)
  box_rhd_mem h := mem_iff.mpr <| .inr ⟨_, rhd_mem h, rfl⟩

end boxClosure

namespace Veltman

variable {L : Logic α} {Φ : Finset (Formula α)}

namespace IndexedSet

variable {x y : IndexedSet L Φ}

/-- `y` is a successor of `x` with the sequence of `x`, or an `F`-critical successor of `x` with
the sequence of `x` followed by `F`. -/
def Step (x y : IndexedSet L Φ) : Prop :=
  Successor x.set y.set ∧ y.seq = x.seq ∨
    ∃ F, CriticalSuccessor F x.set y.set ∧ y.seq = x.seq ++ [F]

lemma Step.rel (h : x.Step y) : x.Rel y := by
  rcases h with ⟨h, h'⟩ | ⟨_, h, h'⟩;
  · exact ⟨h, h' ▸ List.prefix_refl _⟩;
  · exact ⟨h.toSuccessor, h' ▸ List.prefix_append _ _⟩;

end IndexedSet

/-- A branch of indexed sets, listed from its last element back to its root, in which each indexed
set is a step from the next one.

- [dJV90, Theorem 5.2]
-/
structure IndexedBranch (L : Logic α) (Φ : Finset (Formula α)) where
  head : IndexedSet L Φ
  tail : List (IndexedSet L Φ)
  isChain : (head :: tail).IsChain (flip IndexedSet.Step)

namespace IndexedBranch

variable {w u v : IndexedBranch L Φ}

lemma ext (h₁ : w.head = u.head) (h₂ : w.tail = u.tail) : w = u := by
  cases w; cases u; simp_all;

/-- The branch `w` extended by `x`. -/
def cons (w : IndexedBranch L Φ) (x : IndexedSet L Φ) (h : w.head.Step x) : IndexedBranch L Φ :=
  ⟨x, w.head :: w.tail, .cons_cons h w.isChain⟩

lemma length_tail_le (w : IndexedBranch L Φ) : w.tail.length ≤ w.head.set.prebox.card := by
  obtain ⟨a, l, hc⟩ := w;
  induction l generalizing a with
  | nil => simp;
  | cons y l ih =>
    obtain ⟨hs, hc⟩ := List.isChain_cons_cons.mp hc;
    exact Nat.succ_le_of_lt <| (ih y hc).trans_lt <|
      Finset.card_lt_card hs.rel.1.prebox_ssubset;

instance [Adequate Φ] : Finite (IndexedBranch L Φ) := by
  have : Finite {l : List (IndexedSet L Φ) // l.length ≤ Φ.card} :=
    (List.finite_length_le _ _).to_subtype;
  have hc (Γ : MaximalConsistentSet L Φ) : Γ.prebox.card ≤ Φ.card :=
    Finset.card_le_card_of_injOn (□·) (fun _ hA ↦ mem_of_mem (mem_prebox.mp hA))
      fun _ _ _ _ h ↦ box_inj.mp h;
  apply Finite.of_injective
    (β := IndexedSet L Φ × {l : List (IndexedSet L Φ) // l.length ≤ Φ.card})
    fun w ↦ (w.head, ⟨w.tail, w.length_tail_le.trans (hc _)⟩);
  intro w u h;
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h;
  exact ext h.1 h.2

instance [Nonempty (IndexedSet L Φ)] : Nonempty (IndexedBranch L Φ) :=
  ⟨⟨Classical.arbitrary _, [], .singleton _⟩⟩

/-- `w` is a proper initial segment of `u`. -/
def Rel (w u : IndexedBranch L Φ) : Prop := w.head :: w.tail <:+ u.tail

lemma Rel.rel (h : w.Rel u) : w.head.Rel u.head := by
  obtain ⟨a, l, hc⟩ := u;
  induction l generalizing a with
  | nil => simp [Rel] at h;
  | cons y l ih =>
    obtain ⟨hs, hc⟩ := List.isChain_cons_cons.mp hc;
    rcases List.suffix_cons_iff.mp h with h | h;
    · obtain ⟨rfl, -⟩ := List.cons_eq_cons.mp h;
      exact hs.rel;
    · have h₁ := ih y hc h;
      exact ⟨h₁.1.trans hs.rel.1, h₁.2.trans hs.rel.2⟩;

variable [Entailment.Cl L]

lemma not_mem_of_prefix {C : Formula α} (h₁ : w.head :: w.tail <:+ v.head :: v.tail)
    (h₂ : w.head.seq ++ [C] <+: v.head.seq) (hC : ∀ {Γ : MaximalConsistentSet L Φ}, C ▷ C ∈ Γ) :
    □(∼C) ∈ v.head.set ∧ C ∉ v.head.set := by
  obtain ⟨a, l, hc⟩ := v;
  induction l generalizing a with
  | nil =>
    obtain ⟨rfl, -⟩ : w.head = a ∧ w.tail = [] := by simpa [List.suffix_cons_iff] using h₁;
    simpa using h₂.length_le;
  | cons y l ih =>
    obtain ⟨hs, hc⟩ := List.isChain_cons_cons.mp hc;
    rcases List.suffix_cons_iff.mp h₁ with h₁ | h₁;
    · obtain ⟨rfl, -⟩ := List.cons_eq_cons.mp h₁;
      simpa using h₂.length_le;
    by_cases h₃ : w.head.seq ++ [C] <+: y.seq;
    · have h₄ := ih y hc h₁ h₃;
      exact ⟨hs.rel.1.box_mem_of_box_mem h₄.1, hs.rel.1.not_mem_of_box_neg_mem h₄.1⟩;
    rcases hs with ⟨-, hseq⟩ | ⟨F, hF, hseq⟩;
    · exact absurd (hseq ▸ h₂) h₃;
    · rcases List.prefix_concat_iff.mp (hseq ▸ h₂) with h₄ | h₄;
      · obtain rfl : C = F := by simpa using (List.append_inj' h₄ rfl).2;
        exact ⟨hF.box_neg_mem hC, hF.not_mem hC⟩;
      · exact absurd h₄ h₃;

end IndexedBranch

open IndexedBranch

/-- The model on branches of indexed sets in which `w` is related to `u` if `w` is a proper initial
segment of `u`, and `S w u v` holds if moreover the branch `u` without its last element is a proper
initial segment of `v` and the sequence of `u` is an initial segment of the sequence of `v`.

- [dJV90, Theorem 5.2]
-/
def treeCountermodel (L : Logic α) (Φ : Finset (Formula α)) [Nonempty (IndexedSet L Φ)] :
    Model (IndexedBranch L Φ) α where
  Rel' := IndexedBranch.Rel
  S' w u v := w.Rel u ∧ u.tail <:+ v.tail ∧ u.head.seq <+: v.head.seq
  Val' w a := #a ∈ w.head.set

namespace treeCountermodel

open Model Model.World

variable [Nonempty (IndexedSet L Φ)]

instance : IsTrans _ (treeCountermodel L Φ).Rel :=
  ⟨fun _ _ _ h₁ h₂ ↦ h₁.trans <| (List.suffix_cons _ _).trans h₂⟩

instance : Std.Irrefl (treeCountermodel L Φ).Rel := ⟨fun _ h ↦ by simpa using h.length_le⟩

instance [Adequate Φ] : (treeCountermodel L Φ).IsIL where
  rel_of_s_left h := h.1
  rel_of_s_right h := h.1.trans h.2.1
  s_refl h := ⟨h, List.suffix_refl _, List.prefix_refl _⟩
  s_trans h₁ h₂ := ⟨h₁.1, h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩
  s_of_rel h₁ h₂ := ⟨h₁, (List.suffix_cons _ _).trans h₂, h₂.rel.2⟩

instance : (treeCountermodel L Φ).HasP := ⟨fun _ h₁ h₂ ↦ ⟨h₁, h₂.2⟩⟩

variable {𝔸 : Set (Formula α)} [Nonempty (IndexedSet (Logic.ofAxioms 𝔸) Φ)] [ILPAdequate Φ]

/-- - [dJV90, Theorem 5.2] -/
lemma truthlemma (hP : ∀ {B C : Formula α}, Logic.ofAxioms 𝔸 ⊢ Axioms.P B C)
    {w : (treeCountermodel (Logic.ofAxioms 𝔸) Φ).World} {A : Formula α} (hA : A ∈ Φ) :
    w ⊩ A ↔ A ∈ w.head.set := by
  induction A generalizing w with
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
      obtain ⟨Δ, hΔ, hA⟩ := exists_successor_of_box_not_mem hA hn;
      exact not_mem_of_provable_neg hA (Context.by_axm rfl) <| (ih hA').mp <|
        h (w.cons (w.head.successor Δ hΔ) (.inl ⟨hΔ, rfl⟩)) (List.suffix_refl _);
    · intro h u Rwu;
      exact (ih hA').mpr <| Rwu.rel.1.mem_of_box_mem h;
  | rhd B C ihB ihC =>
    have hB := Adequate.rhd_left hA;
    have hC := Adequate.rhd_right hA;
    have hC' : IsRhdOperand Φ C := .of_rhd_right hA;
    constructor;
    · intro h;
      by_contra hn;
      obtain ⟨Δ, hΔ, hBΔ⟩ := exists_criticalSuccessor_of_rhd_not_mem hA hn;
      obtain ⟨v, hS, hv⟩ := h (w.cons (w.head.criticalSuccessor C hC' Δ hΔ.toSuccessor)
        (.inr ⟨C, hΔ, rfl⟩)) (List.suffix_refl _) ((ihB hB).mpr hBΔ);
      have hCC {Γ : MaximalConsistentSet (Logic.ofAxioms 𝔸) Φ} : C ▷ C ∈ Γ :=
        (mem_iff_provable (Adequate.rhd_mem hC' hC')).mpr <| Context.of Logic.ofAxioms.rhd_refl;
      exact (not_mem_of_prefix (hS.2.1.trans (List.suffix_cons _ _)) hS.2.2 hCC).2 <|
        (ihC hC).mp hv;
    · intro h u Rwu hu;
      replace hu := (ihB hB).mp hu;
      obtain ⟨x, _ | ⟨y, l⟩, hc⟩ := u;
      · change _ <:+ [] at Rwu;
        simp at Rwu;
      obtain ⟨hs, hc⟩ := List.isChain_cons_cons.mp hc;
      let p : IndexedBranch (Logic.ofAxioms 𝔸) Φ := ⟨y, l, hc⟩;
      have hBC : B ▷ C ∈ y.set := by
        rcases List.suffix_cons_iff.mp Rwu with h₁ | h₁;
        · obtain ⟨rfl, -⟩ := List.cons_eq_cons.mp h₁;
          exact h;
        · have h₂ : □(B ▷ C) ∈ w.head.set :=
            (mem_iff_provable (ILPAdequate.box_rhd_mem hA)).mpr <|
              Context.of hP ⨀ Context.by_axm (mem_literals h);
          exact (Rel.rel (u := p) h₁).1.mem_of_box_mem h₂;
      rcases hs with ⟨hs, hseq⟩ | ⟨F, hF, hseq⟩;
      · obtain ⟨Θ, hΘ, hCΘ⟩ :=
          (hs.criticalSuccessor_bot Logic.ofAxioms.rhd_bot).exists_criticalSuccessor .bot hBC hu;
        exact ⟨p.cons (y.successor Θ hΘ.toSuccessor) (.inl ⟨hΘ.toSuccessor, rfl⟩),
          ⟨Rwu, List.suffix_refl _, hseq ▸ List.prefix_refl _⟩, (ihC hC).mpr hCΘ⟩
      · have hF' : IsRhdOperand Φ F := x.isRhdOperand_of_mem_seq F (by simp [hseq]);
        obtain ⟨Θ, hΘ, hCΘ⟩ := hF.exists_criticalSuccessor hF' hBC hu;
        refine ⟨p.cons (y.criticalSuccessor F hF' Θ hΘ.toSuccessor) (.inr ⟨F, hΘ, rfl⟩),
          ⟨Rwu, List.suffix_refl _, ?_⟩, (ihC hC).mpr hCΘ⟩
        change x.seq <+: y.seq ++ [F]
        exact hseq ▸ List.prefix_refl _

end treeCountermodel

end Veltman

/-! ### Completeness -/

namespace Logic.ILP

open Veltman Veltman.Model.World

universe u

variable {α : Type u} {A : Formula α}

/-- - [dJV90, Theorem 5.2] -/
theorem complete
    (h : ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α), [M.IsIL] → [M.HasP] →
      M ⊧ A) :
    𝐈𝐋𝐏 ⊢ A := by
  classical
  by_contra hA;
  let Φ := boxClosure (adequateClosure {A});
  have hX : ({∼A} : Set (Formula α)) *⊬[𝐈𝐋𝐏] ⊥ := by
    intro h₁;
    apply hA;
    have h₂ : 𝐈𝐋𝐏 ⊢ ∼A 🡒 ⊥ := Context.emptyPrf <| Context.deduct <| by simpa using h₁;
    cl_prover [h₂];
  obtain ⟨Γ, hΓ⟩ := exists_consistent_union (Φ := Φ) hX;
  have hAΦ : A ∈ Φ := boxClosure.subset <| adequateClosure.subset (by simp);
  exact not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
    (treeCountermodel.truthlemma axiomP hAΦ).mp <|
      h (treeCountermodel _ Φ) ⟨⟨Γ, [], by simp, by simp⟩, [], .singleton _⟩

end Logic.ILP

end FFL.InterpretabilityLogic

end
