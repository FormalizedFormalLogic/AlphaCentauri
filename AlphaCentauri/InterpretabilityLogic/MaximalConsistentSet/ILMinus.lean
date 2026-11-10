module

public import AlphaCentauri.InterpretabilityLogic.ILMinus
public import AlphaCentauri.InterpretabilityLogic.MaximalConsistentSet

/-!
# Maximal consistent sets for extensions of $\mathbf{IL}^-$

Adequate sets in the sense of Kurahashi and Okawa, Ignatiev's successors, and the existence of
successors containing prescribed formulas, for extensions of $\mathbf{IL}^-$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*} [DecidableEq α]

/-! ### Adequate sets -/

/-- `Φ` is adequate and contains `□(B 🡒 ⋁S)` for every antecedent or consequent `B` of a
`▷`-formula in `Φ` and every finite set `S` of such formulas and of their `◇`-formulas.

- [KO21, Definition 4.1]
-/
class ILMinusAdequate (Φ : Finset (Formula α)) : Prop extends Adequate Φ where
  box_imp_disj_mem {B : Formula α} {S : Finset (Formula α)} : IsRhdOperand Φ B →
    (∀ A ∈ S, IsRhdOperand Φ A ∨ ∃ G, IsRhdOperand Φ G ∧ A = ◇G) → □(B 🡒 S.disj) ∈ Φ

/-- A finite set satisfying `ILMinusAdequate` and containing `S`. -/
noncomputable def ilMinusAdequateClosure (S : Finset (Formula α)) : Finset (Formula α) :=
  let T := insert ⊥ (S.biUnion subformulas);
  (T ∪ (T ×ˢ T).image (fun p ↦ p.1 ▷ p.2) ∪ T.image (fun A ↦ □(∼A)) ∪
    (T ×ˢ (T ∪ T.image (◇·)).powerset).image (fun p ↦ □(p.1 🡒 p.2.disj))).biUnion subformulas

namespace ilMinusAdequateClosure

variable {S T : Finset (Formula α)} {A B C : Formula α}

/-- Every `▷`-subformula of `A` has both of its components in `T`. -/
private def RhdClosed (T : Finset (Formula α)) (A : Formula α) : Prop :=
  ∀ B C, B ▷ C ∈ A.subformulas → B ∈ T ∧ C ∈ T

private lemma rhdClosed_bot : RhdClosed T ⊥ := by
  intro B C h;
  simp [subformulas] at h;

private lemma rhdClosed_imp (hA : RhdClosed T A) (hB : RhdClosed T B) : RhdClosed T (A 🡒 B) := by
  intro B' C' h;
  simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h;
  rcases h with h | h | h;
  · simp at h;
  · exact hA B' C' h;
  · exact hB B' C' h;

private lemma rhdClosed_box (hA : RhdClosed T A) : RhdClosed T (□A) := by
  intro B C h;
  simp only [subformulas, Finset.mem_insert] at h;
  rcases h with h | h;
  · simp at h;
  · exact hA B C h;

private lemma rhdClosed_disj : (l : List (Formula α)) → (∀ A ∈ l, RhdClosed T A) →
    RhdClosed T l.disj₂
  | [], _ => rhdClosed_bot
  | [A], h => h A (by simp)
  | A :: B :: l, h =>
    rhdClosed_imp (rhdClosed_imp (h A (by simp)) rhdClosed_bot) <|
      rhdClosed_disj (B :: l) fun C hC ↦ h C (by simp_all)

private lemma base_closed (hA : A ∈ insert ⊥ (S.biUnion subformulas)) (hB : B ∈ A.subformulas) :
    B ∈ insert ⊥ (S.biUnion subformulas) := by
  simp only [Finset.mem_insert, Finset.mem_biUnion] at hA ⊢;
  rcases hA with rfl | ⟨C, hC, hA⟩;
  · simp_all [subformulas];
  · exact .inr ⟨C, hC, subformulas_subset_of_mem hA hB⟩

private lemma rhdClosed_of_base (hA : A ∈ insert ⊥ (S.biUnion subformulas)) :
    RhdClosed (insert ⊥ (S.biUnion subformulas)) A := by
  intro B C h;
  have h₁ := base_closed hA h;
  constructor;
  · exact base_closed h₁ (by simp [subformulas]);
  · exact base_closed h₁ (by simp [subformulas]);

private lemma rhdClosed_of_mem_gen {g : Formula α}
    (hg : g ∈ (let T := insert ⊥ (S.biUnion subformulas);
      T ∪ (T ×ˢ T).image (fun p ↦ p.1 ▷ p.2) ∪ T.image (fun A ↦ □(∼A)) ∪
        (T ×ˢ (T ∪ T.image (◇·)).powerset).image (fun p ↦ □(p.1 🡒 p.2.disj)))) :
    RhdClosed (insert ⊥ (S.biUnion subformulas)) g := by
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_powerset,
    Prod.exists] at hg;
  rcases hg with ((hg | ⟨B, C, ⟨hB, hC⟩, rfl⟩) | ⟨B, hB, rfl⟩) | ⟨B, U, ⟨hB, hU⟩, rfl⟩;
  · exact rhdClosed_of_base hg;
  · intro B' C' h;
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h;
    rcases h with h | h | h;
    · obtain ⟨rfl, rfl⟩ := rhd_inj.mp h;
      exact ⟨hB, hC⟩;
    · exact rhdClosed_of_base hB B' C' h;
    · exact rhdClosed_of_base hC B' C' h;
  · exact rhdClosed_box <| rhdClosed_imp (rhdClosed_of_base hB) rhdClosed_bot;
  · apply rhdClosed_box <| rhdClosed_imp (rhdClosed_of_base hB) <| rhdClosed_disj _ _;
    intro A hA;
    rcases Finset.mem_union.mp (hU (Finset.mem_toList.mp hA)) with hA | hA;
    · exact rhdClosed_of_base hA;
    · obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hA;
      exact rhdClosed_imp (rhdClosed_box <| rhdClosed_imp (rhdClosed_of_base hG) rhdClosed_bot)
        rhdClosed_bot;

private lemma mem_sub (hA : A ∈ ilMinusAdequateClosure S) (hB : B ∈ A.subformulas) :
    B ∈ ilMinusAdequateClosure S := by
  obtain ⟨g, hg, hA⟩ := Finset.mem_biUnion.mp hA;
  exact Finset.mem_biUnion.mpr ⟨g, hg, subformulas_subset_of_mem hA hB⟩

private lemma mem_of_gen {g : Formula α}
    (hg : g ∈ (let T := insert ⊥ (S.biUnion subformulas);
      T ∪ (T ×ˢ T).image (fun p ↦ p.1 ▷ p.2) ∪ T.image (fun A ↦ □(∼A)) ∪
        (T ×ˢ (T ∪ T.image (◇·)).powerset).image (fun p ↦ □(p.1 🡒 p.2.disj)))) :
    g ∈ ilMinusAdequateClosure S :=
  Finset.mem_biUnion.mpr ⟨g, hg, mem_subformulas_self⟩

private lemma isRhdOperand (h : IsRhdOperand (ilMinusAdequateClosure S) A) :
    A ∈ insert ⊥ (S.biUnion subformulas) := by
  obtain ⟨B, h | h⟩ := h <;> obtain ⟨g, hg, h⟩ := Finset.mem_biUnion.mp h;
  · exact (rhdClosed_of_mem_gen hg _ _ h).1;
  · exact (rhdClosed_of_mem_gen hg _ _ h).2;

lemma subset : S ⊆ ilMinusAdequateClosure S := by
  intro A hA;
  apply mem_of_gen;
  simp only [Finset.mem_union];
  exact .inl <| .inl <| .inl <| Finset.mem_insert_of_mem <|
    Finset.mem_biUnion.mpr ⟨A, hA, mem_subformulas_self⟩

instance : ILMinusAdequate (ilMinusAdequateClosure S) where
  imp_left h := mem_sub h (by simp [subformulas])
  imp_right h := mem_sub h (by simp [subformulas])
  box h := mem_sub h (by simp [subformulas])
  rhd_left h := mem_sub h (by simp [subformulas])
  rhd_right h := mem_sub h (by simp [subformulas])
  bot_rhd_bot := mem_of_gen <| by simp
  rhd_mem {A B} hA hB := mem_of_gen <| Finset.mem_union_left _ <| Finset.mem_union_left _ <|
    Finset.mem_union_right _ <|
      Finset.mem_image.mpr ⟨(A, B), Finset.mem_product.mpr ⟨isRhdOperand hA, isRhdOperand hB⟩, rfl⟩
  box_neg_mem hA := mem_of_gen <| Finset.mem_union_left _ <| Finset.mem_union_right _ <|
    Finset.mem_image_of_mem _ (isRhdOperand hA)
  box_imp_disj_mem {B U} hB hU := by
    apply mem_of_gen;
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_powerset,
      Prod.exists];
    have hU' : U ⊆ insert ⊥ (S.biUnion subformulas) ∪
        (insert ⊥ (S.biUnion subformulas)).image (◇·) := by
      intro A hA;
      rcases hU A hA with hA | ⟨G, hG, rfl⟩;
      · exact Finset.mem_union_left _ (isRhdOperand hA);
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (isRhdOperand hG));
    exact .inr ⟨B, U, ⟨isRhdOperand hB, hU'⟩, rfl⟩;

end ilMinusAdequateClosure

/-! ### Successors -/

namespace MaximalConsistentSet

open Logic Logic.ofAxiomsMinus

/-- `Δ` is a successor of `Γ` that contains no `A` with `A ▷ C ∈ Γ`.

- [KO21, Definition 4.3]
-/
structure WeakCriticalSuccessor {L : Logic α} {Φ : Finset (Formula α)} (C : Formula α)
    (Γ Δ : MaximalConsistentSet L Φ) : Prop extends Successor Γ Δ where
  not_mem : ∀ {A}, A ▷ C ∈ Γ → A ∉ Δ

lemma CriticalSuccessor.weakCriticalSuccessor {L : Logic α} {Φ : Finset (Formula α)}
    {C : Formula α} {Γ Δ : MaximalConsistentSet L Φ} (h : CriticalSuccessor C Γ Δ) :
    WeakCriticalSuccessor C Γ Δ :=
  ⟨h.toSuccessor, h.not_mem⟩

variable {𝔸 : Set (Formula α)} {Φ : Finset (Formula α)} [ILMinusAdequate Φ]
  {Γ Δ : MaximalConsistentSet (ofAxiomsMinus 𝔸) Φ} {B D E F : Formula α} {S : Finset (Formula α)}

private lemma exists_successor_of_box_imp_disj_not_mem (hB : IsRhdOperand Φ B)
    (hS : ∀ A ∈ S, IsRhdOperand Φ A ∨ ∃ G, IsRhdOperand Φ G ∧ A = ◇G)
    (h : □(B 🡒 S.disj) ∉ Γ) :
    ∃ Δ, Successor Γ Δ ∧ B ∈ Δ ∧
      (∀ {P}, P ∈ Φ → ofAxiomsMinus 𝔸 ⊢ ∼S.disj 🡒 P → P ∈ Δ) ∧
      ∀ {P}, ofAxiomsMinus 𝔸 ⊢ ∼S.disj 🡒 ∼P → P ∉ Δ := by
  obtain ⟨Δ, hΔ, hc⟩ := exists_successor_of_box_not_mem (ILMinusAdequate.box_imp_disj_mem hB hS) h;
  have hH : ({∼(B 🡒 S.disj)} : Set (Formula α)) *⊢[ofAxiomsMinus 𝔸] ∼(B 🡒 S.disj) :=
    Context.by_axm rfl;
  have h₁ {P} (hP : ofAxiomsMinus 𝔸 ⊢ ∼S.disj 🡒 P) :
      ({∼(B 🡒 S.disj)} : Set (Formula α)) *⊢[ofAxiomsMinus 𝔸] P := by
    have := Context.of (Γ := {∼(B 🡒 S.disj)}) hP;
    cl_prover [hH, this];
  use Δ;
  and_intros;
  · exact hΔ;
  · exact mem_of_provable hc hB.mem <| by cl_prover [hH];
  · intro P hP h;
    exact mem_of_provable hc hP (h₁ h);
  · intro P h;
    exact not_mem_of_provable_neg hc (h₁ h);

omit [ILMinusAdequate Φ] in
private lemma provable_rhd_of_box_imp_disj_mem
    (hS : ∀ A ∈ S, Γ.literals *⊢[ofAxiomsMinus 𝔸] A ▷ F) (h : □(B 🡒 S.disj) ∈ Γ) :
    Γ.literals *⊢[ofAxiomsMinus 𝔸] B ▷ F :=
  Context.of rhd_anti_left_of_box ⨀ Context.by_axm (mem_literals h) ⨀ fdisj_rhd hS

private lemma mem_rhdSet {G : Formula α} : G ∈ Φ.filter (· ▷ F ∈ Γ) ↔ G ▷ F ∈ Γ :=
  ⟨fun h ↦ (Finset.mem_filter.mp h).2,
    fun h ↦ Finset.mem_filter.mpr ⟨Adequate.rhd_left (mem_of_mem h), h⟩⟩

private lemma provable_neg_of_mem {G : Formula α} (h : G ∈ S) :
    ofAxiomsMinus 𝔸 ⊢ ∼S.disj 🡒 ∼G := by
  have := right_Fdisj_intro (𝓢 := ofAxiomsMinus 𝔸) S h;
  cl_prover [this];

private lemma provable_box_neg_of_mem {G : Formula α} (h : ◇G ∈ S) :
    ofAxiomsMinus 𝔸 ⊢ ∼S.disj 🡒 □(∼G) := by
  have : ofAxiomsMinus 𝔸 ⊢ ∼□(∼G) 🡒 S.disj := right_Fdisj_intro S h;
  cl_prover [this];

private lemma rhd_of_mem_diaSet [(ILMinusJ2 : Logic α) ⪯ ofAxiomsMinus 𝔸]
    [(ILMinusJ5 : Logic α) ⪯ ofAxiomsMinus 𝔸] {A : Formula α}
    (h : A ∈ insert (◇F) (Φ.filter (· ▷ F ∈ Γ) ∪ (Φ.filter (· ▷ F ∈ Γ)).image (◇·))) :
    Γ.literals *⊢[ofAxiomsMinus 𝔸] A ▷ F := by
  have hJ5 {G : Formula α} : Γ.literals *⊢[ofAxiomsMinus 𝔸] ◇G ▷ G :=
    Context.of <| WeakerThan.pbl (𝓢 := ILMinusJ5) ILMinusJ5.axiomJ5;
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at h;
  rcases h with rfl | h | ⟨G, hG, rfl⟩;
  · exact hJ5;
  · exact Context.by_axm <| mem_literals <| mem_rhdSet.mp h;
  · have h₁ := Context.of (Γ := Γ.literals) <|
      WeakerThan.pbl (𝓢 := ILMinusJ2) (𝓣 := ofAxiomsMinus 𝔸) <|
        (ILMinusJ2.axiomJ2 (A := ◇G) (B := G) (C := F));
    have h₂ : Γ.literals *⊢[ofAxiomsMinus 𝔸] G ▷ F :=
      Context.by_axm <| mem_literals <| mem_rhdSet.mp hG;
    have h₃ : Γ.literals *⊢[ofAxiomsMinus 𝔸] ◇G ▷ G := hJ5;
    cl_prover [h₁, h₂, h₃];

private lemma diaSet_spec (hF : IsRhdOperand Φ F) {A : Formula α}
    (h : A ∈ insert (◇F) (Φ.filter (· ▷ F ∈ Γ) ∪ (Φ.filter (· ▷ F ∈ Γ)).image (◇·))) :
    IsRhdOperand Φ A ∨ ∃ G, IsRhdOperand Φ G ∧ A = ◇G := by
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at h;
  rcases h with rfl | h | ⟨G, hG, rfl⟩;
  · exact .inr ⟨F, hF, rfl⟩;
  · exact .inl <| .of_rhd_left <| mem_of_mem <| mem_rhdSet.mp h;
  · exact .inr ⟨G, .of_rhd_left <| mem_of_mem <| mem_rhdSet.mp hG, rfl⟩;

private lemma criticalSuccessor_of_diaSet (hΔ : Successor Γ Δ)
    (hn : ∀ {P}, ofAxiomsMinus 𝔸 ⊢
      ∼(insert (◇F) (Φ.filter (· ▷ F ∈ Γ) ∪ (Φ.filter (· ▷ F ∈ Γ)).image (◇·))).disj 🡒 ∼P →
        P ∉ Δ)
    (hp : ∀ {P}, P ∈ Φ → ofAxiomsMinus 𝔸 ⊢
      ∼(insert (◇F) (Φ.filter (· ▷ F ∈ Γ) ∪ (Φ.filter (· ▷ F ∈ Γ)).image (◇·))).disj 🡒 P →
        P ∈ Δ) :
    CriticalSuccessor F Γ Δ := by
  constructor;
  · exact hΔ;
  · intro A hA;
    exact hn <| provable_neg_of_mem <| by simp [mem_rhdSet.mpr hA];
  · intro A hA;
    apply hp (Adequate.box_neg_mem <| .of_rhd_left <| mem_of_mem hA);
    apply provable_box_neg_of_mem;
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image];
    exact .inr <| .inr ⟨_, mem_rhdSet.mpr hA, rfl⟩;

/-- - [KO21, Lemma 4.6] -/
lemma exists_weakCriticalSuccessor_of_rhd_not_mem (h₁ : D ▷ E ∈ Φ) (h₂ : D ▷ E ∉ Γ) :
    ∃ Δ, WeakCriticalSuccessor E Γ Δ ∧ D ∈ Δ := by
  obtain ⟨Δ, hΔ, hD, -, hn⟩ := exists_successor_of_box_imp_disj_not_mem
    (S := Φ.filter (· ▷ E ∈ Γ)) (.of_rhd_left h₁)
    (fun A hA ↦ .inl <| .of_rhd_left <| mem_of_mem <| mem_rhdSet.mp hA) <| by
      intro h;
      exact h₂ <| (mem_iff_provable h₁).mpr <| provable_rhd_of_box_imp_disj_mem
        (fun G hG ↦ Context.by_axm <| mem_literals <| mem_rhdSet.mp hG) h;
  use Δ;
  and_intros;
  · exact ⟨hΔ, fun hG ↦ hn <| provable_neg_of_mem <| mem_rhdSet.mpr hG⟩;
  · exact hD;

/-- - [KO21, Lemma 4.6.a] -/
lemma exists_weakCriticalSuccessor_box_neg_of_rhd_not_mem
    [(ILMinusJ5 : Logic α) ⪯ ofAxiomsMinus 𝔸] (h₁ : D ▷ E ∈ Φ) (h₂ : D ▷ E ∉ Γ) :
    ∃ Δ, WeakCriticalSuccessor E Γ Δ ∧ D ∈ Δ ∧ □(∼E) ∈ Δ := by
  have hE : IsRhdOperand Φ E := .of_rhd_right h₁;
  obtain ⟨Δ, hΔ, hD, hp, hn⟩ := exists_successor_of_box_imp_disj_not_mem
    (S := insert (◇E) (Φ.filter (· ▷ E ∈ Γ))) (.of_rhd_left h₁) (by
      intro A hA;
      rcases Finset.mem_insert.mp hA with rfl | hA;
      · exact .inr ⟨E, hE, rfl⟩;
      · exact .inl <| .of_rhd_left <| mem_of_mem <| mem_rhdSet.mp hA) <| by
      intro h;
      apply h₂ <| (mem_iff_provable h₁).mpr <| provable_rhd_of_box_imp_disj_mem _ h;
      intro A hA;
      rcases Finset.mem_insert.mp hA with rfl | hA;
      · exact Context.of <| WeakerThan.pbl (𝓢 := ILMinusJ5) ILMinusJ5.axiomJ5;
      · exact Context.by_axm <| mem_literals <| mem_rhdSet.mp hA;
  use Δ;
  and_intros;
  · exact ⟨hΔ, fun hG ↦ hn <| provable_neg_of_mem <|
      Finset.mem_insert_of_mem <| mem_rhdSet.mpr hG⟩;
  · exact hD;
  · exact hp (Adequate.box_neg_mem hE) <| provable_box_neg_of_mem <| Finset.mem_insert_self _ _;

/-- - [KO21, Lemma 4.6.b] -/
lemma exists_criticalSuccessor_box_neg_of_rhd_not_mem [(ILMinusJ2 : Logic α) ⪯ ofAxiomsMinus 𝔸]
    [(ILMinusJ5 : Logic α) ⪯ ofAxiomsMinus 𝔸] (h₁ : D ▷ E ∈ Φ) (h₂ : D ▷ E ∉ Γ) :
    ∃ Δ, CriticalSuccessor E Γ Δ ∧ D ∈ Δ ∧ □(∼E) ∈ Δ := by
  have hE : IsRhdOperand Φ E := .of_rhd_right h₁;
  obtain ⟨Δ, hΔ, hD, hp, hn⟩ := exists_successor_of_box_imp_disj_not_mem
    (.of_rhd_left h₁) (fun _ ↦ diaSet_spec hE) <| by
      intro h;
      exact h₂ <| (mem_iff_provable h₁).mpr <|
        provable_rhd_of_box_imp_disj_mem (fun _ h ↦ rhd_of_mem_diaSet (Γ := Γ) h) h;
  use Δ;
  and_intros;
  · exact criticalSuccessor_of_diaSet hΔ hn hp;
  · exact hD;
  · exact hp (Adequate.box_neg_mem hE) <| provable_box_neg_of_mem <| Finset.mem_insert_self _ _;

namespace WeakCriticalSuccessor

private lemma rhd_not_mem (hF : IsRhdOperand Φ F) (hΔ : WeakCriticalSuccessor F Γ Δ)
    (hDE : D ▷ E ∈ Γ) (hD : D ∈ Δ) : ¬Γ.literals *⊢[ofAxiomsMinus 𝔸] D ▷ F := fun h ↦
  hΔ.not_mem ((mem_iff_provable <| Adequate.rhd_mem (.of_rhd_left (mem_of_mem hDE)) hF).mpr h) hD

/-- - [KO21, Lemma 4.7] -/
lemma exists_mem_not_mem (hF : IsRhdOperand Φ F) (hDE : D ▷ E ∈ Γ)
    (hΔ : WeakCriticalSuccessor F Γ Δ) (hD : D ∈ Δ) :
    ∃ Θ : MaximalConsistentSet (ofAxiomsMinus 𝔸) Φ, E ∈ Θ ∧ F ∉ Θ := by
  have hX : (insert E {∼F} : Set (Formula α)) *⊬[ofAxiomsMinus 𝔸] ⊥ := by
    intro h;
    apply rhd_not_mem hF hΔ hDE hD;
    have h₁ : ofAxiomsMinus 𝔸 ⊢ ∼F 🡒 E 🡒 ⊥ :=
      Context.emptyPrf <| Context.deduct <| by simpa using Context.deduct h;
    have h₂ : ofAxiomsMinus 𝔸 ⊢ D ▷ E 🡒 D ▷ F := rhd_mono_right <| by cl_prover [h₁];
    exact Context.of h₂ ⨀ Context.by_axm (mem_literals hDE);
  obtain ⟨Θ, hΘ⟩ := exists_consistent_union (Φ := Φ) hX;
  use Θ;
  and_intros;
  · exact mem_of_provable hΘ (Adequate.rhd_right (mem_of_mem hDE)) (Context.by_axm (by simp));
  · exact not_mem_of_provable_neg hΘ (Context.by_axm (by simp));

/-- - [KO21, Lemma 4.7.a] -/
lemma exists_successor_mem_not_mem [(ILMinusJ4Plus : Logic α) ⪯ ofAxiomsMinus 𝔸]
    (hF : IsRhdOperand Φ F) (hDE : D ▷ E ∈ Γ) (hΔ : WeakCriticalSuccessor F Γ Δ) (hD : D ∈ Δ) :
    ∃ Θ, Successor Γ Θ ∧ E ∈ Θ ∧ F ∉ Θ := by
  have hd : ({F} : Finset (Formula α)).disj = F := by simp [Finset.disj];
  obtain ⟨Θ, hΘ, hE, -, hn⟩ := exists_successor_of_box_imp_disj_not_mem (S := {F})
    (.of_rhd_right (mem_of_mem hDE)) (by simpa using .inl hF) <| by
      intro h;
      apply rhd_not_mem hF hΔ hDE hD;
      rw [hd] at h;
      have h₁ : ofAxiomsMinus 𝔸 ⊢ □(E 🡒 F) 🡒 D ▷ E 🡒 D ▷ F :=
        WeakerThan.pbl (𝓢 := ILMinusJ4Plus) ILMinusJ4Plus.axiomJ4Plus;
      exact Context.of h₁ ⨀ Context.by_axm (mem_literals h) ⨀ Context.by_axm (mem_literals hDE);
  use Θ;
  and_intros;
  · exact hΘ;
  · exact hE;
  · exact hn <| by rw [hd]; exact C_id;

/-- - [KO21, Lemma 4.9] -/
lemma exists_weakCriticalSuccessor_of_rhd_mem [(ILMinusJ2 : Logic α) ⪯ ofAxiomsMinus 𝔸]
    (hF : IsRhdOperand Φ F) (hDE : D ▷ E ∈ Γ) (hΔ : WeakCriticalSuccessor F Γ Δ) (hD : D ∈ Δ) :
    ∃ Θ, WeakCriticalSuccessor F Γ Θ ∧ E ∈ Θ := by
  obtain ⟨Θ, hΘ, hE, -, hn⟩ := exists_successor_of_box_imp_disj_not_mem
    (S := Φ.filter (· ▷ F ∈ Γ)) (.of_rhd_right (mem_of_mem hDE))
    (fun A hA ↦ .inl <| .of_rhd_left <| mem_of_mem <| mem_rhdSet.mp hA) <| by
      intro h;
      apply rhd_not_mem hF hΔ hDE hD;
      have h₁ := provable_rhd_of_box_imp_disj_mem
        (fun G hG ↦ Context.by_axm <| mem_literals <| mem_rhdSet.mp hG) h;
      have h₂ := Context.of (Γ := Γ.literals) <|
        WeakerThan.pbl (𝓢 := ILMinusJ2) (𝓣 := ofAxiomsMinus 𝔸) <|
        (ILMinusJ2.axiomJ2 (A := D) (B := E) (C := F));
      have h₃ : Γ.literals *⊢[ofAxiomsMinus 𝔸] D ▷ E := Context.by_axm (mem_literals hDE);
      cl_prover [h₁, h₂, h₃];
  use Θ;
  and_intros;
  · exact ⟨hΘ, fun hG ↦ hn <| provable_neg_of_mem <| mem_rhdSet.mpr hG⟩;
  · exact hE;

/-- - [KO21, Lemma 4.9.a] -/
lemma exists_criticalSuccessor_box_neg_of_rhd_mem [(ILMinusJ2 : Logic α) ⪯ ofAxiomsMinus 𝔸]
    [(ILMinusJ5 : Logic α) ⪯ ofAxiomsMinus 𝔸] (hF : IsRhdOperand Φ F) (hDE : D ▷ E ∈ Γ)
    (hΔ : WeakCriticalSuccessor F Γ Δ) (hD : D ∈ Δ) :
    ∃ Θ, CriticalSuccessor F Γ Θ ∧ E ∈ Θ ∧ □(∼F) ∈ Θ := by
  obtain ⟨Θ, hΘ, hE, hp, hn⟩ := exists_successor_of_box_imp_disj_not_mem
    (.of_rhd_right (mem_of_mem hDE)) (fun _ ↦ diaSet_spec hF) <| by
      intro h;
      apply rhd_not_mem hF hΔ hDE hD;
      have h₁ := provable_rhd_of_box_imp_disj_mem (fun _ h ↦ rhd_of_mem_diaSet (Γ := Γ) h) h;
      have h₂ := Context.of (Γ := Γ.literals) <|
        WeakerThan.pbl (𝓢 := ILMinusJ2) (𝓣 := ofAxiomsMinus 𝔸) <|
        (ILMinusJ2.axiomJ2 (A := D) (B := E) (C := F));
      have h₃ : Γ.literals *⊢[ofAxiomsMinus 𝔸] D ▷ E := Context.by_axm (mem_literals hDE);
      cl_prover [h₁, h₂, h₃];
  use Θ;
  and_intros;
  · exact criticalSuccessor_of_diaSet hΘ hn hp;
  · exact hE;
  · exact hp (Adequate.box_neg_mem hF) <| provable_box_neg_of_mem <| Finset.mem_insert_self _ _;

end WeakCriticalSuccessor

omit [ILMinusAdequate Φ] in
/-- - [KO21, Lemma 4.8] -/
lemma Successor.exists_successor_of_rhd_mem [Adequate Φ] [(ILMinusJ4 : Logic α) ⪯ ofAxiomsMinus 𝔸]
    (hDE : D ▷ E ∈ Γ) (hΔ : Successor Γ Δ) (hD : D ∈ Δ) : ∃ Θ, Successor Γ Θ ∧ E ∈ Θ := by
  have hE : IsRhdOperand Φ E := .of_rhd_right (mem_of_mem hDE);
  obtain ⟨Θ, hΘ, hc⟩ := exists_successor_of_box_not_mem (Adequate.box_neg_mem hE) <| by
    intro h;
    apply hΔ.not_mem_of_box_neg_mem _ hD;
    apply (mem_iff_provable <| Adequate.box_neg_mem <| .of_rhd_left (mem_of_mem hDE)).mpr;
    have h₁ := Context.of (Γ := Γ.literals) <|
      WeakerThan.pbl (𝓢 := ILMinusJ4) (𝓣 := ofAxiomsMinus 𝔸) (ILMinusJ4.axiomJ4 (A := D) (B := E));
    have h₂ : Γ.literals *⊢[ofAxiomsMinus 𝔸] D ▷ E := Context.by_axm (mem_literals hDE);
    have h₃ : Γ.literals *⊢[ofAxiomsMinus 𝔸] □(∼E) := Context.by_axm (mem_literals h);
    change Γ.literals *⊢[ofAxiomsMinus 𝔸] D ▷ E 🡒 ∼□(∼D) 🡒 ∼□(∼E) at h₁;
    cl_prover [h₁, h₂, h₃];
  use Θ;
  and_intros;
  · exact hΘ;
  · have : ({∼∼E} : Set (Formula α)) *⊢[ofAxiomsMinus 𝔸] ∼∼E := Context.by_axm rfl;
    exact mem_of_provable hc hE.mem <| by cl_prover [this];

end MaximalConsistentSet

end FFL.InterpretabilityLogic

end
