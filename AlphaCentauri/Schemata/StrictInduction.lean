module

public import AlphaCentauri.Schemata.Induction
public import AlphaCentauri.ToFoundation.Definable
public import AlphaCentauri.ToFoundation.Eval
public import Foundation.FirstOrder.Arithmetic.Collection.Equiv
public import Foundation.FirstOrder.Arithmetic.Definability.StrictDefinable

/-!
# Induction over the strict and the broad hierarchy agree

Induction for strict $\Sigma_{s + 1}$ formulas proves collection for them, and collection turns
every formula of the broad class into a strict one, so `𝗜 Γ s` and `𝗜𝗡𝗗 Γ s` are the same
theory.

- [HP98, Theorem I.2.4, Lemma I.2.9, Lemma I.2.11, Lemma I.2.12(2)]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

variable {V : Type*} [ORingStructure V] {Γ : Polarity} {s : ℕ}

/-! ## Strict definitions of definable relations -/

/-- The evaluation of a strict `Γ-[s]` formula in two variables at a fixed assignment of the free
variables is a `StrictDefinableRel`. -/
private lemma strictDefinableRel_of_eval {φ : ArithmeticSemiformula ℕ 2}
    (hφ : StrictHierarchy Γ s φ) (f : ℕ → V) :
    StrictDefinableRel Γ s fun x y ↦ φ.Eval ![x, y] f :=
  (StrictDefinable.of_strictHierarchy (m := 0) (θ := φ ⇜ ![#1, #0]) (hφ.rew _) ![] f).of_iff
    fun v ↦ by simp [Semiformula.eval_substs]

/-- Every `Γ-[s]`-definable relation on `V` is definable by a strict `Γ-[s]` formula. -/
def StrictlyDefinable (V : Type*) [ORingStructure V] (s : ℕ) : Prop :=
  ∀ {Γ : Polarity} {R : V → V → Prop}, Γ-[s].DefinableRel R → StrictDefinableRel Γ s R

/-- In a model of `𝗜𝚺 s` every `Γ-[s]`-definable relation has a strict definition.
- [HP98, Theorem I.2.5(3)]
- [HP98, Lemma I.2.9] -/
lemma strictlyDefinable_of_models_ISigma (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺s] :
    StrictlyDefinable V s := by
  rcases s with _ | t
  · intro Γ R hR
    obtain ⟨f, φ, hφ, hiff⟩ := exists_hierarchy_eval_iff hR
    exact (strictDefinableRel_of_eval (.zero (Hierarchy.zero_iff_delta_zero.mp hφ)) f).of_iff
      fun v ↦ by simpa [← Matrix.fun_eq_vec_two v] using hiff v
  · have : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (t + 1) := ISigma.models_BSigma_succ
    intro Γ R hR
    exact StrictDefinable.of_definable (Γ' := 𝚺) hR

/-! ## Successor induction over the strict hierarchy -/

/-- The existential quantification of a `𝚷-[s]`-definable relation is defined by a strict
$\Sigma_{s + 1}$ formula. -/
private lemma exists_strictHierarchy_sigma_eval (hD : StrictlyDefinable V s) {P : V → Prop}
    {Q : V → V → Prop} (hQ : 𝚷-[s].DefinableRel Q) (hPQ : ∀ x, P x ↔ ∃ w, Q x w) :
    ∃ (φ : ArithmeticSemiformula ℕ 1) (f : ℕ → V),
      StrictHierarchy 𝚺 (s + 1) φ ∧ ∀ x, P x ↔ φ.Eval ![x] f := by
  obtain ⟨f, χ, hχ, hiff⟩ := (hD (Γ := 𝚷) hQ).exists_eval_iff
  have h : ∀ x y : V, Q x y ↔ χ.Eval ![x, y] f := fun x y ↦ by simpa using hiff ![x, y]
  refine ⟨∃¹ (χ ⇜ (#1 :> #0 :> (#·.succ.succ))), f,
    (StrictHierarchy.ofAlt (Γ := 𝚺) (hχ.rew _)).exs, fun x ↦ ?_⟩
  rw [hPQ x, Semiformula.eval_ex]
  exact exists_congr fun w ↦ (h x w).trans (Semiformula.eval_swap01 χ w x ![]).symm

/-- The universal quantification of a `𝚺-[s]`-definable relation is defined by a strict
$\Pi_{s + 1}$ formula. -/
private lemma exists_strictHierarchy_pi_eval (hD : StrictlyDefinable V s) {P : V → Prop}
    {Q : V → V → Prop} (hQ : 𝚺-[s].DefinableRel Q) (hPQ : ∀ x, P x ↔ ∀ w, Q x w) :
    ∃ (φ : ArithmeticSemiformula ℕ 1) (f : ℕ → V),
      StrictHierarchy 𝚷 (s + 1) φ ∧ ∀ x, P x ↔ φ.Eval ![x] f := by
  obtain ⟨f, χ, hχ, hiff⟩ := (hD (Γ := 𝚺) hQ).exists_eval_iff
  have h : ∀ x y : V, Q x y ↔ χ.Eval ![x, y] f := fun x y ↦ by simpa using hiff ![x, y]
  refine ⟨∀¹ (χ ⇜ (#1 :> #0 :> (#·.succ.succ))), f,
    (StrictHierarchy.ofAlt (Γ := 𝚷) (hχ.rew _)).all, fun x ↦ ?_⟩
  rw [hPQ x, Semiformula.eval_all]
  exact forall_congr' fun w ↦ (h x w).trans (Semiformula.eval_swap01 χ w x ![]).symm

/-- Every model of `𝗜 Γ s` satisfies the induction scheme for `StrictHierarchy Γ s`. -/
instance models_InductionScheme_strictHierarchy [V↓[ℒₒᵣ] ⊧* 𝗜 Γ s] :
    V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Arithmetic.StrictHierarchy Γ s) :=
  models_of_ss (U := 𝗜 Γ s) inferInstance Set.subset_union_right

/-- Successor induction for the existential quantification of a `𝚷-[s]`-definable relation, in a
model of `𝗜 𝚺 (s + 1)` whose `𝚷-[s]`-definable relations have strict definitions. -/
private lemma succ_induction_exists_pi_of_sigma [V↓[ℒₒᵣ] ⊧* 𝗜 𝚺 (s + 1)]
    (hD : StrictlyDefinable V s) {P : V → Prop} {Q : V → V → Prop}
    (hQ : 𝚷-[s].DefinableRel Q) (hPQ : ∀ x, P x ↔ ∃ w, Q x w)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  have ⟨φ, f, hφ, hiff⟩ := exists_strictHierarchy_sigma_eval hD hQ hPQ
  InductionScheme.succ_induction (C := Arithmetic.StrictHierarchy 𝚺 (s + 1))
    ⟨f, φ, hφ, hiff⟩ zero succ

/-- Successor induction for the universal quantification of a `𝚺-[s]`-definable relation, in a
model of `𝗜 𝚷 (s + 1)` whose `𝚺-[s]`-definable relations have strict definitions. -/
lemma succ_induction_forall_sigma [V↓[ℒₒᵣ] ⊧* 𝗜 𝚷 (s + 1)] (hD : StrictlyDefinable V s)
    {P : V → Prop} {Q : V → V → Prop} (hQ : 𝚺-[s].DefinableRel Q) (hPQ : ∀ x, P x ↔ ∀ w, Q x w)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  have ⟨φ, f, hφ, hiff⟩ := exists_strictHierarchy_pi_eval hD hQ hPQ
  InductionScheme.succ_induction (C := Arithmetic.StrictHierarchy 𝚷 (s + 1))
    ⟨f, φ, hφ, hiff⟩ zero succ

/-- Every model of `𝗜 Γ s` is a model of `𝗜𝚺₀`. -/
lemma models_ISigma_zero_of_models_InductionOnStrictHierarchy (V : Type*) [ORingStructure V]
    (Γ : Polarity) (s : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗜 Γ s] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ :=
  InductionOnStrictHierarchy_zero Γ ▸
    models_of_ss (U := 𝗜 Γ s) inferInstance (InductionOnStrictHierarchy_subset_mono (Nat.zero_le s))

/-- In a model of `𝗜 𝚷 (s + 1)`, a predicate that is the universal quantification of a
`𝚺-[s]`-definable relation, fails at `0`, and fails at `x + 1` whenever it fails at `x`, fails
everywhere.
- [HP98, Lemma I.2.12(2)] -/
private lemma neg_succ_induction [V↓[ℒₒᵣ] ⊧* 𝗜 𝚷 (s + 1)] (hD : StrictlyDefinable V s)
    {P : V → Prop} {Q : V → V → Prop} (hQ : 𝚺-[s].DefinableRel Q) (hPQ : ∀ x, P x ↔ ∀ w, Q x w)
    (nzero : ¬P 0) (nsucc : ∀ x, ¬P x → ¬P (x + 1)) : ∀ x, ¬P x := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
    models_of_ss (U := 𝗜 𝚷 (s + 1)) inferInstance Set.subset_union_left
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_ISigma_zero_of_models_InductionOnStrictHierarchy V 𝚷 (s + 1)
  have : 𝚺-[s].DefinableRel Q := hQ
  by_contra A
  obtain ⟨a, ha⟩ : ∃ x, P x := by simpa using A
  have key : ∀ x, x ≤ a → P (a - x) := by
    refine succ_induction_forall_sigma hD (P := fun x ↦ x ≤ a → P (a - x))
      (Q := fun x w ↦ x ≤ a → Q (a - x) w) ?_ ?_ ?_ ?_
    · apply HierarchySymbol.Definable.imp
      · apply HierarchySymbol.Definable.bcomp₂ (by definability) (by definability)
      · apply HierarchySymbol.Definable.bcomp₂ (by definability) (by definability)
    · intro x
      rw [imp_congr_right fun _ ↦ hPQ (a - x)]
      exact imp_forall_iff
    · intro _; simpa using ha
    · intro x ih hx
      have h : P (a - x) := ih (le_of_add_le_left hx)
      refine (not_imp_not.mp <| nsucc (a - (x + 1))) ?_
      rw [← Arithmetic.sub_sub, sub_add_self_of_le]
      · exact h
      · exact le_tsub_of_add_le_left hx
  exact nzero (by simpa using key a le_rfl)

/-- Successor induction for the existential quantification of a `𝚷-[s]`-definable relation, in a
model of `𝗜 𝚷 (s + 1)` whose `𝚷-[s]`-definable relations have strict definitions.
- [HP98, Lemma I.2.12(2)] -/
private lemma succ_induction_exists_pi_of_pi [V↓[ℒₒᵣ] ⊧* 𝗜 𝚷 (s + 1)]
    (hD : StrictlyDefinable V s) {P : V → Prop} {Q : V → V → Prop}
    (hQ : 𝚷-[s].DefinableRel Q) (hPQ : ∀ x, P x ↔ ∃ w, Q x w)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := by
  have h := neg_succ_induction (P := fun x ↦ ¬P x) (Q := fun x w ↦ ¬Q x w) hD
    (HierarchySymbol.Definable.not (Γ := 𝚺) hQ) (fun x ↦ by simp [hPQ x])
    (by simpa using zero) (fun x hx ↦ by simpa using succ x (by simpa using hx))
  intro x
  simpa using h x

/-- Successor induction for the existential quantification of a `𝚷-[s]`-definable relation, in a
model of `𝗜 Γ (s + 1)` whose `𝚷-[s]`-definable relations have strict definitions. -/
lemma succ_induction_exists_pi (Γ : Polarity) [V↓[ℒₒᵣ] ⊧* 𝗜 Γ (s + 1)]
    (hD : StrictlyDefinable V s) {P : V → Prop} {Q : V → V → Prop} (hQ : 𝚷-[s].DefinableRel Q)
    (hPQ : ∀ x, P x ↔ ∃ w, Q x w) (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := by
  rcases Γ with _ | _
  · exact succ_induction_exists_pi_of_sigma hD hQ hPQ zero succ
  · exact succ_induction_exists_pi_of_pi hD hQ hPQ zero succ

/-! ## Collection from induction over the strict hierarchy -/

/-- Being bounded below `y` by `w`, for a `𝚷-[s]`-definable relation, is `𝚷-[s]`-definable. -/
private lemma definable_bounded_below [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {R : V → V → Prop}
    (hR : 𝚷-[s].DefinableRel R) (a : V) :
    𝚷-[s].DefinableRel fun y w ↦ ∀ x < y, x < a → ∃ u ≤ w, R x u := by
  have h₁ : 𝚷-[s].Definable fun w : Fin 4 → V ↦ R (w 1) (w 0) := hR.retraction ![1, 0]
  have h₂ : 𝚷-[s].Definable fun w : Fin 3 → V ↦ ∃ u ≤ w 2, R (w 0) u :=
    (HierarchySymbol.Definable.bexs' (P := fun v u ↦ R (v 0) u) h₁
      (#2 : ArithmeticSemiterm V 3)).of_iff (by intro w; simp)
  have hlt : 𝚺-[s].Definable fun w : Fin 3 → V ↦ w 0 < a :=
    HierarchySymbol.Definable.of_iff
      (HierarchySymbol.Definable.retractiont 3
        (inferInstance : 𝚺-[s].DefinableRel (LT.lt : V → V → Prop)) ![#0, &a])
      (by intro w; simp)
  have h₃ : 𝚷-[s].Definable fun w : Fin 3 → V ↦ w 0 < a → ∃ u ≤ w 2, R (w 0) u :=
    HierarchySymbol.Definable.imp hlt h₂
  exact (HierarchySymbol.Definable.ball (P := fun v x ↦ x < a → ∃ u ≤ v 1, R x u) h₃
    (#0 : ArithmeticSemiterm V 2)).of_iff (by intro v; simp)

/-- Witnesses of a `𝚷-[s]`-definable relation below `a` admit a common bound, in a model of
`𝗜 Γ (s + 1)` whose `𝚷-[s]`-definable relations have strict definitions.
- [HP98, Lemma I.2.11] -/
lemma exists_bound_of_definable_pi (Γ : Polarity) [V↓[ℒₒᵣ] ⊧* 𝗜 Γ (s + 1)]
    (hD : StrictlyDefinable V s) {R : V → V → Prop} (hR : 𝚷-[s].DefinableRel R) (a : V)
    (h : ∀ x < a, ∃ u, R x u) : ∃ w, ∀ x < a, ∃ u ≤ w, R x u := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
    models_of_ss (U := 𝗜 Γ (s + 1)) inferInstance Set.subset_union_left
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_ISigma_zero_of_models_InductionOnStrictHierarchy V Γ (s + 1)
  have key : ∀ y : V, ∃ w, ∀ x < y, x < a → ∃ u ≤ w, R x u := by
    refine succ_induction_exists_pi Γ hD (definable_bounded_below hR a) (fun _ ↦ Iff.rfl) ?_ ?_
    · exact ⟨0, fun x hx _ ↦ absurd hx (by simp)⟩
    · rintro y ⟨w, hw⟩
      rcases lt_or_ge y a with hya | hya
      · obtain ⟨u₀, hu₀⟩ := h y hya
        refine ⟨max w u₀, ?_⟩
        intro x hx _
        rcases le_iff_lt_or_eq.mp (Arithmetic.lt_succ_iff_le.mp hx) with hx | rfl
        · obtain ⟨u, hu, hu'⟩ := hw x hx (lt_trans hx hya)
          exact ⟨u, le_trans hu (le_max_left w u₀), hu'⟩
        · exact ⟨u₀, le_max_right w u₀, hu₀⟩
      · refine ⟨w, ?_⟩
        intro x hx hxa
        rcases le_iff_lt_or_eq.mp (Arithmetic.lt_succ_iff_le.mp hx) with hx | rfl
        · exact hw x hx hxa
        · exact absurd hxa (not_lt.mpr hya)
  obtain ⟨w, hw⟩ := key (a + 1)
  exact ⟨w, fun x hx ↦ hw x (lt_trans hx (lt_add_one a)) hx⟩

/-- Every model of `𝗜 Γ (s + 1)` whose `𝚷-[s]`-definable relations have strict definitions is a
model of `𝗕𝚷 s`.
- [HP98, Lemma I.2.11] -/
lemma models_BPi_of_strictlyDefinable (Γ : Polarity) [V↓[ℒₒᵣ] ⊧* 𝗜 Γ (s + 1)]
    (hD : StrictlyDefinable V s) : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 s := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
    models_of_ss (U := 𝗜 Γ (s + 1)) inferInstance Set.subset_union_left
  have h₀ : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_ISigma_zero_of_models_InductionOnStrictHierarchy V Γ (s + 1)
  have h₁ : V↓[ℒₒᵣ] ⊧* CollectionScheme (Hierarchy 𝚷 s) :=
    CollectionScheme.models_of_collection fun hR a h ↦
      have ⟨w, hw⟩ := exists_bound_of_definable_pi Γ hD hR a h
      ⟨w + 1, fun x hx ↦ (hw x hx).imp fun y hy ↦
        ⟨Arithmetic.lt_succ_iff_le.mpr hy.1, hy.2⟩⟩
  exact Semantics.ModelsSet.union_iff.mpr
    ⟨h₀, models_of_ss h₁ (CollectionScheme_subset (·.hierarchy))⟩

/-- Every model of `𝗜 Γ (s + 1)` whose `𝚷-[s]`-definable relations have strict definitions
satisfies `𝗜𝚺 (s + 1)`.
- [HP98, Theorem I.2.4]
- [HP98, Lemma I.2.9] -/
private lemma models_ISigma_succ_of_strictlyDefinable (Γ : Polarity) [V↓[ℒₒᵣ] ⊧* 𝗜 Γ (s + 1)]
    (hD : StrictlyDefinable V s) : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) := by
  have hPA : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
    models_of_ss (U := 𝗜 Γ (s + 1)) inferInstance Set.subset_union_left
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 s := models_BPi_of_strictlyDefinable Γ hD
  suffices V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Hierarchy 𝚺 (s + 1)) by
    simpa [ISigma, InductionOnHierarchy, Semantics.ModelsSet.union_iff] using ⟨hPA, this⟩
  simp only [InductionScheme]
  apply Semantics.ModelsSet.setOf_iff.mpr
  rintro _ ⟨φ, hφ, rfl⟩
  suffices ∀ f : ℕ → V, φ.Eval ![0] f → (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) →
      ∀ x, φ.Eval ![x] f by
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this
  intro f
  obtain ⟨Q, hQ, hiff⟩ := exists_pi_definableRel_iff (definablePred_of_hierarchy hφ f)
  exact succ_induction_exists_pi Γ hD hQ hiff

/-! ## The two induction schemes agree -/

/-- Every model of `𝗜 𝚺 s` satisfies `𝗜𝚺 s`.
- [HP98, Theorem I.2.4] -/
private lemma models_ISigma_of_models_InductionOnStrictHierarchy_sigma :
    ∀ (s : ℕ) (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜 𝚺 s], V↓[ℒₒᵣ] ⊧* 𝗜𝚺s := by
  intro s
  induction s with
  | zero => intro V _ _; exact InductionOnStrictHierarchy_zero 𝚺 ▸ ‹_›
  | succ t ih =>
    intro V _ _
    have : V↓[ℒₒᵣ] ⊧* 𝗜 𝚺 t :=
      models_of_ss inferInstance (InductionOnStrictHierarchy_subset_mono (Nat.le_succ t))
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺t := ih V
    exact models_ISigma_succ_of_strictlyDefinable 𝚺 (strictlyDefinable_of_models_ISigma V)

/-- Every model of `𝗜 Γ s` satisfies `𝗜𝚺 s`.
- [HP98, Theorem I.2.4] -/
lemma models_ISigma_of_models_InductionOnStrictHierarchy (Γ : Polarity) (s : ℕ) (V : Type*)
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜 Γ s] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺s := by
  rcases s with _ | t
  · exact InductionOnStrictHierarchy_zero Γ ▸ ‹_›
  · have : V↓[ℒₒᵣ] ⊧* 𝗜 𝚺 t :=
      models_of_ss inferInstance
        (InductionOnStrictHierarchy_subset_of_lt (Γ' := Γ) (Nat.lt_succ_self t))
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺t := models_ISigma_of_models_InductionOnStrictHierarchy_sigma t V
    exact models_ISigma_succ_of_strictlyDefinable Γ (strictlyDefinable_of_models_ISigma V)

/-- Induction for the broad hierarchy follows from induction for the strict one.
- [HP98, Theorem I.2.4] -/
theorem InductionOnHierarchy_weakerThan_InductionOnStrictHierarchy (Γ : Polarity) (s : ℕ) :
    𝗜𝗡𝗗 Γ s ⪯ 𝗜 Γ s :=
  weakerThan_of_models.{0} _ _ fun V _ _ ↦
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺s := models_ISigma_of_models_InductionOnStrictHierarchy Γ s V
    inferInstance

/-- `𝗜 Γ s` and `𝗜𝗡𝗗 Γ s` are the same theory.
- [HP98, Theorem I.2.4] -/
theorem InductionOnStrictHierarchy_equiv_InductionOnHierarchy (Γ : Polarity) (s : ℕ) :
    𝗜 Γ s ≊ 𝗜𝗡𝗗 Γ s :=
  Equiv.antisymm_iff.mpr
    ⟨inferInstance, InductionOnHierarchy_weakerThan_InductionOnStrictHierarchy Γ s⟩

/-- `𝗜𝚺 s` is at most as strong as the induction scheme for strict $\Sigma_s$ formulas.
- [HP98, Theorem I.2.4] -/
instance ISigma_weakerThan_InductionOnStrictHierarchy (s : ℕ) : 𝗜𝚺s ⪯ 𝗜 𝚺 s :=
  InductionOnHierarchy_weakerThan_InductionOnStrictHierarchy 𝚺 s

/-- Every model of `𝗜 𝚺 (s + 1)` is a model of `𝗕𝚺 (s + 1)`.
- [HP98, Lemma I.2.11] -/
theorem models_BSigma_succ_of_models_InductionOnStrictHierarchy {V : Type*} [ORingStructure V]
    {s : ℕ} [V↓[ℒₒᵣ] ⊧* 𝗜 𝚺 (s + 1)] : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (s + 1) :=
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) :=
    models_ISigma_of_models_InductionOnStrictHierarchy 𝚺 (s + 1) V
  ISigma.models_BSigma_succ

/-! ## The `Δ` induction scheme -/

/-- Every model of `𝗜𝚫 (n + 1)` satisfies `𝗜 𝚺 n`: a strict $\Sigma_n$ formula and its negation
are an admissible pair for the `Δ` induction axiom.
- [Sla04, §1.2] -/
private lemma models_InductionOnStrictHierarchy_of_models_IDelta_succ (n : ℕ) (V : Type*)
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚫 (n + 1)] : V↓[ℒₒᵣ] ⊧* 𝗜 𝚺 n := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_of_ss (U := 𝗜𝚫 (n + 1)) inferInstance Set.subset_union_left
  have hPA : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (s := 0)
  suffices V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (StrictHierarchy 𝚺 n) by
    simpa [InductionOnStrictHierarchy, Semantics.ModelsSet.union_iff] using ⟨hPA, this⟩
  simp only [InductionScheme]
  apply Semantics.ModelsSet.setOf_iff.mpr
  rintro _ ⟨φ, hφ, rfl⟩
  have hax : V↓[ℒₒᵣ] ⊧ (.univCl (deltaInd φ (∼φ)) : ArithmeticSentence) :=
    models_of_mem (T := 𝗜𝚫 (n + 1)) (Set.mem_union_right _
      (mem_DeltaInductionScheme_of_mem (hφ.mono (Nat.le_succ n))
        (StrictHierarchy.ofAlt (Γ := 𝚺) hφ.neg)))
  suffices ∀ f : ℕ → V, φ.Eval ![0] f → (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) →
      ∀ x, φ.Eval ![x] f by
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this
  intro f
  exact (models_deltaInd_iff φ (∼φ)).mp hax f (by simp)

/-- `𝗜𝚺 n` is at most as strong as `𝗜𝚫 (n + 1)`.
- [Sla04, §1.2] -/
theorem ISigma_weakerThan_IDelta_succ (n : ℕ) : 𝗜𝚺n ⪯ 𝗜𝚫 (n + 1) :=
  weakerThan_of_models.{0} _ _ fun V _ _ ↦
    have : V↓[ℒₒᵣ] ⊧* 𝗜 𝚺 n := models_InductionOnStrictHierarchy_of_models_IDelta_succ n V
    models_ISigma_of_models_InductionOnStrictHierarchy 𝚺 n V

end FFL.FirstOrder.Arithmetic
