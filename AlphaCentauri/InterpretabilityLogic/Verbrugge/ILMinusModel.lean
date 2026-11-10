module

public import AlphaCentauri.InterpretabilityLogic.MaximalConsistentSet
public import AlphaCentauri.InterpretabilityLogic.Veltman.IndexedSetModel
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinus

/-!
# The $\mathbf{IL}^-_{\mathrm{set}}$-models on labelled and indexed sets

Finite $\mathbf{IL}^-_{\mathrm{set}}$-models whose worlds are maximal consistent subsets of an
adequate set, labelled by a formula or indexed by a finite sequence of formulas, their truth
lemmas, and the completeness of eight sublogics of $\mathbf{IL}$ with respect to finite
$\mathbf{IL}^-_{\mathrm{set}}$-frames.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula MaximalConsistentSet

namespace Verbrugge

/-! ### The truth lemma -/

section TruthLemma

open Model Model.World

variable {κ α : Type*} [DecidableEq α] [Nonempty κ] {L : Logic α} [Entailment.Cl L]
  {Φ : Finset (Formula α)} [Adequate Φ] {M : Model κ α} {f : κ → MaximalConsistentSet L Φ}

/-- A model whose worlds are sent to maximal consistent subsets of `Φ` so that atoms, `□` and `▷`
agree with membership forces exactly the formulas of `Φ` in the set of each world. -/
lemma forces_iff_mem_of (hval : ∀ {x : M.World} {a}, M x a ↔ #a ∈ f x)
    (hbox₁ : ∀ {x y : M.World} {A}, x ≺ y → □A ∈ f x → A ∈ f y)
    (hbox₂ : ∀ {x : M.World} {A}, □A ∈ Φ → □A ∉ f x → ∃ y, x ≺ y ∧ A ∉ f y)
    (hrhd₁ : ∀ {x y : M.World} {A B}, A ▷ B ∈ f x → x ≺ y → A ∈ f y →
      ∃ V, y ≺[x] V ∧ ∀ z ∈ V, B ∈ f z)
    (hrhd₂ : ∀ {x : M.World} {A B}, A ▷ B ∈ Φ → A ▷ B ∉ f x →
      ∃ y, x ≺ y ∧ A ∈ f y ∧ ∀ V, y ≺[x] V → ∃ z ∈ V, B ∉ f z)
    {x : M.World} {A : Formula α} (hA : A ∈ Φ) : x ⊩ A ↔ A ∈ f x := by
  induction A generalizing x with
  | atom a => exact hval;
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
      obtain ⟨y, Rxy, hy⟩ := hbox₂ hA hn;
      exact hy <| (ih hA').mp <| h y Rxy;
    · intro h y Rxy;
      exact (ih hA').mpr <| hbox₁ Rxy h;
  | rhd B C ihB ihC =>
    have hB := Adequate.rhd_left hA;
    have hC := Adequate.rhd_right hA;
    constructor;
    · intro h;
      by_contra hn;
      obtain ⟨y, Rxy, hy, hV⟩ := hrhd₂ hA hn;
      obtain ⟨V, hS, hV'⟩ := h y Rxy ((ihB hB).mpr hy);
      obtain ⟨z, hz, hz'⟩ := hV V hS;
      exact hz' <| (ihC hC).mp (hV' z hz);
    · intro h y Rxy hy;
      obtain ⟨V, hS, hV⟩ := hrhd₁ h Rxy ((ihB hB).mp hy);
      use V;
      constructor;
      · exact hS;
      · intro z hz;
        exact (ihC hC).mpr (hV z hz);

end TruthLemma

/-! ### Labelled maximal consistent sets -/

variable {α : Type*} [DecidableEq α]

/-- A maximal consistent subset of `Φ` together with an antecedent or consequent of a `▷`-formula
in `Φ`.

- [KO21, Theorem 7.1]
-/
structure LabelledSet (L : Logic α) (Φ : Finset (Formula α)) where
  set : MaximalConsistentSet L Φ
  label : Formula α
  isRhdOperand_label : IsRhdOperand Φ label

namespace LabelledSet

variable {L : Logic α} {Φ : Finset (Formula α)}

instance [Adequate Φ] : Finite (LabelledSet L Φ) := by
  apply Finite.of_injective (β := MaximalConsistentSet L Φ × Φ)
    fun x ↦ (x.set, ⟨x.label, x.isRhdOperand_label.mem⟩);
  rintro ⟨Γ, A, hA⟩ ⟨Δ, B, hB⟩ h;
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h;
  obtain ⟨rfl, rfl⟩ := h;
  rfl

/-- The $\mathbf{IL}^-_{\mathrm{set}}$-model on labelled sets in which `y ≺[x] V` holds when `y`
and some element of `V` are successors of `x` and `P x y V` holds.

- [KO21, Theorem 7.1]
-/
def model (P : LabelledSet L Φ → LabelledSet L Φ → Set (LabelledSet L Φ) → Prop)
    [Nonempty (LabelledSet L Φ)] : Model (LabelledSet L Φ) α where
  Rel' x y := Successor x.set y.set
  S' x y V := Successor x.set y.set ∧ (∃ z ∈ V, Successor x.set z.set) ∧ P x y V
  Val' x a := #a ∈ x.set

/-- `y` is a weak `C`-critical successor of `x` for its label `C`. -/
abbrev IsWeakCritical (x y : LabelledSet L Φ) : Prop :=
  WeakCriticalSuccessor y.label x.set y.set

/-- - [KO21, Theorem 7.1] -/
def condJ4 (x y : LabelledSet L Φ) (V : Set (LabelledSet L Φ)) : Prop :=
  x.IsWeakCritical y → ∃ z ∈ V, y.label ∉ z.set

/-- - [KO21, Theorem 7.1] -/
def condJ4J5 (x y : LabelledSet L Φ) (V : Set (LabelledSet L Φ)) : Prop :=
  x.IsWeakCritical y → □(∼y.label) ∈ y.set → ∃ z ∈ V, y.label ∉ z.set

/-- - [KO21, Theorem 7.1] -/
def condJ2 (x y : LabelledSet L Φ) (V : Set (LabelledSet L Φ)) : Prop :=
  x.IsWeakCritical y →
    (∃ z ∈ V, y.label ∉ z.set) ∧ ∃ z ∈ V, z.label = y.label ∧ x.IsWeakCritical z

/-- - [KO21, Theorem 7.1] -/
def condJ2J4Plus (x y : LabelledSet L Φ) (V : Set (LabelledSet L Φ)) : Prop :=
  x.IsWeakCritical y →
    (∃ z ∈ V, Successor x.set z.set ∧ y.label ∉ z.set) ∧
      ∃ z ∈ V, z.label = y.label ∧ x.IsWeakCritical z

lemma condJ2_mono {x y : LabelledSet L Φ} {V Z : Set (LabelledSet L Φ)} (h : condJ2 x y V)
    (hVZ : V ⊆ Z) : condJ2 x y Z := by
  intro hc;
  obtain ⟨⟨z, hz, h₁⟩, ⟨w, hw, h₂⟩⟩ := h hc;
  exact ⟨⟨z, hVZ hz, h₁⟩, ⟨w, hVZ hw, h₂⟩⟩

lemma condJ2J4Plus_mono {x y : LabelledSet L Φ} {V Z : Set (LabelledSet L Φ)}
    (h : condJ2J4Plus x y V) (hVZ : V ⊆ Z) : condJ2J4Plus x y Z := by
  intro hc;
  obtain ⟨⟨z, hz, h₁⟩, ⟨w, hw, h₂⟩⟩ := h hc;
  exact ⟨⟨z, hVZ hz, h₁⟩, ⟨w, hVZ hw, h₂⟩⟩

section Frame

open Model

variable [Adequate Φ] [Nonempty (LabelledSet L Φ)]
  {P : LabelledSet L Φ → LabelledSet L Φ → Set (LabelledSet L Φ) → Prop}

lemma isILMinus (hP : ∀ {x y V Z}, P x y V → V ⊆ Z → P x y Z) : (model P).IsILMinus where
  trans _ _ _ h₁ h₂ := Successor.trans h₁ h₂
  cwf := by
    have : IsTrans _ (flip (model P).Rel) := ⟨fun _ _ _ h₁ h₂ ↦ Successor.trans h₂ h₁⟩;
    have : Std.Irrefl (flip (model P).Rel) := ⟨fun _ h ↦ Successor.irrefl h⟩;
    exact Finite.wellFounded_of_trans_of_irrefl _;
  rel_of_s h := h.1
  nonempty_of_s := by
    rintro _ _ _ ⟨-, ⟨z, hz, -⟩, -⟩;
    exact ⟨z, hz⟩;
  s_mono := by
    rintro _ _ _ _ ⟨h₁, ⟨z, hz, h₂⟩, h₃⟩ hVZ;
    exact ⟨h₁, ⟨z, hVZ hz, h₂⟩, hP h₃ hVZ⟩

instance : (model P).IsJ4 := ⟨fun h ↦ h.2.1⟩

instance : (model (condJ4 (L := L) (Φ := Φ))).IsILMinus := isILMinus <| by
  intro x y V Z h hVZ hc;
  obtain ⟨z, hz, h⟩ := h hc;
  exact ⟨z, hVZ hz, h⟩

instance : (model (condJ4J5 (L := L) (Φ := Φ))).IsILMinus := isILMinus <| by
  intro x y V Z h hVZ hc hb;
  obtain ⟨z, hz, h⟩ := h hc hb;
  exact ⟨z, hVZ hz, h⟩

instance : (model (condJ2 (L := L) (Φ := Φ))).IsILMinus := isILMinus condJ2_mono

instance : (model (condJ2J4Plus (L := L) (Φ := Φ))).IsILMinus := isILMinus condJ2J4Plus_mono

end Frame

section ILMinus

open Model Model.World Logic

variable {𝔸 : Set (Formula α)} [ILMinusAdequate Φ]
  [Nonempty (LabelledSet (ofAxiomsMinus 𝔸) Φ)]

omit [Nonempty (LabelledSet (ofAxiomsMinus 𝔸) Φ)] in
private lemma not_mem_label [(ILMinusJ1 : Logic α) ⪯ ofAxiomsMinus 𝔸]
    {x y : LabelledSet (ofAxiomsMinus 𝔸) Φ} (h : x.IsWeakCritical y) : y.label ∉ y.set :=
  h.not_mem <| (mem_iff_provable <|
    Adequate.rhd_mem y.isRhdOperand_label y.isRhdOperand_label).mpr <|
      Context.of <| WeakerThan.pbl (𝓢 := ILMinusJ1) ILMinusJ1.axiomJ1'

instance [(ILMinusJ1 : Logic α) ⪯ ofAxiomsMinus 𝔸] :
    (model (condJ4 (L := ofAxiomsMinus 𝔸) (Φ := Φ))).IsJ1 where
  s_refl {_ y} h := ⟨h, ⟨y, rfl, h⟩, fun hc ↦ ⟨y, rfl, not_mem_label hc⟩⟩

instance [(ILMinusJ1 : Logic α) ⪯ ofAxiomsMinus 𝔸] :
    (model (condJ4J5 (L := ofAxiomsMinus 𝔸) (Φ := Φ))).IsJ1 where
  s_refl {_ y} h := ⟨h, ⟨y, rfl, h⟩, fun hc _ ↦ ⟨y, rfl, not_mem_label hc⟩⟩

instance : (model (condJ4J5 (L := ofAxiomsMinus 𝔸) (Φ := Φ))).IsJ5 where
  s_of_rel {_ _ z} h₁ h₂ :=
    ⟨h₁, ⟨z, rfl, h₁.trans h₂⟩, fun _ hb ↦ ⟨z, rfl, h₂.not_mem_of_box_neg_mem hb⟩⟩

omit [ILMinusAdequate Φ] [Nonempty (LabelledSet (ofAxiomsMinus 𝔸) Φ)] in
private lemma subset_biUnion {x v : LabelledSet (ofAxiomsMinus 𝔸) Φ}
    {V : Set (LabelledSet (ofAxiomsMinus 𝔸) Φ)}
    {Z : LabelledSet (ofAxiomsMinus 𝔸) Φ → Set (LabelledSet (ofAxiomsMinus 𝔸) Φ)}
    (hv : v ∈ V) (Rxv : Successor x.set v.set) :
    Z v ⊆ ⋃ v ∈ {v ∈ V | Successor x.set v.set}, Z v :=
  fun _ hw ↦ Set.mem_biUnion (x := v) ⟨hv, Rxv⟩ hw

instance : (model (condJ2 (L := ofAxiomsMinus 𝔸) (Φ := Φ))).IsJ2 where
  s_trans {x y V} Z hS hZ := by
    obtain ⟨Rxy, ⟨z, hz, Rxz⟩, hP⟩ := hS;
    obtain ⟨-, ⟨w, hw, Rxw⟩, -⟩ := hZ z hz Rxz;
    have hP' : condJ2 x y (⋃ v ∈ {v ∈ V | Successor x.set v.set}, Z v) := by
      intro hc;
      obtain ⟨-, ⟨v, hv, hvl, hvc⟩⟩ := hP hc;
      obtain ⟨-, -, hPv⟩ := hZ v hv hvc.toSuccessor;
      have := condJ2_mono hPv (subset_biUnion (Z := Z) hv hvc.toSuccessor) hvc;
      rw [hvl] at this;
      exact this;
    exact ⟨Rxy, ⟨w, subset_biUnion (Z := Z) hz Rxz hw, Rxw⟩, hP'⟩

instance : (model (condJ2J4Plus (L := ofAxiomsMinus 𝔸) (Φ := Φ))).IsJ2 where
  s_trans {x y V} Z hS hZ := by
    obtain ⟨Rxy, ⟨z, hz, Rxz⟩, hP⟩ := hS;
    obtain ⟨-, ⟨w, hw, Rxw⟩, -⟩ := hZ z hz Rxz;
    have hP' : condJ2J4Plus x y (⋃ v ∈ {v ∈ V | Successor x.set v.set}, Z v) := by
      intro hc;
      obtain ⟨-, ⟨v, hv, hvl, hvc⟩⟩ := hP hc;
      obtain ⟨-, -, hPv⟩ := hZ v hv hvc.toSuccessor;
      have := condJ2J4Plus_mono hPv (subset_biUnion (Z := Z) hv hvc.toSuccessor) hvc;
      rw [hvl] at this;
      exact this;
    exact ⟨Rxy, ⟨w, subset_biUnion (Z := Z) hz Rxz hw, Rxw⟩, hP'⟩

instance : (model (condJ2J4Plus (L := ofAxiomsMinus 𝔸) (Φ := Φ))).IsJ4Plus where
  s_inter {x y V} hS := by
    obtain ⟨Rxy, ⟨z, hz, Rxz⟩, hP⟩ := hS;
    have hP' : condJ2J4Plus x y {v ∈ V | Successor x.set v.set} := by
      intro hc;
      obtain ⟨⟨u, hu, Rxu, hu'⟩, ⟨v, hv, hvl, hvc⟩⟩ := hP hc;
      exact ⟨⟨u, ⟨hu, Rxu⟩, Rxu, hu'⟩, ⟨v, ⟨hv, hvc.toSuccessor⟩, hvl, hvc⟩⟩;
    exact ⟨Rxy, ⟨z, ⟨hz, Rxz⟩, Rxz⟩, hP'⟩

private lemma exists_successor_not_mem {P : LabelledSet (ofAxiomsMinus 𝔸) Φ →
      LabelledSet (ofAxiomsMinus 𝔸) Φ → Set (LabelledSet (ofAxiomsMinus 𝔸) Φ) → Prop}
    {x : (model P).World} {A : Formula α} (h₁ : □A ∈ Φ) (h₂ : □A ∉ x.set) :
    ∃ y, x ≺ y ∧ A ∉ y.set := by
  obtain ⟨Δ, hΔ, hA⟩ := exists_box_not_mem h₁ h₂;
  use ⟨Δ, ⊥, .bot⟩
  exact ⟨hΔ, hA⟩

/-- - [KO21, Lemma 7.3] -/
lemma truthlemma_condJ4 [(ILMinusJ4 : Logic α) ⪯ ofAxiomsMinus 𝔸]
    {x : (model (condJ4 (L := ofAxiomsMinus 𝔸) (Φ := Φ))).World} {A : Formula α} (hA : A ∈ Φ) :
    x ⊩ A ↔ A ∈ x.set := by
  apply forces_iff_mem_of (f := LabelledSet.set) Iff.rfl
    (fun h₁ h₂ ↦ Successor.mem_of_box_mem h₁ h₂) exists_successor_not_mem _ _ hA;
  · intro x y D E hDE Rxy hD;
    obtain ⟨Θ, hΘ, hEΘ⟩ := Successor.exists_successor_of_rhd_mem hDE Rxy hD;
    by_cases hc : x.IsWeakCritical y;
    · obtain ⟨Λ, hEΛ, hFΛ⟩ := hc.exists_mem_not_mem y.isRhdOperand_label hDE hD;
      use {⟨Θ, _, y.isRhdOperand_label⟩, ⟨Λ, _, y.isRhdOperand_label⟩}
      constructor
      · exact ⟨Rxy, ⟨_, .inl rfl, hΘ⟩, fun _ ↦ ⟨_, .inr rfl, hFΛ⟩⟩
      · rintro z (rfl | rfl) <;> assumption
    · use {⟨Θ, _, y.isRhdOperand_label⟩}
      constructor
      · exact ⟨Rxy, ⟨_, rfl, hΘ⟩, fun h ↦ absurd h hc⟩
      · rintro z rfl; exact hEΘ
  · intro x D E h₁ h₂;
    obtain ⟨Δ, hΔ, hD⟩ := exists_weakCriticalSuccessor_of_rhd_not_mem h₁ h₂;
    use ⟨Δ, E, .of_rhd_right h₁⟩
    exact ⟨hΔ.toSuccessor, hD, fun _ hS ↦ hS.2.2 hΔ⟩

/-- - [KO21, Lemma 7.3] -/
lemma truthlemma_condJ4J5 [(ILMinusJ4 : Logic α) ⪯ ofAxiomsMinus 𝔸]
    [(ILMinusJ5 : Logic α) ⪯ ofAxiomsMinus 𝔸]
    {x : (model (condJ4J5 (L := ofAxiomsMinus 𝔸) (Φ := Φ))).World} {A : Formula α}
    (hA : A ∈ Φ) : x ⊩ A ↔ A ∈ x.set := by
  apply forces_iff_mem_of (f := LabelledSet.set) Iff.rfl
    (fun h₁ h₂ ↦ Successor.mem_of_box_mem h₁ h₂) exists_successor_not_mem _ _ hA;
  · intro x y D E hDE Rxy hD;
    obtain ⟨Θ, hΘ, hEΘ⟩ := Successor.exists_successor_of_rhd_mem hDE Rxy hD;
    by_cases hc : x.IsWeakCritical y;
    · obtain ⟨Λ, hEΛ, hFΛ⟩ := hc.exists_mem_not_mem y.isRhdOperand_label hDE hD;
      use {⟨Θ, _, y.isRhdOperand_label⟩, ⟨Λ, _, y.isRhdOperand_label⟩}
      constructor
      · exact ⟨Rxy, ⟨_, .inl rfl, hΘ⟩, fun _ _ ↦ ⟨_, .inr rfl, hFΛ⟩⟩
      · rintro z (rfl | rfl) <;> assumption
    · use {⟨Θ, _, y.isRhdOperand_label⟩}
      constructor
      · exact ⟨Rxy, ⟨_, rfl, hΘ⟩, fun h ↦ absurd h hc⟩
      · rintro z rfl; exact hEΘ
  · intro x D E h₁ h₂;
    obtain ⟨Δ, hΔ, hD, hb⟩ := exists_weakCriticalSuccessor_box_neg_of_rhd_not_mem h₁ h₂;
    use ⟨Δ, E, .of_rhd_right h₁⟩
    exact ⟨hΔ.toSuccessor, hD, fun _ hS ↦ hS.2.2 hΔ hb⟩

/-- - [KO21, Lemma 7.3] -/
lemma truthlemma_condJ2 [(ILMinusJ2 : Logic α) ⪯ ofAxiomsMinus 𝔸]
    [(ILMinusJ4 : Logic α) ⪯ ofAxiomsMinus 𝔸]
    {x : (model (condJ2 (L := ofAxiomsMinus 𝔸) (Φ := Φ))).World} {A : Formula α} (hA : A ∈ Φ) :
    x ⊩ A ↔ A ∈ x.set := by
  apply forces_iff_mem_of (f := LabelledSet.set) Iff.rfl
    (fun h₁ h₂ ↦ Successor.mem_of_box_mem h₁ h₂) exists_successor_not_mem _ _ hA;
  · intro x y D E hDE Rxy hD;
    by_cases hc : x.IsWeakCritical y;
    · obtain ⟨Θ, hΘ, hEΘ⟩ :=
        hc.exists_weakCriticalSuccessor_of_rhd_mem y.isRhdOperand_label hDE hD;
      obtain ⟨Λ, hEΛ, hFΛ⟩ := hc.exists_mem_not_mem y.isRhdOperand_label hDE hD;
      use {⟨Θ, _, y.isRhdOperand_label⟩, ⟨Λ, _, y.isRhdOperand_label⟩}
      constructor
      · exact ⟨Rxy, ⟨_, .inl rfl, hΘ.toSuccessor⟩,
          fun _ ↦ ⟨⟨_, .inr rfl, hFΛ⟩, ⟨_, .inl rfl, rfl, hΘ⟩⟩⟩
      · rintro z (rfl | rfl) <;> assumption
    · obtain ⟨Θ, hΘ, hEΘ⟩ := Successor.exists_successor_of_rhd_mem hDE Rxy hD;
      use {⟨Θ, _, y.isRhdOperand_label⟩}
      constructor
      · exact ⟨Rxy, ⟨_, rfl, hΘ⟩, fun h ↦ absurd h hc⟩
      · rintro z rfl; exact hEΘ
  · intro x D E h₁ h₂;
    obtain ⟨Δ, hΔ, hD⟩ := exists_weakCriticalSuccessor_of_rhd_not_mem h₁ h₂;
    use ⟨Δ, E, .of_rhd_right h₁⟩
    exact ⟨hΔ.toSuccessor, hD, fun _ hS ↦ (hS.2.2 hΔ).1⟩

/-- - [KO21, Lemma 7.3] -/
lemma truthlemma_condJ2J4Plus [(ILMinusJ2 : Logic α) ⪯ ofAxiomsMinus 𝔸]
    [(ILMinusJ4 : Logic α) ⪯ ofAxiomsMinus 𝔸] [(ILMinusJ4Plus : Logic α) ⪯ ofAxiomsMinus 𝔸]
    {x : (model (condJ2J4Plus (L := ofAxiomsMinus 𝔸) (Φ := Φ))).World} {A : Formula α}
    (hA : A ∈ Φ) : x ⊩ A ↔ A ∈ x.set := by
  apply forces_iff_mem_of (f := LabelledSet.set) Iff.rfl
    (fun h₁ h₂ ↦ Successor.mem_of_box_mem h₁ h₂) exists_successor_not_mem _ _ hA;
  · intro x y D E hDE Rxy hD;
    by_cases hc : x.IsWeakCritical y;
    · obtain ⟨Θ, hΘ, hEΘ⟩ :=
        hc.exists_weakCriticalSuccessor_of_rhd_mem y.isRhdOperand_label hDE hD;
      obtain ⟨Λ, hΛ, hEΛ, hFΛ⟩ := hc.exists_successor_mem_not_mem y.isRhdOperand_label hDE hD;
      use {⟨Θ, _, y.isRhdOperand_label⟩, ⟨Λ, _, y.isRhdOperand_label⟩}
      constructor
      · exact ⟨Rxy, ⟨_, .inl rfl, hΘ.toSuccessor⟩,
          fun _ ↦ ⟨⟨_, .inr rfl, hΛ, hFΛ⟩, ⟨_, .inl rfl, rfl, hΘ⟩⟩⟩
      · rintro z (rfl | rfl) <;> assumption
    · obtain ⟨Θ, hΘ, hEΘ⟩ := Successor.exists_successor_of_rhd_mem hDE Rxy hD;
      use {⟨Θ, _, y.isRhdOperand_label⟩}
      constructor
      · exact ⟨Rxy, ⟨_, rfl, hΘ⟩, fun h ↦ absurd h hc⟩
      · rintro z rfl; exact hEΘ
  · intro x D E h₁ h₂;
    obtain ⟨Δ, hΔ, hD⟩ := exists_weakCriticalSuccessor_of_rhd_not_mem h₁ h₂;
    use ⟨Δ, E, .of_rhd_right h₁⟩
    exact ⟨hΔ.toSuccessor, hD, fun _ hS ↦ by
      obtain ⟨z, hz, -, hE⟩ := (hS.2.2 hΔ).1
      exact ⟨z, hz, hE⟩⟩

end ILMinus

end LabelledSet

/-! ### Indexed maximal consistent sets -/

namespace IndexedModel

open Veltman (IndexedSet)

variable {L : Logic α} {Φ : Finset (Formula α)}

/-- `y` is a `C`-critical successor of `x` containing `□∼C`, indexed by `C` after the sequence of
`x`. -/
def IsCriticalAfter (x y : IndexedSet L Φ) (C : Formula α) : Prop :=
  x.seq ++ [C] <+: y.seq ∧ CriticalSuccessor C x.set y.set ∧ □(∼C) ∈ y.set

lemma IsCriticalAfter.rel {x y : IndexedSet L Φ} {C : Formula α} (h : IsCriticalAfter x y C) :
    x.Rel y :=
  ⟨h.2.1.toSuccessor, (List.prefix_append _ _).trans h.1⟩

/-- The $\mathbf{IL}^-_{\mathrm{set}}$-model on indexed sets in which `y ≺[x] V` holds when `y`
and some element of `V` extend `x` and `P x C V` holds whenever `y` is critical for `C` after
`x`.

- [KO21, Theorem 7.4]
-/
def model (P : IndexedSet L Φ → Formula α → Set (IndexedSet L Φ) → Prop)
    [Nonempty (IndexedSet L Φ)] : Model (IndexedSet L Φ) α where
  Rel' := IndexedSet.Rel
  S' x y V := x.Rel y ∧ (∃ z ∈ V, x.Rel z) ∧ ∀ C, IsCriticalAfter x y C → P x C V
  Val' x a := #a ∈ x.set

/-- - [KO21, Theorem 7.4] -/
def condJ2J5 (x : IndexedSet L Φ) (C : Formula α) (V : Set (IndexedSet L Φ)) : Prop :=
  (∃ z ∈ V, C ∉ z.set) ∧ ∃ z ∈ V, IsCriticalAfter x z C

/-- - [KO21, Theorem 7.4] -/
def condJ2J4PlusJ5 (x : IndexedSet L Φ) (C : Formula α) (V : Set (IndexedSet L Φ)) : Prop :=
  (∃ z ∈ V, x.Rel z ∧ C ∉ z.set) ∧ ∃ z ∈ V, IsCriticalAfter x z C

lemma condJ2J5_mono {x : IndexedSet L Φ} {C : Formula α} {V Z : Set (IndexedSet L Φ)}
    (h : condJ2J5 x C V) (hVZ : V ⊆ Z) : condJ2J5 x C Z := by
  obtain ⟨⟨z, hz, h₁⟩, ⟨w, hw, h₂⟩⟩ := h;
  exact ⟨⟨z, hVZ hz, h₁⟩, ⟨w, hVZ hw, h₂⟩⟩

lemma condJ2J4PlusJ5_mono {x : IndexedSet L Φ} {C : Formula α} {V Z : Set (IndexedSet L Φ)}
    (h : condJ2J4PlusJ5 x C V) (hVZ : V ⊆ Z) : condJ2J4PlusJ5 x C Z := by
  obtain ⟨⟨z, hz, h₁⟩, ⟨w, hw, h₂⟩⟩ := h;
  exact ⟨⟨z, hVZ hz, h₁⟩, ⟨w, hVZ hw, h₂⟩⟩

private lemma subset_biUnion {x v : IndexedSet L Φ} {V : Set (IndexedSet L Φ)}
    {Z : IndexedSet L Φ → Set (IndexedSet L Φ)} (hv : v ∈ V) (Rxv : x.Rel v) :
    Z v ⊆ ⋃ v ∈ {v ∈ V | x.Rel v}, Z v :=
  fun _ hw ↦ Set.mem_biUnion (x := v) ⟨hv, Rxv⟩ hw

section Frame

open Model

variable [Adequate Φ] [Nonempty (IndexedSet L Φ)]
  {P : IndexedSet L Φ → Formula α → Set (IndexedSet L Φ) → Prop}

lemma isILMinus (hP : ∀ {x C V Z}, P x C V → V ⊆ Z → P x C Z) : (model P).IsILMinus where
  trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  cwf := by
    have : IsTrans _ (flip (model P).Rel) :=
      ⟨fun _ _ _ h₁ h₂ ↦ ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩⟩;
    have : Std.Irrefl (flip (model P).Rel) := ⟨fun _ h ↦ h.1.irrefl⟩;
    exact Finite.wellFounded_of_trans_of_irrefl _;
  rel_of_s h := h.1
  nonempty_of_s := by
    rintro _ _ _ ⟨-, ⟨z, hz, -⟩, -⟩;
    exact ⟨z, hz⟩;
  s_mono := by
    rintro _ _ _ _ ⟨h₁, ⟨z, hz, h₂⟩, h₃⟩ hVZ;
    exact ⟨h₁, ⟨z, hVZ hz, h₂⟩, fun C hC ↦ hP (h₃ C hC) hVZ⟩

instance : (model P).IsJ4 := ⟨fun h ↦ h.2.1⟩

instance : (model (condJ2J5 (L := L) (Φ := Φ))).IsILMinus := isILMinus condJ2J5_mono

instance : (model (condJ2J4PlusJ5 (L := L) (Φ := Φ))).IsILMinus :=
  isILMinus condJ2J4PlusJ5_mono

instance : (model (condJ2J5 (L := L) (Φ := Φ))).IsJ2 where
  s_trans {x y V} Z hS hZ := by
    obtain ⟨Rxy, ⟨z, hz, Rxz⟩, hP⟩ := hS;
    obtain ⟨-, ⟨w, hw, Rxw⟩, -⟩ := hZ z hz Rxz;
    have hP' (C : Formula α) (hC : IsCriticalAfter x y C) :
        condJ2J5 x C (⋃ v ∈ {v ∈ V | x.Rel v}, Z v) := by
      obtain ⟨-, ⟨v, hv, hvC⟩⟩ := hP C hC;
      obtain ⟨-, -, hPv⟩ := hZ v hv hvC.rel;
      exact condJ2J5_mono (hPv C hvC) (subset_biUnion (Z := Z) hv hvC.rel);
    exact ⟨Rxy, ⟨w, subset_biUnion (Z := Z) hz Rxz hw, Rxw⟩, hP'⟩

instance : (model (condJ2J4PlusJ5 (L := L) (Φ := Φ))).IsJ2 where
  s_trans {x y V} Z hS hZ := by
    obtain ⟨Rxy, ⟨z, hz, Rxz⟩, hP⟩ := hS;
    obtain ⟨-, ⟨w, hw, Rxw⟩, -⟩ := hZ z hz Rxz;
    have hP' (C : Formula α) (hC : IsCriticalAfter x y C) :
        condJ2J4PlusJ5 x C (⋃ v ∈ {v ∈ V | x.Rel v}, Z v) := by
      obtain ⟨-, ⟨v, hv, hvC⟩⟩ := hP C hC;
      obtain ⟨-, -, hPv⟩ := hZ v hv hvC.rel;
      exact condJ2J4PlusJ5_mono (hPv C hvC) (subset_biUnion (Z := Z) hv hvC.rel);
    exact ⟨Rxy, ⟨w, subset_biUnion (Z := Z) hz Rxz hw, Rxw⟩, hP'⟩

instance : (model (condJ2J4PlusJ5 (L := L) (Φ := Φ))).IsJ4Plus where
  s_inter {x y V} hS := by
    obtain ⟨Rxy, ⟨z, hz, Rxz⟩, hP⟩ := hS;
    have hP' (C : Formula α) (hC : IsCriticalAfter x y C) :
        condJ2J4PlusJ5 x C {v ∈ V | x.Rel v} := by
      obtain ⟨⟨u, hu, Rxu, hu'⟩, ⟨v, hv, hvC⟩⟩ := hP C hC;
      exact ⟨⟨u, ⟨hu, Rxu⟩, Rxu, hu'⟩, ⟨v, ⟨hv, hvC.rel⟩, hvC⟩⟩;
    exact ⟨Rxy, ⟨z, ⟨hz, Rxz⟩, Rxz⟩, hP'⟩

variable [Entailment.Cl L]

omit [Adequate Φ] [Nonempty (IndexedSet L Φ)] in
private lemma isCriticalAfter_of_rel {x y z : IndexedSet L Φ} {C : Formula α}
    (hC : IsCriticalAfter x y C) (h : y.Rel z) : IsCriticalAfter x z C :=
  ⟨hC.1.trans h.2, hC.2.1.trans_successor h.1, h.1.box_mem_of_box_mem hC.2.2⟩

instance : (model (condJ2J5 (L := L) (Φ := Φ))).IsJ5 where
  s_of_rel {_ _ z} h₁ h₂ := ⟨h₁, ⟨z, rfl, h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩,
    fun _ hC ↦ ⟨⟨z, rfl, h₂.1.not_mem_of_box_neg_mem hC.2.2⟩,
      ⟨z, rfl, isCriticalAfter_of_rel hC h₂⟩⟩⟩

instance : (model (condJ2J4PlusJ5 (L := L) (Φ := Φ))).IsJ5 where
  s_of_rel {_ _ z} h₁ h₂ := ⟨h₁, ⟨z, rfl, h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩,
    fun _ hC ↦ ⟨⟨z, rfl, ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩,
      h₂.1.not_mem_of_box_neg_mem hC.2.2⟩, ⟨z, rfl, isCriticalAfter_of_rel hC h₂⟩⟩⟩

end Frame

section ILMinus

open Model Model.World Logic

variable {𝔸 : Set (Formula α)} [ILMinusAdequate Φ] [Nonempty (IndexedSet (ofAxiomsMinus 𝔸) Φ)]

private lemma exists_successor_not_mem {P : IndexedSet (ofAxiomsMinus 𝔸) Φ → Formula α →
      Set (IndexedSet (ofAxiomsMinus 𝔸) Φ) → Prop}
    {x : (model P).World} {A : Formula α} (h₁ : □A ∈ Φ) (h₂ : □A ∉ x.set) :
    ∃ y, x ≺ y ∧ A ∉ y.set := by
  obtain ⟨Δ, hΔ, hA⟩ := exists_box_not_mem h₁ h₂;
  use x.successor Δ hΔ
  exact ⟨⟨hΔ, List.prefix_refl _⟩, hA⟩

omit [ILMinusAdequate Φ] [Nonempty (IndexedSet (ofAxiomsMinus 𝔸) Φ)] in
private lemma eq_of_isCriticalAfter {x y : IndexedSet (ofAxiomsMinus 𝔸) Φ} {C F : Formula α}
    (hC : IsCriticalAfter x y C) (hF : IsCriticalAfter x y F) : C = F := by
  have h := (List.prefix_of_prefix_length_le hC.1 hF.1 (by simp)).eq_of_length (by simp);
  simpa using h

variable [(ILMinusJ2 : Logic α) ⪯ ofAxiomsMinus 𝔸] [(ILMinusJ4 : Logic α) ⪯ ofAxiomsMinus 𝔸]
  [(ILMinusJ5 : Logic α) ⪯ ofAxiomsMinus 𝔸]

omit [(ILMinusJ4 : Logic α) ⪯ ofAxiomsMinus 𝔸] in
private lemma exists_rhd_not_mem {P : IndexedSet (ofAxiomsMinus 𝔸) Φ → Formula α →
      Set (IndexedSet (ofAxiomsMinus 𝔸) Φ) → Prop}
    (hP : ∀ {x C V}, P x C V → ∃ z ∈ V, C ∉ z.set)
    {x : (model P).World} {D E : Formula α} (h₁ : D ▷ E ∈ Φ) (h₂ : D ▷ E ∉ x.set) :
    ∃ y, x ≺ y ∧ D ∈ y.set ∧ ∀ V, y ≺[x] V → ∃ z ∈ V, E ∉ z.set := by
  obtain ⟨Δ, hΔ, hD, hb⟩ := exists_criticalSuccessor_box_neg_of_rhd_not_mem h₁ h₂;
  use x.criticalSuccessor E (.of_rhd_right h₁) Δ hΔ.toSuccessor
  exact ⟨⟨hΔ.toSuccessor, List.prefix_append _ _⟩, hD,
    fun _ hS ↦ hP <| hS.2.2 E ⟨List.prefix_refl _, hΔ, hb⟩⟩

/-- - [KO21, Lemma 7.6] -/
lemma truthlemma_condJ2J5
    {x : (model (condJ2J5 (L := ofAxiomsMinus 𝔸) (Φ := Φ))).World} {A : Formula α}
    (hA : A ∈ Φ) : x ⊩ A ↔ A ∈ x.set := by
  apply forces_iff_mem_of (f := Veltman.IndexedSet.set) Iff.rfl
    (fun h₁ h₂ ↦ Successor.mem_of_box_mem (And.left h₁) h₂) exists_successor_not_mem _
    (exists_rhd_not_mem fun h ↦ h.1) hA;
  intro x y D E hDE Rxy hD;
  by_cases hc : ∃ F, IsCriticalAfter x y F;
  · obtain ⟨F, hF⟩ := hc;
    have hFo : IsRhdOperand Φ F := y.isRhdOperand_of_mem_seq F <| hF.1.subset (by simp);
    obtain ⟨Θ, hΘ, hEΘ, hbΘ⟩ :=
      hF.2.1.weakCriticalSuccessor.exists_criticalSuccessor_box_neg_of_rhd_mem hFo hDE hD;
    obtain ⟨Λ, hEΛ, hFΛ⟩ := hF.2.1.weakCriticalSuccessor.exists_mem_not_mem hFo hDE hD;
    have hz₂ : IsCriticalAfter x (x.criticalSuccessor F hFo Θ hΘ.toSuccessor) F :=
      ⟨List.prefix_refl _, hΘ, hbΘ⟩;
    use {⟨Λ, [], by simp, by simp⟩, x.criticalSuccessor F hFo Θ hΘ.toSuccessor}
    constructor
    · exact ⟨Rxy, ⟨_, .inr rfl, hz₂.rel⟩, fun C hC ↦ by
        obtain rfl := eq_of_isCriticalAfter hC hF
        exact ⟨⟨_, .inl rfl, hFΛ⟩, ⟨_, .inr rfl, hz₂⟩⟩⟩
    · rintro z (rfl | rfl) <;> assumption
  · obtain ⟨Θ, hΘ, hEΘ⟩ := Successor.exists_successor_of_rhd_mem hDE Rxy.1 hD;
    use {x.successor Θ hΘ}
    constructor
    · exact ⟨Rxy, ⟨_, rfl, hΘ, List.prefix_refl _⟩, fun C hC ↦ absurd ⟨C, hC⟩ hc⟩
    · rintro z rfl; exact hEΘ

/-- - [KO21, Lemma 7.6] -/
lemma truthlemma_condJ2J4PlusJ5 [(ILMinusJ4Plus : Logic α) ⪯ ofAxiomsMinus 𝔸]
    {x : (model (condJ2J4PlusJ5 (L := ofAxiomsMinus 𝔸) (Φ := Φ))).World} {A : Formula α}
    (hA : A ∈ Φ) : x ⊩ A ↔ A ∈ x.set := by
  apply forces_iff_mem_of (f := Veltman.IndexedSet.set) Iff.rfl
    (fun h₁ h₂ ↦ Successor.mem_of_box_mem (And.left h₁) h₂) exists_successor_not_mem _
    (exists_rhd_not_mem fun h ↦ by obtain ⟨z, hz, -, h⟩ := h.1; exact ⟨z, hz, h⟩) hA;
  intro x y D E hDE Rxy hD;
  by_cases hc : ∃ F, IsCriticalAfter x y F;
  · obtain ⟨F, hF⟩ := hc;
    have hFo : IsRhdOperand Φ F := y.isRhdOperand_of_mem_seq F <| hF.1.subset (by simp);
    obtain ⟨Θ, hΘ, hEΘ, hbΘ⟩ :=
      hF.2.1.weakCriticalSuccessor.exists_criticalSuccessor_box_neg_of_rhd_mem hFo hDE hD;
    obtain ⟨Λ, hΛ, hEΛ, hFΛ⟩ :=
      hF.2.1.weakCriticalSuccessor.exists_successor_mem_not_mem hFo hDE hD;
    have hz₂ : IsCriticalAfter x (x.criticalSuccessor F hFo Θ hΘ.toSuccessor) F :=
      ⟨List.prefix_refl _, hΘ, hbΘ⟩;
    use {x.successor Λ hΛ, x.criticalSuccessor F hFo Θ hΘ.toSuccessor}
    constructor
    · exact ⟨Rxy, ⟨_, .inr rfl, hz₂.rel⟩, fun C hC ↦ by
        obtain rfl := eq_of_isCriticalAfter hC hF
        exact ⟨⟨_, .inl rfl, ⟨hΛ, List.prefix_refl _⟩, hFΛ⟩, ⟨_, .inr rfl, hz₂⟩⟩⟩
    · rintro z (rfl | rfl) <;> assumption
  · obtain ⟨Θ, hΘ, hEΘ⟩ := Successor.exists_successor_of_rhd_mem hDE Rxy.1 hD;
    use {x.successor Θ hΘ}
    constructor
    · exact ⟨Rxy, ⟨_, rfl, hΘ, List.prefix_refl _⟩, fun C hC ↦ absurd ⟨C, hC⟩ hc⟩
    · rintro z rfl; exact hEΘ

end ILMinus

end IndexedModel

end Verbrugge

/-! ### Completeness -/

namespace Logic

open Verbrugge Verbrugge.Model

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ4.complete_verbrugge
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ4] → M ⊧ A) :
    ILMinusJ4 ⊢ A := by
  classical
  by_contra hA;
  obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
  have : Nonempty (LabelledSet ILMinusJ4 (ilMinusAdequateClosure {A})) := ⟨⟨Γ, ⊥, .bot⟩⟩;
  exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
    (LabelledSet.truthlemma_condJ4 (x := ⟨Γ, ⊥, .bot⟩)
      (ilMinusAdequateClosure.subset (by simp))).mp <|
        h (LabelledSet.model LabelledSet.condJ4) ⟨Γ, ⊥, .bot⟩

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ1J4.complete_verbrugge
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ4] → M ⊧ A) :
    ILMinusJ1J4 ⊢ A := by
  classical
  by_contra hA;
  obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
  have : Nonempty (LabelledSet ILMinusJ1J4 (ilMinusAdequateClosure {A})) := ⟨⟨Γ, ⊥, .bot⟩⟩;
  exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
    (LabelledSet.truthlemma_condJ4 (x := ⟨Γ, ⊥, .bot⟩)
      (ilMinusAdequateClosure.subset (by simp))).mp <|
        h (LabelledSet.model LabelledSet.condJ4) ⟨Γ, ⊥, .bot⟩

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ4J5.complete_verbrugge
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ4] → [M.IsJ5] → M ⊧ A) :
    ILMinusJ4J5 ⊢ A := by
  classical
  by_contra hA;
  obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
  have : Nonempty (LabelledSet ILMinusJ4J5 (ilMinusAdequateClosure {A})) := ⟨⟨Γ, ⊥, .bot⟩⟩;
  exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
    (LabelledSet.truthlemma_condJ4J5 (x := ⟨Γ, ⊥, .bot⟩)
      (ilMinusAdequateClosure.subset (by simp))).mp <|
        h (LabelledSet.model LabelledSet.condJ4J5) ⟨Γ, ⊥, .bot⟩

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ1J4J5.complete_verbrugge
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ4] → [M.IsJ5] → M ⊧ A) :
    ILMinusJ1J4J5 ⊢ A := by
  classical
  by_contra hA;
  obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
  have : Nonempty (LabelledSet ILMinusJ1J4J5 (ilMinusAdequateClosure {A})) := ⟨⟨Γ, ⊥, .bot⟩⟩;
  exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
    (LabelledSet.truthlemma_condJ4J5 (x := ⟨Γ, ⊥, .bot⟩)
      (ilMinusAdequateClosure.subset (by simp))).mp <|
        h (LabelledSet.model LabelledSet.condJ4J5) ⟨Γ, ⊥, .bot⟩

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ2.complete_verbrugge
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → M ⊧ A) :
    ILMinusJ2 ⊢ A := by
  classical
  by_contra hA;
  obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
  have : Nonempty (LabelledSet ILMinusJ2 (ilMinusAdequateClosure {A})) := ⟨⟨Γ, ⊥, .bot⟩⟩;
  exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
    (LabelledSet.truthlemma_condJ2 (x := ⟨Γ, ⊥, .bot⟩)
      (ilMinusAdequateClosure.subset (by simp))).mp <|
        h (LabelledSet.model LabelledSet.condJ2) ⟨Γ, ⊥, .bot⟩

/-- - [KO21, Theorem 7.1] -/
theorem ILMinusJ2J4Plus.complete_verbrugge
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ4Plus] → M ⊧ A) :
    ILMinusJ2J4Plus ⊢ A := by
  classical
  by_contra hA;
  obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
  have : Nonempty (LabelledSet ILMinusJ2J4Plus (ilMinusAdequateClosure {A})) := ⟨⟨Γ, ⊥, .bot⟩⟩;
  exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
    (LabelledSet.truthlemma_condJ2J4Plus (x := ⟨Γ, ⊥, .bot⟩)
      (ilMinusAdequateClosure.subset (by simp))).mp <|
        h (LabelledSet.model LabelledSet.condJ2J4Plus) ⟨Γ, ⊥, .bot⟩

/-- - [KO21, Theorem 7.4] -/
theorem ILMinusJ2J5.complete_verbrugge
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ5] → M ⊧ A) :
    ILMinusJ2J5 ⊢ A := by
  classical
  by_contra hA;
  obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
  have : Nonempty (Veltman.IndexedSet ILMinusJ2J5 (ilMinusAdequateClosure {A})) :=
    ⟨⟨Γ, [], by simp, by simp⟩⟩;
  exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
    (IndexedModel.truthlemma_condJ2J5 (x := ⟨Γ, [], by simp, by simp⟩)
      (ilMinusAdequateClosure.subset (by simp))).mp <|
        h (IndexedModel.model IndexedModel.condJ2J5) ⟨Γ, [], by simp, by simp⟩

/-- - [KO21, Theorem 7.4] -/
theorem ILMinusJ2J4PlusJ5.complete_verbrugge
    (h : ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α),
      [M.IsILMinus] → [M.IsJ2] → [M.IsJ4Plus] → [M.IsJ5] → M ⊧ A) :
    ILMinusJ2J4PlusJ5 ⊢ A := by
  classical
  by_contra hA;
  obtain ⟨Γ, hΓ⟩ := exists_neg_consistent (Φ := ilMinusAdequateClosure {A}) hA;
  have : Nonempty (Veltman.IndexedSet ILMinusJ2J4PlusJ5 (ilMinusAdequateClosure {A})) :=
    ⟨⟨Γ, [], by simp, by simp⟩⟩;
  exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
    (IndexedModel.truthlemma_condJ2J4PlusJ5 (x := ⟨Γ, [], by simp, by simp⟩)
      (ilMinusAdequateClosure.subset (by simp))).mp <|
        h (IndexedModel.model IndexedModel.condJ2J4PlusJ5) ⟨Γ, [], by simp, by simp⟩

end Logic

end FFL.InterpretabilityLogic

end
