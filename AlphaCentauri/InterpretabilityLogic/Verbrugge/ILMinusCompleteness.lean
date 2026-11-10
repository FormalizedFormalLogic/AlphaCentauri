module

public import AlphaCentauri.InterpretabilityLogic.MaximalConsistentSet.ILMinus
public import AlphaCentauri.InterpretabilityLogic.Veltman.Completeness
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.ILMinus

/-!
# Completeness of sublogics of $\mathbf{IL}$ with respect to $\mathbf{IL}^-_{\mathrm{set}}$-frames

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

lemma exists_box_not_mem {α : Type*} [DecidableEq α] {L : Logic α} [Entailment.Cl L]
    [L.ExtendsGL] {Φ : Finset (Formula α)} [Adequate Φ] {Γ : MaximalConsistentSet L Φ}
    {A : Formula α} (h₁ : □A ∈ Φ) (h₂ : □A ∉ Γ) : ∃ Δ, Successor Γ Δ ∧ A ∉ Δ := by
  obtain ⟨Δ, hΔ, hc⟩ := exists_successor_of_box_not_mem h₁ h₂;
  exact ⟨Δ, hΔ, not_mem_of_provable_neg hc (Context.by_axm rfl)⟩

lemma exists_neg_consistent {α : Type*} [DecidableEq α] {L : Logic α} [Entailment.Cl L]
    {Φ : Finset (Formula α)} {A : Formula α} (h : L ⊬ A) :
    ∃ Γ : MaximalConsistentSet L Φ, ({∼A} ∪ Γ.literals) *⊬[L] ⊥ := by
  apply exists_consistent_union;
  intro h₁;
  apply h;
  have h₂ : L ⊢ ∼A 🡒 ⊥ := Context.emptyPrf <| Context.deduct <| by simpa using h₁;
  cl_prover [h₂];

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
  exact ⟨⟨Δ, ⊥, .bot⟩, hΔ, hA⟩

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
      exact ⟨{⟨Θ, _, y.isRhdOperand_label⟩, ⟨Λ, _, y.isRhdOperand_label⟩},
        ⟨Rxy, ⟨_, .inl rfl, hΘ⟩, fun _ ↦ ⟨_, .inr rfl, hFΛ⟩⟩,
        by rintro z (rfl | rfl) <;> assumption⟩;
    · exact ⟨{⟨Θ, _, y.isRhdOperand_label⟩}, ⟨Rxy, ⟨_, rfl, hΘ⟩, fun h ↦ absurd h hc⟩,
        by rintro z rfl; exact hEΘ⟩;
  · intro x D E h₁ h₂;
    obtain ⟨Δ, hΔ, hD⟩ := exists_weakCriticalSuccessor_of_rhd_not_mem h₁ h₂;
    exact ⟨⟨Δ, E, .of_rhd_right h₁⟩, hΔ.toSuccessor, hD, fun _ hS ↦ hS.2.2 hΔ⟩;

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
      exact ⟨{⟨Θ, _, y.isRhdOperand_label⟩, ⟨Λ, _, y.isRhdOperand_label⟩},
        ⟨Rxy, ⟨_, .inl rfl, hΘ⟩, fun _ _ ↦ ⟨_, .inr rfl, hFΛ⟩⟩,
        by rintro z (rfl | rfl) <;> assumption⟩;
    · exact ⟨{⟨Θ, _, y.isRhdOperand_label⟩}, ⟨Rxy, ⟨_, rfl, hΘ⟩, fun h ↦ absurd h hc⟩,
        by rintro z rfl; exact hEΘ⟩;
  · intro x D E h₁ h₂;
    obtain ⟨Δ, hΔ, hD, hb⟩ := exists_weakCriticalSuccessor_box_neg_of_rhd_not_mem h₁ h₂;
    exact ⟨⟨Δ, E, .of_rhd_right h₁⟩, hΔ.toSuccessor, hD, fun _ hS ↦ hS.2.2 hΔ hb⟩;

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
      exact ⟨{⟨Θ, _, y.isRhdOperand_label⟩, ⟨Λ, _, y.isRhdOperand_label⟩},
        ⟨Rxy, ⟨_, .inl rfl, hΘ.toSuccessor⟩,
          fun _ ↦ ⟨⟨_, .inr rfl, hFΛ⟩, ⟨_, .inl rfl, rfl, hΘ⟩⟩⟩,
        by rintro z (rfl | rfl) <;> assumption⟩;
    · obtain ⟨Θ, hΘ, hEΘ⟩ := Successor.exists_successor_of_rhd_mem hDE Rxy hD;
      exact ⟨{⟨Θ, _, y.isRhdOperand_label⟩}, ⟨Rxy, ⟨_, rfl, hΘ⟩, fun h ↦ absurd h hc⟩,
        by rintro z rfl; exact hEΘ⟩;
  · intro x D E h₁ h₂;
    obtain ⟨Δ, hΔ, hD⟩ := exists_weakCriticalSuccessor_of_rhd_not_mem h₁ h₂;
    exact ⟨⟨Δ, E, .of_rhd_right h₁⟩, hΔ.toSuccessor, hD, fun _ hS ↦ (hS.2.2 hΔ).1⟩;

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
      exact ⟨{⟨Θ, _, y.isRhdOperand_label⟩, ⟨Λ, _, y.isRhdOperand_label⟩},
        ⟨Rxy, ⟨_, .inl rfl, hΘ.toSuccessor⟩,
          fun _ ↦ ⟨⟨_, .inr rfl, hΛ, hFΛ⟩, ⟨_, .inl rfl, rfl, hΘ⟩⟩⟩,
        by rintro z (rfl | rfl) <;> assumption⟩;
    · obtain ⟨Θ, hΘ, hEΘ⟩ := Successor.exists_successor_of_rhd_mem hDE Rxy hD;
      exact ⟨{⟨Θ, _, y.isRhdOperand_label⟩}, ⟨Rxy, ⟨_, rfl, hΘ⟩, fun h ↦ absurd h hc⟩,
        by rintro z rfl; exact hEΘ⟩;
  · intro x D E h₁ h₂;
    obtain ⟨Δ, hΔ, hD⟩ := exists_weakCriticalSuccessor_of_rhd_not_mem h₁ h₂;
    refine ⟨⟨Δ, E, .of_rhd_right h₁⟩, hΔ.toSuccessor, hD, fun _ hS ↦ ?_⟩;
    obtain ⟨z, hz, -, hE⟩ := (hS.2.2 hΔ).1;
    exact ⟨z, hz, hE⟩;

end ILMinus

end LabelledSet

end Verbrugge

end FFL.InterpretabilityLogic

end
