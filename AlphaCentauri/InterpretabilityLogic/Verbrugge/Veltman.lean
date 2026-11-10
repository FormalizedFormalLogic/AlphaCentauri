module

public import AlphaCentauri.InterpretabilityLogic.Verbrugge.Basic

/-!
# Veltman models of generalised Veltman models

The Veltman model of a generalised Veltman model `M`, whose worlds are worlds of `M` paired with
strategies choosing an element of each `≺[x]`-successor set along a play, and forces the same
formulas as `M`.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Verbrugge.Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α}

variable (M) in
/-- A choice of a world after each finite sequence of sets of worlds, the latest set first. -/
abbrev Strategy := List (Set M.World) → M.World

namespace Strategy

variable {σ : M.Strategy} {H H₁ H₂ : List (Set M.World)}

/-- The strategy `σ` continued after the history `H`. -/
def shift (σ : M.Strategy) (H : List (Set M.World)) : M.Strategy := fun Y ↦ σ (Y ++ H)

@[simp] lemma shift_apply {Y : List (Set M.World)} : σ.shift H Y = σ (Y ++ H) := rfl

@[simp] lemma shift_nil : σ.shift [] = σ := by
  funext Y;
  simp;

@[simp] lemma shift_shift : (σ.shift H₁).shift H₂ = σ.shift (H₂ ++ H₁) := by
  funext Y;
  simp;

open Classical in
variable (M) in
/-- The strategy starting at `u` that chooses an element of `G` from a set meeting `G`, and
otherwise any element of a nonempty set. -/
noncomputable def choose (u : M.World) (G : Set M.World) : M.Strategy
  | [] => u
  | Z :: _ => if h : (Z ∩ G).Nonempty then h.some else if h : Z.Nonempty then h.some else u

end Strategy

variable (M) in
/-- A history `H` is a play of `σ` for `x` when each set in `H` is a `≺[x]`-successor of the world
`σ` chooses before it. -/
def IsPlay (x : M.World) (σ : M.Strategy) : List (Set M.World) → Prop
  | [] => True
  | Z :: H => IsPlay x σ H ∧ σ H ≺[x] Z

variable (M) in
/-- `σ` is a strategy for `x` from `u`: it chooses `u` first and, on a play, an element of every
`≺[x]`-successor set of the world it chose last. -/
structure IsStrategy (x u : M.World) (σ : M.Strategy) : Prop where
  nil : σ [] = u
  mem_cons {H : List (Set M.World)} {Z : Set M.World} : M.IsPlay x σ H → σ H ≺[x] Z → σ (Z :: H) ∈ Z

section Strategy

variable {x u w : M.World} {σ : M.Strategy} {H H₁ H₂ : List (Set M.World)} {G : Set M.World}

@[simp] lemma isPlay_nil : M.IsPlay x σ [] := trivial

@[simp] lemma isPlay_cons {Z : Set M.World} : M.IsPlay x σ (Z :: H) ↔ M.IsPlay x σ H ∧ σ H ≺[x] Z :=
  Iff.rfl

lemma isPlay_append : M.IsPlay x σ (H₂ ++ H₁) ↔ M.IsPlay x σ H₁ ∧ M.IsPlay x (σ.shift H₁) H₂ := by
  induction H₂ with
  | nil => simp;
  | cons Z H₂ ih => simp [ih, and_assoc];

lemma IsStrategy.shift (hσ : M.IsStrategy x u σ) (hH : M.IsPlay x σ H) :
    M.IsStrategy x (σ H) (σ.shift H) where
  nil := by simp;
  mem_cons hH' hZ := hσ.mem_cons (isPlay_append.mpr ⟨hH, hH'⟩) hZ

lemma isStrategy_choose [M.IsIL] : M.IsStrategy x u (Strategy.choose M u G) where
  nil := rfl
  mem_cons := by
    intro H Z _ hZ;
    simp only [Strategy.choose];
    split_ifs with h₁ h₂;
    · exact h₁.some_mem.1;
    · exact h₂.some_mem;
    · exact (h₂ <| nonempty_of_s hZ).elim;

lemma choose_mem_of_isPlay (hG : ∀ v ∈ G, ∀ Z, v ≺[w] Z → (Z ∩ G).Nonempty) (hu : u ∈ G)
    (hH : M.IsPlay w (Strategy.choose M u G) H) : Strategy.choose M u G H ∈ G := by
  induction H with
  | nil => exact hu;
  | cons Z H ih =>
    obtain ⟨hH, hZ⟩ := isPlay_cons.mp hH;
    have h := hG _ (ih hH) Z hZ;
    simp only [Strategy.choose, h, ↓reduceDIte];
    exact h.some_mem.2;

end Strategy

variable (M) in
/-- A world of `M` together with, for each `≺`-predecessor `x` of it, a strategy for `x` from it.

- [Per25, Definition 5]
-/
structure VeltmanWorld where
  world : M.World
  strategy : M.World → M.Strategy
  isStrategy {x : M.World} : x ≺ world → M.IsStrategy x world (strategy x)

namespace VeltmanWorld

instance [M.IsIL] : Nonempty M.VeltmanWorld :=
  ⟨⟨Classical.arbitrary κ, fun _ ↦ Strategy.choose M _ ∅, fun _ ↦ isStrategy_choose⟩⟩

/-- `b` lies over a `≺`-successor of the world of `a`, and the strategy of `b` for each
`≺`-predecessor `x` of the world of `a` continues that of `a` after a play. -/
def Rel (a b : M.VeltmanWorld) : Prop :=
  a.world ≺ b.world ∧
    ∀ x, x ≺ a.world → ∃ H, M.IsPlay x (a.strategy x) H ∧ b.strategy x = (a.strategy x).shift H

/-- `b` and `c` are `Rel`-successors of `a`, and the strategy of `c` for the world of `a`
continues that of `b` after a play. -/
def S (a b c : M.VeltmanWorld) : Prop :=
  Rel a b ∧ Rel a c ∧
    ∃ H, M.IsPlay a.world (b.strategy a.world) H ∧
      c.strategy a.world = (b.strategy a.world).shift H

variable [M.IsIL] {u : M.World} {τ : M.Strategy}

lemma isPlay_singleton {a : M.VeltmanWorld} {x : M.World} (hx : x ≺ a.world) (hu : a.world ≺ u) :
    M.IsPlay x (a.strategy x) [{u}] := by
  simpa [(a.isStrategy hx).nil] using s_of_rel hx hu;

open Classical in
/-- The world over `u` whose strategy for the world of `a` is `τ` and whose strategy for each
`≺`-predecessor `x` of the world of `a` continues that of `a` after $\{u\}$. -/
noncomputable def successor (a : M.VeltmanWorld) (hu : a.world ≺ u)
    (hτ : M.IsStrategy a.world u τ) : M.VeltmanWorld where
  world := u
  strategy x :=
    if x ≺ a.world then (a.strategy x).shift [{u}]
    else if x = a.world then τ
    else Strategy.choose M u ∅
  isStrategy {x} _ := by
    split_ifs with hx hx';
    · have hP := isPlay_singleton hx hu;
      have h := (a.isStrategy hx).shift hP;
      rwa [Set.mem_singleton_iff.mp <| (a.isStrategy hx).mem_cons hP.1 hP.2] at h;
    · exact hx' ▸ hτ;
    · exact isStrategy_choose;

variable {a : M.VeltmanWorld} {hu : a.world ≺ u} {hτ : M.IsStrategy a.world u τ}

@[simp] lemma successor_world : (a.successor hu hτ).world = u := rfl

@[simp] lemma successor_strategy_self : (a.successor hu hτ).strategy a.world = τ := by
  simp [successor, (ConverseWellFounded.irrefl (r := M.Rel)).irrefl a.world];

lemma rel_successor : Rel a (a.successor hu hτ) := by
  constructor;
  · exact hu;
  · intro x hx;
    use [{u}];
    constructor;
    · exact isPlay_singleton hx hu;
    · simp [successor, hx];

lemma rel_trans {a b c : M.VeltmanWorld} (Rab : Rel a b) (Rbc : Rel b c) : Rel a c := by
  constructor;
  · exact IsTrans.trans _ _ _ Rab.1 Rbc.1;
  · intro x hx;
    obtain ⟨H₁, hH₁, eb⟩ := Rab.2 x hx;
    obtain ⟨H₂, hH₂, ec⟩ := Rbc.2 x (IsTrans.trans _ _ _ hx Rab.1);
    use H₂ ++ H₁;
    constructor;
    · exact isPlay_append.mpr ⟨hH₁, eb ▸ hH₂⟩;
    · simp [ec, eb];

end VeltmanWorld

open VeltmanWorld

/-- The Veltman model on `M.VeltmanWorld` with relations `VeltmanWorld.Rel` and `VeltmanWorld.S`
and the valuation of `M` on the underlying worlds.

- [Per25, Definition 5]
-/
noncomputable def toVeltman (M : Model κ α) [M.IsIL] : Veltman.Model M.VeltmanWorld α where
  Rel' := VeltmanWorld.Rel
  S' := VeltmanWorld.S
  Val' a := M.Val' a.world

variable [M.IsIL]

/-- - [Per25, Proposition 6] -/
instance : M.toVeltman.IsIL where
  trans _ _ _ := rel_trans
  cwf := by
    apply Subrelation.wf (r := InvImage (flip M.Rel) VeltmanWorld.world);
    · intro a b h;
      exact h.1;
    · exact InvImage.wf _ IsConverseWellFounded.cwf;
  rel_of_s_left h := h.1
  rel_of_s_right h := h.2.1
  s_refl h := by
    constructor;
    · exact h;
    constructor;
    · exact h;
    · use [];
      simp;
  s_trans := by
    rintro a b c d ⟨Rab, Rac, H₁, hH₁, ec⟩ ⟨-, Rad, H₂, hH₂, ed⟩;
    constructor;
    · exact Rab;
    constructor;
    · exact Rad;
    · use H₂ ++ H₁;
      constructor;
      · exact isPlay_append.mpr ⟨hH₁, ec ▸ hH₂⟩;
      · simp [ed, ec];
  s_of_rel := by
    intro a b c Rab Rbc;
    constructor;
    · exact Rab;
    constructor;
    · exact rel_trans Rab Rbc;
    · exact Rbc.2 a.world Rab.1;

open Veltman.Model.World Verbrugge.Model.World in
/-- `M` forces at a world exactly what `M.toVeltman` forces at the worlds over it.

- [Per25, Corollary 7]
-/
theorem forces_toVeltman {a : M.VeltmanWorld} {A : Formula α} :
    a ⊩[M.toVeltman] A ↔ a.world ⊩[M] A := by
  induction A generalizing a with
  | atom p => rfl;
  | falsum => rfl;
  | imp A B ihA ihB => exact imp_congr ihA ihB;
  | box A ihA =>
    constructor;
    · intro ha u hu;
      exact ihA.mp <| ha (a.successor hu (isStrategy_choose (G := ∅))) rel_successor;
    · intro ha b Rab;
      exact ihA.mpr <| ha b.world Rab.1;
  | rhd A B ihA ihB =>
    constructor;
    · intro ha u hu hA;
      by_contra hV;
      set G := {v | a.world ≺ v ∧ ∀ V, v ≺[a.world] V → ∃ z ∈ V, z ⊮[M] B};
      have hGZ : ∀ v ∈ G, ∀ Z, v ≺[a.world] Z → (Z ∩ G).Nonempty := by
        rintro v ⟨-, hv⟩ Z hZ;
        by_contra hZG;
        have hz : ∀ z ∈ Z, ∃ V, z ≺[a.world] V ∧ ∀ y ∈ V, y ⊩[M] B := by
          intro z hz;
          by_contra h;
          push Not at h;
          exact hZG ⟨z, hz, rel_of_mem_of_s hZ hz, h⟩;
        choose! V hV hVB using hz;
        obtain ⟨y, hy, hyB⟩ := hv _ (s_trans V hZ hV);
        simp only [Set.mem_iUnion] at hy;
        obtain ⟨z, hz, hy⟩ := hy;
        exact hyB <| hVB z hz y hy;
      have hu' : u ∈ G := by
        constructor;
        · exact hu;
        · push Not at hV;
          exact hV;
      obtain ⟨c, ⟨-, Rac, H, hH, ec⟩, hc⟩ :=
        ha (a.successor hu (isStrategy_choose (G := G))) rel_successor (ihA.mpr hA);
      rw [successor_strategy_self] at hH ec;
      have hcG : c.world ∈ G := by
        rw [← (c.isStrategy Rac.1).nil, ec, Strategy.shift_apply, List.nil_append];
        exact choose_mem_of_isPlay hGZ hu' hH;
      obtain ⟨z, hz, hzB⟩ := hcG.2 {c.world} (s_refl hcG.1);
      exact hzB <| (Set.mem_singleton_iff.mp hz) ▸ ihB.mp hc;
    · intro ha b Rab hA;
      obtain ⟨V, hV, hVB⟩ := ha b.world Rab.1 (ihA.mp hA);
      have hb := b.isStrategy Rab.1;
      have hP : M.IsPlay a.world (b.strategy a.world) [V] := by
        simpa [hb.nil] using hV;
      have hv := hb.mem_cons hP.1 hP.2;
      use a.successor (rel_of_mem_of_s hV hv) (hb.shift hP);
      constructor;
      · constructor;
        · exact Rab;
        constructor;
        · exact rel_successor;
        · use [V];
          constructor;
          · exact hP;
          · simp;
      · exact ihB.mpr <| hVB _ hv;

end Verbrugge.Model

end FFL.InterpretabilityLogic

end
