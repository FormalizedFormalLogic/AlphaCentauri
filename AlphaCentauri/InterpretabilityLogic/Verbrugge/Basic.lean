module

public import AlphaCentauri.InterpretabilityLogic.Veltman.Basic

/-!
# Generalised Veltman semantics

Generalised Veltman models (Verbrugge semantics), in which each `≺[w]` relates a world to a set of
worlds, forcing, the soundness of extensions of $\mathbf{IL}$ with respect to generalised Veltman
models validating their axioms, and frame conditions for the principles $\mathsf{P}_0$,
$\mathsf{R}$ and $\mathsf{W}$.

A Veltman model is a generalised Veltman model, and conversely the Veltman model of a generalised
Veltman model `M` has as worlds the worlds of `M` paired with strategies choosing an element of
each `≺[x]`-successor set along a play, and forces the same formulas as `M`.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Verbrugge

/-- A model with an accessibility relation `≺` and, for every world `w`, a relation `≺[w]` between
worlds and sets of worlds. -/
structure Model (κ : Type*) [Nonempty κ] (α : Type*) where
  Rel' : κ → κ → Prop
  S' : κ → κ → Set κ → Prop
  Val' : κ → α → Prop

namespace Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α}

abbrev World (_ : Model κ α) := κ

abbrev Rel {M : Model κ α} : M.World → M.World → Prop := M.Rel'
scoped infix:60 " ≺ " => Rel

abbrev S {M : Model κ α} (w : M.World) : M.World → Set M.World → Prop := M.S' w
scoped notation:60 x:61 " ≺[" w "] " V:61 => S w x V

abbrev Val {M : Model κ α} : M.World → α → Prop := M.Val'

instance : CoeFun (Model κ α) (fun M ↦ M.World → α → Prop) := ⟨fun M ↦ M.Val⟩

/-- `≺` is transitive and conversely well-founded, and each `≺[w]` relates `≺`-successors of `w`
to nonempty sets of `≺`-successors of `w`, is quasi-reflexive and quasi-transitive, contains
$u \mathrel{≺[w]} \{v\}$ whenever $w ≺ u ≺ v$, and is monotone.

- [JMMV20, Definition 3.1]
- [Ver92]
- [Mas20, §6.2]
-/
class IsIL (M : Model κ α) extends IsTrans _ M.Rel, IsConverseWellFounded _ M.Rel where
  rel_of_s {w u : M.World} {V : Set M.World} : u ≺[w] V → w ≺ u
  rel_of_mem_of_s {w u v : M.World} {V : Set M.World} : u ≺[w] V → v ∈ V → w ≺ v
  nonempty_of_s {w u : M.World} {V : Set M.World} : u ≺[w] V → V.Nonempty
  s_refl {w u : M.World} : w ≺ u → u ≺[w] {u}
  s_trans {w u : M.World} {V : Set M.World} (Z : M.World → Set M.World) :
    u ≺[w] V → (∀ v ∈ V, v ≺[w] Z v) → u ≺[w] ⋃ v ∈ V, Z v
  s_of_rel {w u v : M.World} : w ≺ u → u ≺ v → u ≺[w] {v}
  s_mono {w u : M.World} {V Z : Set M.World} : u ≺[w] V → V ⊆ Z → (∀ z ∈ Z, w ≺ z) → u ≺[w] Z

export IsIL (rel_of_s rel_of_mem_of_s nonempty_of_s s_refl s_trans s_of_rel s_mono)

end Model

namespace Model.World

open Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {x : M.World} {A B : Formula α}

@[grind]
def Forces (M : Model κ α) (x : M.World) : Formula α → Prop
  | #a    => M x a
  | ⊥     => False
  | A 🡒 B => Forces M x A → Forces M x B
  | □A    => ∀ y, x ≺ y → Forces M y A
  | A ▷ B => ∀ y, x ≺ y → Forces M y A → ∃ V, y ≺[x] V ∧ ∀ z ∈ V, Forces M z B

scoped notation:55 x:56 " ⊩[" M "] " A:56 => Forces M x A

scoped notation:55 x:56 " ⊮[" M "] " A:56 => ¬Forces M x A

scoped notation:55 x:56 " ⊩ " A:56 => Forces _ x A

scoped notation:55 x:56 " ⊮ " A:56 => ¬Forces _ x A

@[simp, grind =] lemma forces_atom {a : α} : x ⊩ #a ↔ M x a := Iff.rfl
@[simp, grind .] lemma not_forces_bot : x ⊮ ⊥ := id
@[simp, grind .] lemma forces_top : x ⊩ ⊤ := id
@[grind =] lemma forces_imp : x ⊩ A 🡒 B ↔ x ⊮ A ∨ x ⊩ B := imp_iff_not_or
@[grind =] lemma forces_and : x ⊩ A ⋏ B ↔ x ⊩ A ∧ x ⊩ B := by
  change ((_ → _ → False) → False) ↔ _; tauto;
@[grind =] lemma forces_or : x ⊩ A ⋎ B ↔ x ⊩ A ∨ x ⊩ B := by
  change ((_ → False) → _) ↔ _; tauto;
@[grind =] lemma forces_neg : x ⊩ ∼A ↔ x ⊮ A := Iff.rfl
@[grind =] lemma forces_iff : x ⊩ A 🡘 B ↔ (x ⊩ A ↔ x ⊩ B) := by
  simp only [LogicalConnective.iff, forces_and]; grind;
@[grind =] lemma forces_box : x ⊩ □A ↔ ∀ y, x ≺ y → y ⊩ A := Iff.rfl
@[grind =] lemma forces_dia : x ⊩ ◇A ↔ ∃ y, x ≺ y ∧ y ⊩ A := by
  change ((∀ y, x ≺ y → y ⊩ A → False) → False) ↔ _; grind;
@[grind =] lemma forces_rhd :
    x ⊩ A ▷ B ↔ ∀ y, x ≺ y → y ⊩ A → ∃ V, y ≺[x] V ∧ ∀ z ∈ V, z ⊩ B := Iff.rfl

@[grind =] lemma not_forces_imp : x ⊮ A 🡒 B ↔ x ⊩ A ∧ x ⊮ B := by grind;
@[grind =] lemma not_forces_box : x ⊮ □A ↔ ∃ y, x ≺ y ∧ y ⊮ A := by grind;
@[grind =] lemma not_forces_rhd :
    x ⊮ A ▷ B ↔ ∃ y, x ≺ y ∧ y ⊩ A ∧ ∀ V, y ≺[x] V → ∃ z ∈ V, z ⊮ B := by
  grind;

lemma forces_axiomL [IsTrans _ M.Rel] [IsConverseWellFounded _ M.Rel] :
    x ⊩ □(□A 🡒 A) 🡒 □A := by
  intro hx;
  by_contra hA;
  obtain ⟨y, Rxy, hy⟩ := not_forces_box.mp hA;
  obtain ⟨t, ⟨Rxt, ht⟩, tmax⟩ :=
    ConverseWellFounded.iff_has_max.mp (IsConverseWellFounded.cwf (rel := M.Rel))
      {y | x ≺ y ∧ y ⊮ A} ⟨y, Rxy, hy⟩;
  apply ht;
  apply hx t Rxt;
  intro z Rtz;
  by_contra hz;
  exact tmax z ⟨IsTrans.trans _ _ _ Rxt Rtz, hz⟩ Rtz;

end Model.World

namespace Model

variable {κ α : Type*} [Nonempty κ]

instance : Semantics (Model κ α) (Formula α) := ⟨fun M A ↦ ∀ x : M.World, World.Forces M x A⟩

lemma models_iff {M : Model κ α} {A : Formula α} : M ⊧ A ↔ ∀ x : M.World, World.Forces M x A :=
  Iff.rfl

end Model

end Verbrugge

/-! ### Soundness -/

namespace Logic.ofAxioms

open Verbrugge Verbrugge.Model Verbrugge.Model.World

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {𝔸 : Set (Formula α)} {A : Formula α}

/-- - [JMMV20, Theorem 3.2]
- [Mas20, §6.2]
-/
theorem sound_verbrugge [M.IsIL] (h𝔸 : ∀ A ∈ 𝔸, M ⊧ A) (h : ofAxioms 𝔸 ⊢ A) : M ⊧ A := by
  intro x;
  induction h generalizing x with
  | axm hA => exact h𝔸 _ hA x;
  | mdp _ _ ih₁ ih₂ => exact ih₁ x (ih₂ x);
  | nec _ ih =>
    intro y _;
    exact ih y;
  | axiomL => exact forces_axiomL;
  | axiomJ1 =>
    intro hx y Rxy hy;
    use {y};
    and_intros;
    · exact s_refl Rxy;
    · simpa using hx y Rxy hy;
  | axiomJ2 =>
    intro hx y Rxy hy;
    obtain ⟨hAB, hBC⟩ := forces_and.mp hx;
    obtain ⟨V, SxyV, hV⟩ := hAB y Rxy hy;
    choose! Z SxZ hZ using fun v hv ↦ hBC v (rel_of_mem_of_s SxyV hv) (hV v hv);
    use ⋃ v ∈ V, Z v;
    and_intros;
    · exact s_trans Z SxyV SxZ;
    · simp only [Set.mem_iUnion];
      rintro z ⟨v, hv, hz⟩;
      exact hZ v hv z hz;
  | axiomJ3 =>
    intro hx y Rxy hy;
    obtain ⟨hAC, hBC⟩ := forces_and.mp hx;
    rcases forces_or.mp hy with hy | hy;
    · exact hAC y Rxy hy;
    · exact hBC y Rxy hy;
  | axiomJ4 =>
    intro hx hA;
    obtain ⟨y, Rxy, hy⟩ := forces_dia.mp hA;
    obtain ⟨V, SxyV, hV⟩ := hx y Rxy hy;
    obtain ⟨z, hz⟩ := nonempty_of_s SxyV;
    apply forces_dia.mpr;
    use z;
    and_intros;
    · exact rel_of_mem_of_s SxyV hz;
    · exact hV z hz;
  | axiomJ5 =>
    intro y Rxy hy;
    obtain ⟨z, Ryz, hz⟩ := forces_dia.mp hy;
    use {z};
    and_intros;
    · exact s_of_rel Rxy Ryz;
    · simpa;
  | _ => grind;

end Logic.ofAxioms

/-! ### Veltman models as generalised Veltman models -/

namespace Veltman.Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α}

/-- The generalised Veltman model on the frame of `M` in which $u \mathrel{≺[w]} V$ holds when
every element of $V$ is a `≺`-successor of `w` and $u \mathrel{≺[w]} v$ in `M` for some $v ∈ V$.

- [JMMV20, Theorem 3.2]
- [Mas20, §9]
-/
def toVerbrugge (M : Model κ α) : Verbrugge.Model κ α where
  Rel' := M.Rel'
  S' w u V := (∀ v ∈ V, M.Rel' w v) ∧ ∃ v ∈ V, M.S' w u v
  Val' := M.Val'

instance [M.IsIL] : M.toVerbrugge.IsIL where
  trans := IsTrans.trans (r := M.Rel)
  cwf := IsConverseWellFounded.cwf (rel := M.Rel)
  rel_of_s := by
    rintro w u V ⟨-, v, -, Suv⟩;
    exact rel_of_s_left Suv;
  rel_of_mem_of_s := by
    rintro w u v V ⟨hV, -⟩ hv;
    exact hV v hv;
  nonempty_of_s := by
    rintro w u V ⟨-, v, hv, -⟩;
    exact ⟨v, hv⟩;
  s_refl := by
    intro w u Rwu;
    constructor;
    · simpa;
    · simpa using s_refl Rwu;
  s_trans := by
    rintro w u V Z ⟨-, v, hv, Suv⟩ hZ;
    obtain ⟨hZv, z, hz, Svz⟩ := hZ v hv;
    constructor;
    · simp only [Set.mem_iUnion];
      rintro y ⟨v', hv', hy⟩;
      exact (hZ v' hv').1 y hy;
    · use z;
      and_intros;
      · simp only [Set.mem_iUnion];
        use v;
      · exact s_trans Suv Svz;
  s_of_rel := by
    intro w u v Rwu Ruv;
    constructor;
    · simpa using IsTrans.trans (r := M.Rel) _ _ _ Rwu Ruv;
    · simpa using s_of_rel Rwu Ruv;
  s_mono := by
    rintro w u V Z ⟨-, v, hv, Suv⟩ hVZ hZ;
    constructor;
    · exact hZ;
    · use v;
      and_intros;
      · exact hVZ hv;
      · exact Suv;

open Veltman.Model.World Verbrugge.Model.World in
/-- `M` and `M.toVerbrugge` force the same formulas.

- [JMMV20, Theorem 3.2]
- [Mas20, §9]
-/
lemma forces_toVerbrugge [M.IsIL] {x : M.World} {A : Formula α} :
    x ⊩[M.toVerbrugge] A ↔ x ⊩[M] A := by
  induction A generalizing x with
  | atom a => rfl;
  | falsum => rfl;
  | imp A B ihA ihB => exact imp_congr ihA ihB;
  | box A ihA => exact forall_congr' fun y ↦ imp_congr_right fun _ ↦ ihA;
  | rhd A B ihA ihB =>
    constructor;
    · intro hx y Rxy hy;
      obtain ⟨V, ⟨-, z, hz, Syz⟩, hV⟩ := hx y Rxy (ihA.mpr hy);
      use z;
      and_intros;
      · exact Syz;
      · exact ihB.mp (hV z hz);
    · intro hx y Rxy hy;
      obtain ⟨z, Syz, hz⟩ := hx y Rxy (ihA.mp hy);
      use {z};
      and_intros;
      · simpa using rel_of_s_right Syz;
      · simpa;
      · simpa using ihB.mpr hz;

end Veltman.Model

namespace Verbrugge.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

/-- If $w ≺ x ≺ u ≺[w] V$ and every element of $V$ has a `≺`-successor in $Z$, then
$u \mathrel{≺[x]} Z'$ for some $Z' \subseteq Z$.

- [MV20, §2.4]
-/
class HasP₀ : Prop where
  exists_subset_of_rel_rel_s {w x u : M.World} {V Z : Set M.World} :
    w ≺ x → x ≺ u → u ≺[w] V → (∀ v ∈ V, ∃ z ∈ Z, v ≺ z) → ∃ Z' ⊆ Z, u ≺[x] Z'

/-- The family of sets $C \subseteq \mathrm{R}[x]$ meeting every $Z$ with $u \mathrel{≺[x]} Z$. -/
def choiceSets (x u : M.World) : Set (Set M.World) :=
  {C | (∀ y ∈ C, x ≺ y) ∧ ∀ Z, u ≺[x] Z → (Z ∩ C).Nonempty}

/-- If $w ≺ x ≺ u ≺[w] V$, then every choice set $C$ has $U \subseteq V$ with $x \mathrel{≺[w]} U$
and $\mathrm{R}[U] \subseteq C$.

- [MV20, §2.5]
- [JMMV20, §4.2]
-/
class HasR : Prop where
  exists_subset_of_rel_rel_s {w x u : M.World} {V : Set M.World} :
    w ≺ x → x ≺ u → u ≺[w] V → ∀ C ∈ M.choiceSets x u,
      ∃ U ⊆ V, x ≺[w] U ∧ ∀ y ∈ U, ∀ z, y ≺ z → z ∈ C

/-- If $u \mathrel{≺[w]} V$, then there is $V' \subseteq V$ with $u \mathrel{≺[w]} V'$ such that no
$≺$-successor of an element of $V'$ has $y \mathrel{≺[w]} V$.

- [MV20, §3]
- [JMMV20, §6.4]
-/
class HasW : Prop where
  exists_subset_of_s {w u : M.World} {V : Set M.World} :
    u ≺[w] V → ∃ V' ⊆ V, u ≺[w] V' ∧ ∀ x ∈ V', ∀ y, x ≺ y → ¬y ≺[w] V

end Verbrugge.Model

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
