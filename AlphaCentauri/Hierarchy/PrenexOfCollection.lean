module

public import AlphaCentauri.Hierarchy.NormalForm
public import AlphaCentauri.Schemata.Collection

/-!
# Prenex normal form from collection

The prenex normal form of `Foundation.FirstOrder.Arithmetic.Prenex`, with the hypothesis
`V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s` weakened to `V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻` together with collection for strict `𝚺-[s]`
formulas.

The `Prenex` codes and every lemma about them that does not mention `𝗜𝚺` are reused from
Foundation. The declarations whose names end in `_of_collection` are copies of Foundation's
`Prenex.models_ball`, `Prenex.models_bexs`, `Prenex.models_and`, `Prenex.models_or`,
`Prenex.models_exs`, `Prenex.models_all`, `Prenex.models_exists_prenex` and
`exists_prenex_of_hierarchy`, taken from `Foundation/FirstOrder/Arithmetic/Prenex.lean` at the
commit `3fc85fb` pinned in `lake-manifest.json`, with their hypothesis weakened; they should be
replaced by Foundation's own declarations once the weakening is taken upstream.
-/

@[expose] public section

open LO

namespace LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] {Γ : Polarity} {s n : ℕ}

/-- Collection for strict `𝚺-[s]` formulas holds in `V`: witnesses for a strict `𝚺-[s]` formula
at every argument below `a` admit a common bound.
- [HP98, §I.2(a)] -/
def StrictCollection (V : Type*) [ORingStructure V] (s : ℕ) : Prop :=
  ∀ {n : ℕ} {θ : ArithmeticSemisentence (n + 2)}, StrictHierarchy 𝚺 s θ →
    ∀ (e : Fin n → V) (a : V), (∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) →
      ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) θ

/-- Collection for strict `𝚺-[s]` formulas is monotone in `s`. -/
lemma StrictCollection.of_le {s' : ℕ} (h : StrictCollection V s') (hs : s ≤ s') :
    StrictCollection V s := fun hθ ↦ h (hθ.mono hs)

namespace Prenex

local notation:64 "∀'[" u "] " φ => Prenex.ball u φ
local notation:64 "∃'[" u "] " φ => Prenex.bexs u φ

private lemma models_bexs_witness [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (hb : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚷 s Empty (m + 1))
      (e : Fin m → V), V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val)
    (φ : Prenex 𝚺 (s + 1) Empty (n + 1)) (x w : V) (e : Fin n → V) :
    V ⊧/(x :> w :> e)
        (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))).val
      ↔ ∃ y ≤ w, V ⊧/(y :> x :> e) φ.sigmaInv.val := by
  rw [hb]
  have hswap : ∀ z : V,
      V ⊧/(z :> x :> w :> e) (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))).val ↔
        V ⊧/(z :> x :> e) φ.sigmaInv.val := by
    intro z
    rw [val_rew, Semiformula.eval_rew]
    have hA : (Semiterm.val (L := ℒₒᵣ) (M := V) (z :> x :> w :> e) Empty.elim) ∘
        (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))) ∘ Semiterm.bvar
        = (z :> x :> e : Fin (n + 2) → V) := by
      funext i
      cases i using Fin.cases with
      | zero => simp
      | succ i =>
        cases i using Fin.cases with
        | zero => simp
        | succ i => simp
    have hB : (Semiterm.val (L := ℒₒᵣ) (M := V) (z :> x :> w :> e) Empty.elim) ∘
        (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))) ∘ Semiterm.fvar
        = (Empty.elim : Empty → V) := by
      funext i; exact i.elim
    rw [hA, hB]
  have hval : (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)).valb (x :> w :> e) = w + 1 := by simp
  rw [hval]
  simp only [hswap, Arithmetic.lt_succ_iff_le]

mutual

/-- A bounded universal quantifier commutes with the prenex normal form, over a model of `𝗣𝗔⁻`
with collection for strict `𝚺-[s]` formulas. -/
theorem models_ball_of_collection :
    {Γ : Polarity} → {s n : ℕ} → [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] → StrictCollection V s →
      (u : ArithmeticSemiterm Empty n) →
      (φ : Prenex Γ s Empty (n + 1)) → (e : Fin n → V) →
    V ⊧/e (∀'[u] φ).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) φ.val
  | _, 0, _, _, _, u, φ, e => by
    simp [ball_zero, Prenex.val, Semiformula.eval_ball]
  | 𝚺, s + 1, _, _, hC, u, φ, e => by
    have iha : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚷 s Empty (m + 1))
        (e : Fin m → V), V ⊧/e (∀'[u] φ).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) φ.val :=
      fun u φ e => models_ball_of_collection (hC.of_le (by omega)) u φ e
    have ihb : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚷 s Empty (m + 1))
        (e : Fin m → V), V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val :=
      fun u φ e => models_bexs_of_collection (hC.of_le (by omega)) u φ e
    rw [ball_succ_sigma (u := u) (φ := φ), models_sigma]
    simp only [iha (Rew.bShift u), Semiterm.val_bShift, models_bexs_witness ihb φ,
      models_sigmaInv φ]
    constructor
    · rintro ⟨w, hw⟩ x hx
      obtain ⟨y, -, hy⟩ := hw x hx
      exact ⟨y, hy⟩
    · intro h
      exact hC (StrictHierarchy.ofAlt φ.sigmaInv.val_strictHierarchy) e (u.valb e) h
  | 𝚷, s + 1, _, _, hC, u, φ, e => by
    have ih : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚺 (s + 1) Empty (m + 1))
        (e : Fin m → V), V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val :=
      fun u φ e => models_bexs_of_collection hC u φ e
    have hthis : V ⊧/e (∃'[u] ∼φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) (∼φ).val := ih u (∼φ) e
    have hval : (∀'[u] φ).val = ∼(∃'[u] ∼φ).val := by
      rw [ball_succ_pi (u := u) (φ := φ)]
      exact val_neg (∃'[u] ∼φ)
    rw [hval]
    simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
      at hthis ⊢
    grind
termination_by Γ s n _inst _hC _u _φ _e => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

/-- A bounded existential quantifier commutes with the prenex normal form, over a model of `𝗣𝗔⁻`
with collection for strict `𝚺-[s]` formulas. -/
theorem models_bexs_of_collection :
    {Γ : Polarity} → {s n : ℕ} → [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] → StrictCollection V s →
      (u : ArithmeticSemiterm Empty n) →
      (φ : Prenex Γ s Empty (n + 1)) → (e : Fin n → V) →
    V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val
  | _, 0, _, _, _, u, φ, e => by
    simp [bexs_zero, Prenex.val, Semiformula.eval_bexs]
  | 𝚺, s + 1, n, _, hC, u, φ, e => by
    have ih : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚷 s Empty (m + 1))
        (e : Fin m → V), V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val :=
      fun u φ e => models_bexs_of_collection (hC.of_le (by omega)) u φ e
    set φ₁' := φ.sigmaInv
    set φ₁ := φ₁'.val
    set v := #1 :> #0 :> fun i => #(i.succ.succ) with hv
    let φ₂' := φ₁'.rew (Rew.subst v)
    have hswap : ∀ (x b : V), V ⊧/(x :> b :> e) φ₂'.val ↔ V ⊧/(b :> x :> e) φ₁ := by
      intro x b
      rw [val_rew, Semiformula.eval_rew]
      have hA : (Semiterm.val (M := V) (x :> b :> e) Empty.elim) ∘ (Rew.subst v) ∘ Semiterm.bvar
          = (b :> x :> e : Fin (n + 2) → V) := by
        funext i
        cases i using Fin.cases with
        | zero => simp [hv]
        | succ i =>
          cases i using Fin.cases with
          | zero => simp [hv]
          | succ i => simp [hv]
      have hB : (Semiterm.val (M := V) (x :> b :> e) Empty.elim) ∘ (Rew.subst v) ∘ Semiterm.fvar
          = (Empty.elim : Empty → V) := by
        funext i; exact i.elim
      rw [hA, hB]
    rw [bexs_succ_sigma (u := u) (φ := φ), val_sigma]
    show (∃ b, V ⊧/(b :> e) (∃'[Rew.bShift u] φ₂').val) ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val
    simp only [ih (Rew.bShift u) φ₂', Semiterm.val_bShift, hswap, models_sigmaInv φ]
    grind
  | 𝚷, s + 1, _, _, hC, u, φ, e => by
    have ih : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚺 (s + 1) Empty (m + 1))
        (e : Fin m → V), V ⊧/e (∀'[u] φ).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) φ.val :=
      fun u φ e => models_ball_of_collection hC u φ e
    have hthis : V ⊧/e (∀'[u] ∼φ).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) (∼φ).val := ih u (∼φ) e
    have hval : (∃'[u] φ).val = ∼(∀'[u] ∼φ).val := by
      rw [bexs_succ_pi (u := u) (φ := φ)]
      exact val_neg (∀'[u] ∼φ)
    rw [hval]
    simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
      at hthis ⊢
    grind
termination_by Γ s n _inst _hC _u _φ _e => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

end

mutual

/-- Conjunction commutes with the prenex normal form, over a model of `𝗣𝗔⁻` with collection for
strict `𝚺-[s]` formulas. -/
theorem models_and_of_collection :
    {Γ : Polarity} → {s n : ℕ} → [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] → StrictCollection V s →
      (φ ψ : Prenex Γ s Empty n) → (e : Fin n → V) →
    V ⊧/e (φ ⋏ ψ).val ↔ V ⊧/e φ.val ∧ V ⊧/e ψ.val
  | _, 0, _, _, _, φ, ψ, e => by
    simp [and_zero, Prenex.val]
  | 𝚺, s + 1, n, _, hC, φ, ψ, e => by
    have iha : ∀ {m : ℕ} (φ ψ : Prenex 𝚷 s Empty m) (e : Fin m → V),
        V ⊧/e (φ ⋏ ψ).val ↔ V ⊧/e φ.val ∧ V ⊧/e ψ.val :=
      fun φ ψ e => models_and_of_collection (hC.of_le (by omega)) φ ψ e
    rw [and_succ_sigma (φ := φ) (ψ := ψ), models_sigma]
    set φ₂' := φ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))
    set ψ₂' := ψ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))
    have hα_eval : ∀ z : V,
        V ⊧/(z :> e) (∃'[‘#0 + 1’] φ₂').val ↔ ∃ x ≤ z, V ⊧/(x :> e) φ.sigmaInv.val := by
      intro z
      rw [models_bexs_of_collection (hC.of_le (by omega)) ‘#0 + 1’ φ₂' (z :> e)]
      simp only [φ₂', val_rew, Semiformula.eval_insert1]
      simp [Arithmetic.lt_succ_iff_le]
    have hβ_eval : ∀ z : V,
        V ⊧/(z :> e) (∃'[‘#0 + 1’] ψ₂').val ↔ ∃ x ≤ z, V ⊧/(x :> e) ψ.sigmaInv.val := by
      intro z
      rw [models_bexs_of_collection (hC.of_le (by omega)) ‘#0 + 1’ ψ₂' (z :> e)]
      simp only [ψ₂', val_rew, Semiformula.eval_insert1]
      simp [Arithmetic.lt_succ_iff_le]
    simp only [iha (∃'[‘#0 + 1’] φ₂') (∃'[‘#0 + 1’] ψ₂'), models_sigmaInv φ, models_sigmaInv ψ,
      hα_eval, hβ_eval]
    constructor
    · rintro ⟨z, ⟨x, -, hx⟩, ⟨y, -, hy⟩⟩
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      exact ⟨max x y, ⟨x, le_max_left x y, hx⟩, ⟨y, le_max_right x y, hy⟩⟩
  | 𝚷, s + 1, _, _, hC, φ, ψ, e => by
    have ih : ∀ {m : ℕ} (φ ψ : Prenex 𝚺 (s + 1) Empty m) (e : Fin m → V),
        V ⊧/e (φ ⋎ ψ).val ↔ V ⊧/e φ.val ∨ V ⊧/e ψ.val :=
      fun φ ψ e => models_or_of_collection hC φ ψ e
    have hthis : V ⊧/e (∼φ ⋎ ∼ψ).val ↔ V ⊧/e (∼φ).val ∨ V ⊧/e (∼ψ).val := ih (∼φ) (∼ψ) e
    have hval : (φ ⋏ ψ).val = ∼(∼φ ⋎ ∼ψ).val := by
      rw [and_succ_pi (φ := φ) (ψ := ψ)]
      exact val_neg (∼φ ⋎ ∼ψ)
    rw [hval]
    simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
      at hthis ⊢
    grind
termination_by Γ s n _inst _hC _φ _ψ _e => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

/-- Disjunction commutes with the prenex normal form, over a model of `𝗣𝗔⁻` with collection for
strict `𝚺-[s]` formulas. -/
theorem models_or_of_collection :
    {Γ : Polarity} → {s n : ℕ} → [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] → StrictCollection V s →
      (φ ψ : Prenex Γ s Empty n) → (e : Fin n → V) →
    V ⊧/e (φ ⋎ ψ).val ↔ V ⊧/e φ.val ∨ V ⊧/e ψ.val
  | _, 0, _, _, _, φ, ψ, e => by
    simp [or_zero, Prenex.val]
  | 𝚺, s + 1, _, _, hC, φ, ψ, e => by
    have ih : ∀ {m : ℕ} (φ ψ : Prenex 𝚷 s Empty m) (e : Fin m → V),
        V ⊧/e (φ ⋎ ψ).val ↔ V ⊧/e φ.val ∨ V ⊧/e ψ.val :=
      fun φ ψ e => models_or_of_collection (hC.of_le (by omega)) φ ψ e
    rw [or_succ_sigma (φ := φ) (ψ := ψ), models_sigma]
    simp only [ih φ.sigmaInv ψ.sigmaInv, models_sigmaInv φ, models_sigmaInv ψ]
    exact exists_or
  | 𝚷, s + 1, _, _, hC, φ, ψ, e => by
    have ih : ∀ {m : ℕ} (φ ψ : Prenex 𝚺 (s + 1) Empty m) (e : Fin m → V),
        V ⊧/e (φ ⋏ ψ).val ↔ V ⊧/e φ.val ∧ V ⊧/e ψ.val :=
      fun φ ψ e => models_and_of_collection hC φ ψ e
    have hthis : V ⊧/e (∼φ ⋏ ∼ψ).val ↔ V ⊧/e (∼φ).val ∧ V ⊧/e (∼ψ).val := ih (∼φ) (∼ψ) e
    have hval : (φ ⋎ ψ).val = ∼(∼φ ⋏ ∼ψ).val := by
      rw [or_succ_pi (φ := φ) (ψ := ψ)]
      exact val_neg (∼φ ⋏ ∼ψ)
    rw [hval]
    simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
      at hthis ⊢
    grind
termination_by Γ s n _inst _hC _φ _ψ _e => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

end

local prefix:64 "∃' " => Prenex.exs
local prefix:64 "∀' " => Prenex.all

/-- An unbounded existential quantifier commutes with the prenex normal form, over a model of
`𝗣𝗔⁻` with collection for strict `𝚺-[s]` formulas. -/
lemma models_exs_of_collection [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (hC : StrictCollection V s)
    (φ : Prenex 𝚺 (s + 1) Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (∃' φ).val ↔ ∃ x, V ⊧/(x :> e) φ.val := by
  show V ⊧/e
      (∃'[‘#0 + 1’] (∃'[‘#1 + 1’]
        (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma.val ↔
    ∃ x, V ⊧/(x :> e) φ.val
  rw [models_sigma]
  have hβeval : ∀ z : V,
      V ⊧/(z :> e)
        (∃'[‘#0 + 1’] (∃'[‘#1 + 1’]
          (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).val ↔
        ∃ y ≤ z, V ⊧/(y :> z :> e)
          (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))).val := by
    intro z
    rw [models_bexs_of_collection hC]
    have hval : (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)).valb (z :> e) = z + 1 := by simp
    rw [hval]
    simp only [Arithmetic.lt_succ_iff_le]
  have hαeval : ∀ y z : V,
      V ⊧/(y :> z :> e)
        (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))).val ↔
        ∃ x ≤ z, V ⊧/(x :> y :> e) φ.sigmaInv.val :=
    fun y z => models_bexs_witness (models_bexs_of_collection hC) φ y z e
  simp only [hβeval, hαeval, models_sigmaInv φ]
  constructor
  · rintro ⟨z, y, -, x, -, hx⟩
    exact ⟨y, x, hx⟩
  · rintro ⟨y, x, hx⟩
    exact ⟨max x y, y, le_max_right x y, x, le_max_left x y, hx⟩

/-- An unbounded universal quantifier commutes with the prenex normal form, over a model of `𝗣𝗔⁻`
with collection for strict `𝚺-[s]` formulas. -/
lemma models_all_of_collection [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (hC : StrictCollection V s)
    (φ : Prenex 𝚷 (s + 1) Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (∀' φ).val ↔ ∀ x, V ⊧/(x :> e) φ.val := by
  have hthis : V ⊧/e (∃' ∼φ).val ↔ ∃ x, V ⊧/(x :> e) (∼φ).val := models_exs_of_collection hC (∼φ) e
  have hval : (∀' φ).val = ∼(∃' ∼φ).val := by
    unfold Prenex.all
    exact val_neg (∃' ∼φ)
  rw [hval]
  simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq] at hthis ⊢
  grind

/-- Every `Hierarchy Γ s` semisentence is equivalent, in every model of `𝗣𝗔⁻` with collection for
strict `𝚺-[s]` formulas, to the value of a `Prenex Γ s` code. -/
theorem models_exists_prenex_of_collection {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
    ∃ φ' : Prenex Γ s Empty n,
      ∀ (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻], StrictCollection V s →
        ∀ e : Fin n → V, V ⊧/e φ ↔ V ⊧/e φ'.val := by
  induction h with
  | verum Γ s n =>
    exact ⟨verum, fun V _ _ _ e => (models_verum e).symm⟩
  | falsum Γ s n =>
    exact ⟨falsum, fun V _ _ _ e => (models_falsum e).symm⟩
  | rel Γ s r v =>
    exact ⟨rel r v, fun V _ _ _ e => (models_rel r v e).symm⟩
  | nrel Γ s r v =>
    exact ⟨nrel r v, fun V _ _ _ e => (models_nrel r v e).symm⟩
  | and _ _ ihφ ihψ =>
    obtain ⟨φ', hφ'⟩ := ihφ
    obtain ⟨ψ', hψ'⟩ := ihψ
    refine ⟨φ' ⋏ ψ', fun V _ _ hC e => ?_⟩
    rw [models_and_of_collection hC φ' ψ' e]
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
    exact and_congr (hφ' V hC e) (hψ' V hC e)
  | or _ _ ihφ ihψ =>
    obtain ⟨φ', hφ'⟩ := ihφ
    obtain ⟨ψ', hψ'⟩ := ihψ
    refine ⟨φ' ⋎ ψ', fun V _ _ hC e => ?_⟩
    rw [models_or_of_collection hC φ' ψ' e]
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]
    exact or_congr (hφ' V hC e) (hψ' V hC e)
  | ball pos _ ih =>
    obtain ⟨u, rfl⟩ := Rew.positive_iff.mp pos
    obtain ⟨φ', hφ'⟩ := ih
    refine ⟨∀'[u] φ', fun V _ _ hC e => ?_⟩
    rw [models_ball_of_collection hC u φ' e]
    simp only [Semiformula.eval_ball]
    exact forall_congr' fun x => (imp_congr Iff.rfl (hφ' V hC (x :> e))).trans (by simp)
  | bexs pos _ ih =>
    obtain ⟨u, rfl⟩ := Rew.positive_iff.mp pos
    obtain ⟨φ', hφ'⟩ := ih
    refine ⟨∃'[u] φ', fun V _ _ hC e => ?_⟩
    rw [models_bexs_of_collection hC u φ' e]
    simp only [Semiformula.eval_bexs]
    exact exists_congr fun x => (and_congr Iff.rfl (hφ' V hC (x :> e))).trans (by simp)
  | @exs s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih
    refine ⟨∃' φ', fun V _ _ hC e => ?_⟩
    rw [models_exs_of_collection (hC.of_le (by omega)) φ' e, Semiformula.eval_ex]
    exact exists_congr fun x => hφ' V (hC.of_le (by omega)) (x :> e)
  | @all s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih
    refine ⟨∀' φ', fun V _ _ hC e => ?_⟩
    rw [models_all_of_collection (hC.of_le (by omega)) φ' e, Semiformula.eval_all]
    exact forall_congr' fun x => hφ' V (hC.of_le (by omega)) (x :> e)
  | @sigma s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih
    refine ⟨φ'.sigma, fun V _ _ hC e => ?_⟩
    rw [models_sigma φ' e, Semiformula.eval_ex]
    exact exists_congr fun x => hφ' V (hC.of_le (by omega)) (x :> e)
  | @pi s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih
    refine ⟨φ'.pi, fun V _ _ hC e => ?_⟩
    rw [models_pi φ' e, Semiformula.eval_all]
    exact forall_congr' fun x => hφ' V (hC.of_le (by omega)) (x :> e)
  | @dummy_sigma s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih
    refine ⟨(∀' φ').altUp, fun V _ _ hC e => ?_⟩
    exact Semiformula.eval_all.trans
      ((forall_congr' fun x => hφ' V (hC.of_le (by omega)) (x :> e)).trans
        ((models_all_of_collection (hC.of_le (by omega)) φ' e).symm.trans
          (models_altUp (∀' φ') e).symm))
  | @dummy_pi s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih
    refine ⟨(∃' φ').altUp, fun V _ _ hC e => ?_⟩
    exact Semiformula.eval_ex.trans
      ((exists_congr fun x => hφ' V (hC.of_le (by omega)) (x :> e)).trans
        ((models_exs_of_collection (hC.of_le (by omega)) φ' e).symm.trans
          (models_altUp (∃' φ') e).symm))

end Prenex

/-- Collection for strict `𝚺-[s]` formulas holds in a model of `𝗣𝗔⁻` that satisfies the
collection axiom of every strict `𝚺-[s]` formula. -/
lemma strictCollection_of_models_collectionAxiom [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (h : ∀ ψ : ArithmeticSemiformula ℕ 2, StrictHierarchy 𝚺 s ψ →
      V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom ψ) : ArithmeticSentence)) :
    StrictCollection V s := by
  intro n θ hθ e a hex
  set ψ : ArithmeticSemiformula ℕ 2 :=
    Rew.embSubsts (#1 :> #0 :> fun i : Fin n ↦ (&(i : ℕ) : ArithmeticSemiterm ℕ 2)) ▹ θ with hψdef
  have hψ : StrictHierarchy 𝚺 s ψ := hθ.rew _
  set f : ℕ → V := fun i ↦ if hi : i < n then e ⟨i, hi⟩ else a with hf
  have heval : ∀ x y : V, ψ.Eval ![x, y] f ↔ V ⊧/(y :> x :> e) θ := by
    intro x y
    rw [hψdef]
    simp only [Semiformula.eval_embSubsts]
    refine Iff.of_eq (congrArg (fun b ↦ Semiformula.Evalb (M := V) b θ) ?_)
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ i =>
      cases i using Fin.cases with
      | zero => simp
      | succ i => simp [hf, i.isLt]
  obtain ⟨b, hb⟩ := (models_collectionAxiom_iff ψ).mp (h ψ hψ) f a
    fun x hx ↦ (hex x hx).imp fun u hu ↦ (heval x u).mpr hu
  exact ⟨b, fun x hx ↦ (hb x hx).imp fun u hu ↦ ⟨le_of_lt hu.1, (heval x u).mp hu.2⟩⟩

/-- Over a theory extending `𝗣𝗔⁻` that proves the collection axiom of every strict `𝚺-[s]`
formula, every `Hierarchy Γ s` semisentence is provably equivalent to the value of a `Prenex Γ s`
code.
- [HP98, Theorem I.2.25] -/
theorem exists_prenex_of_collection (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T]
    (hcol : ∀ ψ : ArithmeticSemiformula ℕ 2, StrictHierarchy 𝚺 s ψ →
      T ⊢ (.univCl (collectionAxiom ψ) : ArithmeticSentence))
    {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
    ∃ φ' : Prenex Γ s Empty n, T ⊢ ∀¹* (φ 🡘 φ'.val) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T :=
    Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻) inferInstance
  obtain ⟨φ', hφ'⟩ := Prenex.models_exists_prenex_of_collection h
  refine ⟨φ', provable_iff_of_models_iff fun V _ _ e ↦ ?_⟩
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
    models_of_subtheory (T := 𝗣𝗔⁻) (U := T) inferInstance
  exact hφ' V (strictCollection_of_models_collectionAxiom fun ψ hψ ↦
    consequence_iff.mp (Theory.Proof.sound (hcol ψ hψ)) V inferInstance) e

/-- In a model of `𝗣𝗔⁻` with collection for strict `𝚺-[s]` formulas, every `Hierarchy Γ s` formula
agrees, at a fixed assignment of its free variables, with a strict `Γ-[s]` formula.
- [HP98, Theorem I.2.25] -/
lemma exists_strictHierarchy_eval_iff [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (hC : StrictCollection V s)
    {φ : ArithmeticSemiformula ℕ 1} (hφ : Hierarchy Γ s φ) (f : ℕ → V) :
    ∃ ψ : ArithmeticSemiformula ℕ 1, StrictHierarchy Γ s ψ ∧
      ∀ x : V, ψ.Eval ![x] f ↔ φ.Eval ![x] f := by
  obtain ⟨θ, hθ⟩ :=
    Prenex.models_exists_prenex_of_collection (φ := φ.toSemisentence ![#0]) (hφ.rew _)
  refine ⟨Rew.embSubsts (#0 :> fun i : Fin φ.fvSup ↦ (&(i : ℕ) : ArithmeticSemiterm ℕ 1)) ▹ θ.val,
    Prenex.val_strictHierarchy.rew _, fun x ↦ ?_⟩
  have hvec : (Semiterm.val (M := V) ![x] f) ∘
      (#0 :> fun i : Fin φ.fvSup ↦ (&(i : ℕ) : ArithmeticSemiterm ℕ 1))
      = (x :> fun i : Fin φ.fvSup ↦ f i) := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simp
  simp only [Semiformula.eval_embSubsts, hvec]
  exact (hθ V hC (x :> fun i : Fin φ.fvSup ↦ f i)).symm.trans (φ.eval_toSemisentence_one x f)

/-- Over a theory extending `𝗣𝗔⁻` that proves the collection axiom of every strict `𝚺-[s]`
formula, every `Hierarchy Γ s` semisentence is provably equivalent to a strict `Γ-[s]` one.
- [HP98, 0.30]
- [HP98, Theorem I.2.25] -/
theorem exists_strictHierarchy_of_collection (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T]
    (hcol : ∀ ψ : ArithmeticSemiformula ℕ 2, StrictHierarchy 𝚺 s ψ →
      T ⊢ (.univCl (collectionAxiom ψ) : ArithmeticSentence))
    {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
    ∃ ψ : ArithmeticSemisentence n, StrictHierarchy Γ s ψ ∧ T ⊢ ∀¹* (φ 🡘 ψ) := by
  obtain ⟨φ', hφ'⟩ := exists_prenex_of_collection T hcol h
  exact ⟨φ'.val, Prenex.val_strictHierarchy, hφ'⟩

end LO.FirstOrder.Arithmetic
