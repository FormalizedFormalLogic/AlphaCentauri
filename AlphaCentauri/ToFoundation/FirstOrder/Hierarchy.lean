module

public import AlphaCentauri.Hierarchy.Bounded
public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
public import Foundation.FirstOrder.Syntax.Classical.BoundingHierarchy

/-!
# The bounded and prenex hierarchies

Companion of Foundation's `Syntax/Classical/BoundingHierarchy.lean`. `ℬ[<, L].Hierarchy 𝚷 (s + 1)`
passes through `Semiformula.univCl`, and every axiom of `𝗣𝗔⁻` is $\Pi_2$. `ℬ.PrenexBlock Γ`
collects the formulas that are a block of `Γ`-quantifiers over a `ℬ`-bounded matrix, which
`ℬ.PrenexHierarchy Γ 1` does not, as it has exactly one quantifier; every axiom of `𝗣𝗔⁻` is such a
block of universal quantifiers. `BooleanCombination Γ` is the closure of a predicate `Γ` on
formulas, together with the negations of its members, under `⋏` and `⋎`. Every formula is
equivalent, in every nonempty structure, to a prenex formula of either polarity and of every large
enough level.
-/

@[expose] public section

namespace FFL.FirstOrder.Bounding.Hierarchy

open Arithmetic

variable {L : Language} [L.LT] {ξ : Type*} {Γ : Polarity} {s n : ℕ}

@[simp] lemma toEmpty_iff [DecidableEq ξ] {φ : Semiformula L ξ n} (h : φ.freeVariables = ∅) :
    ℬ[<, L].Hierarchy Γ s (φ.toEmpty h) ↔ ℬ[<, L].Hierarchy Γ s φ := by
  have : ℬ[<, L].Hierarchy Γ s (Rew.emb ▹ (φ.toEmpty h) : Semiformula L ξ n) ↔
      ℬ[<, L].Hierarchy Γ s (φ.toEmpty h) := rew_iff
  rwa [show (Rew.emb ▹ (φ.toEmpty h) : Semiformula L ξ n) = φ from Semiformula.emb_toEmpty φ h,
    iff_comm] at this

@[simp] lemma allClosure_iff {φ : Semiformula L ξ n} :
    ℬ[<, L].Hierarchy 𝚷 (s + 1) (∀¹* φ) ↔ ℬ[<, L].Hierarchy 𝚷 (s + 1) φ := by
  induction n with
  | zero => simp
  | succ n ih => rw [allClosure_succ]; simp [ih]

@[simp] lemma univCl_iff {φ : Proposition L} :
    ℬ[<, L].Hierarchy 𝚷 (s + 1) (Semiformula.univCl φ) ↔ ℬ[<, L].Hierarchy 𝚷 (s + 1) φ := by
  simp [Semiformula.univCl, Semiformula.univCl']

/-- Every axiom of `𝗘𝗤 ℒₒᵣ` is $\Pi_2$. -/
lemma of_mem_eqAxiom {σ : ArithmeticSentence} (hσ : σ ∈ 𝗘𝗤 ℒₒᵣ) :
    ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2 σ := by
  cases hσ with
  | funcExt f => simp [Theory.Eq.funcExt]
  | relExt r => simp [Theory.Eq.relExt]
  | _ => simp

/-- Every axiom of `𝗣𝗔⁻` is $\Pi_2$. -/
lemma of_mem_peanoMinus {σ : ArithmeticSentence} (hσ : σ ∈ 𝗣𝗔⁻) :
    ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2 σ := by
  cases hσ with
  | equal φ hφ => exact of_mem_eqAxiom hφ
  | addEqOfLt =>
    simp only [PeanoMinus.Axiom.addEqOfLt]
    exact .all (.all (by rw [Semiformula.imp_eq]; exact .or (by simp) (.dummy_pi (by simp))))
  | _ => simp

end FFL.FirstOrder.Bounding.Hierarchy

namespace FFL.FirstOrder.Bounding

variable {L : Language} [L.LT] {ξ : Type*} {n : ℕ}

/-- The body of a bounded existential is bounded. -/
@[grind →]
lemma Closure.of_exs {φ : Semiformula L ξ (n + 1)} (h : ℬ[<, L].Closure (∃¹ φ)) :
    ℬ[<, L].Closure φ := by
  cases h with
  | bexs hR _ hφ =>
    obtain rfl := Set.mem_singleton_iff.mp hR
    exact .and (.rel _ _) hφ

/-- The body of a bounded universal is bounded. -/
@[grind →]
lemma Closure.of_all {φ : Semiformula L ξ (n + 1)} (h : ℬ[<, L].Closure (∀¹ φ)) :
    ℬ[<, L].Closure φ := by
  cases h with
  | ball hR _ hφ =>
    obtain rfl := Set.mem_singleton_iff.mp hR
    exact Closure.imp_iff.mpr ⟨.rel _ _, hφ⟩

/-- A bounded universal quantifies below a term. -/
@[grind →]
lemma Closure.exists_of_all {φ : Semiformula L ξ (n + 1)} (h : ℬ[<, L].Closure (∀¹ φ)) :
    ∃ (t : Semiterm L ξ n) (ψ : Semiformula L ξ (n + 1)),
      φ = “#0 < !!(Rew.bShift t)” 🡒 ψ ∧ ℬ[<, L].Closure ψ := by
  cases h with
  | ball hR pt hψ =>
    rename_i ψ _
    obtain rfl := Set.mem_singleton_iff.mp hR
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp pt
    exact ⟨t, ψ, rfl, hψ⟩

/-- A block of `Γ`-quantifiers in front of a `ℬ`-bounded formula; a bounded formula is the block
of length zero.

- [HP98, Definition I.2.1] -/
inductive PrenexBlock (ℬ : Bounding L) : Polarity → {n : ℕ} → Semiformula L ξ n → Prop
  | bounded {Γ : Polarity} {n : ℕ} {φ : Semiformula L ξ n} : ℬ.Closure φ → PrenexBlock ℬ Γ φ
  | exs {n : ℕ} {φ : Semiformula L ξ (n + 1)} : PrenexBlock ℬ 𝚺 φ → PrenexBlock ℬ 𝚺 (∃¹ φ)
  | all {n : ℕ} {φ : Semiformula L ξ (n + 1)} : PrenexBlock ℬ 𝚷 φ → PrenexBlock ℬ 𝚷 (∀¹ φ)

namespace PrenexBlock

variable {Γ : Polarity} {φ : Semiformula L ξ n}

attribute [grind .] bounded exs all

lemma neg : ∀ {Γ n} {φ : Semiformula L ξ n}, ℬ[<, L].PrenexBlock Γ φ →
    ℬ[<, L].PrenexBlock Γ.alt (∼φ)
  | _, _, _, bounded h => bounded h.neg
  | _, _, _, exs h => by simpa using (neg h).all
  | _, _, _, all h => by simpa using (neg h).exs

@[simp, grind =] lemma neg_iff : ℬ[<, L].PrenexBlock Γ.alt (∼φ) ↔ ℬ[<, L].PrenexBlock Γ φ :=
  ⟨fun h ↦ by simpa using h.neg, fun h ↦ by simpa using h.neg⟩

lemma rew {Γ : Polarity} {n₁ n₂ : ℕ} {ξ₁ ξ₂ : Type*} {φ : Semiformula L ξ₁ n₁}
    (ω : Rew L ξ₁ n₁ ξ₂ n₂) (h : ℬ[<, L].PrenexBlock Γ φ) :
    ℬ[<, L].PrenexBlock Γ (ω ▹ φ) := by
  induction h generalizing n₂ with
  | bounded h => exact bounded (h.rew ω)
  | exs h ih => simpa using (ih ω.q).exs
  | all h ih => simpa using (ih ω.q).all

lemma of_rew {Γ : Polarity} {n₂ : ℕ} {ξ₂ : Type*} {ψ : Semiformula L ξ₂ n₂}
    (h : ℬ[<, L].PrenexBlock Γ ψ) {ξ₁ : Type*} {n₁ : ℕ} {ω : Rew L ξ₁ n₁ ξ₂ n₂}
    {φ : Semiformula L ξ₁ n₁} (e : ω ▹ φ = ψ) : ℬ[<, L].PrenexBlock Γ φ := by
  induction h generalizing n₁ with
  | bounded h => exact bounded (by rw [← e] at h; simpa using h)
  | exs h ih =>
    obtain ⟨φ', hφ', rfl⟩ := (Semiformula.eq_exs_iff _).mp e
    exact exs (ih hφ')
  | all h ih =>
    obtain ⟨φ', hφ', rfl⟩ := (Semiformula.eq_all_iff _).mp e
    exact all (ih hφ')

@[simp, grind =]
lemma rew_iff {Γ : Polarity} {n₁ n₂ : ℕ} {ξ₁ ξ₂ : Type*} {ω : Rew L ξ₁ n₁ ξ₂ n₂}
    {φ : Semiformula L ξ₁ n₁} :
    ℬ[<, L].PrenexBlock Γ (ω ▹ φ) ↔ ℬ[<, L].PrenexBlock Γ φ :=
  ⟨fun h ↦ h.of_rew rfl, rew ω⟩

lemma of_deltaZero {Γ : Polarity} {φ : Semiformula L ξ n} (h : ℬ[<, L].Hierarchy 𝚺 0 φ) :
    ℬ[<, L].PrenexBlock Γ φ := bounded (Hierarchy.zero_iff_bounded.mp h)

lemma allClosure : ∀ {n} {φ : Semiformula L ξ n},
    ℬ[<, L].PrenexBlock 𝚷 φ → ℬ[<, L].PrenexBlock 𝚷 (∀¹* φ)
  | 0, _, h => h
  | _ + 1, _, h => by rw [allClosure_succ]; exact allClosure h.all

/-- The body of a block of existential quantifiers is a block of existential quantifiers. -/
@[grind →]
lemma of_exs {φ : Semiformula L ξ (n + 1)} (h : ℬ[<, L].PrenexBlock 𝚺 (∃¹ φ)) :
    ℬ[<, L].PrenexBlock 𝚺 φ := by
  cases h with
  | bounded h => exact .bounded h.of_exs
  | exs h => exact h

/-- A formula that is both a block of existential and a block of universal quantifiers is
bounded. -/
@[grind →]
lemma bounded_of_sigma_of_pi (hσ : ℬ[<, L].PrenexBlock 𝚺 φ) (hπ : ℬ[<, L].PrenexBlock 𝚷 φ) :
    ℬ[<, L].Closure φ := by
  cases hσ with
  | bounded h => exact h
  | exs _ => cases hπ with | bounded h => exact h

/-- A block that does not start with a quantifier is bounded. -/
lemma bounded_of_ne (h : ℬ[<, L].PrenexBlock Γ φ) (hne : ∀ ψ, φ ≠ ∃¹ ψ)
    (hna : ∀ ψ, φ ≠ ∀¹ ψ) : ℬ[<, L].Closure φ := by
  cases h with
  | bounded h => exact h
  | exs => exact absurd rfl (hne _)
  | all => exact absurd rfl (hna _)

end PrenexBlock

lemma PrenexHierarchy.prenexBlock {Γ : Polarity} {φ : Semiformula L ξ n}
    (h : ℬ[<, L].PrenexHierarchy Γ 1 φ) : ℬ[<, L].PrenexBlock Γ φ := by
  rcases Γ
  · obtain ⟨ψ, hψ, rfl⟩ := PrenexHierarchy.sigma_succ_iff.mp h
    exact .exs (.bounded (PrenexHierarchy.zero_iff_bounded.mp hψ))
  · obtain ⟨ψ, hψ, rfl⟩ := PrenexHierarchy.pi_succ_iff.mp h
    exact .all (.bounded (PrenexHierarchy.zero_iff_bounded.mp hψ))

end FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.PeanoMinus

open Bounding

/-- Every axiom of `𝗣𝗔⁻` is a block of universal quantifiers over a bounded formula. -/
theorem prenexBlock : ∀ φ ∈ 𝗣𝗔⁻, ℬ[<, ℒₒᵣ].PrenexBlock 𝚷 φ := by
  rintro φ ⟨⟩
  case equal h =>
    rcases h
    case refl => exact .all (.of_deltaZero (by simp))
    case symm => exact .all (.all (.of_deltaZero (by simp)))
    case trans => exact .all (.all (.all (.of_deltaZero (by simp))))
    case funcExt => exact .allClosure (.of_deltaZero (by simp))
    case relExt => exact .allClosure (.of_deltaZero (by simp))
  case addZero => exact .all (.of_deltaZero (by simp))
  case addAssoc => exact .all (.all (.all (.of_deltaZero (by simp))))
  case addComm => exact .all (.all (.of_deltaZero (by simp)))
  case addEqOfLt => exact .all (.all (.of_deltaZero (by simp)))
  case zeroLe => exact .all (.of_deltaZero (by simp))
  case zeroLtOne => exact .of_deltaZero (by simp)
  case oneLeOfZeroLt => exact .all (.of_deltaZero (by simp))
  case addLtAdd => exact .all (.all (.all (.of_deltaZero (by simp))))
  case mulZero => exact .all (.of_deltaZero (by simp))
  case mulOne => exact .all (.of_deltaZero (by simp))
  case mulAssoc => exact .all (.all (.all (.of_deltaZero (by simp))))
  case mulComm => exact .all (.all (.of_deltaZero (by simp)))
  case mulLtMul => exact .all (.all (.all (.of_deltaZero (by simp))))
  case distr => exact .all (.all (.all (.of_deltaZero (by simp))))
  case ltIrrefl => exact .all (.of_deltaZero (by simp))
  case ltTrans => exact .all (.all (.all (.of_deltaZero (by simp))))
  case ltTri => exact .all (.all (.of_deltaZero (by simp)))

end FFL.FirstOrder.Arithmetic.PeanoMinus

namespace FFL.FirstOrder.Bounding.HierarchySymbol.Semiformula

variable {L : Language} {ℬ : Bounding L} {ξ : Type*} {n s : ℕ}

@[simp] lemma hierarchy_succ {C : HierarchySymbol ℬ} {Γ : Polarity} (φ : C.Semiformula ξ n)
    (h : C.rank ≤ s + 1) : ℬ.Hierarchy Γ (s + 2) φ.val := hierarchy_of_lt φ (by omega)

end FFL.FirstOrder.Bounding.HierarchySymbol.Semiformula

namespace FFL.FirstOrder

variable {L : Language} {ξ : Type*} {n : ℕ}

/-- The Boolean combinations of the formulas satisfying `Γ`.
- [Bek99, §2] -/
inductive BooleanCombination (Γ : Semiformula L ξ n → Prop) : Semiformula L ξ n → Prop
  | pos {φ} : Γ φ → BooleanCombination Γ φ
  | neg {φ} : Γ φ → BooleanCombination Γ (∼φ)
  | and {φ ψ} : BooleanCombination Γ φ → BooleanCombination Γ ψ → BooleanCombination Γ (φ ⋏ ψ)
  | or {φ ψ} : BooleanCombination Γ φ → BooleanCombination Γ ψ → BooleanCombination Γ (φ ⋎ ψ)

namespace BooleanCombination

variable {Γ Γ' : Semiformula L ξ n → Prop} {φ ψ : Semiformula L ξ n}

@[simp, grind =] lemma neg_iff : BooleanCombination Γ (∼φ) ↔ BooleanCombination Γ φ := by
  have H : ∀ {φ : Semiformula L ξ n}, BooleanCombination Γ φ → BooleanCombination Γ (∼φ) := by
    intro φ h
    induction h with
    | pos hφ => exact neg hφ
    | neg hφ => simpa using pos hφ
    | and _ _ ih₁ ih₂ => simpa using ih₁.or ih₂
    | or _ _ ih₁ ih₂ => simpa using ih₁.and ih₂
  exact ⟨fun h ↦ by simpa using H h, H⟩

lemma mono (h : ∀ {φ}, Γ' φ → BooleanCombination Γ φ) :
    BooleanCombination Γ' φ → BooleanCombination Γ φ := by
  intro hφ
  induction hφ with
  | pos hφ' => exact h hφ'
  | neg hφ' => simpa using h hφ'
  | and _ _ ih₁ ih₂ => exact ih₁.and ih₂
  | or _ _ ih₁ ih₂ => exact ih₁.or ih₂

end BooleanCombination

end FFL.FirstOrder

namespace FFL.FirstOrder.Arithmetic

open FFL.FirstOrder (BooleanCombination)
open scoped FFL.FirstOrder.Bounding

variable {L : Language} [L.LT] {ξ : Type*} {Γ : Polarity} {s n : ℕ} {φ : Semiformula L ξ n}

namespace BooleanCombination

/-- Every Boolean combination of prenex formulas of level `s` lies at level `s + 1` of either
polarity.
- [Bek99, §2] -/
theorem hierarchy_succ (h : BooleanCombination (ℬ[<, L].PrenexHierarchy Γ s) φ)
    (Γ' : Polarity) : ℬ[<, L].Hierarchy Γ' (s + 1) φ := by
  induction h with
  | pos hφ => exact hφ.hierarchy.strict_mono Γ' (by omega)
  | neg hφ => exact hφ.neg.hierarchy.strict_mono Γ' (by omega)
  | and _ _ ih₁ ih₂ => exact ih₁.and ih₂
  | or _ _ ih₁ ih₂ => exact ih₁.or ih₂

theorem prenexHierarchy_alt (h : BooleanCombination (ℬ[<, L].PrenexHierarchy Γ s) φ) :
    BooleanCombination (ℬ[<, L].PrenexHierarchy Γ.alt s) φ := by
  induction h with
  | pos hφ => simpa using (BooleanCombination.neg hφ.neg)
  | neg hφ => exact .pos hφ.neg
  | and _ _ ih₁ ih₂ => exact ih₁.and ih₂
  | or _ _ ih₁ ih₂ => exact ih₁.or ih₂

/-- $\mathcal{B}(\Sigma_s) = \mathcal{B}(\Pi_s)$: a Boolean combination of prenex formulas of
level `s` and polarity `Γ` is one of polarity `Γ.alt`, and conversely.
- [Bek99, §2] -/
theorem prenexHierarchy_alt_iff :
    BooleanCombination (ℬ[<, L].PrenexHierarchy Γ s) φ ↔
      BooleanCombination (ℬ[<, L].PrenexHierarchy Γ.alt s) φ :=
  ⟨prenexHierarchy_alt, fun h ↦ by simpa using prenexHierarchy_alt h⟩

end BooleanCombination

end FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Bounding

universe u

variable {L : Language} {ℬ : Bounding L} {ξ : Type*} {n : ℕ}

variable (ℬ) in
/-- `φ` is equivalent, in every nonempty structure, to a `ℬ`-prenex formula of either polarity and
of every large enough level. -/
private def HasPrenexNormalForm (φ : Semiformula L ξ n) : Prop :=
  ∃ s, ∀ Γ s', s ≤ s' → ∃ ψ, ℬ.PrenexHierarchy Γ s' ψ ∧
    ∀ (M : Type u) [Tarski.Structure L M] [Nonempty M] (e : Fin n → M) (f : ξ → M),
      Semiformula.Eval e f φ ↔ Semiformula.Eval e f ψ

namespace HasPrenexNormalForm

private lemma of_iff {φ ψ : Semiformula L ξ n} (h : HasPrenexNormalForm.{u} ℬ ψ)
    (H : ∀ (M : Type u) [Tarski.Structure L M] [Nonempty M] (e : Fin n → M) (f : ξ → M),
      Semiformula.Eval e f φ ↔ Semiformula.Eval e f ψ) :
    HasPrenexNormalForm.{u} ℬ φ := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, fun Γ s' hs' ↦ (hs Γ s' hs').imp fun _ hχ ↦
    ⟨hχ.1, fun M _ _ e f ↦ (H M e f).trans (hχ.2 M e f)⟩⟩

private lemma of_prenexHierarchy {Γ : Polarity} {s : ℕ} {φ : Semiformula L ξ n}
    (h : ℬ.PrenexHierarchy Γ s φ) : HasPrenexNormalForm.{u} ℬ φ :=
  ⟨s + 1, fun Γ' _ hs ↦ h.exists_eval_iff_of_lt Γ' hs⟩

private lemma of_closure {φ : Semiformula L ξ n} (h : ℬ.Closure φ) : HasPrenexNormalForm.{u} ℬ φ :=
  of_prenexHierarchy (Γ := 𝚺) (PrenexHierarchy.zero_iff_bounded.mpr h)

private lemma neg {φ : Semiformula L ξ n} (h : HasPrenexNormalForm.{u} ℬ φ) :
    HasPrenexNormalForm.{u} ℬ (∼φ) := by
  obtain ⟨s, hs⟩ := h
  use s
  intro Γ s' hs'
  obtain ⟨ψ, hψ, H⟩ := hs Γ.alt s' hs'
  exact ⟨∼ψ, by simpa using hψ.neg, fun M _ _ e f ↦ by simp [H M e f]⟩

private lemma all {φ : Semiformula L ξ (n + 1)} (h : HasPrenexNormalForm.{u} ℬ φ) :
    HasPrenexNormalForm.{u} ℬ (∀¹ φ) := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨ψ, hψ, H⟩ := hs 𝚺 s le_rfl
  exact (of_prenexHierarchy hψ.all).of_iff fun M _ _ e f ↦ by simp [H M]

private lemma exs {φ : Semiformula L ξ (n + 1)} (h : HasPrenexNormalForm.{u} ℬ φ) :
    HasPrenexNormalForm.{u} ℬ (∃¹ φ) := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨ψ, hψ, H⟩ := hs 𝚷 s le_rfl
  exact (of_prenexHierarchy hψ.exs).of_iff fun M _ _ e f ↦ by simp [H M]

private lemma and_of_prenexHierarchy : {Γ₁ Γ₂ : Polarity} → {s₁ s₂ n : ℕ} →
    {ψ₁ ψ₂ : Semiformula L ξ n} → ℬ.PrenexHierarchy Γ₁ s₁ ψ₁ → ℬ.PrenexHierarchy Γ₂ s₂ ψ₂ →
    HasPrenexNormalForm.{u} ℬ (ψ₁ ⋏ ψ₂)
  | _, _, 0, 0, _, _, _, h₁, h₂ =>
    of_closure <| .and (PrenexHierarchy.zero_iff_bounded.mp h₁)
      (PrenexHierarchy.zero_iff_bounded.mp h₂)
  | 𝚺, _, _ + 1, _, _, _, _, h₁, h₂ => by
    obtain ⟨χ, hχ, rfl⟩ := PrenexHierarchy.sigma_succ_iff.mp h₁
    exact (and_of_prenexHierarchy hχ (h₂.rew Rew.bShift)).exs.of_iff fun M _ _ e f ↦ by simp
  | 𝚷, _, _ + 1, _, _, _, _, h₁, h₂ => by
    obtain ⟨χ, hχ, rfl⟩ := PrenexHierarchy.pi_succ_iff.mp h₁
    exact (and_of_prenexHierarchy hχ (h₂.rew Rew.bShift)).all.of_iff fun M _ _ e f ↦ by
      simp [forall_and_right]
  | _, 𝚺, 0, _ + 1, _, _, _, h₁, h₂ => by
    obtain ⟨χ, hχ, rfl⟩ := PrenexHierarchy.sigma_succ_iff.mp h₂
    exact (and_of_prenexHierarchy (h₁.rew Rew.bShift) hχ).exs.of_iff fun M _ _ e f ↦ by simp
  | _, 𝚷, 0, _ + 1, _, _, _, h₁, h₂ => by
    obtain ⟨χ, hχ, rfl⟩ := PrenexHierarchy.pi_succ_iff.mp h₂
    exact (and_of_prenexHierarchy (h₁.rew Rew.bShift) hχ).all.of_iff fun M _ _ e f ↦ by
      simp [forall_and_left]
termination_by _ _ s₁ s₂ => s₁ + s₂

private lemma and {φ₁ φ₂ : Semiformula L ξ n} (h₁ : HasPrenexNormalForm.{u} ℬ φ₁)
    (h₂ : HasPrenexNormalForm.{u} ℬ φ₂) : HasPrenexNormalForm.{u} ℬ (φ₁ ⋏ φ₂) := by
  obtain ⟨s₁, hs₁⟩ := h₁
  obtain ⟨s₂, hs₂⟩ := h₂
  obtain ⟨ψ₁, hψ₁, H₁⟩ := hs₁ 𝚺 s₁ le_rfl
  obtain ⟨ψ₂, hψ₂, H₂⟩ := hs₂ 𝚺 s₂ le_rfl
  exact (and_of_prenexHierarchy hψ₁ hψ₂).of_iff fun M _ _ e f ↦ by simp [H₁ M, H₂ M]

end HasPrenexNormalForm

private lemma hasPrenexNormalForm (φ : Semiformula L ξ n) : HasPrenexNormalForm.{u} ℬ φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact .of_closure (.verum _)
  | hfalsum => exact .of_closure (.falsum _)
  | hrel r v => exact .of_closure (.rel r v)
  | hnrel r v => exact .of_closure (.nrel r v)
  | hand _ _ ih₁ ih₂ => exact ih₁.and ih₂
  | hor _ _ ih₁ ih₂ => simpa using (ih₁.neg.and ih₂.neg).neg
  | hall _ ih => exact ih.all
  | hexs _ ih => exact ih.exs

variable (ℬ) in
/-- Every formula is equivalent, in every nonempty structure, to a `ℬ`-prenex formula of either
polarity and of every large enough level.
- [HP98, p. 8] -/
theorem exists_prenexHierarchy_eval_iff (φ : Semiformula L ξ n) :
    ∃ s, ∀ Γ s', s ≤ s' → ∃ ψ, ℬ.PrenexHierarchy Γ s' ψ ∧
      ∀ (M : Type u) [Tarski.Structure L M] [Nonempty M] (e : Fin n → M) (f : ξ → M),
        Semiformula.Eval e f φ ↔ Semiformula.Eval e f ψ :=
  hasPrenexNormalForm φ

end FFL.FirstOrder.Bounding
