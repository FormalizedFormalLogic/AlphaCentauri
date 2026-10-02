module

public import AlphaCentauri.Hierarchy.Bounded
public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-!
# The arithmetical hierarchy of a universal closure

`ℬ[<, L].Hierarchy 𝚷 (s + 1)` passes through `Semiformula.univCl`, and every axiom of `𝗣𝗔⁻` is
$\Pi_2$. `ℬ.PrenexBlock Γ` collects the formulas that are a block of `Γ`-quantifiers over a
`ℬ`-bounded matrix, which `ℬ.PrenexHierarchy Γ 1` does not, as it has exactly one quantifier; every
axiom of `𝗣𝗔⁻` is such a block of universal quantifiers.
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

/-- Every formula lies at some level of the arithmetical hierarchy. -/
lemma exists_forall_hierarchy (φ : Semiformula L ξ n) : ∃ s, ∀ Γ, ℬ[<, L].Hierarchy Γ s φ := by
  induction φ using Semiformula.rec' with
  | hverum | hfalsum | hrel | hnrel => exact ⟨0, by simp⟩
  | hand φ ψ ihφ ihψ | hor φ ψ ihφ ihψ =>
    obtain ⟨s, hs⟩ := ihφ
    obtain ⟨t, ht⟩ := ihψ
    use max s t;
    intro Γ;
    simp [(hs Γ).mono (le_max_left s t), (ht Γ).mono (le_max_right s t)]
  | hall φ ih =>
    obtain ⟨s, hs⟩ := ih;
    exact ⟨s + 2, (pi (hs 𝚺)).accum⟩
  | hexs φ ih =>
    obtain ⟨s, hs⟩ := ih
    exact ⟨s + 2, (sigma (hs 𝚷)).accum⟩

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

-- The sequent bookkeeping in `Witnessing.lean` (`Γ + ⦃φ⦄` membership) relies on
-- `Multiset.mem_atom_iff`; it is `@[simp]` upstream but not `@[grind]`. `Multiset.mem_add` is
-- already `@[simp, grind =]` in Mathlib.
attribute [grind =] Multiset.mem_atom_iff
