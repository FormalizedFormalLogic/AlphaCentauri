module

public import AlphaCentauri.Calculus.Induction.Basic
public import AlphaCentauri.ToFoundation.Schemata
public import Foundation.FirstOrder.LK.Hauptsatz

/-!
# Forcing over anchored derivations

Avigad's algebraic proof of cut elimination reads a sequent `Γ` as a forcing condition and the
cut-free derivations of `∼Γ` as the proofs of `⊥` over it. Taking instead the `D`-anchored
derivations of `LKI[C]` as the base gives a forcing relation over which `LJ` is still sound, so
that a classical proof from axioms that are forced yields an anchored derivation: free cuts are
eliminated, and the cuts on the axioms remain.

- [Avi01]
- [Bus98A, Section 1.4.2]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.LKI

open Rewriting LawfulSyntacticRewriting
open LK.Derivation.Canonical (StrongerThan inf_def)
open scoped FFL.FirstOrder.Derivation.Canonical

variable {C : ArithmeticSemiformula ℕ 1 → Prop} {D : ArithmeticProposition → Prop}
  {Ξ Γ : LK.Sequent ℒₒᵣ}

namespace Derivation

/-- Grafting a derivation below a positive path, which is where the anchored derivations of the
weaker conditions come from.

- [Avi01, Section 3] -/
def graft {Ξ Γ : LK.Sequent ℒₒᵣ} (b : ⊢ᴸᴷᴵ[C]! Ξ) : (Ξ ⟶⁺ Γ) → ⊢ᴸᴷᴵ[C]! Γ
  | .or d => (b.graft d).or
  | .exs d => (b.graft d).exs
  | .weakening d => (b.graft d).weakening
  | .contraction d => (b.graft d).contraction
  | .refl => b

@[simp] lemma anchored_graft_iff {Ξ : LK.Sequent ℒₒᵣ} {b : ⊢ᴸᴷᴵ[C]! Ξ} :
    ∀ {Γ} (d : Ξ ⟶⁺ Γ), Anchored D (b.graft d) ↔ Anchored D b
  | _, .or d => by simpa [graft] using anchored_graft_iff d
  | _, .exs d => by simpa [graft] using anchored_graft_iff d
  | _, .weakening d => by simpa [graft] using anchored_graft_iff d
  | _, .contraction d => by simpa [graft] using anchored_graft_iff d
  | _, .refl => by simp [graft]

end Derivation

namespace Canonical

variable {Γ Δ : LK.Sequent ℒₒᵣ} {φ ψ : Propositionᵢ ℒₒᵣ} {χ : ArithmeticProposition}

/-- Forcing over the `D`-anchored derivations of `LKI[C]`: a condition is a sequent `Γ`, and the
proofs of `⊥` over it are the anchored derivations of `∼Γ`.

- [Avi01, Section 3] -/
def Forces (C : ArithmeticSemiformula ℕ 1 → Prop) (D : ArithmeticProposition → Prop)
    (Γ : LK.Sequent ℒₒᵣ) : Propositionᵢ ℒₒᵣ → Type
  |        ⊥ => ⊢ᴸᴷᴵ[C, D]! ∼Γ
  | .rel R v => ⊢ᴸᴷᴵ[C, D]! ∼Γ + ⦃Semiformula.rel R v⦄
  |    φ ⋏ ψ => Forces C D Γ φ × Forces C D Γ ψ
  |    φ ⋎ ψ => Forces C D Γ φ ⊕ Forces C D Γ ψ
  |    φ 🡒 ψ => (Δ : LK.Sequent ℒₒᵣ) → Δ ≼ Γ → Forces C D Δ φ → Forces C D Δ ψ
  |     ∀¹ φ => (t : ArithmeticTerm ℕ) → Forces C D Γ (φ/[t])
  |     ∃¹ φ => (t : ArithmeticTerm ℕ) × Forces C D Γ (φ/[t])
  termination_by φ => φ.complexity

@[inherit_doc] notation:45 Γ:45 " ⊩[" C ", " D "] " φ:45 => Forces C D Γ φ

namespace Forces

def falsumEquiv : (Γ ⊩[C, D] ⊥) ≃ ⊢ᴸᴷᴵ[C, D]! ∼Γ := by
  unfold Forces; exact .refl _

def relEquiv {k} {R : (ℒₒᵣ).Rel k} {v} :
    (Γ ⊩[C, D] .rel R v) ≃ ⊢ᴸᴷᴵ[C, D]! ∼Γ + ⦃Semiformula.rel R v⦄ := by
  unfold Forces; exact .refl _

def andEquiv : (Γ ⊩[C, D] φ ⋏ ψ) ≃ (Γ ⊩[C, D] φ) × (Γ ⊩[C, D] ψ) := by
  conv => lhs; unfold Forces; exact .refl _

def orEquiv : (Γ ⊩[C, D] φ ⋎ ψ) ≃ ((Γ ⊩[C, D] φ) ⊕ (Γ ⊩[C, D] ψ)) := by
  conv => lhs; unfold Forces; exact .refl _

def implyEquiv :
    (Γ ⊩[C, D] φ 🡒 ψ) ≃ ((Δ : LK.Sequent ℒₒᵣ) → Δ ≼ Γ → (Δ ⊩[C, D] φ) → Δ ⊩[C, D] ψ) := by
  conv => lhs; unfold Forces; exact .refl _

def allEquiv {φ} : (Γ ⊩[C, D] ∀¹ φ) ≃ ((t : ArithmeticTerm ℕ) → Forces C D Γ (φ/[t])) := by
  conv => lhs; unfold Forces; exact .refl _

def exsEquiv {φ} : (Γ ⊩[C, D] ∃¹ φ) ≃ ((t : ArithmeticTerm ℕ) × Forces C D Γ (φ/[t])) := by
  conv => lhs; unfold Forces; exact .refl _

def cast (f : Γ ⊩[C, D] φ) (e : φ = ψ) : Γ ⊩[C, D] ψ := e ▸ f

def monotone (s : Δ ≼ Γ) : {φ : Propositionᵢ ℒₒᵣ} → (Γ ⊩[C, D] φ) → Δ ⊩[C, D] φ
  | ⊥, b =>
    let ⟨d, hd⟩ := b.falsumEquiv
    falsumEquiv.symm ⟨d.graft s.val, by simpa using hd⟩
  | .rel R v, b =>
    let ⟨d, hd⟩ := b.relEquiv
    relEquiv.symm ⟨d.graft (s.val.cons (Semiformula.rel R v)), by simpa using hd⟩
  | _ ⋏ _, b => andEquiv.symm ⟨monotone s b.andEquiv.1, monotone s b.andEquiv.2⟩
  | _ ⋎ _, b =>
    orEquiv.symm <| b.orEquiv.rec (fun b ↦ .inl <| b.monotone s) (fun b ↦ .inr <| b.monotone s)
  | _ 🡒 _, b => implyEquiv.symm fun Θ s' bφ ↦ b.implyEquiv Θ (s'.trans s) bφ
  | ∀¹ _, b => allEquiv.symm fun t ↦ (b.allEquiv t).monotone s
  | ∃¹ φ, b =>
    let ⟨t, d⟩ : (t : ArithmeticTerm ℕ) × (Γ ⊩[C, D] φ/[t]) := b.exsEquiv
    exsEquiv.symm ⟨t, d.monotone s⟩
  termination_by φ => φ.complexity

def explosion {Γ} (b : Γ ⊩[C, D] ⊥) : (φ : Propositionᵢ ℒₒᵣ) → Γ ⊩[C, D] φ
  | ⊥ => b
  | .rel R v =>
    let ⟨d, hd⟩ := b.falsumEquiv
    relEquiv.symm ⟨d.weakening, hd⟩
  | φ ⋏ ψ => andEquiv.symm ⟨b.explosion φ, b.explosion ψ⟩
  | φ ⋎ _ => orEquiv.symm <| .inl <| b.explosion φ
  | _ 🡒 ψ => implyEquiv.symm fun Δ s _ ↦ (b.monotone s).explosion ψ
  | ∀¹ φ => allEquiv.symm fun t ↦ b.explosion (φ/[t])
  | ∃¹ φ => exsEquiv.symm ⟨default, b.explosion (φ/[default])⟩
  termination_by φ => φ.complexity

def implyOf (tΓ : (∼Γ).Traversal)
    (b : (Δ : LK.Sequent ℒₒᵣ) → (∼Δ).Traversal → (Δ ⊩[C, D] φ) → Γ ⊓ Δ ⊩[C, D] ψ) :
    Γ ⊩[C, D] φ 🡒 ψ := implyEquiv.symm fun Δ s fφ ↦
  let tΔ := s.val.traversal tΓ
  (b Δ tΔ fφ).monotone (StrongerThan.leMinRightOfLe s tΔ)

def modusPonens (f : Γ ⊩[C, D] φ 🡒 ψ) (g : Γ ⊩[C, D] φ) : Γ ⊩[C, D] ψ :=
  f.implyEquiv Γ (StrongerThan.refl Γ) g

end Forces

/-- A condition forcing every formula of an `LJ` context. -/
abbrev ContextForces (C : ArithmeticSemiformula ℕ 1 → Prop) (D : ArithmeticProposition → Prop)
    (Γ : LK.Sequent ℒₒᵣ) (Λ : LJ.Sequent ℒₒᵣ) := (φ : Propositionᵢ ℒₒᵣ) → φ ∈ Λ → Γ ⊩[C, D] φ

namespace ContextForces

variable {Λ Λ' : LJ.Sequent ℒₒᵣ}

def ofSubset (b : ContextForces C D Γ Λ') (h : Λ ⊆ Λ') : ContextForces C D Γ Λ :=
  fun φ hφ ↦ b φ (h hφ)

def monotone (b : ContextForces C D Γ Λ) (s : Δ ≼ Γ) : ContextForces C D Δ Λ :=
  fun φ hφ ↦ (b φ hφ).monotone s

def atom (b : Γ ⊩[C, D] φ) : ContextForces C D Γ ⦃φ⦄ :=
  fun _ hψ ↦ b.cast (Multiset.mem_singleton.mp hψ).symm

def cons (b : ContextForces C D Γ Λ) (hφ : Γ ⊩[C, D] φ) : ContextForces C D Γ (Λ + ⦃φ⦄) :=
  fun ψ hψ ↦ if h : φ = ψ then hφ.cast h else b ψ (by simp_all [eq_comm])

end ContextForces

/-- A condition forcing the succedent of an `LJ` sequent. -/
def HeadForces (C : ArithmeticSemiformula ℕ 1 → Prop) (D : ArithmeticProposition → Prop)
    (Γ : LK.Sequent ℒₒᵣ) : LJ.Head ℒₒᵣ → Type
  | none => Γ ⊩[C, D] ⊥
  | some φ => Γ ⊩[C, D] φ

namespace Forces

private lemma rewrite_shift_eq (t : ArithmeticTerm ℕ) (φ : Propositionᵢ ℒₒᵣ) :
    Rew.rewrite (t :>ₙ fun x ↦ &x) ▹ Rewriting.shift φ = φ := by
  rw [← TransitiveRewriting.comp_app, Rew.rewrite_comp_shift_eq_id, ReflectiveRewriting.id_app]

/-- Soundness of `LJ` for forcing over anchored derivations.

- [Avi01, Section 3] -/
def sound {Λ : LJ.Sequent ℒₒᵣ} {Ξ : LJ.Head ℒₒᵣ}
    (d : Λ ⊢ᴸᴶ¹ Ξ) (Γ : LK.Sequent ℒₒᵣ) (tΓ : (∼Γ).Traversal)
    (b : ContextForces C D Γ Λ) : HeadForces C D Γ Ξ :=
  match d with
  | .identity R v => b (.rel R v) (by simp)
  | .cut dφ d =>
      let bΛ := b.ofSubset (by intro ψ hψ; simp_all)
      let bΛ' := b.ofSubset (by intro ψ hψ; simp_all)
      sound d Γ tΓ <| bΛ'.cons (sound dφ Γ tΓ bΛ)
  | .contraction d => sound d Γ tΓ fun ψ hψ ↦ b ψ (by simp_all)
  | .weakening d => sound d Γ tΓ (b.ofSubset Multiset.subset_add_left)
  | .weakeningRight d => (sound d Γ tΓ b).explosion _
  | .verum => implyEquiv.symm fun _ _ h ↦ h
  | .falsum => b ⊥ (by simp)
  | .positiveImply d => implyEquiv.symm fun Δ s bφ ↦
      sound d Δ (s.val.traversal tΓ) <| (b.monotone s).cons bφ
  | .negativeImply (φ := φ) (ψ := ψ) dφ d =>
      let bΛ := b.ofSubset (by intro θ hθ; simp_all)
      let bΛ' := b.ofSubset (by intro θ hθ; simp_all)
      let bi : Γ ⊩[C, D] φ 🡒 ψ := b _ (by simp)
      sound d Γ tΓ <| bΛ'.cons (bi.modusPonens <| sound dφ Γ tΓ bΛ)
  | .positiveAnd dφ dψ => andEquiv.symm ⟨sound dφ Γ tΓ b, sound dψ Γ tΓ b⟩
  | .negativeAnd (φ := φ) (ψ := ψ) (Γ := Λ) d =>
      let bΛ : ContextForces C D Γ Λ := b.ofSubset Multiset.subset_add_left
      let ⟨bφ, bψ⟩ := (b (φ ⋏ ψ) (by simp)).andEquiv
      sound d Γ tΓ <| ((bΛ.cons bφ).cons bψ).ofSubset
        (by intro θ hθ; simpa [add_assoc] using hθ)
  | .positiveOrLeft d => orEquiv.symm <| .inl <| sound d Γ tΓ b
  | .positiveOrRight d => orEquiv.symm <| .inr <| sound d Γ tΓ b
  | .negativeOr (φ := φ) (ψ := ψ) dφ dψ =>
      let bΛ := b.ofSubset (by intro θ hθ; simp_all)
      (b (φ ⋎ ψ) (by simp)).orEquiv.rec
        (fun bφ ↦ sound dφ Γ tΓ <| bΛ.cons bφ)
        (fun bψ ↦ sound dψ Γ tΓ <| bΛ.cons bψ)
  | .positiveForall (Γ := Λ) (φ := φ) d => allEquiv.symm fun t ↦
      let f : ℕ → ArithmeticTerm ℕ := t :>ₙ fun x ↦ &x
      let dt : Λ ⊢ᴸᴶ¹ some (φ/[t]) := (d.rewrite f).cast
        (by simp [f, Rewriting.shifts, Multiset.map_map, rewrite_shift_eq])
        (by simp [f, LJ.Head.rewrite, rewrite_free_eq_subst])
      sound dt Γ tΓ b
  | .negativeForall (φ := φ) d =>
      let bΛ := b.ofSubset (by intro θ hθ; simp_all)
      let bAll := (b (∀¹ φ) (by simp)).allEquiv _
      sound d Γ tΓ <| bΛ.cons bAll
  | .positiveExists (t := t) d => exsEquiv.symm ⟨t, sound d Γ tΓ b⟩
  | .negativeExists (Γ := Λ) (Ξ := Ξ) (φ := φ) d =>
      let ⟨t, bt⟩ := (b (∃¹ φ) (by simp)).exsEquiv
      let f : ℕ → ArithmeticTerm ℕ := t :>ₙ fun x ↦ &x
      let dt : Λ + ⦃φ/[t]⦄ ⊢ᴸᴶ¹ Ξ := (d.rewrite f).cast
        (by simp [f, Rewriting.shifts, Multiset.map_map, rewrite_shift_eq, rewrite_free_eq_subst])
        (by cases Ξ <;> simp [f, LJ.Head.shift, LJ.Head.rewrite, rewrite_shift_eq])
      let bΛ := b.ofSubset (by intro θ hθ; simp_all)
      sound dt Γ tΓ <| bΛ.cons bt
  termination_by d.height
  decreasing_by
    all_goals simp [LJ.Derivation.height]
    all_goals try omega
    all_goals
      exact Nat.lt_succ_iff.mpr <| Nat.le_of_eq <|
        (LJ.Derivation.height_cast _ _ _).trans (LJ.Derivation.height_rewrite (t :>ₙ fun x ↦ &x) d)

/-! ## The reflexive forcing of a formula by itself -/

variable [RewriteClosed C] [RewriteClosed D]

-- Transparency is lowered for the structural recursion through translated formulas.
set_option backward.isDefEq.respectTransparency false in
/-- Every formula is forced by the condition consisting of itself.

- [Avi01, Section 3] -/
protected def refl : (φ : ArithmeticProposition) → ⦃φ⦄ ⊩[C, D] φᴺ
  |         ⊤ => implyEquiv.symm fun _ _ dφ ↦ dφ
  |         ⊥ => falsumEquiv.symm ⟨Derivation.verum, by simp⟩
  |  .rel R v => implyOf (.atom _) fun Δ tΔ dΔ ↦
    let tr : (∼(⦃Semiformula.rel R v⦄ : LK.Sequent ℒₒᵣ)).Traversal := .atom _
    let b : ⦃Semiformula.rel R v⦄ ⊓ Δ ⊩[C, D] .rel R v :=
      (relEquiv.symm ⟨Derivation.cast <| Derivation.identity R v, by simp⟩).monotone
        (StrongerThan.minLeLeft _ _ tΔ)
    dΔ.implyEquiv (⦃Semiformula.rel R v⦄ ⊓ Δ) (StrongerThan.minLeRight _ _ tr) b
  | .nrel R v => implyOf (.atom _) fun Δ _ dΔ ↦
    let ⟨d, hd⟩ := dΔ.relEquiv
    falsumEquiv.symm ⟨Derivation.cast d (by simp [inf_def]; abel), by simpa using hd⟩
  |     φ ⋏ ψ =>
    let ihφ : ⦃φ⦄ ⊩[C, D] φᴺ := Forces.refl φ
    let ihψ : ⦃ψ⦄ ⊩[C, D] ψᴺ := Forces.refl ψ
    andEquiv.symm ⟨by simpa using ihφ.monotone (.K_left (p := 0) φ ψ),
      by simpa using ihψ.monotone (.K_right (p := 0) φ ψ)⟩
  |     φ ⋎ ψ =>
    let ihφ : ⦃φ⦄ ⊩[C, D] φᴺ := Forces.refl φ
    let ihψ : ⦃ψ⦄ ⊩[C, D] ψᴺ := Forces.refl ψ
    implyOf (.atom _) fun Δ tΔ dΔ ↦
      let ⟨dφ, dψ⟩ : (Δ ⊩[C, D] ∼φᴺ) × (Δ ⊩[C, D] ∼ψᴺ) := dΔ.andEquiv
      let tφ : (∼(⦃φ⦄ : LK.Sequent ℒₒᵣ)).Traversal := .atom _
      let tψ : (∼(⦃ψ⦄ : LK.Sequent ℒₒᵣ)).Traversal := .atom _
      let bφ : ⦃φ⦄ ⊓ Δ ⊩[C, D] ⊥ :=
        dφ.implyEquiv (⦃φ⦄ ⊓ Δ) (.minLeRight _ _ tφ) (ihφ.monotone (.minLeLeft _ _ tΔ))
      let bψ : ⦃ψ⦄ ⊓ Δ ⊩[C, D] ⊥ :=
        dψ.implyEquiv (⦃ψ⦄ ⊓ Δ) (.minLeRight _ _ tψ) (ihψ.monotone (.minLeLeft _ _ tΔ))
      let ⟨bbφ, hbbφ⟩ := bφ.falsumEquiv
      let ⟨bbψ, hbbψ⟩ := bψ.falsumEquiv
      let bbφ' : ⊢ᴸᴷᴵ[C]! ∼Δ + ⦃∼φ⦄ := Derivation.cast bbφ (by simp [inf_def]; abel)
      let bbψ' : ⊢ᴸᴷᴵ[C]! ∼Δ + ⦃∼ψ⦄ := Derivation.cast bbψ (by simp [inf_def]; abel)
      let band : ⊢ᴸᴷᴵ[C]! ∼Δ + ⦃∼φ ⋏ ∼ψ⦄ := Derivation.and bbφ' bbψ'
      falsumEquiv.symm ⟨Derivation.cast band (by simp [inf_def]; abel), by
        simpa [band, bbφ', bbψ'] using And.intro hbbφ hbbψ⟩
  |      ∀¹ φ => allEquiv.symm fun t ↦
    let b : ⦃φ/[t]⦄ ⊩[C, D] φᴺ/[t] := by
      simpa [Semiformula.rew_doubleNegation] using Forces.refl (φ/[t])
    by simpa using b.monotone (StrongerThan.all (p := 0) φ t)
  |      ∃¹ φ => implyOf (.atom _) fun Δ tΔ f ↦
    let x := LK.Sequent.newVar (∼Δ + ⦃∀¹ ∼φ⦄)
    let ih : ⦃φ/[&x]⦄ ⊩[C, D] φᴺ/[&x] :=
      cast (Forces.refl (φ/[&x])) (by simp [Semiformula.subst_doubleNegation])
    let b : ⦃φ/[&x]⦄ ⊓ Δ ⊩[C, D] ⊥ :=
      let tφ : (∼(⦃φ/[&x]⦄ : LK.Sequent ℒₒᵣ)).Traversal := .atom _
      (f.allEquiv &x).implyEquiv (⦃φ/[&x]⦄ ⊓ Δ)
        (StrongerThan.minLeRight _ _ tφ) (ih.monotone (StrongerThan.minLeLeft _ _ tΔ))
    let ⟨b, hb⟩ := b.falsumEquiv
    let hp : ¬(∼φ).FVar? x := by
      have : ¬(∀¹ ∼φ).FVar? x := LK.Sequent.not_fvar?_newVar (by simp)
      simpa using this
    let hq : ∀ ψ ∈ ∼Δ, ¬ψ.FVar? x := fun ψ hψ ↦ LK.Sequent.not_fvar?_newVar (by simp [hψ])
    let b' : ⊢ᴸᴷᴵ[C]! ∼Δ + ⦃(∼φ)/[&x]⦄ := Derivation.cast b (by simp [inf_def]; abel)
    let ba : ⊢ᴸᴷᴵ[C]! ∼Δ + ⦃∀¹ ∼φ⦄ := Derivation.generalizeByNewVar hp hq b'
    falsumEquiv.symm ⟨Derivation.cast ba (by simp [inf_def]; abel), by
      simpa [ba, b'] using Derivation.anchored_generalizeByNewVar (by simpa [b'] using hb)⟩
  termination_by φ => φ.complexity

/-! ## Forcing and anchored derivations -/

def castCondition {Γ Δ : LK.Sequent ℒₒᵣ} (f : Γ ⊩[C, D] φ) (e : Γ = Δ) : Δ ⊩[C, D] φ := e ▸ f

/-- The cut that `cutForces` performs: a cut against a formula of `D`, followed by the
contraction that merges the two copies of the condition. -/
def cutAnchored {Γ Θ : LK.Sequent ℒₒᵣ} (hχ : D χ)
    (tΓ : (∼Γ).Traversal) (d : ⊢ᴸᴷᴵ[C, D]! ∼Γ + ⦃χ⦄)
    (e : ⊢ᴸᴷᴵ[C, D]! ∼Γ + ⦃∼χ⦄ + Θ) : ⊢ᴸᴷᴵ[C, D]! ∼Γ + Θ :=
  let dc : ⊢ᴸᴷᴵ[C]! Θ + (∼Γ + ∼Γ) :=
    Derivation.cast (Derivation.cut (Γ := ∼Γ) (Δ := ∼Γ + Θ) (φ := χ) d.val (e.val.cast (by abel)))
  let s : (∼Γ + ∼Γ : LK.Sequent ℒₒᵣ) ⟶⁺ ∼Γ :=
    (StrongerThan.leMinRightOfLe (StrongerThan.refl Γ) tΓ).val.cast (by simp [inf_def]) rfl
  ⟨Derivation.cast (dc.graft (s.addLeft Θ)), by simp [dc, hχ, d.prop, e.prop]⟩

/-- A cut against a formula of `D` is absorbed into the forcing relation.

- [Bus98A, Section 1.4.2] -/
def cutForces (hχ : D χ) :
    {Γ : LK.Sequent ℒₒᵣ} → (∼Γ).Traversal → ⊢ᴸᴷᴵ[C, D]! ∼Γ + ⦃χ⦄ →
      {ψ : Propositionᵢ ℒₒᵣ} → (Γ + ⦃χ⦄ ⊩[C, D] ψ) → Γ ⊩[C, D] ψ
  | _, tΓ, d, ⊥, b =>
    falsumEquiv.symm <|
      cutAnchored (Θ := 0) hχ tΓ d (b.falsumEquiv.cast (by simp)) |>.cast (by simp)
  | _, tΓ, d, .rel R v, b =>
    relEquiv.symm <| cutAnchored (Θ := ⦃Semiformula.rel R v⦄) hχ tΓ d (b.relEquiv.cast (by simp))
  | _, tΓ, d, _ ⋏ _, b =>
    andEquiv.symm ⟨cutForces hχ tΓ d b.andEquiv.1, cutForces hχ tΓ d b.andEquiv.2⟩
  | _, tΓ, d, _ ⋎ _, b =>
    orEquiv.symm <| b.orEquiv.rec
      (fun b ↦ .inl <| cutForces hχ tΓ d b) (fun b ↦ .inr <| cutForces hχ tΓ d b)
  | Γ, tΓ, d, _ 🡒 _, b => implyEquiv.symm fun Δ sΔ bφ ↦
    let sχ : Δ + ⦃χ⦄ ≼ Γ + ⦃χ⦄ := ⟨(sΔ.val.cons (∼χ)).cast (by simp) (by simp)⟩
    let s₀ : Δ + ⦃χ⦄ ≼ Δ := ⟨(LK.Derivation.Positive.weakening (φ := ∼χ) .refl).cast rfl (by simp)⟩
    cutForces hχ (sΔ.val.traversal tΓ) ⟨d.val.graft (sΔ.val.cons χ), by simp [d.prop]⟩
      (b.implyEquiv (Δ + ⦃χ⦄) sχ (bφ.monotone s₀))
  | _, tΓ, d, ∀¹ _, b => allEquiv.symm fun t ↦ cutForces hχ tΓ d (b.allEquiv t)
  | _, tΓ, d, ∃¹ _, b =>
    let ⟨t, f⟩ := b.exsEquiv
    exsEquiv.symm ⟨t, cutForces hχ tΓ d f⟩
  termination_by _ _ _ ψ _ => ψ.complexity

/-- A formula of `D` with an anchored derivation of it over `∼Γ` is forced by `Γ`: the converse
of `derivableOfForced`.

- [Bus98A, Section 1.4.2] -/
def forcesOfAnchored (hχ : D χ) (tΓ : (∼Γ).Traversal) (d : ⊢ᴸᴷᴵ[C, D]! ∼Γ + ⦃χ⦄) :
    Γ ⊩[C, D] χᴺ :=
  cutForces hχ tΓ d <|
    ((Forces.refl χ).monotone (StrongerThan.minLeRight Γ ⦃χ⦄ tΓ)).castCondition (inf_def Γ ⦃χ⦄)

/-- A condition forcing the translation of `χ` yields an anchored derivation of `χ` over the
negated condition.

- [Bus98A, Section 1.4.2] -/
def derivableOfForced (tΓ : (∼Γ).Traversal) (f : Γ ⊩[C, D] χᴺ) : ⊢ᴸᴷᴵ[C, D]! ∼Γ + ⦃χ⦄ :=
  let tχ : (∼(⦃∼χ⦄ : LK.Sequent ℒₒᵣ)).Traversal := .atom _
  let b : Γ ⊓ ⦃∼χ⦄ ⊩[C, D] ∼χᴺ :=
    sound (LJ.Derivation.negDoubleNegation χ).2 (Γ ⊓ ⦃∼χ⦄) ((tΓ.add tχ).cast (by simp [inf_def]))
      fun ψ hψ ↦ ((Forces.refl (∼χ)).monotone (StrongerThan.minLeRight Γ ⦃∼χ⦄ tΓ)).cast
        (Multiset.mem_singleton.mp hψ).symm
  (b.modusPonens (f.monotone (StrongerThan.minLeLeft Γ ⦃∼χ⦄ tχ))).falsumEquiv.cast
    (by simp [inf_def])

/-! ## The translated connectives -/

/-- Transporting a forced formula along an `LJ` derivation from it. -/
def ofLJ (tΓ : (∼Γ).Traversal) (d : ⦃φ⦄ ⊢ᴸᴶ¹ ψ) (b : Γ ⊩[C, D] φ) : Γ ⊩[C, D] ψ :=
  sound d Γ tΓ (.atom b)

variable {χ' : ArithmeticProposition}

/-- Forcing the translation of an implication: it is enough to turn a forced antecedent into a
forced consequent at every stronger condition. -/
def forcesImply (tΓ : (∼Γ).Traversal)
    (b : (Δ : LK.Sequent ℒₒᵣ) → (s : Δ ≼ Γ) → (Δ ⊩[C, D] χᴺ) → Δ ⊩[C, D] χ'ᴺ) :
    Γ ⊩[C, D] (χ 🡒 χ')ᴺ :=
  Forces.cast (implyEquiv.symm fun Δ s c ↦
    let tΔ := s.val.traversal tΓ
    let ⟨c₁, c₂⟩ := c.andEquiv
    c₂.modusPonens <| b Δ s <| ofLJ tΔ (LJ.Derivation.negDoubleNegation' χ).1 c₁)
    (Semiformula.doubleNegation_imply χ χ').symm

/-- Using the translation of an implication. -/
def modusPonensImply (tΓ : (∼Γ).Traversal) (f : Γ ⊩[C, D] (χ 🡒 χ')ᴺ) (b : Γ ⊩[C, D] χᴺ) :
    Γ ⊩[C, D] χ'ᴺ :=
  let f : Γ ⊩[C, D] ∼(∼(∼χ)ᴺ ⋏ ∼χ'ᴺ) := f.cast (Semiformula.doubleNegation_imply χ χ')
  let g : Γ ⊩[C, D] ∼(∼χ'ᴺ) := implyEquiv.symm fun Δ s c ↦
    (f.monotone s).modusPonens <| andEquiv.symm
      ⟨ofLJ (s.val.traversal tΓ) (LJ.Derivation.negDoubleNegation' χ).2 (b.monotone s), c⟩
  ofLJ tΓ (LJ.Derivation.dneOfNegative (by simp)) g

/-! ## Universal closure -/

/-- A condition forcing every substitution instance of `ψ` forces its universal closure. -/
def forcesAllClosure : {n : ℕ} → (ψ : ArithmeticSemiformula ℕ n) →
    ((v : Fin n → ArithmeticTerm ℕ) → Γ ⊩[C, D] (ψ⇜v)ᴺ) → Γ ⊩[C, D] (∀¹* ψ)ᴺ
  | 0, ψ, h => (h ![]).cast (by simp)
  | _ + 1, ψ, h => by
    refine forcesAllClosure (∀¹ ψ) fun v ↦ ?_
    rw [show ((∀¹ ψ)⇜v : ArithmeticProposition) = ∀¹ ((Rew.subst v).q ▹ ψ) from rfl]
    exact allEquiv.symm fun t ↦ (h (t :> v)).cast (by
      rw [Semiformula.subst_doubleNegation, Rew.subst_q_app])

/-- A condition forcing every rewriting of `χ` forces its universal closure. -/
def forcesUnivCl (h : (f : ℕ → ArithmeticTerm ℕ) → Γ ⊩[C, D] (Rew.rewrite f ▹ χ)ᴺ) :
    Γ ⊩[C, D] (χ.univCl')ᴺ :=
  forcesAllClosure _ fun v ↦
    (h fun x ↦ if hx : x < χ.fvSup then v ⟨x, by omega⟩ else default).cast (by
      have e : (fun x : Fin (0 + χ.fvSup) ↦
          if hx : (x : ℕ) < χ.fvSup then v ⟨x, by omega⟩ else default) = v := by
        funext x
        have hx : (x : ℕ) < χ.fvSup := by simpa using x.isLt
        simp [hx]
      rw [← Semiformula.subst_comp_fixitr_eq_map χ, e])

/-! ## The induction axiom -/

/-- The induction axiom for a formula of `C` is forced: the induction rule of the calculus does
the work, so no induction on `ℕ` enters the argument.

- [Bus98A, Section 1.4.2] -/
def forcesSuccInd {ξ : ArithmeticSemiformula ℕ 1} (hξ : C ξ) (hD : ∀ t, D (ξ/[t]))
    (tΓ : (∼Γ).Traversal) : Γ ⊩[C, D] (succInd ξ)ᴺ := by
  rw [show (succInd ξ : ArithmeticProposition)
      = (ξ/[‘0’]) 🡒 ((∀¹ (ξ 🡒 ξ/[‘(#0 + 1)’])) 🡒 ∀¹ ξ) from by simp [succInd]]
  refine forcesImply tΓ fun Δ s g₀ ↦ forcesImply (s.val.traversal tΓ) fun Θ s' gstep ↦ ?_
  let tΘ : (∼Θ).Traversal := s'.val.traversal (s.val.traversal tΓ)
  refine allEquiv.symm fun t ↦ ?_
  rw [Semiformula.subst_doubleNegation]
  -- `Θ ⊩ (ξ/[t])ᴺ`, by the induction rule at a variable fresh for `Θ` and `ξ`
  refine forcesOfAnchored (hD t) tΘ ?_
  let m := LK.Sequent.newVar (∼Θ + ⦃∀¹ ξ⦄)
  have hξm : ¬ξ.FVar? m := by
    have : ¬(∀¹ ξ).FVar? m := LK.Sequent.not_fvar?_newVar (by simp)
    simpa using this
  have hΘ : ∀ ψ ∈ ∼Θ, ¬ψ.FVar? m := fun ψ hψ ↦ LK.Sequent.not_fvar?_newVar (by simp [hψ])
  -- the base case
  let d₀ : ⊢ᴸᴷᴵ[C, D]! ∼Θ + ⦃ξ/[‘0’]⦄ := derivableOfForced tΘ (g₀.monotone s')
  -- the step case, at the condition `Θ` extended by the induction hypothesis
  let tΘ' : (∼(Θ + ⦃ξ/[&m]⦄)).Traversal := (tΘ.add (.atom (∼(ξ/[&m])))).cast (by simp)
  let sΘ' : Θ + ⦃ξ/[&m]⦄ ≼ Θ :=
    ⟨(LK.Derivation.Positive.weakening (φ := ∼(ξ/[&m])) .refl).cast rfl (by simp)⟩
  let gxy : Θ ⊩[C, D] (ξ/[&m] 🡒 ξ/[‘&m + 1’])ᴺ := (gstep.allEquiv &m).cast (by
    simp [Semiformula.subst_doubleNegation, Rew.subst_subst_eq])
  let gY : Θ + ⦃ξ/[&m]⦄ ⊩[C, D] (ξ/[‘&m + 1’])ᴺ :=
    modusPonensImply tΘ' (gxy.monotone sΘ')
      ((Forces.refl (ξ/[&m])).monotone (StrongerThan.ofSubset (.atom _) tΘ' (by simp)))
  let dstep : ⊢ᴸᴷᴵ[C, D]! ∼Θ + ⦃∼(ξ/[&m]), ξ/[‘&m + 1’]⦄ :=
    (derivableOfForced tΘ' gY).cast (by simp; abel)
  exact ⟨Derivation.indByNewVar hξ t hξm hΘ d₀.val dstep.val,
    Derivation.anchored_indByNewVar d₀.prop dstep.prop⟩

/-- Every axiom of the `C`-induction scheme is forced.

- [Bus98A, Section 1.4.2] -/
def forcesInd {ξ : ArithmeticSemiformula ℕ 1}
    (hCD : (η : ArithmeticSemiformula ℕ 1) → C η → ∀ t, D (η/[t])) (hξ : C ξ)
    (tΓ : (∼Γ).Traversal) : Γ ⊩[C, D] ((succInd ξ).univCl')ᴺ :=
  forcesUnivCl fun f ↦
    let hq : C ((Rew.rewrite f).q ▹ ξ) := by
      simpa [Rew.q_rewrite] using RewriteClosed.rewrite (C := C) (Rew.bShift ∘ f) hξ
    (forcesSuccInd hq (hCD _ hq) tΓ).cast (by rw [rew_succInd])

end Forces

/-! ## Free-cut elimination -/

open Forces in
/-- Free-cut elimination: a classical proof of `Γ` from axioms that are forced by the empty
condition becomes a `D`-anchored derivation of `Γ`. The cuts on the axioms survive, and every
other cut is eliminated.

- [Bus98A, Section 1.4.2]
- [Avi01, Section 3] -/
def hauptsatz [RewriteClosed C] [RewriteClosed D] {Γ Δ : LK.Sequent ℒₒᵣ}
    (tΓ : Γ.Traversal) (tΔ : Δ.Traversal)
    (hΔ : (φ : ArithmeticProposition) → φ ∈ Δ → (0 ⊩[C, D] φᴺ))
    (d : ⊢ᴸᴷ¹ Γ + ∼Δ) : ⊢ᴸᴷᴵ[C, D]! Γ :=
  let t : (∼(∼Γ)).Traversal := tΓ.cast (by simp)
  let g : ContextForces C D (∼Γ) (∼(Γ + ∼Δ))ᴺ := fun ψ hψ ↦
    if h : ψ ∈ (∼Γ : LK.Sequent ℒₒᵣ)ᴺ then
      let φ₀ := (tΓ.map (∼·)).getPreimage (f := Semiformula.doubleNegation) h
      let hφ₀ : ∼(φ₀.val) ∈ Γ := by
        obtain ⟨a, ha, e⟩ := Multiset.mem_map.mp φ₀.property.1
        simpa [← e] using ha
      ((Forces.refl φ₀.val).monotone
        (StrongerThan.ofSubset (.atom _) t (by simpa using hφ₀))).cast φ₀.property.2
    else
      let φ₀ := tΔ.getPreimage (f := Semiformula.doubleNegation) (by
        have h₂ : ψ ∈ (∼Γ : LK.Sequent ℒₒᵣ)ᴺ + Δᴺ := by simpa using hψ
        rcases Multiset.mem_add.mp h₂ with h₃ | h₃
        · exact absurd h₃ h
        · exact h₃)
      ((hΔ φ₀.val φ₀.property.1).monotone
        (StrongerThan.ofSubset (Multiset.Traversal.zero.cast (by simp)) t
          (by simp))).cast φ₀.property.2
  (sound d.gödelGentzen (∼Γ) t g).falsumEquiv.cast (by simp)

end Canonical

end FFL.FirstOrder.Arithmetic.LKI

end
