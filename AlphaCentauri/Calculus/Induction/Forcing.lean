module

public import AlphaCentauri.Calculus.Induction.Basic
public import AlphaCentauri.Calculus.Induction.Theory
public import Foundation.FirstOrder.LK.Hauptsatz

/-!
# Forcing over anchored derivations

Avigad's algebraic proof of cut elimination reads a sequent `p` as a forcing condition and the
cut-free derivations of `∼p` as the proofs of `⊥` over it. Taking instead the `D`-anchored
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

variable {p q : LK.Sequent ℒₒᵣ} {φ ψ : Propositionᵢ ℒₒᵣ} {χ : ArithmeticProposition}

/-- Forcing over the `D`-anchored derivations of `LKI[C]`: a condition is a sequent `p`, and the
proofs of `⊥` over it are the anchored derivations of `∼p`.

- [Avi01, Section 3] -/
def Forces (C : ArithmeticSemiformula ℕ 1 → Prop) (D : ArithmeticProposition → Prop)
    (p : LK.Sequent ℒₒᵣ) : Propositionᵢ ℒₒᵣ → Type
  |        ⊥ => ⊢ᴸᴷᴵ[C, D]! ∼p
  | .rel R v => ⊢ᴸᴷᴵ[C, D]! ∼p + ⦃Semiformula.rel R v⦄
  |    φ ⋏ ψ => Forces C D p φ × Forces C D p ψ
  |    φ ⋎ ψ => Forces C D p φ ⊕ Forces C D p ψ
  |    φ 🡒 ψ => (q : LK.Sequent ℒₒᵣ) → q ≼ p → Forces C D q φ → Forces C D q ψ
  |     ∀¹ φ => (t : ArithmeticTerm ℕ) → Forces C D p (φ/[t])
  |     ∃¹ φ => (t : ArithmeticTerm ℕ) × Forces C D p (φ/[t])
  termination_by φ => φ.complexity

@[inherit_doc] notation:45 p:45 " ⊩[" C ", " D "] " φ:45 => Forces C D p φ

namespace Forces

def falsumEquiv : (p ⊩[C, D] ⊥) ≃ ⊢ᴸᴷᴵ[C, D]! ∼p := by
  unfold Forces; exact .refl _

def relEquiv {k} {R : (ℒₒᵣ).Rel k} {v} :
    (p ⊩[C, D] .rel R v) ≃ ⊢ᴸᴷᴵ[C, D]! ∼p + ⦃Semiformula.rel R v⦄ := by
  unfold Forces; exact .refl _

def andEquiv : (p ⊩[C, D] φ ⋏ ψ) ≃ (p ⊩[C, D] φ) × (p ⊩[C, D] ψ) := by
  conv => lhs; unfold Forces; exact .refl _

def orEquiv : (p ⊩[C, D] φ ⋎ ψ) ≃ ((p ⊩[C, D] φ) ⊕ (p ⊩[C, D] ψ)) := by
  conv => lhs; unfold Forces; exact .refl _

def implyEquiv :
    (p ⊩[C, D] φ 🡒 ψ) ≃ ((q : LK.Sequent ℒₒᵣ) → q ≼ p → (q ⊩[C, D] φ) → q ⊩[C, D] ψ) := by
  conv => lhs; unfold Forces; exact .refl _

def allEquiv {φ} : (p ⊩[C, D] ∀¹ φ) ≃ ((t : ArithmeticTerm ℕ) → Forces C D p (φ/[t])) := by
  conv => lhs; unfold Forces; exact .refl _

def exsEquiv {φ} : (p ⊩[C, D] ∃¹ φ) ≃ ((t : ArithmeticTerm ℕ) × Forces C D p (φ/[t])) := by
  conv => lhs; unfold Forces; exact .refl _

def cast (f : p ⊩[C, D] φ) (e : φ = ψ) : p ⊩[C, D] ψ := e ▸ f

def monotone (s : q ≼ p) : {φ : Propositionᵢ ℒₒᵣ} → (p ⊩[C, D] φ) → q ⊩[C, D] φ
  | ⊥, b =>
    let ⟨d, hd⟩ := b.falsumEquiv
    falsumEquiv.symm ⟨d.graft s.val, by simpa using hd⟩
  | .rel R v, b =>
    let ⟨d, hd⟩ := b.relEquiv
    relEquiv.symm ⟨d.graft (s.val.cons (Semiformula.rel R v)), by simpa using hd⟩
  | _ ⋏ _, b => andEquiv.symm ⟨monotone s b.andEquiv.1, monotone s b.andEquiv.2⟩
  | _ ⋎ _, b =>
    orEquiv.symm <| b.orEquiv.rec (fun b ↦ .inl <| b.monotone s) (fun b ↦ .inr <| b.monotone s)
  | _ 🡒 _, b => implyEquiv.symm fun r s' bφ ↦ b.implyEquiv r (s'.trans s) bφ
  | ∀¹ _, b => allEquiv.symm fun t ↦ (b.allEquiv t).monotone s
  | ∃¹ φ, b =>
    let ⟨t, d⟩ : (t : ArithmeticTerm ℕ) × (p ⊩[C, D] φ/[t]) := b.exsEquiv
    exsEquiv.symm ⟨t, d.monotone s⟩
  termination_by φ => φ.complexity

def explosion {p} (b : p ⊩[C, D] ⊥) : (φ : Propositionᵢ ℒₒᵣ) → p ⊩[C, D] φ
  | ⊥ => b
  | .rel R v =>
    let ⟨d, hd⟩ := b.falsumEquiv
    relEquiv.symm ⟨d.weakening, hd⟩
  | φ ⋏ ψ => andEquiv.symm ⟨b.explosion φ, b.explosion ψ⟩
  | φ ⋎ _ => orEquiv.symm <| .inl <| b.explosion φ
  | _ 🡒 ψ => implyEquiv.symm fun q s _ ↦ (b.monotone s).explosion ψ
  | ∀¹ φ => allEquiv.symm fun t ↦ b.explosion (φ/[t])
  | ∃¹ φ => exsEquiv.symm ⟨default, b.explosion (φ/[default])⟩
  termination_by φ => φ.complexity

def implyOf (tp : (∼p).Traversal)
    (b : (q : LK.Sequent ℒₒᵣ) → (∼q).Traversal → (q ⊩[C, D] φ) → p ⊓ q ⊩[C, D] ψ) :
    p ⊩[C, D] φ 🡒 ψ := implyEquiv.symm fun q s fφ ↦
  let tq := s.val.traversal tp
  (b q tq fφ).monotone (StrongerThan.leMinRightOfLe s tq)

def modusPonens (f : p ⊩[C, D] φ 🡒 ψ) (g : p ⊩[C, D] φ) : p ⊩[C, D] ψ :=
  f.implyEquiv p (StrongerThan.refl p) g

end Forces

/-- A condition forcing every formula of an `LJ` context. -/
abbrev ContextForces (C : ArithmeticSemiformula ℕ 1 → Prop) (D : ArithmeticProposition → Prop)
    (p : LK.Sequent ℒₒᵣ) (Γ : LJ.Sequent ℒₒᵣ) := (φ : Propositionᵢ ℒₒᵣ) → φ ∈ Γ → p ⊩[C, D] φ

namespace ContextForces

variable {Γ Δ : LJ.Sequent ℒₒᵣ}

def ofSubset (b : ContextForces C D p Δ) (h : Γ ⊆ Δ) : ContextForces C D p Γ :=
  fun φ hφ ↦ b φ (h hφ)

def monotone (b : ContextForces C D p Γ) (s : q ≼ p) : ContextForces C D q Γ :=
  fun φ hφ ↦ (b φ hφ).monotone s

def atom (b : p ⊩[C, D] φ) : ContextForces C D p ⦃φ⦄ :=
  fun _ hψ ↦ b.cast (Multiset.mem_singleton.mp hψ).symm

def cons (b : ContextForces C D p Γ) (hφ : p ⊩[C, D] φ) : ContextForces C D p (Γ + ⦃φ⦄) :=
  fun ψ hψ ↦ if h : φ = ψ then hφ.cast h else b ψ (by simp_all [eq_comm])

end ContextForces

/-- A condition forcing the succedent of an `LJ` sequent. -/
def HeadForces (C : ArithmeticSemiformula ℕ 1 → Prop) (D : ArithmeticProposition → Prop)
    (p : LK.Sequent ℒₒᵣ) : LJ.Head ℒₒᵣ → Type
  | none => p ⊩[C, D] ⊥
  | some φ => p ⊩[C, D] φ

namespace Forces

private lemma rewrite_shift_eq (t : ArithmeticTerm ℕ) (φ : Propositionᵢ ℒₒᵣ) :
    Rew.rewrite (t :>ₙ fun x ↦ &x) ▹ Rewriting.shift φ = φ := by
  rw [← TransitiveRewriting.comp_app, Rew.rewrite_comp_shift_eq_id, ReflectiveRewriting.id_app]

/-- Soundness of `LJ` for forcing over anchored derivations.

- [Avi01, Section 3] -/
def sound {Γ : LJ.Sequent ℒₒᵣ} {Ξ : LJ.Head ℒₒᵣ}
    (d : Γ ⊢ᴸᴶ¹ Ξ) (p : LK.Sequent ℒₒᵣ) (tp : (∼p).Traversal)
    (b : ContextForces C D p Γ) : HeadForces C D p Ξ :=
  match d with
  | .identity R v => b (.rel R v) (by simp)
  | .cut dφ d =>
      let bΓ := b.ofSubset (by intro ψ hψ; simp_all)
      let bΔ := b.ofSubset (by intro ψ hψ; simp_all)
      sound d p tp <| bΔ.cons (sound dφ p tp bΓ)
  | .contraction d => sound d p tp fun ψ hψ ↦ b ψ (by simp_all)
  | .weakening d => sound d p tp (b.ofSubset Multiset.subset_add_left)
  | .weakeningRight d => (sound d p tp b).explosion _
  | .verum => implyEquiv.symm fun _ _ h ↦ h
  | .falsum => b ⊥ (by simp)
  | .positiveImply d => implyEquiv.symm fun q s bφ ↦
      sound d q (s.val.traversal tp) <| (b.monotone s).cons bφ
  | .negativeImply (φ := φ) (ψ := ψ) dφ d =>
      let bΓ := b.ofSubset (by intro θ hθ; simp_all)
      let bΔ := b.ofSubset (by intro θ hθ; simp_all)
      let bi : p ⊩[C, D] φ 🡒 ψ := b _ (by simp)
      sound d p tp <| bΔ.cons (bi.modusPonens <| sound dφ p tp bΓ)
  | .positiveAnd dφ dψ => andEquiv.symm ⟨sound dφ p tp b, sound dψ p tp b⟩
  | .negativeAnd (φ := φ) (ψ := ψ) (Γ := Γ) d =>
      let bΓ : ContextForces C D p Γ := b.ofSubset Multiset.subset_add_left
      let ⟨bφ, bψ⟩ := (b (φ ⋏ ψ) (by simp)).andEquiv
      sound d p tp <| ((bΓ.cons bφ).cons bψ).ofSubset
        (by intro θ hθ; simpa [add_assoc] using hθ)
  | .positiveOrLeft d => orEquiv.symm <| .inl <| sound d p tp b
  | .positiveOrRight d => orEquiv.symm <| .inr <| sound d p tp b
  | .negativeOr (φ := φ) (ψ := ψ) dφ dψ =>
      let bΓ := b.ofSubset (by intro θ hθ; simp_all)
      (b (φ ⋎ ψ) (by simp)).orEquiv.rec
        (fun bφ ↦ sound dφ p tp <| bΓ.cons bφ)
        (fun bψ ↦ sound dψ p tp <| bΓ.cons bψ)
  | .positiveForall (Γ := Γ) (φ := φ) d => allEquiv.symm fun t ↦
      let f : ℕ → ArithmeticTerm ℕ := t :>ₙ fun x ↦ &x
      let dt : Γ ⊢ᴸᴶ¹ some (φ/[t]) := (d.rewrite f).cast
        (by simp [f, Rewriting.shifts, Multiset.map_map, rewrite_shift_eq])
        (by simp [f, LJ.Head.rewrite, rewrite_free_eq_subst])
      sound dt p tp b
  | .negativeForall (φ := φ) d =>
      let bΓ := b.ofSubset (by intro θ hθ; simp_all)
      let bAll := (b (∀¹ φ) (by simp)).allEquiv _
      sound d p tp <| bΓ.cons bAll
  | .positiveExists (t := t) d => exsEquiv.symm ⟨t, sound d p tp b⟩
  | .negativeExists (Γ := Γ) (Ξ := Ξ) (φ := φ) d =>
      let ⟨t, bt⟩ := (b (∃¹ φ) (by simp)).exsEquiv
      let f : ℕ → ArithmeticTerm ℕ := t :>ₙ fun x ↦ &x
      let dt : Γ + ⦃φ/[t]⦄ ⊢ᴸᴶ¹ Ξ := (d.rewrite f).cast
        (by simp [f, Rewriting.shifts, Multiset.map_map, rewrite_shift_eq, rewrite_free_eq_subst])
        (by cases Ξ <;> simp [f, LJ.Head.shift, LJ.Head.rewrite, rewrite_shift_eq])
      let bΓ := b.ofSubset (by intro θ hθ; simp_all)
      sound dt p tp <| bΓ.cons bt
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
  |  .rel R v => implyOf (.atom _) fun q tq dΔ ↦
    let tr : (∼(⦃Semiformula.rel R v⦄ : LK.Sequent ℒₒᵣ)).Traversal := .atom _
    let b : ⦃Semiformula.rel R v⦄ ⊓ q ⊩[C, D] .rel R v :=
      (relEquiv.symm ⟨Derivation.cast <| Derivation.identity R v, by simp⟩).monotone
        (StrongerThan.minLeLeft _ _ tq)
    dΔ.implyEquiv (⦃Semiformula.rel R v⦄ ⊓ q) (StrongerThan.minLeRight _ _ tr) b
  | .nrel R v => implyOf (.atom _) fun q _ dΔ ↦
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
    implyOf (.atom _) fun q tq dΔ ↦
      let ⟨dφ, dψ⟩ : (q ⊩[C, D] ∼φᴺ) × (q ⊩[C, D] ∼ψᴺ) := dΔ.andEquiv
      let tφ : (∼(⦃φ⦄ : LK.Sequent ℒₒᵣ)).Traversal := .atom _
      let tψ : (∼(⦃ψ⦄ : LK.Sequent ℒₒᵣ)).Traversal := .atom _
      let bφ : ⦃φ⦄ ⊓ q ⊩[C, D] ⊥ :=
        dφ.implyEquiv (⦃φ⦄ ⊓ q) (.minLeRight _ _ tφ) (ihφ.monotone (.minLeLeft _ _ tq))
      let bψ : ⦃ψ⦄ ⊓ q ⊩[C, D] ⊥ :=
        dψ.implyEquiv (⦃ψ⦄ ⊓ q) (.minLeRight _ _ tψ) (ihψ.monotone (.minLeLeft _ _ tq))
      let ⟨bbφ, hbbφ⟩ := bφ.falsumEquiv
      let ⟨bbψ, hbbψ⟩ := bψ.falsumEquiv
      let bbφ' : ⊢ᴸᴷᴵ[C]! ∼q + ⦃∼φ⦄ := Derivation.cast bbφ (by simp [inf_def]; abel)
      let bbψ' : ⊢ᴸᴷᴵ[C]! ∼q + ⦃∼ψ⦄ := Derivation.cast bbψ (by simp [inf_def]; abel)
      let band := Derivation.and bbφ' bbψ'
      falsumEquiv.symm ⟨Derivation.cast band (by simp [inf_def]; abel), by
        simpa [band, bbφ', bbψ'] using And.intro hbbφ hbbψ⟩
  |      ∀¹ φ => allEquiv.symm fun t ↦
    let b : ⦃φ/[t]⦄ ⊩[C, D] φᴺ/[t] := by
      simpa [Semiformula.rew_doubleNegation] using Forces.refl (φ/[t])
    by simpa using b.monotone (StrongerThan.all (p := 0) φ t)
  |      ∃¹ φ => implyOf (.atom _) fun q tq f ↦
    let x := LK.Sequent.newVar (∼q + ⦃∀¹ ∼φ⦄)
    let ih : ⦃φ/[&x]⦄ ⊩[C, D] φᴺ/[&x] :=
      cast (Forces.refl (φ/[&x])) (by simp [Semiformula.subst_doubleNegation])
    let b : ⦃φ/[&x]⦄ ⊓ q ⊩[C, D] ⊥ :=
      let tφ : (∼(⦃φ/[&x]⦄ : LK.Sequent ℒₒᵣ)).Traversal := .atom _
      (f.allEquiv &x).implyEquiv (⦃φ/[&x]⦄ ⊓ q)
        (StrongerThan.minLeRight _ _ tφ) (ih.monotone (StrongerThan.minLeLeft _ _ tq))
    let ⟨b, hb⟩ := b.falsumEquiv
    let hp : ¬(∼φ).FVar? x := by
      have : ¬(∀¹ ∼φ).FVar? x := LK.Sequent.not_fvar?_newVar (by simp)
      simpa using this
    let hq : ∀ ψ ∈ ∼q, ¬ψ.FVar? x := fun ψ hψ ↦ LK.Sequent.not_fvar?_newVar (by simp [hψ])
    let b' : ⊢ᴸᴷᴵ[C]! ∼q + ⦃(∼φ)/[&x]⦄ := Derivation.cast b (by simp [inf_def]; abel)
    let ba : ⊢ᴸᴷᴵ[C]! ∼q + ⦃∀¹ ∼φ⦄ := Derivation.generalizeByNewVar hp hq b'
    falsumEquiv.symm ⟨Derivation.cast ba (by simp [inf_def]; abel), by
      simpa [ba, b'] using Derivation.anchored_generalizeByNewVar (by simpa [b'] using hb)⟩
  termination_by φ => φ.complexity

/-! ## Forcing and anchored derivations -/

def castCondition {p q : LK.Sequent ℒₒᵣ} (f : p ⊩[C, D] φ) (e : p = q) : q ⊩[C, D] φ := e ▸ f

/-- The cut that `cutForces` performs: a cut against a formula of `D`, followed by the
contraction that merges the two copies of the condition. -/
def cutAnchored {p r : LK.Sequent ℒₒᵣ} (hχ : D χ)
    (tp : (∼p).Traversal) (d : ⊢ᴸᴷᴵ[C, D]! ∼p + ⦃χ⦄)
    (e : ⊢ᴸᴷᴵ[C, D]! ∼p + ⦃∼χ⦄ + r) : ⊢ᴸᴷᴵ[C, D]! ∼p + r :=
  let dc : ⊢ᴸᴷᴵ[C]! r + (∼p + ∼p) :=
    Derivation.cast (Derivation.cut (Γ := ∼p) (Δ := ∼p + r) (φ := χ) d.val (e.val.cast (by abel)))
  let s : (∼p + ∼p : LK.Sequent ℒₒᵣ) ⟶⁺ ∼p :=
    (StrongerThan.leMinRightOfLe (StrongerThan.refl p) tp).val.cast (by simp [inf_def]) rfl
  ⟨Derivation.cast (dc.graft (s.addLeft r)), by simp [dc, hχ, d.prop, e.prop]⟩

/-- A cut against a formula of `D` is absorbed into the forcing relation.

- [Bus98A, Section 1.4.2] -/
def cutForces (hχ : D χ) :
    {p : LK.Sequent ℒₒᵣ} → (∼p).Traversal → ⊢ᴸᴷᴵ[C, D]! ∼p + ⦃χ⦄ →
      {ψ : Propositionᵢ ℒₒᵣ} → (p + ⦃χ⦄ ⊩[C, D] ψ) → p ⊩[C, D] ψ
  | _, tp, d, ⊥, b =>
    falsumEquiv.symm <|
      cutAnchored (r := 0) hχ tp d (b.falsumEquiv.cast (by simp)) |>.cast (by simp)
  | _, tp, d, .rel R v, b =>
    relEquiv.symm <| cutAnchored (r := ⦃Semiformula.rel R v⦄) hχ tp d (b.relEquiv.cast (by simp))
  | _, tp, d, _ ⋏ _, b =>
    andEquiv.symm ⟨cutForces hχ tp d b.andEquiv.1, cutForces hχ tp d b.andEquiv.2⟩
  | _, tp, d, _ ⋎ _, b =>
    orEquiv.symm <| b.orEquiv.rec
      (fun b ↦ .inl <| cutForces hχ tp d b) (fun b ↦ .inr <| cutForces hχ tp d b)
  | p, tp, d, _ 🡒 _, b => implyEquiv.symm fun q sq bφ ↦
    let sχ : q + ⦃χ⦄ ≼ p + ⦃χ⦄ := ⟨(sq.val.cons (∼χ)).cast (by simp) (by simp)⟩
    let s₀ : q + ⦃χ⦄ ≼ q := ⟨(LK.Derivation.Positive.weakening (φ := ∼χ) .refl).cast rfl (by simp)⟩
    cutForces hχ (sq.val.traversal tp) ⟨d.val.graft (sq.val.cons χ), by simp [d.prop]⟩
      (b.implyEquiv (q + ⦃χ⦄) sχ (bφ.monotone s₀))
  | _, tp, d, ∀¹ _, b => allEquiv.symm fun t ↦ cutForces hχ tp d (b.allEquiv t)
  | _, tp, d, ∃¹ _, b =>
    let ⟨t, f⟩ := b.exsEquiv
    exsEquiv.symm ⟨t, cutForces hχ tp d f⟩
  termination_by _ _ _ ψ _ => ψ.complexity

/-- A formula of `D` with an anchored derivation of it over `∼p` is forced by `p`: the converse
of `derivableOfForced`.

- [Bus98A, Section 1.4.2] -/
def forcesOfAnchored (hχ : D χ) (tp : (∼p).Traversal) (d : ⊢ᴸᴷᴵ[C, D]! ∼p + ⦃χ⦄) :
    p ⊩[C, D] χᴺ :=
  cutForces hχ tp d <|
    ((Forces.refl χ).monotone (StrongerThan.minLeRight p ⦃χ⦄ tp)).castCondition (inf_def p ⦃χ⦄)

/-- A condition forcing the translation of `χ` yields an anchored derivation of `χ` over the
negated condition.

- [Bus98A, Section 1.4.2] -/
def derivableOfForced (tp : (∼p).Traversal) (f : p ⊩[C, D] χᴺ) : ⊢ᴸᴷᴵ[C, D]! ∼p + ⦃χ⦄ :=
  let tχ : (∼(⦃∼χ⦄ : LK.Sequent ℒₒᵣ)).Traversal := .atom _
  let b : p ⊓ ⦃∼χ⦄ ⊩[C, D] ∼χᴺ :=
    sound (LJ.Derivation.negDoubleNegation χ).2 (p ⊓ ⦃∼χ⦄) ((tp.add tχ).cast (by simp [inf_def]))
      fun ψ hψ ↦ ((Forces.refl (∼χ)).monotone (StrongerThan.minLeRight p ⦃∼χ⦄ tp)).cast
        (Multiset.mem_singleton.mp hψ).symm
  (b.modusPonens (f.monotone (StrongerThan.minLeLeft p ⦃∼χ⦄ tχ))).falsumEquiv.cast
    (by simp [inf_def])

/-! ## The translated connectives -/

/-- Transporting a forced formula along an `LJ` derivation from it. -/
def ofLJ (tp : (∼p).Traversal) (d : ⦃φ⦄ ⊢ᴸᴶ¹ ψ) (b : p ⊩[C, D] φ) : p ⊩[C, D] ψ :=
  sound d p tp (.atom b)

variable {χ' : ArithmeticProposition}

/-- Forcing the translation of an implication: it is enough to turn a forced antecedent into a
forced consequent at every stronger condition. -/
def forcesImply (tp : (∼p).Traversal)
    (b : (q : LK.Sequent ℒₒᵣ) → (s : q ≼ p) → (q ⊩[C, D] χᴺ) → q ⊩[C, D] χ'ᴺ) :
    p ⊩[C, D] (χ 🡒 χ')ᴺ :=
  Forces.cast (implyEquiv.symm fun q s c ↦
    let tq := s.val.traversal tp
    let ⟨c₁, c₂⟩ := c.andEquiv
    c₂.modusPonens <| b q s <| ofLJ tq (LJ.Derivation.negDoubleNegation' χ).1 c₁)
    (Semiformula.doubleNegation_imply χ χ').symm

/-- Using the translation of an implication. -/
def modusPonensImply (tp : (∼p).Traversal) (f : p ⊩[C, D] (χ 🡒 χ')ᴺ) (b : p ⊩[C, D] χᴺ) :
    p ⊩[C, D] χ'ᴺ :=
  let f : p ⊩[C, D] ∼(∼(∼χ)ᴺ ⋏ ∼χ'ᴺ) := f.cast (Semiformula.doubleNegation_imply χ χ')
  let g : p ⊩[C, D] ∼(∼χ'ᴺ) := implyEquiv.symm fun q s c ↦
    (f.monotone s).modusPonens <| andEquiv.symm
      ⟨ofLJ (s.val.traversal tp) (LJ.Derivation.negDoubleNegation' χ).2 (b.monotone s), c⟩
  ofLJ tp (LJ.Derivation.dneOfNegative (by simp)) g

/-! ## Universal closure -/

/-- A condition forcing every substitution instance of `ψ` forces its universal closure. -/
def forcesAllClosure : {n : ℕ} → (ψ : ArithmeticSemiformula ℕ n) →
    ((v : Fin n → ArithmeticTerm ℕ) → p ⊩[C, D] (ψ⇜v)ᴺ) → p ⊩[C, D] (∀¹* ψ)ᴺ
  | 0, ψ, h => (h ![]).cast (by simp)
  | _ + 1, ψ, h => by
    refine forcesAllClosure (∀¹ ψ) fun v ↦ ?_
    rw [show ((∀¹ ψ)⇜v : ArithmeticProposition) = ∀¹ ((Rew.subst v).q ▹ ψ) from rfl]
    exact allEquiv.symm fun t ↦ (h (t :> v)).cast (by
      rw [Semiformula.subst_doubleNegation, Rew.subst_q_app])

/-- A condition forcing every rewriting of `χ` forces its universal closure. -/
def forcesUnivCl (h : (f : ℕ → ArithmeticTerm ℕ) → p ⊩[C, D] (Rew.rewrite f ▹ χ)ᴺ) :
    p ⊩[C, D] (χ.univCl')ᴺ :=
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
    (tp : (∼p).Traversal) : p ⊩[C, D] (succInd ξ)ᴺ := by
  rw [show (succInd ξ : ArithmeticProposition)
      = (ξ/[‘0’]) 🡒 ((∀¹ (ξ 🡒 ξ/[‘(#0 + 1)’])) 🡒 ∀¹ ξ) from by simp [succInd]]
  refine forcesImply tp fun q s g₀ ↦ forcesImply (s.val.traversal tp) fun r s' gstep ↦ ?_
  let tr := s'.val.traversal (s.val.traversal tp)
  refine allEquiv.symm fun t ↦ ?_
  rw [Semiformula.subst_doubleNegation]
  -- `r ⊩ (ξ/[t])ᴺ`, by the induction rule at a variable fresh for `r` and `ξ`
  refine forcesOfAnchored (hD t) tr ?_
  let m := LK.Sequent.newVar (∼r + ⦃∀¹ ξ⦄)
  have hξm : ¬ξ.FVar? m := by
    have : ¬(∀¹ ξ).FVar? m := LK.Sequent.not_fvar?_newVar (by simp)
    simpa using this
  have hr : ∀ ψ ∈ ∼r, ¬ψ.FVar? m := fun ψ hψ ↦ LK.Sequent.not_fvar?_newVar (by simp [hψ])
  -- the base case
  let d₀ := derivableOfForced tr (g₀.monotone s')
  -- the step case, at the condition `r` extended by the induction hypothesis
  let tr' : (∼(r + ⦃ξ/[&m]⦄)).Traversal := (tr.add (.atom (∼(ξ/[&m])))).cast (by simp)
  let sr' : r + ⦃ξ/[&m]⦄ ≼ r :=
    ⟨(LK.Derivation.Positive.weakening (φ := ∼(ξ/[&m])) .refl).cast rfl (by simp)⟩
  let gxy : r ⊩[C, D] (ξ/[&m] 🡒 ξ/[‘&m + 1’])ᴺ := (gstep.allEquiv &m).cast (by
    simp [Semiformula.subst_doubleNegation, Rew.subst_subst_eq])
  let gY :=
    modusPonensImply tr' (gxy.monotone sr')
      ((Forces.refl (ξ/[&m])).monotone (StrongerThan.ofSubset (.atom _) tr' (by simp)))
  let dstep : ⊢ᴸᴷᴵ[C, D]! ∼r + ⦃∼(ξ/[&m]), ξ/[‘&m + 1’]⦄ :=
    (derivableOfForced tr' gY).cast (by simp; abel)
  -- the rule leaves the base case as a side formula; cut it off against `d₀`
  refine cutAnchored (r := ⦃ξ/[t]⦄) (hD ‘0’) tr d₀ ⟨?_, ?_⟩
  · exact (Derivation.indByNewVar hξ t hξm hr dstep.val).cast (by abel)
  · simpa using Derivation.anchored_indByNewVar dstep.prop

/-- Every axiom of `𝗣𝗔⁻` is forced: it is a leaf of the calculus, so it has an anchored
derivation.

- [Bus98A, Section 1.4.2] -/
def forcesPeanoMinus {σ : ArithmeticSentence} (hD : D (Rewriting.emb σ)) (h : σ ∈ 𝗣𝗔⁻)
    (tp : (∼p).Traversal) : p ⊩[C, D] (Rewriting.emb σ : ArithmeticProposition)ᴺ :=
  forcesOfAnchored hD tp ⟨(Derivation.weakeningMany tp (.axm h)).cast (by abel), by simp⟩

/-- Every axiom of the `C`-induction scheme is forced.

- [Bus98A, Section 1.4.2] -/
def forcesInd {ξ : ArithmeticSemiformula ℕ 1}
    (hCD : ∀ η, C η → ∀ t, D (η/[t])) (hξ : C ξ)
    (tp : (∼p).Traversal) : p ⊩[C, D] ((succInd ξ).univCl')ᴺ :=
  forcesUnivCl fun f ↦
    let hq : C ((Rew.rewrite f).q ▹ ξ) := by
      simpa [Rew.q_rewrite] using RewriteClosed.rewrite (C := C) (Rew.bShift ∘ f) hξ
    (forcesSuccInd hq (hCD _ hq) tp).cast (by rw [rew_succInd])

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

/-! ## Anchored derivations from proofs -/

open Forces in
/-- Free-cut elimination for `𝗣𝗔⁻` with `C`-induction: an `LK` derivation of `Γ` from finitely
many axioms becomes a `D`-anchored `LKI[C]` derivation of `Γ`, provided `D` holds of the axioms
of `𝗣𝗔⁻` and of the instances of the `C`-formulas.

- [Bus98A, Section 1.4.2] -/
theorem nonempty_anchored_of_derivation [RewriteClosed C] [RewriteClosed D]
    (hCD : ∀ η, C η → ∀ t, D (η/[t]))
    (hPA : ∀ τ ∈ 𝗣𝗔⁻, D (Rewriting.emb τ))
    {Γ : LK.Sequent ℒₒᵣ} {Δ : Multiset ArithmeticSentence}
    (hΔ : ∀ τ ∈ Δ, τ ∈ 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ C)
    (d : ⊢ᴸᴷ¹ Γ + ∼LK.Sequent.embed Δ) : ⊢ᴸᴷᴵ[C, D] Γ := by
  have key : ∀ φ ∈ LK.Sequent.embed Δ, Nonempty ((0 : LK.Sequent ℒₒᵣ) ⊩[C, D] φᴺ) := by
    intro φ hφ
    obtain ⟨τ, hτ, rfl⟩ := Multiset.mem_map.mp hφ
    rcases hΔ τ hτ with hτ' | hτ'
    · exact ⟨forcesPeanoMinus (hPA τ hτ') hτ' (Multiset.Traversal.zero.cast (by simp))⟩
    · obtain ⟨ξ, hξ, rfl⟩ := by simpa [InductionScheme] using hτ'
      exact ⟨(forcesInd hCD hξ (Multiset.Traversal.zero.cast (by simp))).cast (by simp)⟩
  exact ⟨hauptsatz default default (fun φ hφ ↦ Classical.choice (key φ hφ)) d⟩

/-- A proof from `𝗣𝗔⁻` with `C`-induction becomes a `D`-anchored derivation.

- [Bus98A, Section 1.4.2] -/
theorem nonempty_anchored_of_provable [RewriteClosed C] [RewriteClosed D]
    (hCD : ∀ η, C η → ∀ t, D (η/[t]))
    (hPA : ∀ τ ∈ 𝗣𝗔⁻, D (Rewriting.emb τ)) {σ : ArithmeticSentence}
    (h : 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ C ⊢ σ) :
    ⊢ᴸᴷᴵ[C, D] ⦃σ⦄ := by
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := Theory.Proof.provable_iff.mp h
  exact nonempty_anchored_of_derivation hCD hPA hΔ d

/-- A proof in `𝗜 𝚺 1` becomes a derivation anchored in the strict $\Sigma_1$ and the strict
$\Pi_1$ propositions: the free cuts are eliminated.

- [Bus98A, Section 1.4.2] -/
theorem nonempty_anchored_of_provable_inductionOnStrictHierarchy {σ : ArithmeticSentence}
    (h : 𝗜 𝚺 1 ⊢ σ) :
    ⊢ᴸᴷᴵ[StrictHierarchy 𝚺 1, fun φ ↦ StrictHierarchy 𝚺 1 φ ∨ StrictHierarchy 𝚷 1 φ]
      ⦃σ⦄ :=
  nonempty_anchored_of_provable (fun _ hη _ ↦ .inl (StrictHierarchy.rew _ hη))
    (fun τ hτ ↦ .inr (StrictHierarchy.rew _ (PeanoMinus.strictHierarchy τ hτ))) h

end Canonical

end FFL.FirstOrder.Arithmetic.LKI

end
