module

public import Foundation.FirstOrder.Syntax.Classical.BinderNotation
public import Foundation.FirstOrder.Syntax.Classical.Rew
public import Foundation.FirstOrder.Tarski.Basic

/-!
# Semiformulas and their rewritings

Companion of Foundation's `Semiformula` and `Rew` (`Syntax/Classical/Rew.lean`): commutation and
congruence lemmas for substitutions and rewritings, quantifier-rank invariance, distinctness lemmas
and constructor equations for `Semiformula`, formulas with `ℕ`-indexed free variables read as
semisentences, and `t ^' n` in the term notation of `“…”`, the power of `t` by the numeral `n` for
a natural number `n` given by an identifier.
-/

@[expose] public section

namespace FFL.FirstOrder.Rew

variable {L : Language} {ξ : Type*} {n : ℕ}

lemma qpow_map {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) (k : ℕ) :
    (Rew.map (L := L) b e).qpow k = Rew.map (fun x : Fin (n₁ + k) ↦
      if h : (x : ℕ) < k then (⟨x, by omega⟩ : Fin (n₂ + k)) else
        (b ⟨x - k, by omega⟩).addNat k) e := by
  induction k with
  | zero => congr 1
  | succ k ih =>
    rw [Rew.qpow_succ, ih, Rew.q_map]
    congr 1; funext x
    cases x using Fin.cases with
    | zero => simp
    | succ x =>
      ext
      by_cases h : (x : ℕ) < k <;> simp [h]
      omega

@[simp] lemma emb_subst_app {m : ℕ} (w : Fin n → Semiterm L Empty m) (φ : Semiformula L Empty n) :
    Rewriting.emb (Rew.subst w ▹ φ : Semiformula L Empty m) =
      Rew.subst (fun i ↦ Rew.emb (w i)) ▹ (Rewriting.emb φ : Semiformula L ℕ n) := by
  unfold Rewriting.emb
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app]
  apply Rewriting.smul_ext'
  ext x
  · simp [Rew.comp_app]
  · exact x.elim

lemma app_substs (ω : Rew L ξ 0 ξ 0) (φ : Semiformula L ξ 1) (t : Semiterm L ξ 0) :
    ω ▹ (φ/[t]) = (ω.q ▹ φ)/[ω t] := by
  change ω ▹ (Rew.subst ![t] ▹ φ) = Rew.subst ![ω t] ▹ (ω.q ▹ φ)
  have h : ω.comp (Rew.subst ![t]) = (Rew.subst ![ω t]).comp ω.q := by
    ext x
    · cases x using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ i => exact i.elim0
    · simp [Rew.comp_app]
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, h]

lemma subst_comp_subst_q (w : Fin n → Semiterm L ξ 0) (s : Semiterm L ξ 0) :
    (Rew.subst ![s]).comp (Rew.subst w).q = Rew.subst (s :> w) := by
  ext x
  · cases x using Fin.cases with
    | zero => simp [Rew.comp_app]
    | succ i => simp [Rew.comp_app]
  · simp [Rew.comp_app]

lemma subst_q_app (w : Fin n → Semiterm L ξ 0) (s : Semiterm L ξ 0)
    (φ : Semiformula L ξ (n + 1)) : ((Rew.subst w).q ▹ φ)/[s] = Rew.subst (s :> w) ▹ φ := by
  change Rew.subst ![s] ▹ ((Rew.subst w).q ▹ φ) = Rew.subst (s :> w) ▹ φ
  rw [← TransitiveRewriting.comp_app, subst_comp_subst_q]

lemma val_subst_congr {M : Type*} [Tarski.Structure L M] {ε : ξ → M} {w w' : Fin n → Semiterm L ξ 0}
    (h : ∀ i, Semiterm.val ![] ε (w i) = Semiterm.val ![] ε (w' i)) (t : Semiterm L ξ n) :
    Semiterm.val ![] ε (Rew.subst w t) = Semiterm.val ![] ε (Rew.subst w' t) := by
  simp only [Semiterm.val_substs]
  exact congrArg (Semiterm.val · ε t) (funext h)

lemma rewrite_subst_shift_eq (f : ℕ → SyntacticTerm L) (t : SyntacticTerm L)
    (φ : Semiformula L ℕ 1) :
    Rew.rewrite (&0 :>ₙ fun x ↦ Rew.shift (f x)) ▹ ((Rewriting.shift φ)/[t]) =
      (Rewriting.shift (Rew.rewrite (Rew.bShift ∘ f) ▹ φ))/[
        Rew.rewrite (&0 :>ₙ fun x ↦ Rew.shift (f x)) t] := by
  simpa [← TransitiveRewriting.comp_app] using Rewriting.smul_ext' <| by
    ext x
    · simp [Rew.comp_app]
    · have e : (Rew.shift : SyntacticRew L 1 1) (Rew.bShift (f x)) =
          Rew.bShift (Rew.shift (f x)) := by
        simpa using Rew.q_comp_bShift_app (ω := (Rew.shift : SyntacticRew L 0 0)) (f x)
      simp [Rew.comp_app, e]

lemma subst_subst_eq {m : ℕ} (v : Fin n → Semiterm L ξ m) (φ : Semiformula L ξ 1)
    (t : Semiterm L ξ n) : Rew.subst v ▹ (φ/[t]) = φ/[Rew.subst v t] := by
  simpa [← TransitiveRewriting.comp_app] using Rewriting.smul_ext' <| by
    ext x
    · cases x using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ i => exact i.elim0
    · simp [Rew.comp_app]

@[simp] lemma subst_bShift_eq (v : Fin 1 → Semiterm L ξ 1) (t : Semiterm L ξ 0) :
    Rew.subst v (Rew.bShift t) = Rew.bShift t := by
  have e : (Rew.subst v).comp (Rew.bShift : Rew L ξ 0 ξ 1) = Rew.bShift := by
    ext x
    · exact x.elim0
    · simp [Rew.comp_app]
  simpa [Rew.comp_app] using Rew.ext' e t

lemma shift_subst_eq (φ : Semiformula L ℕ 1) (t : SyntacticSemiterm L n) :
    Rew.shift ▹ (φ/[t]) = (Rew.shift ▹ φ)/[Rew.shift t] := by
  simpa [← TransitiveRewriting.comp_app] using Rewriting.smul_ext' <| by
    ext x
    · cases x using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ i => exact i.elim0
    · simp [Rew.comp_app]

lemma bShift_eq_subst : (Rew.bShift : Rew L ξ n ξ (n + 1)) = Rew.subst fun i ↦ #i.succ := by
  ext x <;> rfl

end FFL.FirstOrder.Rew

namespace FFL.FirstOrder.Semiformula

variable {L : Language} {ξ : Type*} {n : ℕ}

section
variable {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ}

@[simp] lemma qr_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) : (ω ▹ φ).qr = φ.qr := by
  induction φ using Semiformula.rec' generalizing n₂ <;> simp [*]

end

@[simp] lemma qr_substs (φ : Semiformula L ξ 1) (t : Semiterm L ξ 0) : (φ/[t]).qr = φ.qr :=
  qr_rew _ φ

@[simp, grind .] lemma ne_and_left (φ ψ : Semiformula L ξ n) : φ ≠ φ ⋏ ψ :=
  ne_of_ne_complexity (by simp)

@[simp, grind .] lemma ne_and_right (φ ψ : Semiformula L ξ n) : ψ ≠ φ ⋏ ψ :=
  ne_of_ne_complexity (by simp)

@[simp, grind .] lemma all_ne_subst (φ : Semiformula L ξ 1) (t : Semiterm L ξ 0) : φ/[t] ≠ ∀¹ φ :=
  ne_of_ne_complexity (by simp)

attribute [grind .] ne_or_left ne_or_right ex_ne_subst

@[grind =] lemma verum_eq : (⊤ : Semiformula L ξ n) = Semiformula.verum := rfl

@[grind =] lemma falsum_eq : (⊥ : Semiformula L ξ n) = Semiformula.falsum := rfl

@[grind =] lemma and_eq (φ ψ : Semiformula L ξ n) : φ ⋏ ψ = Semiformula.and φ ψ := rfl

@[grind =] lemma or_eq (φ ψ : Semiformula L ξ n) : φ ⋎ ψ = Semiformula.or φ ψ := rfl

@[grind =] lemma all_eq (φ : Semiformula L ξ (n + 1)) : ∀¹ φ = Semiformula.all φ := rfl

@[grind =] lemma exs_eq (φ : Semiformula L ξ (n + 1)) : ∃¹ φ = Semiformula.exs φ := rfl

attribute [grind =] Multiset.mem_atom_iff

section

variable {m : ℕ}

/-- Substituting a variable that the formula avoids, and then renaming it to the new bound
variable, is `Rewriting.free`. -/
lemma rewriteMap_subst_eq_free (φ : Semiformula L ℕ 1) (h : ¬φ.FVar? m) :
    (@Rew.rewriteMap L ℕ ℕ 0 fun x ↦ if x = m then 0 else x + 1) ▹ (φ/[&m]) =
      Rewriting.free φ := by
  simp only [← TransitiveRewriting.comp_app]
  exact Semiformula.rew_eq_of_funEqOn (by simp [Rew.comp_app])
    fun x hx ↦ by simp [Rew.comp_app, ne_of_mem_of_not_mem hx h]

/-- Renaming a variable that the formula avoids to the new bound variable shifts the formula. -/
lemma rewriteMap_eq_shift {n} (φ : Semiformula L ℕ n) (h : ¬φ.FVar? m) :
    (@Rew.rewriteMap L ℕ ℕ n fun x ↦ if x = m then 0 else x + 1) ▹ φ = Rewriting.shift φ := by
  have e : (@Rew.rewriteMap L ℕ ℕ n fun x ↦ if x = m then 0 else x + 1) ▹ φ =
      (Rew.shift : SyntacticRew L n n) ▹ φ :=
    Semiformula.rew_eq_of_funEqOn (by simp) (by
      intro x hx
      simp [ne_of_mem_of_not_mem hx h])
  simpa [Rewriting.shift] using e

/-- Renaming a variable that none of the formulas mentions shifts the multiset. -/
lemma map_rewriteMap_eq_shifts (Γ : Multiset (Semiformula L ℕ 0))
    (h : ∀ φ ∈ Γ, ¬φ.FVar? m) :
    Γ.map (fun φ ↦ (@Rew.rewriteMap L ℕ ℕ 0 fun x ↦ if x = m then 0 else x + 1) ▹ φ) = Γ⁺ :=
  Multiset.map_congr rfl fun φ hφ ↦ rewriteMap_eq_shift φ (h φ hφ)

end

section Fvar

variable {k : ℕ}

/-- The substitution sending the bound variables of `φ` to `b` and the free variables below
`φ.fvSup` to the remaining bound variables. -/
noncomputable def paramSubst [NeZero k] (φ : Semiformula L ℕ k)
    (b : Fin k → Semiterm L Empty (φ.fvSup + k)) : Rew L ℕ k Empty (φ.fvSup + k) :=
  haveI : NeZero (φ.fvSup + k) := ⟨by have := Nat.pos_of_ne_zero (NeZero.ne k); omega⟩
  Rew.bind b fun x ↦ if h : x < φ.fvSup then #⟨x + k, by omega⟩ else #0

/-- `φ`, viewed as a semisentence whose extra bound variables are its free variables, with its
own bound variables placed by `b`. -/
noncomputable def toSemisentence [NeZero k] (φ : Semiformula L ℕ k)
    (b : Fin k → Semiterm L Empty (φ.fvSup + k)) : Semisentence L (φ.fvSup + k) :=
  paramSubst φ b ▹ φ

variable {M : Type*} [Tarski.Structure L M]

lemma eval_toSemisentence [NeZero k] {φ : Semiformula L ℕ k}
    (b : Fin k → Semiterm L Empty (φ.fvSup + k)) {v : Fin (φ.fvSup + k) → M} {w : Fin k → M}
    {f : ℕ → M} (hb : ∀ i, Semiterm.val v Empty.elim (b i) = w i)
    (hv : ∀ y : Fin φ.fvSup, v ⟨y + k, by omega⟩ = f y) :
    M ⊧/v (φ.toSemisentence b) ↔ φ.Eval w f := by
  rw [toSemisentence, Semiformula.eval_rew]
  have hbv : (Semiterm.val v Empty.elim ∘ φ.paramSubst b ∘ Semiterm.bvar) = w := funext hb
  rw [hbv]
  apply Semiformula.eval_iff_of_funEqOn φ
  intro y hy
  have hlt : y < φ.fvSup := Semiformula.lt_fvSup_of_fvar? hy
  simp [paramSubst, hlt, hv ⟨y, hlt⟩]

/-- `eval_toSemisentence` at `k = 1`, with `b` placing the bound variable at `#0`. -/
lemma eval_toSemisentence_one (φ : Semiformula L ℕ 1) (x : M)
    (f : ℕ → M) :
    M ⊧/(x :> fun i : Fin φ.fvSup ↦ f i) (φ.toSemisentence ![#0]) ↔ φ.Eval ![x] f :=
  eval_toSemisentence ![#0]
    (fun i ↦ by induction i using Fin.cases with | zero => simp | succ i => exact i.elim0)
    (fun _ ↦ by simp)

/-- `eval_toSemisentence` at `k = 2`, with `b` placing the two bound variables at `#1`, `#0` (the
witness-then-bound order). -/
lemma eval_toSemisentence_two (φ : Semiformula L ℕ 2) (x y : M)
    (f : ℕ → M) :
    M ⊧/(y :> x :> fun i : Fin φ.fvSup ↦ f i) (φ.toSemisentence ![#1, #0]) ↔ φ.Eval ![x, y] f :=
  eval_toSemisentence ![#1, #0]
    (fun i ↦ by
      induction i using Fin.cases with
      | zero => simp
      | succ i => induction i using Fin.cases with
        | zero => simp
        | succ i => exact i.elim0)
    (fun _ ↦ by simp)

end Fvar

end FFL.FirstOrder.Semiformula

namespace FFL.FirstOrder.BinderNotation

open Semiterm

syntax:70 first_order_term " ^' " ident : first_order_term

macro_rules
  | `(⤫term(lit)[ $binders* | $fbinders* | $e ^' $n:ident ]) =>
    `((Semiterm.Operator.npow _ $n).operator ![⤫term(lit)[ $binders* | $fbinders* | $e ]])

end FFL.FirstOrder.BinderNotation
