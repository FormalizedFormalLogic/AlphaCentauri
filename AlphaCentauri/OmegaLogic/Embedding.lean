module

public import AlphaCentauri.OmegaLogic.Elimination
public import AlphaCentauri.Vorspiel.Rew
public import Foundation.FirstOrder.Arithmetic.Schemata
public import Foundation.FirstOrder.Basic.Calculus2

/-!
# Embedding `𝗣𝗔` into `Z_∞`

Every Foundation `Derivation2` from `𝗣𝗔` becomes a `Z_∞` derivation, once its free variables are
closed by a numeral assignment `asg e`.

Three of the rules need something the finitary calculus does not have: a way to admit an axiom of
`𝗣𝗔` without it being an axiom of `Z_∞`, an ω-rule for the universal quantifier, and admission of
an existential witness that need not be a numeral.

Absorbing the axioms by their truth in `ℕ` is what makes the ordinal height existential here: the
result is `∃ α`, not a bound computed from the `𝗣𝗔` derivation. That is enough for soundness and
so for `AlphaCentauri/OmegaLogic/Consistency.lean`, and it is deliberately *not* the
ordinal-bounded embedding an ordinal analysis needs.

Neither [HP98] nor [Lin97] treats ω-logic; the presentation followed is [Tow20] and [Buc03].
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.OmegaLogic

variable {n : ℕ} {Γ : Sequent}

/-- **The closing assignment.** `asg e` sends the free variable `&x` to the numeral of `e x`, and
so sends every `ArithmeticFormula ℕ` to a formula without free variables — the form the leaves and
the ω-rule of `Z_∞` need.

- [Tow20, Section 16] -/
noncomputable def asg (e : ℕ → ℕ) : Rew ℒₒᵣ ℕ 0 ℕ 0 :=
  Rew.rewrite fun x => (↑(e x) : ArithmeticTerm ℕ)

@[simp] lemma asg_fvar (e : ℕ → ℕ) (x : ℕ) : asg e &x = (↑(e x) : ArithmeticTerm ℕ) := rfl

/-- Closing after a shift re-indexes the assignment.

- [Tow20, Section 16] -/
lemma asg_comp_shift (e : ℕ → ℕ) : (asg e).comp Rew.shift = asg (e ∘ Nat.succ) := by
  ext x
  · exact x.elim0
  · simp [asg, Rew.comp_app]

/-- The `Finset.image` form of `asg_comp_shift`, matching the sequent of `Derivation2.shift`. -/
lemma asg_image_shift (e : ℕ → ℕ) (Γ : Sequent) :
    (Γ.image Rewriting.shift).image (fun ψ => asg e ▹ ψ)
      = Γ.image (fun ψ => asg (e ∘ Nat.succ) ▹ ψ) := by
  rw [Finset.image_image]
  refine Finset.image_congr fun ψ _ => ?_
  show asg e ▹ (Rew.shift ▹ ψ) = asg (e ∘ Nat.succ) ▹ ψ
  rw [← TransitiveRewriting.comp_app, asg_comp_shift]

/-- Freeing the eigenvariable and closing it to the numeral `m` is the same as closing the rest and
substituting that numeral: the step that turns `Derivation2.all` into the ω-rule.

- [Tow20, Section 16] -/
lemma asg_cons_free (m : ℕ) (e : ℕ → ℕ) (φ : ArithmeticSemiformula ℕ 1) :
    asg (m :>ₙ e) ▹ (Rewriting.free φ) = ((asg e).q ▹ φ)/[(↑m : ArithmeticTerm ℕ)] := by
  have h : (asg (m :>ₙ e)).comp Rew.free
      = (Rew.subst ![(↑m : ArithmeticTerm ℕ)]).comp (asg e).q := by
    ext x
    · refine Fin.cases ?_ (fun i => i.elim0) x
      simp [asg, Rew.comp_app]
    · simp [asg, Rew.comp_app]
  show asg (m :>ₙ e) ▹ (Rew.free ▹ φ) = Rew.subst ![(↑m : ArithmeticTerm ℕ)] ▹ ((asg e).q ▹ φ)
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, h]

section ExcludedMiddle

/-! ### Value-congruent excluded middle

`Provable.lem` closes a sequent containing a formula and its negation. `em_cong` closes one
containing `ψ/[s]` and `∼(ψ/[s'])` for closed terms `s`, `s'` of the same standard value — the
form `exI_closed` needs, since `Derivation2.exs` may pick a witness term that is not a numeral. -/

variable {b : Bool} {k : ℕ} {w w' : Fin n → ArithmeticTerm ℕ}

/-- Truth of a literal depends on the substituted terms only through their values. -/
private lemma litTrue_subst_congr
    (h : ∀ i, Semiterm.val (M := ℕ) ![] id (w i) = Semiterm.val (M := ℕ) ![] id (w' i))
    (b : Bool) (r : (ℒₒᵣ).Rel k) (v : Fin k → Semiterm ℒₒᵣ ℕ n) :
    LitTrue (signedLit b r fun i => Rew.subst w (v i))
      ↔ LitTrue (signedLit b r fun i => Rew.subst w' (v i)) := by
  have hv : (fun i => Semiterm.val (M := ℕ) ![] id (Rew.subst w (v i)))
      = fun i => Semiterm.val (M := ℕ) ![] id (Rew.subst w' (v i)) :=
    funext fun i => Rew.val_subst_congr h (v i)
  cases b <;>
    simp only [signedLit, LitTrue, Semiformula.Evalf, Semiformula.eval_rel, Semiformula.eval_nrel,
      hv, Function.comp_def]

namespace Provable

/-- The `∧`/`∨` step of `em_congAux`: two premises for the conjuncts, over a sequent already
carrying both disjuncts, collapse in two rules. -/
private lemma em_binary {A B C D : ArithmeticFormula ℕ} (hab : A ⋏ B ∈ Γ) (hcd : C ⋎ D ∈ Γ)
    (h₁ : ∃ α, Z∞ ⊢[α, 0] insert A (insert C (insert D Γ)))
    (h₂ : ∃ α, Z∞ ⊢[α, 0] insert B (insert C (insert D Γ))) : ∃ α, Z∞ ⊢[α, 0] Γ := by
  obtain ⟨α₁, h₁⟩ := h₁
  obtain ⟨α₂, h₂⟩ := h₂
  have h := (andI h₁ h₂).insert_absorb
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hab))
  exact ⟨_, h.orI.insert_absorb hcd⟩

/-- The `∀`/`∃` step of `em_congAux`: an ω-family of premises, each carrying the matching
existential instance, collapses in two rules. -/
private lemma em_quant {φₓ ψₓ : ArithmeticSemiformula ℕ 1} (hall : (∀¹ φₓ) ∈ Γ)
    (hexs : (∃¹ ψₓ) ∈ Γ)
    (fam : ∀ m : ℕ, ∃ α, Z∞ ⊢[α, 0] insert (ψₓ/[(↑m : ArithmeticTerm ℕ)])
      (insert (φₓ/[(↑m : ArithmeticTerm ℕ)]) Γ)) : ∃ α, Z∞ ⊢[α, 0] Γ := by
  choose βₓ hβ using fam
  have h : ∀ m : ℕ, Z∞ ⊢[βₓ m + 1, 0] insert (φₓ/[(↑m : ArithmeticTerm ℕ)]) Γ := fun m =>
    (exI m (hβ m)).insert_absorb (Finset.mem_insert_of_mem hexs)
  exact ⟨_, (allω h).insert_absorb hall⟩

/-- The leaf of `em_congAux`: a literal and its opposite polarity, substituted by value-equal
vectors, are settled by whichever of the two is true in `ℕ`. -/
private lemma em_atomic
    (h : ∀ i, Semiterm.val (M := ℕ) ![] id (w i) = Semiterm.val (M := ℕ) ![] id (w' i))
    (b : Bool) (r : (ℒₒᵣ).Rel k) (v : Fin k → Semiterm ℒₒᵣ ℕ n)
    (hp : signedLit b r (fun i => Rew.subst w (v i)) ∈ Γ)
    (hn : signedLit (!b) r (fun i => Rew.subst w' (v i)) ∈ Γ) : ∃ α, Z∞ ⊢[α, 0] Γ := by
  rcases litTrue_or_neg (signedLit b r fun i => Rew.subst w (v i)) with ht | ht
  · exact ⟨0, axTrue b r _ ht hp⟩
  · rw [neg_signedLit] at ht
    exact ⟨0, axTrue (!b) r _ ((litTrue_subst_congr h (!b) r v).mp ht) hn⟩

/-- The induction underlying `em_cong`, on the complexity of the formula. -/
private lemma em_congAux : ∀ (k : ℕ) {n : ℕ} (w w' : Fin n → ArithmeticTerm ℕ)
    (ψ : ArithmeticSemiformula ℕ n), ψ.complexity ≤ k →
    (∀ i, Semiterm.val (M := ℕ) ![] id (w i) = Semiterm.val (M := ℕ) ![] id (w' i)) →
    ∀ {Γ : Sequent}, (Rew.subst w ▹ ψ) ∈ Γ → (∼(Rew.subst w' ▹ ψ)) ∈ Γ →
      ∃ α, Z∞ ⊢[α, 0] Γ := by
  intro k
  induction k with
  | zero =>
    intro n w w' ψ hk h Γ hp hn
    cases ψ using Semiformula.cases' with
    | hverum => exact ⟨0, verumR (by simpa using hp)⟩
    | hfalsum => exact ⟨0, verumR (by simpa using hn)⟩
    | hrel r v =>
      exact em_atomic h true r v (by simpa [signedLit, Function.comp_def] using hp)
        (by simpa [signedLit, Function.comp_def] using hn)
    | hnrel r v =>
      exact em_atomic h false r v (by simpa [signedLit, Function.comp_def] using hp)
        (by simpa [signedLit, Function.comp_def] using hn)
    | _ => simp at hk
  | succ k ih =>
    intro n w w' ψ hk h Γ hp hn
    cases ψ using Semiformula.cases' with
    | hverum => exact ⟨0, verumR (by simpa using hp)⟩
    | hfalsum => exact ⟨0, verumR (by simpa using hn)⟩
    | hrel r v =>
      exact em_atomic h true r v (by simpa [signedLit, Function.comp_def] using hp)
        (by simpa [signedLit, Function.comp_def] using hn)
    | hnrel r v =>
      exact em_atomic h false r v (by simpa [signedLit, Function.comp_def] using hp)
        (by simpa [signedLit, Function.comp_def] using hn)
    | hand a b =>
      simp only [Semiformula.complexity_and] at hk
      refine em_binary (show ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b)) ∈ Γ by simpa using hp)
        (show (∼(Rew.subst w' ▹ a) ⋎ ∼(Rew.subst w' ▹ b)) ∈ Γ by simpa using hn)
        (ih w w' a (by omega) h (by simp) (by simp))
        (ih w w' b (by omega) h (by simp) (by simp))
    | hor a b =>
      simp only [Semiformula.complexity_or] at hk
      refine em_binary (show (∼(Rew.subst w' ▹ a) ⋏ ∼(Rew.subst w' ▹ b)) ∈ Γ by simpa using hn)
        (show ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) ∈ Γ by simpa using hp)
        (ih w w' a (by omega) h (by simp) (by simp))
        (ih w w' b (by omega) h (by simp) (by simp))
    | hall a =>
      simp only [Semiformula.complexity_all] at hk
      refine em_quant (show (∀¹ ((Rew.subst w).q ▹ a)) ∈ Γ by simpa using hp)
        (show (∃¹ ((Rew.subst w').q ▹ ∼a)) ∈ Γ by simpa using hn) fun m => ?_
      have hx := ih ((↑m : ArithmeticTerm ℕ) :> w) ((↑m : ArithmeticTerm ℕ) :> w') a (by omega)
        (cons_val_congr h m)
        (Γ := insert (((Rew.subst w).q ▹ a)/[(↑m : ArithmeticTerm ℕ)])
          (insert (∼(((Rew.subst w').q ▹ a)/[(↑m : ArithmeticTerm ℕ)])) Γ))
        (by rw [← Rew.subst_q_app]; simp) (by rw [← Rew.subst_q_app]; simp)
      rw [show (((Rew.subst w').q ▹ ∼a)/[(↑m : ArithmeticTerm ℕ)])
        = ∼(((Rew.subst w').q ▹ a)/[(↑m : ArithmeticTerm ℕ)]) by simp, Finset.insert_comm]
      exact hx
    | hexs a =>
      simp only [Semiformula.complexity_exs] at hk
      refine em_quant (show (∀¹ ((Rew.subst w').q ▹ ∼a)) ∈ Γ by simpa using hn)
        (show (∃¹ ((Rew.subst w).q ▹ a)) ∈ Γ by simpa using hp) fun m => ?_
      have hx := ih ((↑m : ArithmeticTerm ℕ) :> w) ((↑m : ArithmeticTerm ℕ) :> w') a (by omega)
        (cons_val_congr h m)
        (Γ := insert (((Rew.subst w).q ▹ a)/[(↑m : ArithmeticTerm ℕ)])
          (insert (∼(((Rew.subst w').q ▹ a)/[(↑m : ArithmeticTerm ℕ)])) Γ))
        (by rw [← Rew.subst_q_app]; simp) (by rw [← Rew.subst_q_app]; simp)
      rwa [show (((Rew.subst w').q ▹ ∼a)/[(↑m : ArithmeticTerm ℕ)])
        = ∼(((Rew.subst w').q ▹ a)/[(↑m : ArithmeticTerm ℕ)]) by simp]
where
  cons_val_congr {n} {w w' : Fin n → ArithmeticTerm ℕ}
      (h : ∀ i, Semiterm.val (M := ℕ) ![] id (w i) = Semiterm.val (M := ℕ) ![] id (w' i))
      (m : ℕ) : ∀ i, Semiterm.val (M := ℕ) ![] id (((↑m : ArithmeticTerm ℕ) :> w) i)
        = Semiterm.val (M := ℕ) ![] id (((↑m : ArithmeticTerm ℕ) :> w') i) := by
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => simpa using h j

/-- **Value-congruent excluded middle.** For closed terms `s`, `s'` of the same standard value, a
sequent containing `ψ/[s]` and `∼(ψ/[s'])` is derivable cut-free.

- [Tow20, Section 16] -/
lemma em_cong (s s' : ArithmeticTerm ℕ)
    (h : Semiterm.val (M := ℕ) ![] id s = Semiterm.val (M := ℕ) ![] id s')
    (ψ : ArithmeticSemiformula ℕ 1) (hp : (ψ/[s]) ∈ Γ) (hn : (∼(ψ/[s'])) ∈ Γ) :
    ∃ α, Z∞ ⊢[α, 0] Γ := by
  refine em_congAux ψ.complexity ![s] ![s'] ψ le_rfl ?_ hp hn
  intro i
  cases i using Fin.cases with
  | zero => simpa using h
  | succ j => exact j.elim0

end Provable

end ExcludedMiddle

namespace Provable

section ClosedWitness

variable {α : Ordinal.{0}} {c : ℕ}

/-- **Existential introduction with an arbitrary closed witness.** `Z_∞`'s `exI` admits only
numerals, but a `Derivation2.exs` may have picked any term. Cutting the numeral of the term's
value against `em_cong` closes the gap, at the price of raising the cut rank to admit `ψ`.

- [Tow20, Section 16] -/
lemma exI_closed (ψ : ArithmeticSemiformula ℕ 1) (s : ArithmeticTerm ℕ)
    (h : Z∞ ⊢[α, c] insert (ψ/[s]) Γ) :
    ∃ β, Z∞ ⊢[β, max c (ψ.qr + 1)] insert (∃¹ ψ) Γ := by
  set m := Semiterm.val (M := ℕ) ![] id s with hm
  have h₁ : Z∞ ⊢[α, max c (ψ.qr + 1)]
      insert (ψ/[s]) (insert (ψ/[(↑m : ArithmeticTerm ℕ)]) Γ) :=
    (h.weakening (Finset.insert_subset_insert _ (Finset.subset_insert _ _))).mono_cutRank
      (le_max_left _ _)
  obtain ⟨β, h₂⟩ := em_cong (↑m) s (by simp [hm]) ψ
    (Γ := insert (∼(ψ/[s])) (insert (ψ/[(↑m : ArithmeticTerm ℕ)]) Γ)) (by simp) (by simp)
  have hcut : ((ψ/[s]) : ArithmeticFormula ℕ).qr < max c (ψ.qr + 1) := by
    simp only [Semiformula.qr_substs]
    omega
  exact ⟨_, exI m (cut _ hcut h₁ (h₂.mono_cutRank (Nat.zero_le _)))⟩

end ClosedWitness

section Embedding

/-- **The embedding.** Every `𝗣𝗔`-derivation embeds into `Z_∞`, at every numeral assignment of its
free variables, with a cut rank read off the derivation and an unbounded ordinal height.

The height cannot be bounded here, since it is read off axioms of `𝗣𝗔` known only to be true in
`ℕ`.

- [Tow20, Section 16]
- [Buc03, Section 5.5] -/
theorem of_derivation2 (d : 𝗣𝗔 ⟹₂ Γ) :
    ∃ c, ∀ e : ℕ → ℕ, ∃ α, Z∞ ⊢[α, c] (Γ.image fun φ => asg e ▹ φ) := by
  induction d with
  | closed Γ φ hp hn =>
    have h : ∀ e : ℕ → ℕ, ∼(asg e ▹ φ) ∈ Γ.image fun ψ => asg e ▹ ψ := fun e => by
      simpa using Finset.mem_image_of_mem (fun ψ => asg e ▹ ψ) hn
    exact ⟨0, fun e => ⟨_, lem (Finset.mem_image_of_mem _ hp) (h e)⟩⟩
  | axm φ hφ hΓ =>
    refine ⟨0, fun e => ⟨_, of_true ?_ (Finset.mem_image_of_mem _ hΓ)⟩⟩
    have hmod : (ℕ↓[ℒₒᵣ]) ⊧ φ := Semantics.modelsSet_iff.mp inferInstance hφ
    simp_all [LitTrue, asg, Semiformula.eval_emb, models_iff]
  | @verum Γ hΓ =>
    have h : ∀ e : ℕ → ℕ, (⊤ : ArithmeticFormula ℕ) ∈ Γ.image fun ψ => asg e ▹ ψ := fun e => by
      simpa using Finset.mem_image_of_mem (fun ψ => asg e ▹ ψ) hΓ
    exact ⟨0, fun e => ⟨0, verumR (h e)⟩⟩
  | @and Γ φ ψ hmem _ _ ih₁ ih₂ =>
    obtain ⟨c₁, ih₁⟩ := ih₁
    obtain ⟨c₂, ih₂⟩ := ih₂
    refine ⟨max c₁ c₂, fun e => ?_⟩
    obtain ⟨α₁, h₁⟩ := ih₁ e
    obtain ⟨α₂, h₂⟩ := ih₂ e
    rw [Finset.image_insert] at h₁ h₂
    exact ⟨_, (andI (h₁.mono_cutRank (le_max_left _ _))
      (h₂.mono_cutRank (le_max_right _ _))).insert_absorb
      (by simpa using Finset.mem_image_of_mem (fun φ => asg e ▹ φ) hmem)⟩
  | @or Γ φ ψ hmem _ ih =>
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, fun e => ?_⟩
    obtain ⟨α, h⟩ := ih e
    rw [Finset.image_insert, Finset.image_insert] at h
    exact ⟨_, h.orI.insert_absorb (by simpa using Finset.mem_image_of_mem (fun φ => asg e ▹ φ) hmem)⟩
  | @all Γ φ hmem _ ih =>
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, fun e => ?_⟩
    have hfam : ∀ n : ℕ, ∃ α, Z∞ ⊢[α, c]
        insert (((asg e).q ▹ φ)/[(↑n : ArithmeticTerm ℕ)]) (Γ.image fun ψ => asg e ▹ ψ) := by
      intro n
      obtain ⟨α, h⟩ := ih (n :>ₙ e)
      rw [Finset.image_insert, asg_cons_free n e φ,
        asg_image_shift, show (n :>ₙ e) ∘ Nat.succ = e from rfl] at h
      exact ⟨α, h⟩
    choose βₓ hβ using hfam
    exact ⟨_, (allω hβ).insert_absorb
      (by simpa using Finset.mem_image_of_mem (fun ψ => asg e ▹ ψ) hmem)⟩
  | @exs Γ φ hmem t _ ih =>
    obtain ⟨c, ih⟩ := ih
    refine ⟨max c (φ.qr + 1), fun e => ?_⟩
    obtain ⟨α, h⟩ := ih e
    rw [Finset.image_insert, Rew.app_substs (asg e) φ t] at h
    obtain ⟨β, hβ⟩ := exI_closed ((asg e).q ▹ φ) (asg e t) h
    rw [show (((asg e).q ▹ φ).qr + 1) = (φ.qr + 1) by simp] at hβ
    exact ⟨_, hβ.insert_absorb (by simpa using Finset.mem_image_of_mem (fun ψ => asg e ▹ ψ) hmem)⟩
  | wk _ hsub ih =>
    obtain ⟨c, ih⟩ := ih
    exact ⟨c, fun e => (ih e).imp fun _ h => h.weakening (Finset.image_subset_image hsub)⟩
  | @shift Γ _ ih =>
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, fun e => ?_⟩
    rw [asg_image_shift]
    exact ih (e ∘ Nat.succ)
  | @cut Γ φ _ _ ih₁ ih₂ =>
    obtain ⟨c₁, ih₁⟩ := ih₁
    obtain ⟨c₂, ih₂⟩ := ih₂
    refine ⟨max (φ.qr + 1) (max c₁ c₂), fun e => ?_⟩
    obtain ⟨α₁, h₁⟩ := ih₁ e
    obtain ⟨α₂, h₂⟩ := ih₂ e
    rw [Finset.image_insert] at h₁ h₂
    rw [show (asg e ▹ (∼φ)) = ∼(asg e ▹ φ) by simp] at h₂
    exact ⟨_, cut (asg e ▹ φ) (by simp only [Semiformula.qr_rew]; omega)
      (h₁.mono_cutRank (by omega)) (h₂.mono_cutRank (by omega))⟩

/-- **The cut-free embedding**: `of_derivation2` followed by `cut_elimination`.

- [Tow20, Section 16] -/
theorem of_derivation2_cutFree (d : 𝗣𝗔 ⟹₂ Γ) (e : ℕ → ℕ) :
    ∃ α, Z∞ ⊢[α, 0] (Γ.image fun φ => asg e ▹ φ) := by
  obtain ⟨c, h⟩ := of_derivation2 d
  obtain ⟨α, hα⟩ := h e
  exact ⟨_, cut_elimination hα⟩

end Embedding

end Provable

end LO.FirstOrder.Arithmetic.OmegaLogic
