module

public import AlphaCentauri.Schemata.BoundedInduction
public import AlphaCentauri.ToFoundation.BinderNotation
public import AlphaCentauri.ToMathlib.OpenPredicate
public import AlphaCentauri.ToMathlib.Algebra.Order.Ring.RingOfDifferences

/-!
# The least number principle in the ring of differences of a model of $\mathsf{I}\mathsf{E}_1$

Over a model $V$ of $\mathsf{I}\mathsf{E}_1$, the ring of differences of $V$ is discretely ordered
and satisfies `LeastNumberPrinciple` for bounded existential open predicates.

- [Wil85]
- [Smi93, Theorem 2.3]
-/

@[expose] public section

namespace RingOfDifferences

open OpenPredicate

variable {M : Type*} [CommSemiring M] [LinearOrder M] [IsStrictOrderedRing M]
  [CanonicallyOrderedAdd M]

private lemma leastNumberPrinciple_of_boundedExists_induction
    [DiscretelyOrdered (RingOfDifferences M)]
    (ind : ∀ {n : ℕ} {Φ : (Fin (n + 1) → RingOfDifferences M) → Prop}, IsOpen Φ →
      ∀ B : RingOfDifferences M, BoundedExists B Φ (of 0) →
        (∀ t : M, BoundedExists B Φ (of t) → BoundedExists B Φ (of (t + 1))) →
          ∀ t : M, BoundedExists B Φ (of t)) :
    LeastNumberPrinciple (RingOfDifferences M) := by
  intro n Φ hΦ B x₀ hx₀ hB
  by_contra hne
  push Not at hne
  obtain ⟨m₀, rfl⟩ := nonneg_iff.1 hx₀
  let Φ' : (Fin (n + 1 + 1) → RingOfDifferences M) → Prop := fun u ↦
    0 ≤ u 1 ∧ u 1 + u 0 ≤ of m₀ ∧ (∀ j : Fin n, |u j.succ.succ| < B) ∧ Φ fun i ↦ u i.succ
  have hΦ' : IsOpen Φ' := by is_open
  have hT (t : M) : BoundedExists (of m₀ + 1 + |B|) Φ' (of t) ↔
      ∃ z, 0 ≤ z ∧ z + of t ≤ of m₀ ∧ BoundedExists B Φ z := by
    constructor
    · rintro ⟨ys, -, h₁, h₂, h₃, h₄⟩
      use ys 0
      refine ⟨h₁, h₂, ?_⟩
      use Fin.tail ys
      exact ⟨h₃, by simpa using h₄⟩
    · rintro ⟨z, hz, e, ys, hys, h⟩
      use Fin.cons z ys
      have := abs_nonneg B
      have := le_abs_self B
      have hj : ∀ j, |(Fin.cons z ys : Fin (n + 1) → _) j| < of m₀ + 1 + |B| := by
        simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, abs_of_nonneg hz]
        exact ⟨by linarith [of_nonneg t], fun j ↦ by linarith [hys j]⟩
      exact ⟨hj, hz, e, hys, h⟩
  have h₀ : ∃ z, 0 ≤ z ∧ z + of 0 ≤ of m₀ ∧ BoundedExists B Φ z := by
    use of m₀
    exact ⟨of_nonneg m₀, by simp, hB⟩
  have hall := ind hΦ' _ ((hT 0).2 h₀) (fun t ht ↦ (hT (t + 1)).2 <| by
    obtain ⟨z, hz, e, hBz⟩ := (hT t).1 ht
    obtain ⟨y, hy, hyz, hBy⟩ := hne z hz hBz
    have := DiscretelyOrdered.one_le_of_pos (z - y) (sub_pos.2 hyz)
    use y
    exact ⟨hy, by rw [map_add, map_one]; linarith, hBy⟩) (m₀ + 1)
  obtain ⟨z, hz, e, -⟩ := (hT _).1 hall
  rw [map_add, map_one] at e
  linarith

end RingOfDifferences

namespace FFL.FirstOrder.Arithmetic

open RingOfDifferences OpenPredicate

section

variable {V W : Type}

/-- `∃ x₁ < &k, ⋯, ∃ xₙ < &k, φ`. -/
private def bexsBlock {ξ : Type} (k : ξ) {m : ℕ} :
    (n : ℕ) → ArithmeticSemiformula ξ (m + n) → ArithmeticSemiformula ξ m
  | 0, φ => φ
  | n + 1, φ => bexsBlock k n (φ.bexsLT &k)

private lemma bexsBlock_boundedExistential {ξ : Type} (k : ξ) {m : ℕ} :
    ∀ (n : ℕ) {φ : ArithmeticSemiformula ξ (m + n)},
      Semiformula.BoundedExistential 1 φ → Semiformula.BoundedExistential 1 (bexsBlock k n φ)
  | 0, _, h => h
  | n + 1, _, h => bexsBlock_boundedExistential k n (.bexsLT _ h)

variable [ORingStructure V]

private lemma eval_bexsBlock {ξ : Type} (k : ξ) (ε : ξ → V) {m : ℕ} :
    ∀ (n : ℕ) (φ : ArithmeticSemiformula ξ (m + n)) (e : Fin m → V),
      (bexsBlock k n φ).Eval e ε ↔
        ∃ xs : Fin n → V, (∀ i, xs i < ε k) ∧ φ.Eval (Matrix.appendr xs e) ε
  | 0, φ, e => by simp [bexsBlock, Matrix.empty_eq]
  | n + 1, φ, e => by
    simp [bexsBlock, eval_bexsBlock k ε n, Matrix.vecExists_iff, Fin.forall_fin_succ]
    aesop

variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {N : ℕ} (pv nv : W → ArithmeticSemiterm V N)

private lemma poly_translate {f : (W → RingOfDifferences V) → RingOfDifferences V}
    (hf : IsPolynomial f) : ∃ tp tn : ArithmeticSemiterm V N, ∀ e : Fin N → V,
      of (tp.val e id) - of (tn.val e id) =
        f fun i ↦ of ((pv i).val e id) - of ((nv i).val e id) := by
  induction hf with
  | var i =>
    use pv i, nv i
    exact fun _ ↦ rfl
  | const c =>
    use &(posPart c), &(negPart c)
    simp [RingOfDifferences.posPart_sub_negPart]
  | add _ _ ih₁ ih₂ =>
    obtain ⟨p₁, n₁, h₁⟩ := ih₁
    obtain ⟨p₂, n₂, h₂⟩ := ih₂
    use ‘!!p₁ + !!p₂’, ‘!!n₁ + !!n₂’
    simp [← h₁, ← h₂, map_add (of : V →+* _), sub_add_sub_comm]
  | mul _ _ ih₁ ih₂ =>
    obtain ⟨p₁, n₁, h₁⟩ := ih₁
    obtain ⟨p₂, n₂, h₂⟩ := ih₂
    use ‘!!p₁ * !!p₂ + !!n₁ * !!n₂’, ‘!!p₁ * !!n₂ + !!n₁ * !!p₂’
    intro e
    simp [← h₁, ← h₂, map_add (of : V →+* _), map_mul (of : V →+* _)]
    ring
  | neg _ ih =>
    obtain ⟨p, n, h⟩ := ih
    use n, p
    simp [← h]

private lemma open_translate {P : (W → RingOfDifferences V) → Prop} (hP : IsOpen P) :
    ∃ θ : ArithmeticSemiformula V N, θ.Open ∧ ∀ e : Fin N → V,
      (θ.Eval e id ↔ P fun i ↦ of ((pv i).val e id) - of ((nv i).val e id)) := by
  induction hP with
  | eq hf hg =>
    obtain ⟨p₁, n₁, h₁⟩ := poly_translate pv nv hf
    obtain ⟨p₂, n₂, h₂⟩ := poly_translate pv nv hg
    use “!!p₁ + !!n₂ = !!p₂ + !!n₁”
    simp [← h₁, ← h₂, sub_eq_sub_iff_add_eq_add, ← map_add (of : V →+* _)]
  | lt hf hg =>
    obtain ⟨p₁, n₁, h₁⟩ := poly_translate pv nv hf
    obtain ⟨p₂, n₂, h₂⟩ := poly_translate pv nv hg
    use “!!p₁ + !!n₂ < !!p₂ + !!n₁”
    simp [← h₁, ← h₂, sub_lt_sub_iff, ← map_add (of : V →+* _)]
  | not _ ih =>
    obtain ⟨θ, hθ, h⟩ := ih
    use ∼θ
    simp [hθ, h]
  | and _ _ ih₁ ih₂ =>
    obtain ⟨θ₁, hθ₁, h₁⟩ := ih₁
    obtain ⟨θ₂, hθ₂, h₂⟩ := ih₂
    use θ₁ ⋏ θ₂
    simp [hθ₁, hθ₂, h₁, h₂]
  | or _ _ ih₁ ih₂ =>
    obtain ⟨θ₁, hθ₁, h₁⟩ := ih₁
    obtain ⟨θ₂, hθ₂, h₂⟩ := ih₂
    use θ₁ ⋎ θ₂
    simp [hθ₁, hθ₂, h₁, h₂]

private lemma exists_e1 {n : ℕ} {Φ : (Fin (n + 1) → RingOfDifferences V) → Prop}
    (hΦ : IsOpen Φ) (B : RingOfDifferences V) :
    ∃ (ε : ℕ → V) (φ : ArithmeticSemiformula ℕ 1), Semiformula.BoundedExistential 1 φ ∧
      ∀ x : V, BoundedExists B Φ (of x) ↔ φ.Eval ![x] ε := by
  classical
  obtain ⟨b, hb⟩ := exists_forall_abs_lt_exists_sub B
  let pv : Fin (n + 1) → ArithmeticSemiterm V (1 + (n + n)) :=
    Fin.cons #((0 : Fin 1).addNat (n + n)) fun j ↦ #((j.castAdd n).addCast 1)
  let nv : Fin (n + 1) → ArithmeticSemiterm V (1 + (n + n)) :=
    Fin.cons ‘0’ fun j ↦ #((j.natAdd n).addCast 1)
  obtain ⟨θ, hθ, h⟩ := open_translate pv nv
    (P := fun w ↦ Φ w ∧ ∀ j : Fin n, |w j.succ| < B) (by is_open)
  let l := b :: θ.freeVariables.toList
  have hl {x} (hx : x ∈ l) : l.getD (l.idxOf x) b = x := by
    rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hx), List.getElem_idxOf]
  use fun k ↦ l.getD k b, bexsBlock (l.idxOf b) (n + n) (Rew.rewriteMap l.idxOf ▹ θ)
  constructor
  · exact bexsBlock_boundedExistential _ _ (.of_open (by simpa using hθ))
  intro x
  have hε : Function.funEqOn θ.FVar? (fun y ↦ l.getD (l.idxOf y) b) id := fun y hy ↦
    hl (List.mem_cons_of_mem _ (Finset.mem_toList.2 hy))
  have hv (xs : Fin (n + n) → V) : (fun i ↦ of ((pv i).val (Matrix.appendr xs ![x]) id) -
      of ((nv i).val (Matrix.appendr xs ![x]) id)) =
      Fin.cons (of x) fun j ↦ of (xs (j.castAdd n)) - of (xs (j.natAdd n)) := by
    funext i
    cases i using Fin.cases <;> simp [pv, nv]
  simp only [eval_bexsBlock, Semiformula.eval_rewriteMap, Semiformula.eval_iff_of_funEqOn θ hε,
    hl List.mem_cons_self, h, hv]
  constructor
  · rintro ⟨ys, hys, h⟩
    choose p q hpq hp hq using fun j ↦ hb (ys j) (hys j)
    have hq' (j : Fin n) : Fin.append p q (j.addNat n) = q j := by
      simpa using Fin.append_right p q j
    use Fin.append p q
    and_intros
    · intro i
      cases i using Fin.addCases <;> simp [hp, hq, hq']
    · simpa [hq', hpq] using h
    · intro j
      simpa [pv, nv, hq', hpq] using hys j
  · rintro ⟨xs, -, h, h'⟩
    use fun j ↦ of (xs (j.castAdd n)) - of (xs (j.natAdd n))
    exact ⟨fun j ↦ by simpa [pv, nv] using h' j, h⟩

end

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

instance : DiscretelyOrdered (RingOfDifferences V) :=
  ⟨fun _ hx ↦ one_le_of_pos one_le_of_zero_lt hx⟩

/-- The ring of differences of a model of $\mathsf{PA}^-$ that satisfies induction for bounded
existential formulas satisfies the least number principle for bounded existential open
predicates.
- [Wil85]
- [Smi93, Theorem 2.3] -/
lemma leastNumberPrinciple_of_models_induction
    [V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Semiformula.BoundedExistential 1)] :
    LeastNumberPrinciple (RingOfDifferences V) :=
  leastNumberPrinciple_of_boundedExists_induction fun hΦ B h0 hs t ↦
    InductionScheme.succ_induction (C := Semiformula.BoundedExistential 1)
      (P := fun t ↦ BoundedExists B _ (of t)) (exists_e1 hΦ B) h0 hs t

end FFL.FirstOrder.Arithmetic
