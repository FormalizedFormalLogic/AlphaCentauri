module

public import AlphaCentauri.Schemata.EA
public import Foundation.FirstOrder.Arithmetic.Omega1.Nuon

/-!
# Factorial

The factorial function on a model of $\mathsf{E}\mathsf{A}$, read off from the last block of a
number whose blocks list the partial products $0!, 1!, \dots, x!$.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

noncomputable section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

attribute [local instance] ElementaryArithmetic.models_ISigma0_union_Omega1

local notation S "{" L "}[" i "]" => Nuon.ext L S i

namespace Factorial

variable {a d x k k' L L' I S S' U : V}

/-- The blocks of `S` of width `‖L‖` list the partial products up to `k!`. -/
def IsSeq (L S k : V) : Prop := S{L}[0] = 1 ∧ ∀ i < k, S{L}[i + 1] = S{L}[i] * (i + 1)

lemma IsSeq.of_le (H : IsSeq L S k) (h : k' ≤ k) : IsSeq L S k' :=
  ⟨H.1, fun i hi ↦ H.2 i (lt_of_lt_of_le hi h)⟩

lemma IsSeq.ext_pos (H : IsSeq L S k) : ∀ i ≤ k, 0 < S{L}[i] := by
  intro i
  induction i using ISigma0.succ_induction
  · definability
  case zero => intro _; simp [H.1]
  case succ i IH =>
    intro hi
    rw [H.2 i (succ_le_iff_lt.mp hi)]
    exact mul_pos (IH (le_trans (by simp) hi)) (by simp)

private lemma IsSeq.exists_ext_eq_mul (H : IsSeq L S k) (pos : 0 < d) :
    ∀ i ≤ k, d ≤ i → ∃ c ≤ S, S{L}[i] = d * c := by
  intro i
  induction i using ISigma0.succ_induction
  · definability
  case zero => intro _ h; exact absurd h (not_le.mpr pos)
  case succ i IH =>
    intro hi hd
    have hrec : S{L}[i + 1] = S{L}[i] * (i + 1) := H.2 i (succ_le_iff_lt.mp hi)
    rcases hd with rfl | hd
    · exact ⟨S{L}[i], Nuon.ext_le_self L S i, by rw [hrec, mul_comm]⟩
    · obtain ⟨c, _, hc⟩ := IH (le_trans (by simp) hi) (lt_succ_iff_le.mp hd)
      have hle : c * (i + 1) ≤ S := calc
        c * (i + 1) ≤ d * (c * (i + 1)) := le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp pos)
        _           = S{L}[i + 1]       := by rw [hrec, hc, mul_assoc]
        _           ≤ S                 := Nuon.ext_le_self L S (i + 1)
      exact ⟨c * (i + 1), hle, by rw [hrec, hc, mul_assoc]⟩

lemma IsSeq.ext_dvd (H : IsSeq L S k) (pos : 0 < d) : ∀ i ≤ k, d ≤ i → d ∣ S{L}[i] := by
  intro i hi hd
  obtain ⟨c, _, hc⟩ := H.exists_ext_eq_mul pos i hi hd
  exact ⟨c, hc⟩

lemma IsSeq.ext_eq (H : IsSeq L S k) (H' : IsSeq L' S' k) : ∀ i ≤ k, S{L}[i] = S'{L'}[i] := by
  intro i
  induction i using ISigma0.succ_induction
  · definability
  case zero => intro _; rw [H.1, H'.1]
  case succ i IH =>
    intro hi
    rw [H.2 i (succ_le_iff_lt.mp hi), H'.2 i (succ_le_iff_lt.mp hi), IH (le_trans (by simp) hi)]

private lemma mul_length_lt_length (hL : Exponential (x * ‖x‖) L) {i : V} (hi : i ≤ x) :
    i * ‖x‖ < ‖L‖ := by
  rw [hL.length_eq]; exact lt_succ_iff_le.mpr (mul_le_mul_right hi)

private lemma length_lt_length (hL : Exponential (x * ‖x‖) L) : ‖x‖ < ‖L‖ := by
  rcases Arithmetic.zero_le x with (rfl | pos)
  · simp [hL.length_eq]
  · simpa using mul_length_lt_length hL (i := 1) (pos_iff_one_le.mp pos)

private lemma mul_succ_le_bexp (hL : Exponential (x * ‖x‖) L) (hk : k + 1 ≤ x)
    (ha : a ≤ bexp L (k * ‖x‖)) : a * (k + 1) ≤ bexp L ((k + 1) * ‖x‖) := by
  have h₁ : k + 1 ≤ bexp L ‖x‖ :=
    le_of_lt (lt_of_le_of_lt hk (lt_exp_len_self (exp_bexp_of_lt (length_lt_length hL))))
  have e : (k + 1) * ‖x‖ = k * ‖x‖ + ‖x‖ := by simp [add_mul]
  have h₂ : bexp L ((k + 1) * ‖x‖) = bexp L (k * ‖x‖) * bexp L ‖x‖ := by
    rw [e]; exact bexp_add (by rw [← e]; exact mul_length_lt_length hL hk)
  rw [h₂]
  exact mul_le_mul ha h₁ (by simp) (by simp)

lemma IsSeq.le_bexp (H : IsSeq L S k) (hL : Exponential (x * ‖x‖) L) (hk : k ≤ x) :
    ∀ i ≤ k, S{L}[i] ≤ bexp L (i * ‖x‖) := by
  intro i
  induction i using ISigma0.succ_induction
  · definability
  case zero => intro _; simp [H.1, bexp_pos_zero hL.range_pos]
  case succ i IH =>
    intro hi
    rw [H.2 i (succ_le_iff_lt.mp hi)]
    exact mul_succ_le_bexp hL (le_trans hi hk) (IH (le_trans (by simp) hi))

lemma IsSeq.length_ext_mul_le (H : IsSeq L S k) (hL : Exponential (x * ‖x‖) L)
    (hk : k + 1 ≤ x) : ‖S{L}[k] * (k + 1)‖ ≤ ‖L‖ := calc
  ‖S{L}[k] * (k + 1)‖ ≤ ‖bexp L ((k + 1) * ‖x‖)‖ :=
    length_monotone (mul_succ_le_bexp hL hk (H.le_bexp hL (le_trans (by simp) hk) k le_rfl))
  _                   = (k + 1) * ‖x‖ + 1        := len_bexp (mul_length_lt_length hL hk)
  _                   ≤ ‖L‖                      := by
    rw [hL.length_eq]; exact add_le_add (mul_le_mul_right hk) le_rfl

private lemma one_lt_sq_smash (hL : Exponential (x * ‖x‖) L) (hI : Exponential x I) :
    (1 : V) < (I ⨳ L) ^ 2 := by
  have h₁ : (1 : V) ≤ ‖I‖ * ‖L‖ := by
    have hI' : (1 : V) ≤ ‖I‖ := by simp [hI.length_eq]
    have hL' : (1 : V) ≤ ‖L‖ := by simp [hL.length_eq]
    simpa using mul_le_mul hI' hL' (by simp) (by simp)
  have h₂ : I ⨳ L ≤ (I ⨳ L) ^ 2 := by simpa [sq] using pos_iff_one_le.mp (smash_pos I L)
  exact lt_of_lt_of_le (lt_of_le_of_lt h₁ (smash_lt I L)) h₂

private lemma succ_le_length (hI : Exponential x I) (hk : k + 1 ≤ x) : k + 1 ≤ ‖I‖ := by
  rw [hI.length_eq]; exact add_le_add (le_trans (by simp) hk) le_rfl

private lemma IsSeq.append (H : IsSeq L S k) (hL : Exponential (x * ‖x‖) L)
    (hI : Exponential x I) (hk : k + 1 ≤ x) :
    IsSeq L (Nuon.append I L S (k + 1) (S{L}[k] * (k + 1))) (k + 1) := by
  have hX : ‖S{L}[k] * (k + 1)‖ ≤ ‖L‖ := H.length_ext_mul_le hL hk
  have hlast := Nuon.ext_append_last I L S (succ_le_length hI hk) hX
  have hlt : ∀ j < k + 1, (Nuon.append I L S (k + 1) (S{L}[k] * (k + 1))){L}[j] = S{L}[j] :=
    fun j hj ↦ Nuon.ext_append_lt I L S (succ_le_length hI hk) hj
  constructor
  · rw [hlt 0 (by simp)]; exact H.1
  · intro i hik
    rcases lt_succ_iff_le.mp hik with rfl | hik
    · rw [hlast, hlt i (by simp)]
    · rw [hlt (i + 1) (by simpa using hik), hlt i (lt_trans hik (by simp)), H.2 i hik]

lemma exists_lt_isSeq (hL : Exponential (x * ‖x‖) L) (hI : Exponential x I)
    (hU : (I ⨳ L) ^ 2 ≤ U) : ∀ k ≤ x, ∃ S < U, IsSeq L S k := by
  have hone : (1 : V) < U := lt_of_lt_of_le (one_lt_sq_smash hL hI) hU
  intro k
  induction k using ISigma0.succ_induction
  · definability
  case zero =>
    intro _
    exact ⟨1, hone, Nuon.ext_zero_eq_self_of_le (by simp [hL.length_eq]), by simp⟩
  case succ k IH =>
    intro hk
    obtain ⟨S, _, H⟩ := IH (le_trans (by simp) hk)
    exact ⟨Nuon.append I L S (k + 1) (S{L}[k] * (k + 1)),
      lt_of_lt_of_le (Nuon.append_lt_sq_smash I L S (succ_le_length hI hk)
        (H.length_ext_mul_le hL hk) hI.range_pos) hU,
      H.append hL hI hk⟩

lemma exists_isSeq (x : V) : ∃ L S, IsSeq L S x := by
  obtain ⟨L, hL⟩ := ElementaryArithmetic.exponential_total (x * ‖x‖)
  obtain ⟨I, hI⟩ := ElementaryArithmetic.exponential_total x
  obtain ⟨S, _, H⟩ := exists_lt_isSeq hL hI (le_refl ((I ⨳ L) ^ 2)) x le_rfl
  exact ⟨L, S, H⟩

def isSeqDef : 𝚺₀.Semisentence 3 := .mkSigma
  “L S k.
    !Nuon.extDef 1 L S 0 ∧
    ∀ i < k, ∃ b <⁺ S, !Nuon.extDef b L S i ∧ !Nuon.extDef (b * (i + 1)) L S (i + 1)”

instance isSeq_defined :
    𝚺₀.Defined (V := V) (fun v ↦ IsSeq (v 0) (v 1) (v 2)) isSeqDef := .mk fun v ↦ by
  simp [IsSeq, isSeqDef, Eq.comm]

end Factorial

/-- `y` is the factorial of `x`. -/
def Factorial (x y : V) : Prop := ∃ L S, Factorial.IsSeq L S x ∧ S{L}[x] = y

lemma Factorial.exists_unique (x : V) : ∃! y, Factorial x y := by
  obtain ⟨L, S, H⟩ := Factorial.exists_isSeq x
  apply ExistsUnique.intro (S{L}[x]) ⟨L, S, H, rfl⟩
  rintro y ⟨L', S', H', rfl⟩
  exact H'.ext_eq H x le_rfl

/-- - [HP98, Theorem I.1.58(1)] -/
def factorial (x : V) : V := Classical.choose! (Factorial.exists_unique x)

@[simp] lemma factorial_factorial (x : V) : Factorial x (factorial x) :=
  Classical.choose!_spec (Factorial.exists_unique x)

lemma Factorial.factorial_eq {x y : V} (h : Factorial x y) : factorial x = y :=
  (Factorial.exists_unique x).unique (factorial_factorial x) h

lemma Factorial.eq_iff {x y : V} : y = factorial x ↔ Factorial x y :=
  Classical.choose!_eq_iff_right (Factorial.exists_unique x)

@[simp] lemma factorial_zero : factorial (0 : V) = 1 :=
  Factorial.factorial_eq
    ⟨1, 1, ⟨Nuon.ext_zero_eq_self_of_le (by simp), by simp⟩,
      Nuon.ext_zero_eq_self_of_le (by simp)⟩

@[simp] lemma factorial_succ (x : V) : factorial (x + 1) = factorial x * (x + 1) := by
  obtain ⟨L, S, H⟩ := Factorial.exists_isSeq (x + 1)
  rw [Factorial.factorial_eq (⟨L, S, H, rfl⟩ : Factorial (x + 1) _),
    Factorial.factorial_eq (⟨L, S, H.of_le (by simp), rfl⟩ : Factorial x _),
    H.2 x (by simp)]

def factorialDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. ∃ L, ∃ S, !Factorial.isSeqDef L S x ∧ !Nuon.extDef y L S x”

instance factorial_defined : 𝚺₁-Function₁[V] factorial via factorialDef := .mk fun v ↦ by
  simp [factorialDef, Factorial.eq_iff, Factorial, Eq.comm]

instance factorial_definable : 𝚺₁-Function₁[V] factorial := factorial_defined.to_definable

@[simp] lemma factorial_pos (x : V) : 0 < factorial x := by
  obtain ⟨L, S, H⟩ := Factorial.exists_isSeq x
  rw [Factorial.factorial_eq (⟨L, S, H, rfl⟩ : Factorial x _)]
  exact H.ext_pos x le_rfl

lemma dvd_factorial {d x : V} (pos : 0 < d) (h : d ≤ x) : d ∣ factorial x := by
  obtain ⟨L, S, H⟩ := Factorial.exists_isSeq x
  rw [Factorial.factorial_eq (⟨L, S, H, rfl⟩ : Factorial x _)]
  exact H.ext_dvd pos x le_rfl h

end

end FFL.FirstOrder.Arithmetic
