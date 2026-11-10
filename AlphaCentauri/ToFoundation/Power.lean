module

public import AlphaCentauri.ToFoundation.BlockSequence
public import AlphaCentauri.ToFoundation.Exponential

/-!
# Bounded powers over $\mathsf{I}\Sigma_0 + \Omega_1$

Over a model of $\mathsf{I}\Sigma_0 + \Omega_1$, `bpow B x k` is $x^k$ whenever $k \|x\| \le \|B\|$:
the value is read off from a number below $(B \mathbin{\#} B)^2$ whose blocks of width $\|B\|$ list
the partial powers $x^0, \dots, x^k$. The graph is $\Delta_0$ in the parameter `B`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

noncomputable section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ ∪ 𝝮₁]

local notation S "{" L "}[" i "]" => Nuon.ext L S i

namespace Power

variable {B x k k' S S' L L' : V}

lemma one_lt_sq_smash (hB : 0 < B) : (1 : V) < (B ⨳ B) ^ 2 := by
  have hB1 : (1 : V) ≤ ‖B‖ := pos_iff_one_le.mp (length_pos_iff.mpr hB)
  have h₁ : (1 : V) < B ⨳ B := lt_smash_iff.mpr (by simpa using one_le_mul hB1 hB1)
  calc (1 : V) < B ⨳ B := h₁
    _ ≤ (B ⨳ B) * (B ⨳ B) := le_mul_of_one_le_left (Arithmetic.zero_le _) h₁.le
    _ = (B ⨳ B) ^ 2 := (sq _).symm

/-- The blocks of `S` of width `‖L‖` list the powers $x^0, \dots, x^k$. -/
def IsSeq (L S x k : V) : Prop := S{L}[0] = 1 ∧ ∀ i < k, S{L}[i + 1] = S{L}[i] * x

def isSeqDef : 𝚺ᴬ₀.Semisentence 4 := .mkSigma
  “L S x k.
    !Nuon.extDef 1 L S 0 ∧
    ∀ i < k, ∃ b <⁺ S, !Nuon.extDef b L S i ∧ !Nuon.extDef (b * x) L S (i + 1)”

instance isSeq_defined :
    𝚺ᴬ₀.Defined (V := V) (fun v ↦ IsSeq (v 0) (v 1) (v 2) (v 3)) isSeqDef := .mk fun v ↦ by
  simp [IsSeq, isSeqDef, Eq.comm]

lemma definable_isSeq : 𝚺ᴬ₀.DefinableRel₄ (IsSeq : V → V → V → V → Prop) :=
  isSeq_defined.to_definable

lemma IsSeq.of_le (H : IsSeq L S x k) (h : k' ≤ k) : IsSeq L S x k' :=
  ⟨H.1, fun i hi ↦ H.2 i (lt_of_lt_of_le hi h)⟩

lemma IsSeq.ext_eq (H : IsSeq L S x k) (H' : IsSeq L' S' x k) :
    ∀ i ≤ k, S{L}[i] = S'{L'}[i] := by
  intro i
  induction i using ISigma0.succ_induction
  · definability
  case zero => intro _; rw [H.1, H'.1]
  case succ i IH =>
    intro hi
    rw [H.2 i (succ_le_iff_lt.mp hi), H'.2 i (succ_le_iff_lt.mp hi), IH (le_trans (by simp) hi)]

lemma exists_isSeq (hB : 0 < B) (hx : 0 < x) (hk : k * ‖x‖ < ‖B‖) :
    ∃ S < (B ⨳ B) ^ 2, IsSeq B S x k ∧ ‖S{B}[k]‖ ≤ k * ‖x‖ + 1 := by
  have hx1 : 1 ≤ ‖x‖ := pos_iff_one_le.mp (length_pos_iff.mpr hx)
  have hone := one_lt_sq_smash hB
  have key : ∀ i ≤ k, ∃ S < (B ⨳ B) ^ 2, IsSeq B S x i ∧ ‖S{B}[i]‖ ≤ i * ‖x‖ + 1 := by
    intro i
    induction i using ISigma0.succ_induction
    · have := definable_isSeq (V := V)
      definability
    case zero =>
      intro _
      have h1 : (1 : V){B}[0] = 1 :=
        Nuon.ext_zero_eq_self_of_le (by simpa using pos_iff_one_le.mp (length_pos_iff.mpr hB))
      use 1
      and_intros
      · exact hone
      · exact h1
      · simp
      · simp [h1]
    case succ i IH =>
      intro hi
      obtain ⟨S, -, H, hlen⟩ := IH (le_trans (by simp) hi)
      have hlen' : ‖S{B}[i] * x‖ ≤ (i + 1) * ‖x‖ + 1 := calc
        ‖S{B}[i] * x‖ ≤ ‖S{B}[i]‖ + ‖x‖ := length_mul_le _ _
        _ ≤ i * ‖x‖ + 1 + ‖x‖ := by simpa using hlen
        _ = (i + 1) * ‖x‖ + 1 := by rw [add_mul, one_mul]; grind
      have hiB : (i + 1) * ‖x‖ < ‖B‖ := lt_of_le_of_lt (mul_le_mul_right hi) hk
      have hiI : i + 1 ≤ ‖B‖ :=
        le_trans (le_mul_of_one_le_right (Arithmetic.zero_le _) hx1) hiB.le
      have hX : ‖S{B}[i] * x‖ ≤ ‖B‖ := hlen'.trans (succ_le_iff_lt.mpr hiB)
      have hlast := Nuon.ext_append_last B B S hiI hX
      have hlt : ∀ j < i + 1, (Nuon.append B B S (i + 1) (S{B}[i] * x)){B}[j] = S{B}[j] :=
        fun j hj ↦ Nuon.ext_append_lt B B S hiI hj
      use Nuon.append B B S (i + 1) (S{B}[i] * x)
      and_intros
      · exact Nuon.append_lt_sq_smash B B S hiI hX hB
      · rw [hlt 0 (by simp)]; exact H.1
      · intro j hj
        rcases lt_succ_iff_le.mp hj with rfl | hj
        · rw [hlast, hlt j (by simp)]
        · rw [hlt (j + 1) (by simpa using hj), hlt j (lt_trans hj (by simp)), H.2 j hj]
      · rwa [hlast]
  exact key k le_rfl

/-- `y` is $x^k$, as listed by a sequence with blocks of width `‖B‖`. -/
def IsPow (B x k y : V) : Prop := ∃ S < (B ⨳ B) ^ 2, IsSeq B S x k ∧ S{B}[k] = y

lemma IsPow.unique {y y' : V} (h : IsPow B x k y) (h' : IsPow B x k y') : y = y' := by
  obtain ⟨S, -, H, rfl⟩ := h
  obtain ⟨S', -, H', rfl⟩ := h'
  exact H.ext_eq H' k le_rfl

lemma definable_isPow (B : V) : 𝚺ᴬ₀.DefinableRel₃ (IsPow B) := by
  have := definable_isSeq (V := V)
  unfold IsPow
  definability

lemma IsPow.lt {y : V} (h : IsPow B x k y) : y < B ⨳ 1 := by
  obtain ⟨S, -, -, rfl⟩ := h
  exact mod_lt _ (smash_pos B 1)

end Power

open Power

open Classical in
/-- $x^k$, computed with blocks of width `‖B‖`; it is $0$ if no such sequence exists. -/
def bpow (B x k : V) : V := if h : ∃ y, IsPow B x k y then h.choose else 0

section bpow

variable {B x y k : V}

lemma Power.IsPow.bpow_eq (h : IsPow B x k y) : bpow B x k = y := by
  unfold bpow
  split_ifs with h'
  · exact h'.choose_spec.unique h
  · exact absurd ⟨y, h⟩ h'

lemma bpow_eq_iff : y = bpow B x k ↔ IsPow B x k y ∨ ((¬∃ y' < B ⨳ 1, IsPow B x k y') ∧ y = 0) := by
  constructor
  · rintro rfl
    by_cases h : ∃ y, IsPow B x k y
    · left
      obtain ⟨y, hy⟩ := h
      rwa [hy.bpow_eq]
    · right
      push Not at h
      constructor
      · rintro ⟨y, -, hy⟩
        exact h y hy
      · unfold bpow
        split_ifs with h'
        · obtain ⟨y, hy⟩ := h'
          exact absurd hy (h y)
        · rfl
  · rintro (h | ⟨h, rfl⟩)
    · exact h.bpow_eq.symm
    · unfold bpow
      split_ifs with h'
      · obtain ⟨y, hy⟩ := h'
        exact absurd ⟨y, hy.lt, hy⟩ h
      · rfl

instance (B : V) : 𝚺ᴬ₀.DefinableFunction₂ (bpow B) := by
  have := definable_isPow B
  simp only [Bounding.HierarchySymbol.DefinableFunction₂,
    Bounding.HierarchySymbol.DefinableFunction, bpow_eq_iff]
  definability

lemma bpow_lt (B x k : V) : bpow B x k < B ⨳ 1 := by
  unfold bpow
  split_ifs with h
  · exact h.choose_spec.lt
  · exact smash_pos B 1

instance (B : V) : Bounded₂ (bpow B) := ⟨&(B ⨳ 1), fun _ ↦ by simpa using (bpow_lt B _ _).le⟩

lemma isPow_bpow (hB : 0 < B) (hx : 0 < x) (hk : k * ‖x‖ < ‖B‖) :
    IsPow B x k (bpow B x k) ∧ ‖bpow B x k‖ ≤ k * ‖x‖ + 1 := by
  obtain ⟨S, hS, H, hlen⟩ := exists_isSeq hB hx hk
  have h : IsPow B x k (S{B}[k]) := ⟨S, hS, H, rfl⟩
  rw [h.bpow_eq]
  exact ⟨h, hlen⟩

lemma length_bpow_le (hB : 0 < B) (hx : 0 < x) (hk : k * ‖x‖ < ‖B‖) :
    ‖bpow B x k‖ ≤ k * ‖x‖ + 1 :=
  (isPow_bpow hB hx hk).2

@[simp] lemma bpow_zero (hB : 0 < B) (x : V) : bpow B x 0 = 1 := by
  have h1 : (1 : V){B}[0] = 1 :=
    Nuon.ext_zero_eq_self_of_le (by simpa using pos_iff_one_le.mp (length_pos_iff.mpr hB))
  apply Power.IsPow.bpow_eq
  use 1
  and_intros
  · exact one_lt_sq_smash hB
  · exact h1
  · simp
  · exact h1

lemma bpow_succ (hB : 0 < B) (hx : 0 < x) (hk : (k + 1) * ‖x‖ < ‖B‖) :
    bpow B x (k + 1) = bpow B x k * x := by
  obtain ⟨S, hS, H, -⟩ := exists_isSeq hB hx hk
  rw [Power.IsPow.bpow_eq (⟨S, hS, H, rfl⟩ : IsPow B x (k + 1) _),
    Power.IsPow.bpow_eq (⟨S, hS, H.of_le (by simp), rfl⟩ : IsPow B x k _), H.2 k (by simp)]

lemma bpow_pos (hB : 0 < B) (hx : 0 < x) (hk : k * ‖x‖ < ‖B‖) : 0 < bpow B x k := by
  revert hk
  induction k using ISigma0.succ_induction
  · definability
  case zero => intro _; simp [hB]
  case succ k IH =>
    intro hk
    rw [bpow_succ hB hx hk]
    exact mul_pos (IH (lt_of_le_of_lt (mul_le_mul_right (by simp)) hk)) hx

lemma bpow_mul {y : V} (hB : 0 < B) (hx : 0 < x) (hy : 0 < y) (hk : k * ‖x * y‖ < ‖B‖) :
    bpow B (x * y) k = bpow B x k * bpow B y k := by
  revert hk
  induction k using ISigma0.succ_induction
  · definability
  case zero => intro _; simp [hB]
  case succ k IH =>
    intro hk
    have hxy : 0 < x * y := mul_pos hx hy
    have hkx : (k + 1) * ‖x‖ < ‖B‖ :=
      lt_of_le_of_lt (mul_le_mul_left (length_monotone (le_mul_of_one_le_right
        (Arithmetic.zero_le _) (pos_iff_one_le.mp hy)))) hk
    have hky : (k + 1) * ‖y‖ < ‖B‖ :=
      lt_of_le_of_lt (mul_le_mul_left (length_monotone (le_mul_of_one_le_left
        (Arithmetic.zero_le _) (pos_iff_one_le.mp hx)))) hk
    rw [bpow_succ hB hxy hk, bpow_succ hB hx hkx, bpow_succ hB hy hky,
      IH (lt_of_le_of_lt (mul_le_mul_right (by simp)) hk)]
    grind

lemma bpow_monotone {y : V} (hB : 0 < B) (hx : 0 < x) (hxy : x ≤ y) (hk : k * ‖y‖ < ‖B‖) :
    bpow B x k ≤ bpow B y k := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  revert hk
  induction k using ISigma0.succ_induction
  · definability
  case zero => intro _; simp [hB]
  case succ k IH =>
    intro hk
    have hkx : (k + 1) * ‖x‖ < ‖B‖ := lt_of_le_of_lt (mul_le_mul_left (length_monotone hxy)) hk
    rw [bpow_succ hB hx hkx, bpow_succ hB hy hk]
    exact mul_le_mul (IH (lt_of_le_of_lt (mul_le_mul_right (by simp)) hk)) hxy
      (Arithmetic.zero_le _)
      (Arithmetic.zero_le _)

lemma bpow_one_left (hB : 0 < B) (hk : k < ‖B‖) : bpow B 1 k = 1 := by
  revert hk
  induction k using ISigma0.succ_induction
  · definability
  case zero => intro _; simp [hB]
  case succ k IH =>
    intro hk
    rw [bpow_succ hB one_pos (by simpa using hk), IH (lt_of_le_of_lt (by simp) hk), mul_one]

lemma length_bpow_two_mul {w : V} (hB : 0 < B) (hw : 0 < w) (hk : k * ‖(2 : V)‖ < ‖B‖) :
    ‖bpow B 2 k * w‖ = ‖w‖ + k := by
  revert hk
  induction k using ISigma0.succ_induction
  · definability
  case zero => intro _; simp [hB]
  case succ k IH =>
    intro hk
    rw [bpow_succ hB two_pos hk, mul_comm (bpow B 2 k) 2, mul_assoc,
      length_two_mul_of_pos (mul_pos (bpow_pos hB two_pos
        (lt_of_le_of_lt (mul_le_mul_right (by simp)) hk)) hw),
      IH (lt_of_le_of_lt (mul_le_mul_right (by simp)) hk), add_assoc]

end bpow

end

end FFL.FirstOrder.Arithmetic
