module

public import AlphaCentauri.Model.EnumerationCut
public import AlphaCentauri.Model.ProperCut
public import AlphaCentauri.ToFoundation.PrenexDefinable

/-!
# The coded limit of an enumeration cut

Over a model of $\mathsf{EA}$, two codes of initial segments of an enumeration cut agree on the
entries of the shorter one, and the longer code lies less than one block-bound above the shorter.
Under $\mathsf{I}\Delta_1$, a single code agrees with every code of the cut on its entries.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

noncomputable section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

attribute [local instance] ElementaryArithmetic.models_ISigma0_union_Omega1

lemma enumCode.ext_eq_of_le {a I i i' z z' t t' : V} {G : V → V → Prop}
    (hG : 𝚺ᴬ₀.DefinableRel G) (hfun : ∀ x y y', G x y → G x y' → y = y')
    (hinj : ∀ x x' y, G x y → G x' y → x = x') (hii' : i ≤ i')
    (h : enumCode a (I ⨳ a) G i z t) (h' : enumCode a (I ⨳ a) G i' z' t') :
    ∀ M, a - i ≤ M → M ≤ a → Nuon.ext a z M = Nuon.ext a z' M := by
  have h₁ := h.mono hfun (le_self_add (a := t) (b := t'))
  have h₂ := h'.mono hfun (le_add_self (a := t') (b := t))
  have key : ∀ j, j ≤ i → ∃ y ≤ t + t', G (entry a z j) y ∧ G (entry a z' j) y := by
    intro j
    induction j using ISigma0.succ_induction
    · unfold entry
      definability
    case zero =>
      intro _
      obtain ⟨-, y, hy, hGy⟩ := h₁.2.2.2.1 0 (Arithmetic.zero_le i)
      obtain ⟨-, y', hy', hGy'⟩ := h₂.2.2.2.1 0 (Arithmetic.zero_le i')
      have hy₁ : y ≤ y' :=
        h₁.2.2.2.2.1 (entry a z' 0) (h₂.2.2.2.1 0 (Arithmetic.zero_le i')).1 y' hy' hGy' y hy hGy
      have hy₂ : y' ≤ y :=
        h₂.2.2.2.2.1 (entry a z 0) (h₁.2.2.2.1 0 (Arithmetic.zero_le i)).1 y hy hGy y' hy' hGy'
      exact ⟨y, hy, hGy, (le_antisymm hy₁ hy₂) ▸ hGy'⟩
    case succ j IH =>
      intro hj
      obtain ⟨c, hc, hGc, hGc'⟩ := IH (le_trans le_self_add hj)
      have hjlt : j < i := (lt_add_one j).trans_le hj
      obtain ⟨hza, v, hv, hGv⟩ := h₁.2.2.2.1 (j + 1) hj
      obtain ⟨hza', v', hv', hGv'⟩ := h₂.2.2.2.1 (j + 1) (hj.trans hii')
      obtain ⟨hcv, hminv⟩ := h₁.2.2.2.2.2 j hjlt c hc v hv hGc hGv
      obtain ⟨hcv', hminv'⟩ := h₂.2.2.2.2.2 j (hjlt.trans_le hii') c hc v' hv' hGc' hGv'
      have hvv' : v ≤ v' := hminv (entry a z' (j + 1)) hza' v' hv' hGv' hcv'
      have hv'v : v' ≤ v := hminv' (entry a z (j + 1)) hza v hv hGv hcv
      exact ⟨v, hv, hGv, (le_antisymm hvv' hv'v) ▸ hGv'⟩
  intro M hM hMa
  have hj : a - M ≤ i := tsub_le_iff_right.mpr (by rw [add_comm]; exact tsub_le_iff_right.mp hM)
  obtain ⟨y, -, hG₁, hG₂⟩ := key (a - M) hj
  rw [ext_eq_entry hMa, ext_eq_entry hMa]
  exact hinj _ _ y hG₁ hG₂

lemma enumCode.mod_eq_zero {a I i z t q : V} {G : V → V → Prop} (hI : ‖I‖ = a + 1)
    (h : enumCode a (I ⨳ a) G i z t) (hq : Exponential ((a - i) * ‖a‖) q) : z % q = 0 := by
  have hk : a - i ≤ ‖I‖ := by
    rw [hI]
    exact (sub_le_self a i).trans le_self_add
  refine Nuon.ext_ext hq (mod_lt z hq.range_pos) hq.range_pos fun m hm => ?_
  have hma : m ≤ a := hm.le.trans (sub_le_self a i)
  have hia : i < a - m := lt_tsub_iff_right.mpr (by rw [add_comm]; exact lt_tsub_iff_right.mp hm)
  rw [Nuon.ext_zero, ext_mod_pow2 hk hm hq, ext_eq_entry hma]
  exact h.2.2.1 (a - m) (sub_le_self a m) hia

lemma enumCode.le_lt_add {a I i i' z z' t t' q : V} {G : V → V → Prop}
    (hG : 𝚺ᴬ₀.DefinableRel G) (hfun : ∀ x y y', G x y → G x y' → y = y')
    (hinj : ∀ x x' y, G x y → G x' y → x = x') (hI : ‖I‖ = a + 1) (hii' : i ≤ i')
    (h : enumCode a (I ⨳ a) G i z t) (h' : enumCode a (I ⨳ a) G i' z' t')
    (hq : Exponential ((a - i) * ‖a‖) q) : z ≤ z' ∧ z' < z + q := by
  have hia : i ≤ a := h.1
  have hi1 : i + 1 ≤ ‖I‖ := by rw [hI]; exact add_le_add_left hia 1
  obtain ⟨b, hb⟩ : ∃ b, Exponential ((i + 1) * ‖a‖) b :=
    ⟨_, exp_bexp_of_lt (Nuon.mul_len_lt_len_smash hi1)⟩
  have hsum : (a - i) * ‖a‖ + (i + 1) * ‖a‖ = ‖I‖ * ‖a‖ := by
    rw [← add_mul, hI, ← add_assoc, tsub_add_cancel_of_le hia]
  have hqb : q * b = I ⨳ a := by
    have h₁ := Exponential.add_mul hq hb
    rw [hsum] at h₁
    exact Exponential.uniq h₁ (exponential_smash I a)
  have hdiv : ∀ x, x < q * b → x / q < b := by
    intro x hx
    by_contra hc
    have h₁ : q * b ≤ q * (x / q) := mul_le_mul_left (not_lt.mp hc)
    have h₂ : q * (x / q) ≤ x := le_self_add.trans_eq (div_add_mod x q)
    exact absurd hx (not_lt.mpr (h₁.trans h₂))
  have hzB : z < q * b := by rw [hqb]; exact h.2.1
  have hz'B : z' < q * b := by rw [hqb]; exact h'.2.1
  have hdz : z / q = z' / q := by
    refine Nuon.ext_ext hb (hdiv z hzB) (hdiv z' hz'B) fun m hm => ?_
    have hkm : a - i + m ≤ a := (add_le_add_right (lt_succ_iff_le.mp hm) (a - i)).trans_eq
      (tsub_add_cancel_of_le hia)
    have hkI : a - i + m ≤ ‖I‖ := by rw [hI]; exact hkm.trans le_self_add
    rw [ext_div_pow2 hkI hq, ext_div_pow2 hkI hq]
    exact enumCode.ext_eq_of_le hG hfun hinj hii' h h' (a - i + m) le_self_add hkm
  have hz0 := enumCode.mod_eq_zero hI h hq
  have hzq : q * (z / q) = z := by
    have h₁ := div_add_mod z q
    rw [hz0, add_zero] at h₁
    exact h₁
  constructor
  · calc z = q * (z / q) := hzq.symm
      _ = q * (z' / q) := by rw [hdz]
      _ ≤ z' := le_self_add.trans_eq (div_add_mod z' q)
  · calc z' = q * (z' / q) + z' % q := (div_add_mod z' q).symm
      _ < q * (z' / q) + q := add_lt_add_right (mod_lt z' hq.range_pos) _
      _ = z + q := by rw [← hdz, hzq]

lemma enumCode.ext_eq_of_le_lt {a I i z e t q : V} {G : V → V → Prop} (hI : ‖I‖ = a + 1)
    (h : enumCode a (I ⨳ a) G i z t) (hq : Exponential ((a - i) * ‖a‖) q)
    (h₁ : z ≤ e) (h₂ : e < z + q) : ∀ M, a - i ≤ M → M ≤ a → Nuon.ext a e M = Nuon.ext a z M := by
  have hzq : q * (z / q) = z := by
    have h₃ := div_add_mod z q
    rw [enumCode.mod_eq_zero hI h hq, add_zero] at h₃
    exact h₃
  have hed : e / q = z / q :=
    div_eq_of (by rw [hzq]; exact h₁) (by rw [mul_add, mul_one, hzq]; exact h₂)
  intro M hM hMa
  obtain ⟨m, rfl⟩ := le_iff_exists_add.mp hM
  have hkI : a - i + m ≤ ‖I‖ := by rw [hI]; exact hMa.trans le_self_add
  rw [← ext_div_pow2 hkI hq, hed, ext_div_pow2 hkI hq]

lemma enumCode.definable_cut_body {a I : V} {G : V → V → Prop} (hG : 𝚺ᴬ₀.DefinableRel G) :
    𝚺ᴬ₀.Definable fun w : Fin (1 + 3) → V ↦
      enumCode a (I ⨳ a) G (w 0) (w 1) (w 2) ∧ w 3 < w 1 := by
  have := definable_enumCode hG a (I ⨳ a)
  definability

lemma enumCode.definable_gap_body {a I : V} {G : V → V → Prop} (hG : 𝚺ᴬ₀.DefinableRel G) :
    𝚺ᴬ₀.Definable fun w : Fin (1 + 3) → V ↦ I ⨳ a ≤ w 3 ∨
      (enumCode a (I ⨳ a) G (w 0) (w 1) (w 2) ∧
        ∃ p ≤ w 3, Exponential ((a - w 0) * ‖a‖) p ∧ w 1 + p ≤ w 3) := by
  have := definable_enumCode hG a (I ⨳ a)
  definability

lemma exists_gap {a I : V} [V↓[ℒₒᵣ] ⊧* 𝗜𝚫 1] {G : V → V → Prop} (hG : 𝚺ᴬ₀.DefinableRel G)
    (hdom : ∀ x y, G x y → x < a) (hfun : ∀ x y y', G x y → G x y' → y = y')
    (hinj : ∀ x x' y, G x y → G x' y → x = x') (hunb : ∀ s, ∃ x y, G x y ∧ s < y)
    (hI : ‖I‖ = a + 1)
    (hnomax : ∀ i z t, enumCode a (I ⨳ a) G i z t →
      ∃ i' z' t', enumCode a (I ⨳ a) G i' z' t' ∧ z < z') :
    ∃ e < I ⨳ a, ∀ i z t, enumCode a (I ⨳ a) G i z t →
      ∀ q, Exponential ((a - i) * ‖a‖) q → z ≤ e ∧ e < z + q := by
  let C : Set V := {x | ∃ i z t, enumCode a (I ⨳ a) G i z t ∧ x < z}
  let D : Set V := {x | ∃ i z t, I ⨳ a ≤ x ∨
    (enumCode a (I ⨳ a) G i z t ∧ ∃ p ≤ x, Exponential ((a - i) * ‖a‖) p ∧ z + p ≤ x)}
  have hC : PrenexDefinablePred 𝚺 1 (· ∈ C) :=
    (PrenexDefinable.exists_exists_exists_of_sigmaZero (k := 1)
      (R := fun v i z t ↦ enumCode a (I ⨳ a) G i z t ∧ v 0 < z)
      (enumCode.definable_cut_body hG)).of_iff fun v ↦ Iff.rfl
  have hD : PrenexDefinablePred 𝚺 1 (· ∈ D) :=
    (PrenexDefinable.exists_exists_exists_of_sigmaZero (k := 1)
      (R := fun v i z t ↦ I ⨳ a ≤ v 0 ∨
        (enumCode a (I ⨳ a) G i z t ∧ ∃ p ≤ v 0, Exponential ((a - i) * ‖a‖) p ∧ z + p ≤ v 0))
      (enumCode.definable_gap_body hG)).of_iff fun v ↦ Iff.rfl
  have hdisj : ∀ x, x ∈ C → x ∉ D := by
    rintro x ⟨i, z, t, hc, hxz⟩ ⟨i', z', t', hor⟩
    rcases hor with hBx | ⟨hc', p, hpe, hpq, hle⟩
    · exact lt_irrefl z ((hc.2.1.trans_le hBx).trans hxz)
    · rcases le_total i i' with hii | hii
      · obtain ⟨q, hq⟩ := exists_exponential_mul_length (a - i) a
        have hzz' := (enumCode.le_lt_add hG hfun hinj hI hii hc hc' hq).1
        exact absurd hxz (not_lt.mpr (hzz'.trans (le_self_add.trans hle)))
      · have hlt := (enumCode.le_lt_add hG hfun hinj hI hii hc' hc hpq).2
        exact lt_asymm (hlt.trans_le hle) hxz
  have hsucc : ∀ x, x ∈ C → x + 1 ∈ C := by
    rintro x ⟨i, z, t, hc, hxz⟩
    obtain ⟨i', z', t', hc', hzz'⟩ := hnomax i z t hc
    exact ⟨i', z', t', hc', (succ_le_iff_lt.mpr hxz).trans_lt hzz'⟩
  have hmem_of_lt : ∀ x y, x < y → y ∈ C → x ∈ C := by
    rintro x y hxy ⟨i, z, t, hc, hyz⟩
    exact ⟨i, z, t, hc, hxy.trans hyz⟩
  have hzero : (0 : V) ∈ C := by
    obtain ⟨z₀, -, t₀, h₀⟩ := enumCode.exists_zero hG hdom hfun hunb hI
    obtain ⟨i', z', t', hc', hzz'⟩ := hnomax 0 z₀ t₀ h₀
    exact ⟨i', z', t', hc', (Arithmetic.zero_le z₀).trans_lt hzz'⟩
  have hnotB : I ⨳ a ∉ C := by
    rintro ⟨i, z, t, hc, hBz⟩
    exact lt_irrefl z (hc.2.1.trans hBz)
  let K : Cut V :=
    { carrier := C, succ_mem := fun hx ↦ hsucc _ hx,
      mem_of_lt := fun hxy hy ↦ hmem_of_lt _ _ hxy hy }
  have hproper : K.Proper := ⟨hzero, I ⨳ a, hnotB⟩
  have hgap : ∃ e, e ∉ C ∧ e ∉ D := by
    by_contra hall
    push Not at hall
    have hπ : PrenexDefinablePred 𝚺 1 (· ∉ K.carrier) :=
      hD.of_iff fun v ↦ ⟨fun hx ↦ hall (v 0) hx, fun hx hxC ↦ hdisj (v 0) hxC hx⟩
    exact not_models_IDelta_of_proper_cut K 1 hproper hC hπ inferInstance
  obtain ⟨e, heC, heD⟩ := hgap
  refine ⟨e, not_le.mp fun h ↦ heD ⟨0, 0, 0, Or.inl h⟩, fun i z t hc q hq => ⟨?_, ?_⟩⟩
  · exact not_lt.mp fun h ↦ heC ⟨i, z, t, hc, h⟩
  · exact not_le.mp fun hle ↦ heD ⟨i, z, t, Or.inr ⟨hc, q, le_add_self.trans hle, hq, hle⟩⟩

/-- The codes of the initial segments of an enumeration cut converge to a single code.
- [Tha05, Lemma 1] -/
theorem exists_coded_limit [V↓[ℒₒᵣ] ⊧* 𝗜𝚫 1] {a I : V} {f : V → V}
    (hI : ‖I‖ = a + 1) (hinj : ∀ x < a, ∀ y < a, f x = f y → x = y)
    (hunb : ∀ s, ∃ x < a, s < f x) (hgraph : 𝚺ᴬ₀.DefinableRel fun x y ↦ x < a ∧ f x = y) :
    ∃ e < I ⨳ a, ∀ i ∈ (enumerationCut a I f hI hunb hgraph).carrier, ∀ z t,
      enumCode a (I ⨳ a) (fun x y ↦ x < a ∧ f x = y) i z t →
        ∀ j ≤ i, entry a e j = entry a z j := by
  have hfun : ∀ x y y' : V, (x < a ∧ f x = y) → (x < a ∧ f x = y') → y = y' :=
    fun x y y' h h' ↦ h.2.symm.trans h'.2
  have hinj' : ∀ x x' y : V, (x < a ∧ f x = y) → (x' < a ∧ f x' = y) → x = x' :=
    fun x x' y h h' ↦ hinj x h.1 x' h'.1 (h.2.trans h'.2.symm)
  by_cases hmax : ∃ i₀ z₀ t₀, enumCode a (I ⨳ a) (fun x y ↦ x < a ∧ f x = y) i₀ z₀ t₀ ∧
      ∀ i z t, enumCode a (I ⨳ a) (fun x y ↦ x < a ∧ f x = y) i z t → z ≤ z₀
  · obtain ⟨i₀, z₀, t₀, h₀, hmax⟩ := hmax
    refine ⟨z₀, h₀.2.1, fun i _ z t h j hj => ?_⟩
    rcases le_total i i₀ with hii | hii
    · have hM : a - i ≤ a - j := tsub_le_tsub_left hj a
      exact (enumCode.ext_eq_of_le hgraph hfun hinj' hii h h₀ (a - j) hM (sub_le_self a j)).symm
    · obtain ⟨q, hq⟩ := exists_exponential_mul_length (a - i₀) a
      have hzz := (enumCode.le_lt_add hgraph hfun hinj' hI hii h₀ h hq).1
      rw [le_antisymm (hmax i z t h) hzz]
  · push Not at hmax
    obtain ⟨e, he, hgap⟩ :=
      exists_gap hgraph (fun x y h ↦ h.1) hfun hinj' (exists_graph_unbounded a hunb) hI hmax
    refine ⟨e, he, fun i _ z t h j hj => ?_⟩
    obtain ⟨q, hq⟩ := exists_exponential_mul_length (a - i) a
    obtain ⟨h₁, h₂⟩ := hgap i z t h q hq
    have hM : a - i ≤ a - j := tsub_le_tsub_left hj a
    exact enumCode.ext_eq_of_le_lt hI h hq h₁ h₂ (a - j) hM (sub_le_self a j)

end

end FFL.FirstOrder.Arithmetic
