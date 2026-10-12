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
  have key := enumCode.exists_common_value hG hfun hii' h h'
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

lemma enumCode.mul_div_eq {a I i z t q : V} {G : V → V → Prop} (hI : ‖I‖ = a + 1)
    (h : enumCode a (I ⨳ a) G i z t) (hq : Exponential ((a - i) * ‖a‖) q) : q * (z / q) = z := by
  have h₁ := div_add_mod z q
  rwa [enumCode.mod_eq_zero hI h hq, add_zero] at h₁

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
  have hzq := enumCode.mul_div_eq hI h hq
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
  have hzq := enumCode.mul_div_eq hI h hq
  have hed : e / q = z / q :=
    div_eq_of (by rw [hzq]; exact h₁) (by rw [mul_add, mul_one, hzq]; exact h₂)
  intro M hM hMa
  obtain ⟨m, rfl⟩ := le_iff_exists_add.mp hM
  have hkI : a - i + m ≤ ‖I‖ := by rw [hI]; exact hMa.trans le_self_add
  rw [← ext_div_pow2 hkI hq, hed, ext_div_pow2 hkI hq]

private def codeBelow (a I : V) (G : V → V → Prop) (x : V) : Prop :=
  ∃ i z t, enumCode a (I ⨳ a) G i z t ∧ x < z

private def codeAbove (a I : V) (G : V → V → Prop) (x : V) : Prop :=
  ∃ i z t, I ⨳ a ≤ x ∨
    (enumCode a (I ⨳ a) G i z t ∧ ∃ p ≤ x, Exponential ((a - i) * ‖a‖) p ∧ z + p ≤ x)

private def NoMaximalCode (a I : V) (G : V → V → Prop) : Prop :=
  ∀ i z t, enumCode a (I ⨳ a) G i z t →
    ∃ i' z' t', enumCode a (I ⨳ a) G i' z' t' ∧ z < z'

private lemma prenexDefinablePred_codeBelow {a I : V} {G : V → V → Prop}
    (hG : 𝚺ᴬ₀.DefinableRel G) : PrenexDefinablePred 𝚺 1 (codeBelow a I G) := by
  have := definable_enumCode hG a (I ⨳ a)
  exact (PrenexDefinable.exists_exists_exists_of_sigmaZero (k := 1)
    (R := fun v i z t ↦ enumCode a (I ⨳ a) G i z t ∧ v 0 < z) (by definability)).of_iff
    fun v ↦ Iff.rfl

private lemma prenexDefinablePred_codeAbove {a I : V} {G : V → V → Prop}
    (hG : 𝚺ᴬ₀.DefinableRel G) : PrenexDefinablePred 𝚺 1 (codeAbove a I G) := by
  have := definable_enumCode hG a (I ⨳ a)
  exact (PrenexDefinable.exists_exists_exists_of_sigmaZero (k := 1)
    (R := fun v i z t ↦ I ⨳ a ≤ v 0 ∨
      (enumCode a (I ⨳ a) G i z t ∧ ∃ p ≤ v 0, Exponential ((a - i) * ‖a‖) p ∧ z + p ≤ v 0))
    (by definability)).of_iff fun v ↦ Iff.rfl

private lemma not_codeAbove_of_codeBelow {a I x : V} {G : V → V → Prop}
    (hG : 𝚺ᴬ₀.DefinableRel G) (hfun : ∀ x y y', G x y → G x y' → y = y')
    (hinj : ∀ x x' y, G x y → G x' y → x = x') (hI : ‖I‖ = a + 1)
    (hx : codeBelow a I G x) : ¬codeAbove a I G x := by
  rintro ⟨i', z', t', hor⟩
  obtain ⟨i, z, t, hc, hxz⟩ := hx
  rcases hor with hBx | ⟨hc', p, hpe, hpq, hle⟩
  · exact lt_irrefl z ((hc.2.1.trans_le hBx).trans hxz)
  · rcases le_total i i' with hii | hii
    · obtain ⟨q, hq⟩ := exists_exponential_mul_length (a - i) a
      have hzz' := (enumCode.le_lt_add hG hfun hinj hI hii hc hc' hq).1
      exact absurd hxz (not_lt.mpr (hzz'.trans (le_self_add.trans hle)))
    · have hlt := (enumCode.le_lt_add hG hfun hinj hI hii hc' hc hpq).2
      exact lt_asymm (hlt.trans_le hle) hxz

private def codeCut {a I : V} {G : V → V → Prop} (hnomax : NoMaximalCode a I G) : Cut V where
  carrier := {x | codeBelow a I G x}
  succ_mem := by
    rintro x ⟨i, z, t, hc, hxz⟩
    obtain ⟨i', z', t', hc', hzz'⟩ := hnomax i z t hc
    exact ⟨i', z', t', hc', (succ_le_iff_lt.mpr hxz).trans_lt hzz'⟩
  mem_of_lt := by
    rintro x y hxy ⟨i, z, t, hc, hyz⟩
    exact ⟨i, z, t, hc, hxy.trans hyz⟩

private lemma codeCut_proper {a I : V} {G : V → V → Prop} (hG : 𝚺ᴬ₀.DefinableRel G)
    (hdom : ∀ x y, G x y → x < a) (hfun : ∀ x y y', G x y → G x y' → y = y')
    (hunb : ∀ s, ∃ x y, G x y ∧ s < y) (hI : ‖I‖ = a + 1) (hnomax : NoMaximalCode a I G) :
    (codeCut hnomax).Proper := by
  refine ⟨?_, I ⨳ a, ?_⟩
  · obtain ⟨z₀, -, t₀, h₀⟩ := enumCode.exists_zero hG hdom hfun hunb hI
    obtain ⟨i', z', t', hc', hzz'⟩ := hnomax 0 z₀ t₀ h₀
    exact ⟨i', z', t', hc', (Arithmetic.zero_le z₀).trans_lt hzz'⟩
  · rintro ⟨i, z, t, hc, hBz⟩
    exact lt_irrefl z (hc.2.1.trans hBz)

lemma exists_gap {a I : V} [V↓[ℒₒᵣ] ⊧* 𝗜𝚫 1] {G : V → V → Prop} (hG : 𝚺ᴬ₀.DefinableRel G)
    (hdom : ∀ x y, G x y → x < a) (hfun : ∀ x y y', G x y → G x y' → y = y')
    (hinj : ∀ x x' y, G x y → G x' y → x = x') (hunb : ∀ s, ∃ x y, G x y ∧ s < y)
    (hI : ‖I‖ = a + 1)
    (hnomax : ∀ i z t, enumCode a (I ⨳ a) G i z t →
      ∃ i' z' t', enumCode a (I ⨳ a) G i' z' t' ∧ z < z') :
    ∃ e < I ⨳ a, ∀ i z t, enumCode a (I ⨳ a) G i z t →
      ∀ q, Exponential ((a - i) * ‖a‖) q → z ≤ e ∧ e < z + q := by
  obtain ⟨e, heC, heD⟩ : ∃ e, ¬codeBelow a I G e ∧ ¬codeAbove a I G e := by
    by_contra hall
    push Not at hall
    have hπ : PrenexDefinablePred 𝚺 1 (· ∉ (codeCut hnomax).carrier) :=
      (prenexDefinablePred_codeAbove (a := a) (I := I) hG).of_iff fun v ↦
        ⟨fun hx ↦ hall (v 0) hx, fun hx hxC ↦
          not_codeAbove_of_codeBelow hG hfun hinj hI hxC hx⟩
    exact not_models_IDelta_of_proper_cut _ 1 (codeCut_proper hG hdom hfun hunb hI hnomax)
      (prenexDefinablePred_codeBelow hG) hπ inferInstance
  unfold codeBelow at heC
  unfold codeAbove at heD
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
