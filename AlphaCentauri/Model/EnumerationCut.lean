module

public import AlphaCentauri.ToFoundation.CodedPigeonhole
public import AlphaCentauri.Model.Cut
public import Foundation.FirstOrder.Arithmetic.Definability.Definable

/-!
# The cut of an enumeration of the range of an injection

Over a model of $\mathsf{EA}$, an unbounded injection on $[0, a)$ enumerates its range in increasing
order by a block-coded sequence; the codes form a $\Sigma_1$ cut of $[0, a)$.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

noncomputable section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

attribute [local instance] ElementaryArithmetic.models_ISigma0_union_Omega1

/-- The `j`-th entry of a code `z` of blocks of width `‖a‖`, counted from the top block.
- [Tha05, Lemmas 4–7] -/
def entry (a z j : V) : V := Nuon.ext a z (a - j)

/-- The bounded form of the code condition for the enumeration of the graph `G` of a function
on `[0, a)`: `i` is the length of the code `z`, and `t` bounds the values of the entries.
- [Tha05, Lemmas 4–7] -/
def enumCode (a B : V) (G : V → V → Prop) (i z t : V) : Prop :=
  i ≤ a ∧ z < B ∧
  (∀ j ≤ a, i < j → entry a z j = 0) ∧
  (∀ j ≤ i, entry a z j < a ∧ ∃ y ≤ t, G (entry a z j) y) ∧
  (∀ x < a, ∀ y ≤ t, G x y → ∀ y₀ ≤ t, G (entry a z 0) y₀ → y₀ ≤ y) ∧
  (∀ j < i, ∀ y ≤ t, ∀ y' ≤ t, G (entry a z j) y → G (entry a z (j + 1)) y' →
    y < y' ∧ ∀ x < a, ∀ w ≤ t, G x w → y < w → y' ≤ w)

lemma definable_enumCode {G : V → V → Prop} (hG : 𝚺ᴬ₀.DefinableRel G) (a B : V) :
    𝚺ᴬ₀.DefinableRel₃ (enumCode a B G) := by
  unfold enumCode entry
  definability

lemma entry_zero_left (a j : V) : entry a 0 j = 0 := by
  simp [entry]

lemma ext_eq_entry {a z j : V} (hj : j ≤ a) : Nuon.ext a z j = entry a z (a - j) := by
  unfold entry
  rw [tsub_tsub_cancel_of_le hj]

lemma sub_inj_of_le {a j k : V} (hj : j ≤ a) (hk : k ≤ a) (h : a - j = a - k) : j = k := by
  rw [← tsub_tsub_cancel_of_le hj, h, tsub_tsub_cancel_of_le hk]

lemma exists_update_entry {a I z k v : V} (hz : z < I ⨳ a) (hI : ‖I‖ = a + 1) (hk : k ≤ a)
    (hv : v < a) :
    ∃ z' < I ⨳ a, entry a z' k = v ∧ ∀ j ≤ a, j ≠ k → entry a z' j = entry a z j := by
  have hkI : a - k < ‖I‖ := by
    rw [hI]
    exact lt_of_le_of_lt (sub_le_self a k) (lt_add_one a)
  have hv' : v < a ⨳ 1 := lt_of_lt_of_le hv (lt_smash_one_right a).le
  obtain ⟨z', hz', h₁, h₂⟩ := exists_update hz hkI hv'
  refine ⟨z', hz', h₁, fun j hj hjk => ?_⟩
  unfold entry
  apply h₂ (a - j)
  · rw [hI]
    exact (sub_le_self a j).trans le_self_add
  · intro hne
    exact hjk (sub_inj_of_le hj hk hne)

lemma enumCode.mono {a B i z t t' : V} {G : V → V → Prop}
    (hfun : ∀ x y y', G x y → G x y' → y = y') (h : enumCode a B G i z t) (ht : t ≤ t') :
    enumCode a B G i z t' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hle : ∀ j ≤ i, ∀ y, G (entry a z j) y → y ≤ t := by
    intro j hj y hy
    obtain ⟨-, y', hy', hG'⟩ := h4 j hj
    rw [hfun _ _ _ hy hG']
    exact hy'
  refine ⟨h1, h2, h3, fun j hj => ?_, fun x hx y hy hG y₀ hy₀ hG₀ => ?_,
    fun j hj y hy y' hy' hG hG' => ?_⟩
  · obtain ⟨hja, y, hy, hG⟩ := h4 j hj
    exact ⟨hja, y, hy.trans ht, hG⟩
  · by_cases hyt : y ≤ t
    · exact h5 x hx y hyt hG y₀ (hle 0 (Arithmetic.zero_le i) y₀ hG₀) hG₀
    · exact (hle 0 (Arithmetic.zero_le i) y₀ hG₀).trans (not_le.mp hyt).le
  · have hyt := hle j hj.le y hG
    have hy't := hle (j + 1) (succ_le_iff_lt.mpr hj) y' hG'
    obtain ⟨hlt, hmin⟩ := h6 j hj y hyt y' hy't hG hG'
    refine ⟨hlt, fun x hx w hw hGw hyw => ?_⟩
    by_cases hwt : w ≤ t
    · exact hmin x hx w hwt hGw hyw
    · exact hy't.trans (not_le.mp hwt).le

lemma enumCode.exists_common_value {a I i i' z z' t t' : V} {G : V → V → Prop}
    (hG : 𝚺ᴬ₀.DefinableRel G) (hfun : ∀ x y y', G x y → G x y' → y = y') (hii' : i ≤ i')
    (h : enumCode a (I ⨳ a) G i z t) (h' : enumCode a (I ⨳ a) G i' z' t') :
    ∀ j ≤ i, ∃ y ≤ t + t', G (entry a z j) y ∧ G (entry a z' j) y := by
  have h₁ := h.mono hfun (le_self_add (a := t) (b := t'))
  have h₂ := h'.mono hfun (le_add_self (a := t') (b := t))
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

lemma enumCode.unique {a I i z z' t t' : V} {G : V → V → Prop}
    (hG : 𝚺ᴬ₀.DefinableRel G)
    (hfun : ∀ x y y', G x y → G x y' → y = y')
    (hinj : ∀ x x' y, G x y → G x' y → x = x') (hI : ‖I‖ = a + 1)
    (hz : z < I ⨳ a) (hz' : z' < I ⨳ a)
    (h : enumCode a (I ⨳ a) G i z t) (h' : enumCode a (I ⨳ a) G i z' t') : z = z' := by
  have key := enumCode.exists_common_value hG hfun le_rfl h h'
  have hentry : ∀ k ≤ a, entry a z k = entry a z' k := by
    intro k hk
    by_cases hki : k ≤ i
    · obtain ⟨y, -, hG₁, hG₂⟩ := key k hki
      exact hinj _ _ y hG₁ hG₂
    · have hik : i < k := not_le.mp hki
      rw [h.2.2.1 k hk hik, h'.2.2.1 k hk hik]
  obtain hb : Exponential ((a + 1) * ‖a‖) (I ⨳ a) := by
    rw [← hI]
    exact exponential_smash I a
  refine Nuon.ext_ext (i := a + 1) hb hz hz' fun j hj => ?_
  have hja : j ≤ a := lt_succ_iff_le.mp hj
  rw [ext_eq_entry hja, ext_eq_entry hja, hentry (a - j) (sub_le_self a j)]

lemma enumCode.strictMono {a B i z t : V} {G : V → V → Prop} (hG : 𝚺ᴬ₀.DefinableRel G)
    (hfun : ∀ x y y', G x y → G x y' → y = y') (h : enumCode a B G i z t)
    {j k : V} (hjk : j < k) (hki : k ≤ i) {y y' : V} (hy : G (entry a z j) y)
    (hy' : G (entry a z k) y') : y < y' := by
  obtain ⟨-, -, -, h4, -, h6⟩ := h
  have hbd : ∀ j ≤ i, ∀ y, G (entry a z j) y → y ≤ t := by
    intro j hj y hy
    obtain ⟨-, y', hy', hG'⟩ := h4 j hj
    rw [hfun _ _ _ hy hG']
    exact hy'
  have key : ∀ k, k ≤ i → ∀ j < k, ∀ y ≤ t, ∀ y' ≤ t,
      G (entry a z j) y → G (entry a z k) y' → y < y' := by
    intro k
    induction k using ISigma0.succ_induction
    · clear h4 h6 hbd hy hy' hfun
      unfold entry
      definability
    case zero => intro _ j hj; exact absurd hj (by simp)
    case succ k IH =>
      intro hk j hj y hyt y' hy't hGj hGk
      have hkz : k ≤ i := le_trans le_self_add hk
      have hki : k < i := (lt_add_one k).trans_le hk
      rcases lt_or_eq_of_le (lt_succ_iff_le.mp hj) with hjk | rfl
      · obtain ⟨-, w, hw, hGw⟩ := h4 k hkz
        exact (IH hkz j hjk y hyt w hw hGj hGw).trans (h6 k hki w hw y' hy't hGw hGk).1
      · exact (h6 j hki y hyt y' hy't hGj hGk).1
  exact key k hki j hjk y (hbd j (hjk.le.trans hki) y hy) y' (hbd k hki y' hy') hy hy'

lemma enumCode.entry_ne {a B i z t j k : V} {G : V → V → Prop} (hG : 𝚺ᴬ₀.DefinableRel G)
    (hfun : ∀ x y y', G x y → G x y' → y = y') (h : enumCode a B G i z t) (hjk : j < k)
    (hki : k ≤ i) : entry a z j ≠ entry a z k := by
  intro heq
  obtain ⟨-, y, -, hy⟩ := h.2.2.2.1 j (hjk.le.trans hki)
  obtain ⟨-, y', -, hy'⟩ := h.2.2.2.1 k hki
  exact (enumCode.strictMono hG hfun h hjk hki hy hy').ne (hfun _ _ _ (heq ▸ hy) hy')

lemma enumCode.lt_of_enumCode {a I i z t : V} {G : V → V → Prop}
    (hG : 𝚺ᴬ₀.DefinableRel G)
    (hfun : ∀ x y y', G x y → G x y' → y = y') (h : enumCode a (I ⨳ a) G i z t) : i < a := by
  by_contra hlt
  have hia : i = a := le_antisymm h.1 (not_lt.mp hlt)
  have hinj : ∀ k ≤ a, ∀ k' ≤ a, entry a z k = entry a z k' → k = k' := by
    intro k hk k' hk' heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt' | hgt'
    · exact enumCode.entry_ne hG hfun h hlt' (hia ▸ hk') heq
    · exact enumCode.entry_ne hG hfun h hgt' (hia ▸ hk) heq.symm
  have hlt_ext : ∀ j ≤ a, Nuon.ext a z j < a := by
    intro j hj
    rw [ext_eq_entry hj]
    exact (h.2.2.2.1 (a - j) (hia ▸ sub_le_self a j)).1
  have hinj_ext : ∀ j ≤ a, ∀ j' ≤ a, Nuon.ext a z j = Nuon.ext a z j' → j = j' := by
    intro j hj j' hj' heq
    rw [ext_eq_entry hj, ext_eq_entry hj'] at heq
    exact sub_inj_of_le hj hj' (hinj _ (sub_le_self a j) _ (sub_le_self a j') heq)
  exact no_coded_injection a a z le_rfl hlt_ext hinj_ext

lemma enumCode.exists_zero {a I : V} {G : V → V → Prop}
    (hG : 𝚺ᴬ₀.DefinableRel G)
    (hdom : ∀ x y, G x y → x < a) (hfun : ∀ x y y', G x y → G x y' → y = y')
    (hunb : ∀ s, ∃ x y, G x y ∧ s < y) (hI : ‖I‖ = a + 1) :
    ∃ z < I ⨳ a, ∃ t, enumCode a (I ⨳ a) G 0 z t := by
  obtain ⟨x₀, y₀, hGx₀, -⟩ := hunb 0
  have hP : 𝚺ᴬ₀.DefinablePred fun s ↦ ∃ x < a, G x s := by
    definability
  obtain ⟨s₀, ⟨m, hm, hGm⟩, hmin⟩ :=
    ISigma0.least_number hP (x := y₀) ⟨x₀, hdom _ _ hGx₀, hGx₀⟩
  obtain ⟨z, hz, e₁, e₂⟩ :=
    exists_update_entry (z := 0) (k := 0) (v := m) (smash_pos I a) hI (Arithmetic.zero_le a) hm
  refine ⟨z, hz, s₀, Arithmetic.zero_le a, hz, ?_, ?_, ?_, ?_⟩
  · intro j hj hj0
    rw [e₂ j hj (Ne.symm (ne_of_lt hj0)), entry_zero_left]
  · intro j hj
    obtain rfl : j = 0 := le_antisymm hj (Arithmetic.zero_le j)
    rw [e₁]
    exact ⟨hm, s₀, le_rfl, hGm⟩
  · intro x hx y hy hG y₀ hy₀ hG₀
    rw [e₁] at hG₀
    have hy₀s : y₀ = s₀ := hfun _ _ _ hG₀ hGm
    rw [hy₀s]
    by_contra hlt
    exact hmin y (not_le.mp hlt) ⟨x, hx, hG⟩
  · intro j hj
    exact absurd hj (by simp)

lemma enumCode.exists_pred {a I i z t : V} {G : V → V → Prop}
    (hI : ‖I‖ = a + 1) (h : enumCode a (I ⨳ a) G (i + 1) z t) :
    ∃ z' < I ⨳ a, enumCode a (I ⨳ a) G i z' t := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hi1 : i + 1 ≤ a := h1
  obtain ⟨z', hz', e₁, e₂⟩ :=
    exists_update_entry (k := i + 1) (v := 0) h2 hI hi1 (lt_of_lt_of_le (by simp) hi1)
  have hij : ∀ j ≤ i, entry a z' j = entry a z j := fun j hj =>
    e₂ j (hj.trans (le_trans le_self_add hi1)) (ne_of_lt (lt_of_le_of_lt hj (lt_add_one i)))
  refine ⟨z', hz', (le_self_add).trans h1, hz', ?_, ?_, ?_, ?_⟩
  · intro j hj hij'
    by_cases hj1 : j = i + 1
    · rw [hj1]
      exact e₁
    · rw [e₂ j hj hj1]
      exact h3 j hj (lt_of_le_of_ne (succ_le_iff_lt.mpr hij') (Ne.symm hj1))
  · intro j hj
    rw [hij j hj]
    exact h4 j (hj.trans le_self_add)
  · have hne : 0 ≠ i + 1 := ne_of_lt (lt_of_le_of_lt (Arithmetic.zero_le i) (lt_add_one i))
    rw [e₂ 0 (Arithmetic.zero_le a) hne]
    exact h5
  · intro j hj
    rw [hij j (le_of_lt hj), hij (j + 1) (succ_le_iff_lt.mpr hj)]
    exact h6 j (hj.trans (lt_add_one i))

lemma enumCode.exists_succ {a I i z t : V} {G : V → V → Prop}
    (hG : 𝚺ᴬ₀.DefinableRel G)
    (hdom : ∀ x y, G x y → x < a) (hfun : ∀ x y y', G x y → G x y' → y = y')
    (hunb : ∀ s, ∃ x y, G x y ∧ s < y) (hI : ‖I‖ = a + 1)
    (h : enumCode a (I ⨳ a) G i z t) :
    ∃ z' < I ⨳ a, ∃ t', enumCode a (I ⨳ a) G (i + 1) z' t' := by
  have hia : i < a := enumCode.lt_of_enumCode hG hfun h
  obtain ⟨-, c, hc, hGc⟩ := h.2.2.2.1 i le_rfl
  obtain ⟨x₁, y₁, hGx₁, hcy₁⟩ := hunb c
  have hP : 𝚺ᴬ₀.DefinablePred fun s ↦ ∃ x < a, G x s ∧ c < s := by
    definability
  obtain ⟨s₀, ⟨m, hm, hGm, hcs⟩, hmin⟩ :=
    ISigma0.least_number hP (x := y₁) ⟨x₁, hdom _ _ hGx₁, hGx₁, hcy₁⟩
  obtain ⟨z', hz', e₁, e₂⟩ := exists_update_entry h.2.1 hI (succ_le_iff_lt.mpr hia) hm
  have h' := h.mono hfun (le_self_add (a := t) (b := s₀))
  refine ⟨z', hz', t + s₀, succ_le_iff_lt.mpr hia, hz', ?_, ?_, ?_, ?_⟩
  · intro j hj hij
    rw [e₂ j hj hij.ne']
    exact h.2.2.1 j hj (lt_trans (lt_add_one i) hij)
  · intro j hj
    by_cases hj1 : j = i + 1
    · rw [hj1, e₁]
      exact ⟨hm, s₀, le_add_self (a := s₀) (b := t), hGm⟩
    · have hji : j ≤ i := lt_succ_iff_le.mp (lt_of_le_of_ne hj hj1)
      rw [e₂ j (hji.trans (le_trans le_self_add (succ_le_iff_lt.mpr hia))) hj1]
      obtain ⟨hja, y, hy, hGy⟩ := h.2.2.2.1 j hji
      exact ⟨hja, y, hy.trans (le_self_add (a := t) (b := s₀)), hGy⟩
  · intro x hx y hy hG y₀ hy₀ hG₀
    have hne : 0 ≠ i + 1 := ne_of_lt (lt_of_le_of_lt (Arithmetic.zero_le i) (lt_add_one i))
    rw [e₂ 0 (Arithmetic.zero_le a) hne] at hG₀
    exact h'.2.2.2.2.1 x hx y hy hG y₀ hy₀ hG₀
  · intro j hj y hy y' hy' hGj hGj'
    by_cases hji : j < i
    · have hja : j ≤ a := hji.le.trans hia.le
      have hj1a : j + 1 ≤ a := (succ_le_iff_lt.mpr hji).trans hia.le
      rw [e₂ j hja (lt_trans hji (lt_add_one i)).ne] at hGj
      rw [e₂ (j + 1) hj1a (lt_of_le_of_lt (succ_le_iff_lt.mpr hji) (lt_add_one i)).ne] at hGj'
      exact h'.2.2.2.2.2 j hji y hy y' hy' hGj hGj'
    · have hjeq : j = i := le_antisymm (lt_succ_iff_le.mp hj) (not_lt.mp hji)
      rw [hjeq] at hGj hGj'
      rw [e₂ i (le_of_lt hia) (lt_add_one i).ne] at hGj
      rw [e₁] at hGj'
      have hyc : y = c := hfun _ _ _ hGj hGc
      have hys : y' = s₀ := hfun _ _ _ hGj' hGm
      rw [hyc, hys]
      exact ⟨hcs, fun x hx w _ hGw hcw => not_lt.mp fun hlt => hmin w hlt ⟨x, hx, hGw, hcw⟩⟩

lemma enumCode.exists_le {a I b z t B : V} {G : V → V → Prop}
    (hG : 𝚺ᴬ₀.DefinableRel G) (hI : ‖I‖ = a + 1)
    (hB : B = I ⨳ a) (h : enumCode a B G b z t) :
    ∀ c ≤ b, ∃ z' < B, enumCode a B G c z' t := by
  have key : ∀ d, d ≤ b → ∃ z' < B, enumCode a B G (b - d) z' t := by
    intro d
    induction d using ISigma0.succ_induction
    · have hdef := definable_enumCode hG a B
      definability
    case zero => intro _; rw [tsub_zero]; exact ⟨z, h.2.1, h⟩
    case succ d IH =>
      intro hd
      obtain ⟨z₁, -, h₁⟩ := IH (le_trans le_self_add hd)
      have e : b - d = b - (d + 1) + 1 :=
        sub_remove_left (by rw [add_assoc, add_comm 1 d, sub_add_self_of_le hd])
      rw [e, hB] at h₁
      rw [hB]
      exact enumCode.exists_pred hI h₁
  intro c hc
  obtain ⟨z', hz', h'⟩ := key (b - c) (sub_le_self b c)
  rw [tsub_tsub_cancel_of_le hc] at h'
  exact ⟨z', hz', h'⟩

variable (a I : V)

omit [V↓[ℒₒᵣ] ⊧* 𝗘𝗔] in
lemma exists_graph_unbounded {f : V → V} (hunb : ∀ s, ∃ x < a, s < f x) :
    ∀ s, ∃ x y, (x < a ∧ f x = y) ∧ s < y := by
  intro s
  obtain ⟨x, hx, hs⟩ := hunb s
  exact ⟨x, f x, ⟨hx, rfl⟩, hs⟩

/-- The `Σ₁` cut of `[0, a)` given by the enumeration of the range of a function `f` with unbounded
values below `a` whose graph on `[0, a)` is `Δ₀`-definable.
- [Tha05, Lemmas 4–7] -/
def enumerationCut (f : V → V) (hI : ‖I‖ = a + 1) (hunb : ∀ s, ∃ x < a, s < f x)
    (hgraph : 𝚺ᴬ₀.DefinableRel fun x y ↦ x < a ∧ f x = y) : Cut V where
  carrier := {i | ∃ z < I ⨳ a, ∃ t, enumCode a (I ⨳ a) (fun x y ↦ x < a ∧ f x = y) i z t}
  succ_mem := by
    rintro i ⟨z, hz, t, h⟩
    obtain ⟨z', hz', t', h'⟩ := enumCode.exists_succ hgraph (fun x y h ↦ h.1)
      (fun x y y' h h' ↦ h.2.symm.trans h'.2) (exists_graph_unbounded a hunb) hI h
    exact ⟨z', hz', t', h'⟩
  mem_of_lt := by
    intro c b hcb hb
    obtain ⟨z, hz, t, h⟩ := hb
    obtain ⟨z', hz', h'⟩ := enumCode.exists_le hgraph hI rfl h c hcb.le
    exact ⟨z', hz', t, h'⟩

lemma zero_mem_enumerationCut (f : V → V) (hI : ‖I‖ = a + 1) (hunb : ∀ s, ∃ x < a, s < f x)
    (hgraph : 𝚺ᴬ₀.DefinableRel fun x y ↦ x < a ∧ f x = y) :
    (0 : V) ∈ (enumerationCut a I f hI hunb hgraph).carrier := by
  obtain ⟨z, hz, t, h⟩ := enumCode.exists_zero hgraph (fun x y h ↦ h.1)
    (fun x y y' h h' ↦ h.2.symm.trans h'.2) (exists_graph_unbounded a hunb) hI
  exact ⟨z, hz, t, h⟩

lemma lt_of_mem_enumerationCut (f : V → V) (hI : ‖I‖ = a + 1) (hunb : ∀ s, ∃ x < a, s < f x)
    (hgraph : 𝚺ᴬ₀.DefinableRel fun x y ↦ x < a ∧ f x = y) {i : V}
    (hi : i ∈ (enumerationCut a I f hI hunb hgraph).carrier) : i < a := by
  obtain ⟨z, hz, t, h⟩ := hi
  exact enumCode.lt_of_enumCode hgraph (fun x y y' h h' ↦ h.2.symm.trans h'.2) h

end

end FFL.FirstOrder.Arithmetic
