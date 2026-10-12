module

public import AlphaCentauri.Model.CodedLimit
public import AlphaCentauri.Model.InjectiveEnumeration
public import AlphaCentauri.Model.ProperCut
public import AlphaCentauri.ToFoundation.PrenexDefinable

/-!
# Collection for $\Delta_0$ formulas from $\Delta_1$ induction

Over a model of $\mathsf{EA}$, $\mathsf{I}\Delta_1$ yields collection for $\Delta_0$ formulas with
parameters.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

noncomputable section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

attribute [local instance] ElementaryArithmetic.models_ISigma0_union_Omega1

lemma enumCode.anti {a B i z t t' : V} {G : V → V → Prop}
    (hfun : ∀ x y y', G x y → G x y' → y = y') (h : enumCode a B G i z t)
    (ht : ∀ j ≤ i, ∀ y, G (entry a z j) y → y ≤ t') : enumCode a B G i z t' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, fun j hj => ?_, fun x hx y hy hG y₀ hy₀ hG₀ => ?_,
    fun j hj y _ y' _ hG hG' => ?_⟩
  · obtain ⟨hja, y, -, hGy⟩ := h4 j hj
    exact ⟨hja, y, ht j hj y hGy, hGy⟩
  · obtain ⟨-, w, hw, hGw⟩ := h4 0 (Arithmetic.zero_le i)
    have hy₀w : y₀ = w := hfun _ _ _ hG₀ hGw
    rw [hy₀w]
    by_cases hyt : y ≤ t
    · exact h5 x hx y hyt hG w hw hGw
    · exact hw.trans (not_le.mp hyt).le
  · obtain ⟨-, w₁, hw₁, hG₁⟩ := h4 j hj.le
    obtain ⟨-, w₂, hw₂, hG₂⟩ := h4 (j + 1) (succ_le_iff_lt.mpr hj)
    have e₁ : y = w₁ := hfun _ _ _ hG hG₁
    have e₂ : y' = w₂ := hfun _ _ _ hG' hG₂
    rw [e₁] at hG
    rw [e₂] at hG'
    obtain ⟨hlt, hmin⟩ := h6 j hj w₁ hw₁ w₂ hw₂ hG hG'
    rw [e₁, e₂]
    refine ⟨hlt, fun x hx w hw hGw hyw => ?_⟩
    by_cases hwt : w ≤ t
    · exact hmin x hx w hwt hGw hyw
    · exact hw₂.trans (not_le.mp hwt).le

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

lemma exists_enumCode_of_not_definable {a I : V} {G : V → V → Prop}
    (hG : 𝚺ᴬ₀.DefinableRel G) (hfun : ∀ x y y', G x y → G x y' → y = y')
    (K : Cut V) (hK : ∀ i, i ∈ K.carrier ↔ ∃ z < I ⨳ a, ∃ t, enumCode a (I ⨳ a) G i z t)
    (hzero : (0 : V) ∈ K.carrier) (hlt : ∀ i ∈ K.carrier, i < a) (T : V) :
    ∃ i z t, enumCode a (I ⨳ a) G i z t ∧ ∃ j ≤ i, ∃ y, G (entry a z j) y ∧ T < y := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ i, i ∈ K.carrier ↔ ∃ z < I ⨳ a, enumCode a (I ⨳ a) G i z T := by
    intro i
    rw [hK i]
    constructor
    · rintro ⟨z, hz, t, h⟩
      exact ⟨z, hz, enumCode.anti hfun h (hcon i z t h)⟩
    · rintro ⟨z, hz, h⟩
      exact ⟨z, hz, T, h⟩
  have hdef : 𝚺ᴬ₀.DefinablePred (· ∈ K.carrier) := by
    have hP : 𝚺ᴬ₀.DefinablePred fun i ↦ ∃ z < I ⨳ a, enumCode a (I ⨳ a) G i z T := by
      have := definable_enumCode hG a (I ⨳ a)
      clear hcon hmem hK hlt hzero
      definability
    exact hP.of_iff fun i ↦ hmem i
  exact Cut.not_proper_of_definable K hdef ⟨hzero, a, fun ha ↦ lt_irrefl a (hlt a ha)⟩

lemma prenexDefinable_compl_of_enumCode {a I c : V} {G : V → V → Prop}
    (hG : 𝚺ᴬ₀.DefinableRel G)
    (hfun : ∀ x y y', G x y → G x y' → y = y') (htot : ∀ x < a, ∃ y, G x y)
    (K : Cut V) (hK : ∀ i, i ∈ K.carrier ↔ ∃ z < I ⨳ a, ∃ t, enumCode a (I ⨳ a) G i z t)
    (hlt : ∀ i ∈ K.carrier, i < a)
    (hD : ∀ T, ∃ i z t, enumCode a (I ⨳ a) G i z t ∧ ∃ j ≤ i, ∃ y, G (entry a z j) y ∧ T < y)
    (hc : ∀ i ∈ K.carrier, ∀ z t, enumCode a (I ⨳ a) G i z t → ∀ j ≤ i, entry a c j = entry a z j) :
    PrenexDefinablePred 𝚺 1 (· ∉ K.carrier) := by
  have hR : 𝚺ᴬ₀.Definable fun v : Fin (1 + 2) → V ↦
      a < v 2 ∨ a ≤ entry a c (v 2) ∨
        ∃ i'' < v 2, (G (entry a c i'') (v 0) ∧ G (entry a c (v 2)) (v 1) ∧ v 1 ≤ v 0) := by
    unfold entry
    definability
  have h := PrenexDefinable.exists_exists_of_sigmaZero
    (R := fun (p : Fin 1 → V) (y'' y' : V) ↦ a < p 0 ∨ a ≤ entry a c (p 0) ∨
      ∃ i'' < p 0, (G (entry a c i'') y'' ∧ G (entry a c (p 0)) y' ∧ y' ≤ y'')) hR
  refine h.of_iff fun v ↦ ?_
  change v 0 ∉ K.carrier ↔ _
  constructor
  · intro hn
    by_cases h1 : a < v 0
    · exact ⟨0, 0, Or.inl h1⟩
    by_cases h2 : a ≤ entry a c (v 0)
    · exact ⟨0, 0, Or.inr (Or.inl h2)⟩
    obtain ⟨y₀, hy₀⟩ := htot _ (not_le.mp h2)
    obtain ⟨i', z, t, hcode, j, hji, y, hGy, hyy⟩ := hD y₀
    have hi'K : i' ∈ K.carrier := (hK i').mpr ⟨z, hcode.2.1, t, hcode⟩
    have hi'lt : i' < v 0 := by
      by_contra hle
      rcases lt_or_eq_of_le (not_lt.mp hle) with h | h
      · exact hn (K.mem_of_lt h hi'K)
      · exact hn (by rw [h]; exact hi'K)
    have hej : entry a c j = entry a z j := hc i' hi'K z t hcode j hji
    refine ⟨y, y₀, Or.inr (Or.inr ⟨j, lt_of_le_of_lt hji hi'lt, ?_, hy₀, hyy.le⟩)⟩
    rw [hej]
    exact hGy
  · rintro ⟨y'', y', h⟩ hmem
    obtain ⟨z, hz, t, hcode⟩ := (hK (v 0)).mp hmem
    have hz' : ∀ j ≤ v 0, entry a c j = entry a z j := hc (v 0) hmem z t hcode
    obtain h | h | ⟨i'', hi'', hG'', hG', hle⟩ := h
    · exact lt_asymm h (hlt _ hmem)
    · rw [hz' (v 0) le_rfl] at h
      exact not_lt.mpr h (hcode.2.2.2.1 (v 0) le_rfl).1
    · rw [hz' i'' hi''.le] at hG''
      rw [hz' (v 0) le_rfl] at hG'
      have hlt' := enumCode.strictMono hG hfun hcode hi'' le_rfl hG'' hG'
      exact not_le.mpr hlt' hle

lemma prenexDefinable_mem_of_enumCode {a I : V} {G : V → V → Prop}
    (hG : 𝚺ᴬ₀.DefinableRel G) (K : Cut V)
    (hK : ∀ i, i ∈ K.carrier ↔ ∃ z < I ⨳ a, ∃ t, enumCode a (I ⨳ a) G i z t) :
    PrenexDefinablePred 𝚺 1 (· ∈ K.carrier) := by
  have hd := definable_enumCode hG a (I ⨳ a)
  have hR : 𝚺ᴬ₀.Definable fun v : Fin (1 + 2) → V ↦
      (fun (p : Fin 1 → V) (z t : V) ↦ enumCode a (I ⨳ a) G (p 0) z t)
        (fun i ↦ v i.succ.succ) (v 0) (v 1) :=
    (hd.retraction ![2, 0, 1]).of_iff (by intro v; simp)
  have h := PrenexDefinable.exists_exists_of_sigmaZero
    (R := fun (p : Fin 1 → V) (z t : V) ↦ enumCode a (I ⨳ a) G (p 0) z t) hR
  exact h.of_iff fun v ↦ by
    change v 0 ∈ K.carrier ↔ _
    rw [hK]
    exact ⟨fun ⟨z, hz, t, h⟩ ↦ ⟨z, t, h⟩, fun ⟨z, t, h⟩ ↦ ⟨z, h.2.1, t, h⟩⟩

/-- An unbounded injection on `[0, a)` whose graph is `Δ₀`-definable, `I` of length `a + 1`:
$\mathsf{I}\Delta_1$ gives collection for `Δ₀` formulas with parameters. -/
theorem collection_of_models_IDelta_one [V↓[ℒₒᵣ] ⊧* 𝗜𝚫 1]
    {m : ℕ} {θ : ArithmeticSemisentence (m + 2)} (hθ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 θ)
    (e : Fin m → V) (a : V) (hex : ∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) :
    ∃ w, ∀ x < a, ∃ u < w, V ⊧/(u :> x :> e) θ := by
  by_contra hne
  push Not at hne
  have hnb : ∀ w, ∃ x < a, ∀ u ≤ w, ¬V ⊧/(u :> x :> e) θ := fun w ↦ by
    obtain ⟨x, hx, hu⟩ := hne (w + 1)
    exact ⟨x, hx, fun u hu' ↦ hu u (lt_of_le_of_lt hu' (lt_add_one w))⟩
  obtain ⟨f, hinj, hunb, hgraph⟩ := exists_injective_unbounded_of_not_collection hθ e a hex hnb
  obtain ⟨I, hIe⟩ := ElementaryArithmetic.exponential_total a
  have hIlen : ‖I‖ = a + 1 := hIe.length_eq
  have hfun : ∀ x y y' : V, (x < a ∧ f x = y) → (x < a ∧ f x = y') → y = y' :=
    fun x y y' h h' ↦ h.2.symm.trans h'.2
  have htot : ∀ x < a, ∃ y : V, x < a ∧ f x = y := fun x hx ↦ ⟨f x, hx, rfl⟩
  have hK : ∀ i, i ∈ (enumerationCut a I f hIlen hunb hgraph).carrier ↔
      ∃ z < I ⨳ a, ∃ t, enumCode a (I ⨳ a) (fun x y ↦ x < a ∧ f x = y) i z t :=
    fun i ↦ Iff.rfl
  have hzero := zero_mem_enumerationCut a I f hIlen hunb hgraph
  have hlt : ∀ i ∈ (enumerationCut a I f hIlen hunb hgraph).carrier, i < a :=
    fun i hi ↦ lt_of_mem_enumerationCut a I f hIlen hunb hgraph hi
  have hD : ∀ T, ∃ i z t, enumCode a (I ⨳ a) (fun x y ↦ x < a ∧ f x = y) i z t ∧
      ∃ j ≤ i, ∃ y, (fun x y ↦ x < a ∧ f x = y) (entry a z j) y ∧ T < y :=
    fun T ↦ exists_enumCode_of_not_definable hgraph hfun _ hK hzero hlt T
  obtain ⟨c, -, hc⟩ := exists_coded_limit hIlen hinj hunb hgraph
  have hπ := prenexDefinable_compl_of_enumCode hgraph hfun htot _ hK hlt hD hc
  have hσ := prenexDefinable_mem_of_enumCode hgraph _ hK
  exact not_models_IDelta_of_proper_cut _ 1 ⟨hzero, a, fun ha ↦ lt_irrefl a (hlt a ha)⟩ hσ hπ
    inferInstance

end

end FFL.FirstOrder.Arithmetic
