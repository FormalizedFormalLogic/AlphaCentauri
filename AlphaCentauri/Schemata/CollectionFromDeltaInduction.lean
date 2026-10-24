module

public import AlphaCentauri.Model.CodedLimit
public import AlphaCentauri.Model.InjectiveEnumeration
public import AlphaCentauri.Model.ProperCut
public import AlphaCentauri.ToFoundation.PrenexDefinable

/-!
# Collection for $\Delta_0$ formulas from $\Delta_1$ induction

Over a model of $\mathsf{EA}$, $\mathsf{I}\Delta_1$ yields collection for $\Delta_0$-definable
relations, and hence the collection scheme $\mathsf{B}\Sigma_1$.
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

private def LimitFails (a c : V) (G : V → V → Prop) (p y'' y' : V) : Prop :=
  a < p ∨ a ≤ entry a c p ∨
    ∃ i'' < p, G (entry a c i'') y'' ∧ G (entry a c p) y' ∧ y' ≤ y''

private lemma exists_limitFails_of_not_mem {a I c p : V} {G : V → V → Prop}
    (htot : ∀ x < a, ∃ y, G x y) (K : Cut V)
    (hK : ∀ i, i ∈ K.carrier ↔ ∃ z < I ⨳ a, ∃ t, enumCode a (I ⨳ a) G i z t)
    (hD : ∀ T, ∃ i z t, enumCode a (I ⨳ a) G i z t ∧ ∃ j ≤ i, ∃ y, G (entry a z j) y ∧ T < y)
    (hc : ∀ i ∈ K.carrier, ∀ z t, enumCode a (I ⨳ a) G i z t → ∀ j ≤ i, entry a c j = entry a z j)
    (hn : p ∉ K.carrier) : ∃ y'' y', LimitFails a c G p y'' y' := by
  by_cases h₁ : a < p
  · exact ⟨0, 0, Or.inl h₁⟩
  by_cases h₂ : a ≤ entry a c p
  · exact ⟨0, 0, Or.inr (Or.inl h₂)⟩
  obtain ⟨y₀, hy₀⟩ := htot _ (not_le.mp h₂)
  obtain ⟨i', z, t, hcode, j, hji, y, hGy, hyy⟩ := hD y₀
  have hi'K : i' ∈ K.carrier := (hK i').mpr ⟨z, hcode.2.1, t, hcode⟩
  have hi'lt : i' < p := by
    by_contra hle
    rcases lt_or_eq_of_le (not_lt.mp hle) with h | h
    · exact hn (K.mem_of_lt h hi'K)
    · exact hn (by rw [h]; exact hi'K)
  refine ⟨y, y₀, Or.inr (Or.inr ⟨j, lt_of_le_of_lt hji hi'lt, ?_, hy₀, hyy.le⟩)⟩
  rw [hc i' hi'K z t hcode j hji]
  exact hGy

private lemma not_mem_of_limitFails {a I c p y'' y' : V} {G : V → V → Prop}
    (hG : 𝚺ᴬ₀.DefinableRel G) (hfun : ∀ x y y', G x y → G x y' → y = y') (K : Cut V)
    (hK : ∀ i, i ∈ K.carrier ↔ ∃ z < I ⨳ a, ∃ t, enumCode a (I ⨳ a) G i z t)
    (hlt : ∀ i ∈ K.carrier, i < a)
    (hc : ∀ i ∈ K.carrier, ∀ z t, enumCode a (I ⨳ a) G i z t → ∀ j ≤ i, entry a c j = entry a z j)
    (h : LimitFails a c G p y'' y') : p ∉ K.carrier := by
  intro hmem
  obtain ⟨z, hz, t, hcode⟩ := (hK p).mp hmem
  have hz' : ∀ j ≤ p, entry a c j = entry a z j := hc p hmem z t hcode
  obtain h | h | ⟨i'', hi'', hG'', hG', hle⟩ := h
  · exact lt_asymm h (hlt _ hmem)
  · rw [hz' p le_rfl] at h
    exact not_lt.mpr h (hcode.2.2.2.1 p le_rfl).1
  · rw [hz' i'' hi''.le] at hG''
    rw [hz' p le_rfl] at hG'
    exact not_le.mpr (enumCode.strictMono hG hfun hcode hi'' le_rfl hG'' hG') hle

lemma prenexDefinable_compl_of_enumCode {a I c : V} {G : V → V → Prop}
    (hG : 𝚺ᴬ₀.DefinableRel G)
    (hfun : ∀ x y y', G x y → G x y' → y = y') (htot : ∀ x < a, ∃ y, G x y)
    (K : Cut V) (hK : ∀ i, i ∈ K.carrier ↔ ∃ z < I ⨳ a, ∃ t, enumCode a (I ⨳ a) G i z t)
    (hlt : ∀ i ∈ K.carrier, i < a)
    (hD : ∀ T, ∃ i z t, enumCode a (I ⨳ a) G i z t ∧ ∃ j ≤ i, ∃ y, G (entry a z j) y ∧ T < y)
    (hc : ∀ i ∈ K.carrier, ∀ z t, enumCode a (I ⨳ a) G i z t → ∀ j ≤ i, entry a c j = entry a z j) :
    PrenexDefinablePred 𝚺 1 (· ∉ K.carrier) := by
  have hR : 𝚺ᴬ₀.Definable fun v : Fin (1 + 2) → V ↦ LimitFails a c G (v 2) (v 0) (v 1) := by
    unfold LimitFails entry
    definability
  refine (PrenexDefinable.exists_exists_of_sigmaZero
    (R := fun (p : Fin 1 → V) y'' y' ↦ LimitFails a c G (p 0) y'' y') hR).of_iff fun v ↦ ?_
  exact ⟨exists_limitFails_of_not_mem htot K hK hD hc, fun ⟨_, _, h⟩ ↦
    not_mem_of_limitFails hG hfun K hK hlt hc h⟩

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

/-- If a $\Delta_0$-definable relation `Q` has a witness `u` for every `x < a`, then the witnesses
can be bounded uniformly by some `w`.
- [Sla04, Theorem 2.1]
- [Tha05, Theorem 2] -/
theorem collection_of_models_IDelta_one [V↓[ℒₒᵣ] ⊧* 𝗜𝚫 1]
    {Q : V → V → Prop} (hQ : 𝚺ᴬ₀.DefinableRel Q) (a : V) (hex : ∀ x < a, ∃ u, Q u x) :
    ∃ w, ∀ x < a, ∃ u < w, Q u x := by
  by_contra hne
  push Not at hne
  have hnb : ∀ w, ∃ x < a, ∀ u ≤ w, ¬Q u x := fun w ↦ by
    obtain ⟨x, hx, hu⟩ := hne (w + 1)
    exact ⟨x, hx, fun u hu' ↦ hu u (lt_of_le_of_lt hu' (lt_add_one w))⟩
  obtain ⟨f, hinj, hunb, hgraph⟩ := exists_injective_unbounded_of_not_collection hQ a hex hnb
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

/-- The pairing of a witness `u` with a value `y`, relating a bound on a single code to the
pair of its components. -/
lemma definableRel_exists_pair {Q : V → V → V → Prop} (hQ : 𝚺ᴬ₀.DefinableRel₃ Q) :
    𝚺ᴬ₀.DefinableRel fun p x : V ↦ ∃ y ≤ p, ∃ u ≤ p, p = ⟪y, u⟫ ∧ Q u x y := by
  have hpair : 𝚺ᴬ₀.DefinableRel₃ fun y u p : V ↦ p = ⟪y, u⟫ := by definability
  definability

/-- Collection for a $\Delta_0$-definable three-place relation whose witnesses are pairs. -/
theorem collection_of_exists_pair [V↓[ℒₒᵣ] ⊧* 𝗜𝚫 1] {Q : V → V → V → Prop}
    (hQ : 𝚺ᴬ₀.DefinableRel₃ Q) (a : V) (h : ∀ x < a, ∃ y u, Q u x y) :
    ∃ b, ∀ x < a, ∃ y < b, ∃ u, Q u x y := by
  obtain ⟨w, hw⟩ := collection_of_models_IDelta_one (definableRel_exists_pair hQ) a
    (fun x hx ↦ by
      obtain ⟨y, u, hq⟩ := h x hx
      exact ⟨⟪y, u⟫, y, le_pair_left y u, u, le_pair_right y u, rfl, hq⟩)
  refine ⟨w, fun x hx ↦ ?_⟩
  obtain ⟨p, hp, y, hy, u, -, -, hq⟩ := hw x hx
  exact ⟨y, lt_of_le_of_lt hy hp, u, hq⟩

/-- Collection for the prenex $\Sigma_1$ formulas, as a scheme over `V`. -/
lemma models_collection_prenex_sigmaOne [V↓[ℒₒᵣ] ⊧* 𝗜𝚫 1] :
    V↓[ℒₒᵣ] ⊧* CollectionScheme (ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 1) := by
  apply Semantics.ModelsSet.setOf_iff.mpr
  rintro _ ⟨φ, hφ, rfl⟩
  suffices ∀ e : ℕ → V, ∀ a : V, (∀ x < a, ∃ y, φ.Eval ![x, y] e) →
      ∃ b, ∀ x < a, ∃ y < b, φ.Eval ![x, y] e by
    simpa [models_iff, Semiformula.eval_univCl, collectionAxiom, Semiformula.eval_ballLT,
      Semiformula.eval_bexsLT, Semiformula.eval_substs] using this
  intro e a h
  obtain ⟨ψ, hψ, rfl⟩ := Bounding.PrenexHierarchy.sigma_succ_iff.mp hφ
  have hψ₀ := Bounding.PrenexHierarchy.zero_iff.mp hψ
  have hdef : 𝚺ᴬ₀.DefinableRel₃ fun u x y : V ↦ ψ.Eval ![u, x, y] e := by
    refine (Bounding.definable_of_hierarchy hψ₀ e).of_iff fun v ↦ ?_
    change ψ.Eval ![v 0, v 1, v 2] e ↔ ψ.Eval v e
    rw [← Matrix.fun_eq_vec_three v]
  have hEq : ∀ x y : V, (∃¹ψ).Eval ![x, y] e ↔ ∃ u, ψ.Eval ![u, x, y] e := by
    intro x y
    simp
  obtain ⟨w, hw⟩ := collection_of_exists_pair hdef a fun x hx ↦ by
    obtain ⟨y, hy⟩ := h x hx
    obtain ⟨u, hu⟩ := (hEq x y).mp hy
    exact ⟨y, u, hu⟩
  exact ⟨w, fun x hx ↦ by
    obtain ⟨y, hy, u, hu⟩ := hw x hx
    exact ⟨y, hy, (hEq x y).mpr ⟨u, hu⟩⟩⟩

/-- The collection scheme `𝗕𝚺 1`, over a model of `𝗘𝗔` and `𝗜𝚫 1`. -/
lemma models_BSigma_one [V↓[ℒₒᵣ] ⊧* 𝗜𝚫 1] : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 1 :=
  Semantics.ModelsSet.union_iff.mpr ⟨inferInstance, models_collection_prenex_sigmaOne⟩

/-- Over `𝗘𝗔`, `𝗜𝚫 1` proves the collection scheme `𝗕𝚺 1`.
- [Sla04, Theorem 2.1]
- [Tha05, Theorem 2] -/
theorem BSigma_one_weakerThan_EA_IDelta_one : 𝗘𝗔 ∪ 𝗕𝚺 1 ⪯ 𝗘𝗔 ∪ 𝗜𝚫 1 := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗘𝗔 ∪ 𝗜𝚫 1 :=
    _root_.FFL.Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗘𝗔)
      (_root_.FFL.Entailment.WeakerThan.ofSubset Set.subset_union_left)
  refine weakerThan_of_models.{0} _ _ fun M _ _ ↦ ?_
  have hEA : M↓[ℒₒᵣ] ⊧* 𝗘𝗔 := models_of_ss (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗘𝗔 ∪ 𝗜𝚫 1)
    Set.subset_union_left
  have hID : M↓[ℒₒᵣ] ⊧* 𝗜𝚫 1 := models_of_ss (inferInstance : M↓[ℒₒᵣ] ⊧* 𝗘𝗔 ∪ 𝗜𝚫 1)
    Set.subset_union_right
  exact Semantics.ModelsSet.union_iff.mpr ⟨hEA, models_BSigma_one⟩

end

end FFL.FirstOrder.Arithmetic
