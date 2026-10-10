module

public import AlphaCentauri.Bootstrapping.Completeness.Henkin

/-!
# The Henkin set

The decision sequence of Henkin's construction exists and is unique in a model of
$\mathsf{PA}$, and the set of formulas decided positively is $\Delta_2$-definable.

## References

- [Lin97, Theorem 6.4]
- [HP98, Theorem I.4.25]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {L : Language} [L.Encodable] [L.LORDefinable] (S : Theory L) [S.Δ₁]

section definability

instance formulaOfCode.definable : 𝚺ᴬ₁-Function₁ (formulaOfCode (V := V) L) := by
  have : 𝚺ᴬ₁.Definable fun v : Fin 2 → V ↦
      (IsFormula L (v 1) ∧ v 0 = v 1) ∨ (¬IsFormula L (v 1) ∧ v 0 = ^⊤) := by
    definability
  apply this.of_iff
  intro v
  by_cases h : IsFormula L (v 1) <;> simp [formulaOfCode, h]

instance henkinFormula.definable : 𝚺ᴬ₁-Function₂ (henkinFormula (V := V) L) := by
  have : 𝚺ᴬ₁.Definable fun v : Fin 3 → V ↦
      ((IsFormula L (v 1) ∧ ∃ p < v 1, v 1 = ^∃ p) ∧
          v 0 = imp L (v 1) (substs1 L ^&(v 2) (π₂ (v 1 - 1)))) ∨
        (¬(IsFormula L (v 1) ∧ ∃ p < v 1, v 1 = ^∃ p) ∧ v 0 = ^⊤) := by
    definability
  apply this.of_iff
  intro v
  by_cases h : IsFormula L (v 1) ∧ ∃ p < v 1, v 1 = ^∃ p <;> simp [henkinFormula, h]

instance henkinStep.definable : 𝚫ᴬ_[2]-Function₂ (henkinStep (V := V) S) := by
  have hD : 𝚺ᴬ₁.Definable fun v : Fin 3 → V ↦
      Derivable S (insert (neg L (henkinFormula L (v 1) (v 1 + v 2)))
        (insert (formulaOfCode L (v 1)) (v 2))) := by
    definability
  have hpos : 𝚺ᴬ₁.Definable fun v : Fin 3 → V ↦
      v 0 = insert (neg L (henkinFormula L (v 1) (v 1 + v 2)))
        (insert (neg L (formulaOfCode L (v 1))) (v 2)) := by
    definability
  have hneg : 𝚺ᴬ₁.Definable fun v : Fin 3 → V ↦
      v 0 = insert (neg L (henkinFormula L (v 1) (v 1 + v 2)))
        (insert (formulaOfCode L (v 1)) (v 2)) := by
    definability
  have hD₂ := hD.of_lt (Γ := 𝚫) (s := 2) (by simp)
  apply (HierarchySymbol.Definable.or (hD₂.and <| hpos.of_lt (by simp))
    (hD₂.notDelta.and <| hneg.of_lt (by simp))).of_iff
  intro v
  by_cases h : Derivable S (insert (neg L (henkinFormula L (v 1) (v 1 + v 2)))
    (insert (formulaOfCode L (v 1)) (v 2))) <;> simp [henkinStep, h]

end definability

/-- `y` is the sequence of the first `n + 1` contexts of the decision sequence of the Henkin
completion of `S`. -/
def IsHenkinSeq (n y : V) : Prop :=
  Seq y ∧ lh y = n + 1 ∧ znth y 0 = ∅ ∧ ∀ i < n, znth y (i + 1) = henkinStep S i (znth y i)

instance IsHenkinSeq.definable : 𝚫ᴬ_[2]-Relation (IsHenkinSeq (V := V) S) := by
  unfold IsHenkinSeq
  definability

lemma exists_isHenkinSeq (n : V) : ∃ y, IsHenkinSeq S n y := by
  apply InductionOnHierarchy.succ_induction_sigma 𝚺 2 (P := fun n : V ↦ ∃ y, IsHenkinSeq S n y)
    (by definability)
  · exact ⟨∅ ⁀' ∅, seq_empty.seqCons ∅, by simp,
      (seq_empty.seqCons ∅).znth_eq_of_mem (by simp), by simp⟩
  · rintro n ⟨y, hy, hlh, h0, hstep⟩
    have hcons := hy.seqCons (henkinStep S n (znth y n))
    have hlt : ∀ {i}, i ≤ n → znth (y ⁀' henkinStep S n (znth y n)) i = znth y i := by
      intro i hi
      exact hcons.znth_eq_of_mem <| Seq.subset_seqCons _ _ <| hy.znth <| by
        rw [hlh]; exact lt_succ_iff_le.mpr hi
    have hlast : znth (y ⁀' henkinStep S n (znth y n)) (n + 1) = henkinStep S n (znth y n) := by
      simpa [hlh] using hcons.znth_eq_of_mem (Seq.mem_seqCons y (henkinStep S n (znth y n)))
    have hstep' : ∀ i < n + 1, znth (y ⁀' henkinStep S n (znth y n)) (i + 1) =
        henkinStep S i (znth (y ⁀' henkinStep S n (znth y n)) i) := by
      intro i hi
      rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with (hi | rfl)
      · rw [hlt (succ_le_iff_lt.mpr hi), hlt hi.le, hstep i hi]
      · rw [hlast, hlt le_rfl]
    exact ⟨y ⁀' henkinStep S n (znth y n), hcons, by simp [hy, hlh], by rw [hlt zero_le, h0],
      hstep'⟩

variable {S} in
lemma IsHenkinSeq.znth_eq {n m y y' : V} (hy : IsHenkinSeq S n y) (hy' : IsHenkinSeq S m y')
    {i : V} (hn : i ≤ n) (hm : i ≤ m) : znth y i = znth y' i := by
  revert hn hm
  induction i using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro _ _; rw [hy.2.2.1, hy'.2.2.1]
  case succ i ih =>
    intro hn hm
    have hn' : i < n := succ_le_iff_lt.mp hn
    have hm' : i < m := succ_le_iff_lt.mp hm
    rw [hy.2.2.2 i hn', hy'.2.2.2 i hm', ih hn'.le hm'.le]

theorem exists_isHenkinContext :
    ∃ c : V → V, IsHenkinContext S c ∧ 𝚫ᴬ_[2]-Function₁[V] c := by
  choose f hf using exists_isHenkinSeq (V := V) S
  have hzero : znth (f 0) 0 = ∅ := (hf 0).2.2.1
  have hsucc : ∀ n, znth (f (n + 1)) (n + 1) = henkinStep S n (znth (f n) n) := by
    intro n
    rw [(hf (n + 1)).2.2.2 n (lt_add_one n), (hf (n + 1)).znth_eq (hf n) le_self_add le_rfl]
  have hσ : 𝚺ᴬ_[2].Definable fun v : Fin 2 → V ↦
      ∃ y, IsHenkinSeq S (v 1) y ∧ v 0 = znth y (v 1) := by
    definability
  have hπ : 𝚷ᴬ_[2].Definable fun v : Fin 2 → V ↦
      ∀ y, IsHenkinSeq S (v 1) y → v 0 = znth y (v 1) := by
    definability
  have hdef : 𝚫ᴬ_[2]-Function₁[V] fun n ↦ znth (f n) n := by
    apply HierarchySymbol.Definable.of_sigma_of_pi
    · apply hσ.of_iff
      intro v
      constructor
      · intro h
        exact ⟨f (v 1), hf (v 1), h⟩
      · rintro ⟨y, hy, h⟩
        rw [h]
        exact hy.znth_eq (hf (v 1)) le_rfl le_rfl
    · apply hπ.of_iff
      intro v
      constructor
      · intro h y hy
        rw [h]
        exact (hf (v 1)).znth_eq hy le_rfl le_rfl
      · intro h
        exact h (f (v 1)) (hf (v 1))
  exact ⟨fun n ↦ znth (f n) n, ⟨hzero, hsucc⟩, hdef⟩

variable {S} in
lemma IsHenkinContext.unique {c c' : V → V} (hc : IsHenkinContext S c)
    (hc' : IsHenkinContext S c') (hdef : 𝚫ᴬ_[2]-Function₁[V] c)
    (hdef' : 𝚫ᴬ_[2]-Function₁[V] c') : c = c' := by
  have hP : 𝚫ᴬ_[2]-Predicate fun n : V ↦ c n = c' n :=
    HierarchySymbol.DefinableRel.comp HierarchySymbol.DefinableRel.eq hdef.of_delta
      hdef'.of_delta
  have hzero : c 0 = c' 0 := by rw [hc.1, hc'.1]
  have hsucc : ∀ n, c n = c' n → c (n + 1) = c' (n + 1) := by
    intro n ih
    rw [hc.2, hc'.2, ih]
  funext n
  exact InductionOnHierarchy.succ_induction_sigma 𝚫 2 hP hzero hsucc n

open Classical in
/-- The contexts of the decision sequence of the Henkin completion of `S`. -/
noncomputable def henkinContext : V → V := Classical.choose (exists_isHenkinContext (V := V) S)

lemma isHenkinContext_henkinContext : IsHenkinContext S (henkinContext S : V → V) :=
  (Classical.choose_spec (exists_isHenkinContext (V := V) S)).1

lemma henkinContext_definable : 𝚫ᴬ_[2]-Function₁[V] (henkinContext S) :=
  (Classical.choose_spec (exists_isHenkinContext (V := V) S)).2

/-- The Henkin set of `S`: the formulas decided positively along the decision sequence. -/
def HenkinSet (x : V) : Prop := HenkinMem S (henkinContext S) x

theorem henkinSet_definable : 𝚫ᴬ_[2]-Predicate[V] (HenkinSet S) := by
  have hmem : 𝚺ᴬ₁-Relation fun x c : V ↦
      IsFormula L x ∧ Derivable S (insert (neg L (henkinFormula L x (x + c))) (insert x c)) := by
    definability
  have hmem₂ : 𝚫ᴬ_[2]-Relation fun x c : V ↦
      IsFormula L x ∧ Derivable S (insert (neg L (henkinFormula L x (x + c))) (insert x c)) :=
    hmem.of_lt (by simp)
  have hc : 𝚺ᴬ_[2]-Function₁[V] henkinContext S := (henkinContext_definable S).of_delta
  exact hmem₂.comp (HierarchySymbol.DefinableFunction.var 0) hc

lemma HenkinSet.isFormula {x : V} (h : HenkinSet S x) : IsFormula L x := h.1

lemma HenkinSet.of_provable {φ : V} (hφ : IsFormula L φ) (h : Provable S φ) : HenkinSet S φ :=
  henkinMem_of_provable S (isHenkinContext_henkinContext S) (henkinContext_definable S) hφ h

lemma not_derivable_henkinContext (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p)
    (hcons : S.Consistent V) (n : V) : ¬Derivable S (henkinContext S n) :=
  not_derivable_of_isHenkinContext S hS hcons (isHenkinContext_henkinContext S)
    (henkinContext_definable S) n

variable {S} (hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p) (hcons : S.Consistent V)
include hS hcons

lemma HenkinSet.neg_iff {φ : V} (hφ : IsFormula L φ) :
    HenkinSet S (neg L φ) ↔ ¬HenkinSet S φ :=
  henkinMem_neg_iff S hS hcons (isHenkinContext_henkinContext S) (henkinContext_definable S) hφ

lemma HenkinSet.of_derivable {s ψ : V} (hψ : IsFormula L ψ)
    (hs : ∀ p ∈ s, HenkinSet S (neg L p)) (h : Derivable S (insert ψ s)) : HenkinSet S ψ :=
  henkinMem_of_derivable S hS hcons (isHenkinContext_henkinContext S) (henkinContext_definable S)
    hψ hs h

lemma HenkinSet.modus_ponens {α β : V} (hα : HenkinSet S α) (hαβ : HenkinSet S (imp L α β)) :
    HenkinSet S β :=
  henkinMem_modus_ponens S hS hcons (isHenkinContext_henkinContext S) (henkinContext_definable S)
    hα hαβ

lemma HenkinSet.exists_substs1 {α : V} (hα : IsSemiformula L 1 α) (h : HenkinSet S (^∃ α)) :
    ∃ u, HenkinSet S (substs1 L ^&u α) :=
  exists_henkinMem_substs1 S hS hcons (isHenkinContext_henkinContext S)
    (henkinContext_definable S) hα h

lemma HenkinSet.henkinFormula (n : V) :
    HenkinSet S (henkinFormula L n (n + henkinContext S n)) :=
  henkinMem_henkinFormula S hS hcons (isHenkinContext_henkinContext S)
    (henkinContext_definable S) n

end FFL.FirstOrder.Arithmetic.Bootstrapping
