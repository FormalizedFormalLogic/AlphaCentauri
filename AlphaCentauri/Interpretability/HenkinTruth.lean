module

public import AlphaCentauri.Bootstrapping.Completeness.HenkinSatisfaction
public import AlphaCentauri.Bootstrapping.Interpretability.Soundness
public import AlphaCentauri.Interpretability.Henkin

/-!
# The formalized truth lemma of the Henkin translation

In every model of $\mathsf{I}\Sigma_1$, along a table of the Henkin translation of a theory $S$
into $T + \mathrm{Con}_S$, the translation of every coded axiom of $S$ is provable in
$T + \mathrm{Con}_S$. The proof is an induction inside the model over coded formulas `p` with `n`
bound variables, showing that $T + \mathrm{Con}_S$ proves, under the hypotheses that the free
variables $x_i$ belong to the domain and are provably equal in the Henkin set to the free variables
$u_i$, the equivalence of the translation of `p` at the $x_i$ with the satisfaction of `p` at the
$u_i$ in the Henkin set.

## References

- [Vis90, §6.2.2.1]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping

section facts

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] (S : Theory L) [S.Δ₁]
  [Theory.Δ₁.Sentential S] [𝗘𝗤 L ⪯ S] (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

omit [L.Eq] [𝗘𝗤 L ⪯ S] in
lemma provable_imp_of_models_henkin {k m : ℕ} (c : 𝚺ᴬ₁.Semisentence k)
    (φ : ArithmeticSemisentence (k + m))
    (H : ∀ (W : Type) [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗣𝗔],
      (∀ p ∈ S.Δ₁Class (V := W), shift L p = p) → S.Consistent W →
        ∀ e : Fin (k + m) → W, W ⊧/(fun i ↦ e (i.castAdd m)) c.val → W ⊧/e φ) :
    T ∪ S.Con ⊢ ∀¹* ((Rew.subst (fun i ↦ #(i.castAdd m)) ▹ c.val) 🡒 φ) :=
  provable_of_models_henkin S T _ fun W _ _ hS hcons ↦ by
    simp only [models_iff, Semiformula.eval_allClosure, LogicalConnective.HomClass.map_imply,
      Semiformula.eval_rew, Function.comp_def, Rew.subst_bvar, Semiterm.val_bvar,
      LogicalConnective.Prop.arrow_eq]
    intro e hc
    exact H W hS hcons e hc

/-! ### Conditions on the numeral arguments -/

section conditions

variable (L)

noncomputable def verumCond : 𝚺ᴬ₁.Semisentence 2 := .mkSigma “c n. !qqVerumDef c”

noncomputable def falsumCond : 𝚺ᴬ₁.Semisentence 2 := .mkSigma “c n. !qqFalsumDef c”

noncomputable def andCond : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “a b c n. !(isSemiformula L).sigma n a ∧ !(isSemiformula L).sigma n b ∧ !qqAndDef c a b”

noncomputable def orCond : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “a b c n. !(isSemiformula L).sigma n a ∧ !(isSemiformula L).sigma n b ∧ !qqOrDef c a b”

noncomputable def negCond : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “c d n. !(isSemiformula L).sigma n c ∧ !(negGraph L) d c”

noncomputable def allCond : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “a b n m. !(isSemiformula L).sigma m a ∧ m = n + 1 ∧ !qqAllDef b a”

noncomputable def exsCond : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “a b n m. !(isSemiformula L).sigma m a ∧ m = n + 1 ∧ !qqExsDef b a”

noncomputable def trueCond : 𝚺ᴬ₁.Semisentence 0 := .mkSigma “⊤”

noncomputable def zeroCond : 𝚺ᴬ₁.Semisentence 1 := .mkSigma “i. i = 0”

noncomputable def succCond : 𝚺ᴬ₁.Semisentence 2 := .mkSigma “k m. m = k + 1”

noncomputable def bvarCond : 𝚺ᴬ₁.Semisentence 3 := .mkSigma “t i n. !qqBvarDef t i ∧ i < n”

end conditions

noncomputable def axiomCond : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
  “a. !(S.Δ₁ch).sigma a ∧ !(isSemiformula L).sigma 0 a”

/-! ### Clauses of satisfaction -/

section clauses

omit [L.Eq]

noncomputable def satisfiesVerum : ArithmeticSemisentence 3 :=
  “c n s. !(henkinSatisfiesDef S).val c n s”

noncomputable def satisfiesFalsum : ArithmeticSemisentence 3 :=
  “c n s. ¬!(henkinSatisfiesDef S).val c n s”

noncomputable def satisfiesAnd : ArithmeticSemisentence 5 :=
  “a b c n s. !(henkinSatisfiesDef S).val c n s ↔
    (!(henkinSatisfiesDef S).val a n s ∧ !(henkinSatisfiesDef S).val b n s)”

noncomputable def satisfiesOr : ArithmeticSemisentence 5 :=
  “a b c n s. !(henkinSatisfiesDef S).val c n s ↔
    (!(henkinSatisfiesDef S).val a n s ∨ !(henkinSatisfiesDef S).val b n s)”

noncomputable def satisfiesNeg : ArithmeticSemisentence 4 :=
  “c d n s. !(henkinSatisfiesDef S).val d n s ↔ ¬!(henkinSatisfiesDef S).val c n s”

noncomputable def satisfiesAll : ArithmeticSemisentence 5 :=
  “a b n m s. !(henkinSatisfiesDef S).val b n s ↔
    ∀ v, !(henkinSatisfiesDef S).val a m ((v + s) * (v + s) + v + 1)”

noncomputable def satisfiesExs : ArithmeticSemisentence 5 :=
  “a b n m s. !(henkinSatisfiesDef S).val b n s ↔
    ∃ v, !(henkinSatisfiesDef S).val a m ((v + s) * (v + s) + v + 1)”

noncomputable def satisfiesAxiom : ArithmeticSemisentence 2 :=
  “a s. !(henkinSatisfiesDef S).val a 0 s”

variable [𝗘𝗤 L ⪯ S]

omit [𝗘𝗤 L ⪯ S] in
lemma provable_satisfiesVerum :
    T ∪ S.Con ⊢ ∀¹* ((Rew.subst (fun i ↦ #(i.castAdd 1)) ▹ verumCond.val) 🡒 satisfiesVerum S) :=
  provable_imp_of_models_henkin S T _ _ fun _ _ _ _ _ e hc ↦ by
    have hc' : e 0 = ^⊤ := by simpa [verumCond] using hc
    simp [satisfiesVerum, hc', henkinSatisfies_verum]

omit [𝗘𝗤 L ⪯ S] in
lemma provable_satisfiesFalsum :
    T ∪ S.Con ⊢ ∀¹* ((Rew.subst (fun i ↦ #(i.castAdd 1)) ▹ falsumCond.val) 🡒 satisfiesFalsum S) :=
  provable_imp_of_models_henkin S T _ _ fun _ _ _ hS hcons e hc ↦ by
    have hc' : e 0 = ^⊥ := by simpa [falsumCond] using hc
    simp [satisfiesFalsum, hc', not_henkinSatisfies_falsum hS hcons]

omit [𝗘𝗤 L ⪯ S] in
lemma provable_satisfiesAnd :
    T ∪ S.Con ⊢ ∀¹* ((Rew.subst (fun i ↦ #(i.castAdd 1)) ▹ (andCond L).val) 🡒 satisfiesAnd S) :=
  provable_imp_of_models_henkin S T _ _ fun _ _ _ hS hcons e hc ↦ by
    have hc' : IsSemiformula L (e 3) (e 0) ∧ IsSemiformula L (e 3) (e 1) ∧ e 2 = e 0 ^⋏ e 1 := by
      simpa [andCond] using hc
    have h := henkinSatisfies_and_iff hS hcons hc'.1 hc'.2.1 (e 4)
    rw [← hc'.2.2] at h
    simpa [satisfiesAnd] using h

omit [𝗘𝗤 L ⪯ S] in
lemma provable_satisfiesOr :
    T ∪ S.Con ⊢ ∀¹* ((Rew.subst (fun i ↦ #(i.castAdd 1)) ▹ (orCond L).val) 🡒 satisfiesOr S) :=
  provable_imp_of_models_henkin S T _ _ fun _ _ _ hS hcons e hc ↦ by
    have hc' : IsSemiformula L (e 3) (e 0) ∧ IsSemiformula L (e 3) (e 1) ∧ e 2 = e 0 ^⋎ e 1 := by
      simpa [orCond] using hc
    have h := henkinSatisfies_or_iff hS hcons hc'.1 hc'.2.1 (e 4)
    rw [← hc'.2.2] at h
    simpa [satisfiesOr] using h

omit [𝗘𝗤 L ⪯ S] in
lemma provable_satisfiesNeg :
    T ∪ S.Con ⊢ ∀¹* ((Rew.subst (fun i ↦ #(i.castAdd 1)) ▹ (negCond L).val) 🡒 satisfiesNeg S) :=
  provable_imp_of_models_henkin S T _ _ fun _ _ _ hS hcons e hc ↦ by
    have hc' : IsSemiformula L (e 2) (e 0) ∧ e 1 = neg L (e 0) := by simpa [negCond] using hc
    have h := henkinSatisfies_neg_iff hS hcons hc'.1 (e 3)
    rw [← hc'.2] at h
    simpa [satisfiesNeg] using h

omit [𝗘𝗤 L ⪯ S] in
lemma provable_satisfiesAll :
    T ∪ S.Con ⊢ ∀¹* ((Rew.subst (fun i ↦ #(i.castAdd 1)) ▹ (allCond L).val) 🡒 satisfiesAll S) :=
  provable_imp_of_models_henkin S T _ _ fun _ _ _ hS hcons e hc ↦ by
    have hc' : IsSemiformula L (e 3) (e 0) ∧ e 3 = e 2 + 1 ∧ e 1 = ^∀ e 0 := by
      simpa [allCond] using hc
    have h := henkinSatisfies_all_iff hS hcons (hc'.2.1 ▸ hc'.1) (e 4)
    rw [← hc'.2.2, ← hc'.2.1] at h
    simpa [satisfiesAll, squarePair] using h

omit [𝗘𝗤 L ⪯ S] in
lemma provable_satisfiesExs :
    T ∪ S.Con ⊢ ∀¹* ((Rew.subst (fun i ↦ #(i.castAdd 1)) ▹ (exsCond L).val) 🡒 satisfiesExs S) :=
  provable_imp_of_models_henkin S T _ _ fun _ _ _ hS hcons e hc ↦ by
    have hc' : IsSemiformula L (e 3) (e 0) ∧ e 3 = e 2 + 1 ∧ e 1 = ^∃ e 0 := by
      simpa [exsCond] using hc
    have h := henkinSatisfies_exs_iff hS hcons (hc'.2.1 ▸ hc'.1) (e 4)
    rw [← hc'.2.2, ← hc'.2.1] at h
    simpa [satisfiesExs, squarePair] using h

omit [𝗘𝗤 L ⪯ S] in
lemma provable_satisfiesAxiom :
    T ∪ S.Con ⊢ ∀¹* ((Rew.subst (fun i ↦ #(i.castAdd 1)) ▹ (axiomCond S).val) 🡒
      satisfiesAxiom S) :=
  provable_imp_of_models_henkin S T _ _ fun _ _ _ _ _ e hc ↦ by
    have hc' : e 0 ∈ S.Δ₁Class ∧ IsSemiformula L 0 (e 0) := by simpa [axiomCond] using hc
    have h : HenkinSatisfies S (e 0) 0 (e 1) :=
      (henkinSatisfies_zero_iff hc'.2 (e 1)).mpr (HenkinSet.of_provable S hc'.2
        (Derivable.by_axm (by simp [hc'.2]) _ (by simp) hc'.1).toProvable)
    simpa [satisfiesAxiom] using h

end clauses

/-! ### Representatives, lists and variables -/

section representatives

noncomputable def representativeExists : ArithmeticSentence :=
  “∀ v, ∃ y, !(henkinDomainDef S).val y ∧ !(henkinEqDef S).val y v”

noncomputable def henkinEqRefl : ArithmeticSentence := “∀ y, !(henkinEqDef S).val y y”

noncomputable def squarePairNthZero : ArithmeticSemisentence 3 :=
  “i a s. !squarePairNthGraph.val a ((a + s) * (a + s) + a + 1) i”

noncomputable def squarePairNthSucc : ArithmeticSemisentence 5 :=
  “k m a s y. !squarePairNthGraph.val y s k →
    !squarePairNthGraph.val y ((a + s) * (a + s) + a + 1) m”

noncomputable def equatesBvar : ArithmeticSemisentence 6 :=
  “t i n s y x. !squarePairNthGraph.val y s i → !(henkinEqDef S).val x y →
    ∀ z, !(henkinDomainDef S).val z → z = x → !(henkinEquatesDef S).val t n s z”

lemma provable_representativeExists : T ∪ S.Con ⊢ representativeExists S :=
  provable_of_models_henkin S T _ fun _ _ _ hS hcons ↦ by
    simpa [models_iff, representativeExists] using exists_isRepresentative S hS hcons

lemma provable_henkinEqRefl : T ∪ S.Con ⊢ henkinEqRefl S :=
  provable_of_models_henkin S T _ fun _ _ _ _ _ ↦ by
    simpa [models_iff, henkinEqRefl] using HenkinEq.refl S

omit [L.Eq] [𝗘𝗤 L ⪯ S] in
lemma provable_squarePairNthZero :
    T ∪ S.Con ⊢ ∀¹* ((Rew.subst (fun i ↦ #(i.castAdd 2)) ▹ zeroCond.val) 🡒 squarePairNthZero) :=
  provable_imp_of_models_henkin S T _ _ fun _ _ _ _ _ e hc ↦ by
    have hc' : e 0 = 0 := by simpa [zeroCond] using hc
    simpa [squarePairNthZero, hc', squarePair] using
      (squarePairNth_squarePair_zero (e 1) (e 2)).symm

omit [L.Eq] [𝗘𝗤 L ⪯ S] in
lemma provable_squarePairNthSucc :
    T ∪ S.Con ⊢ ∀¹* ((Rew.subst (fun i ↦ #(i.castAdd 3)) ▹ succCond.val) 🡒 squarePairNthSucc) :=
  provable_imp_of_models_henkin S T _ _ fun _ _ _ _ _ e hc ↦ by
    have hc' : e 1 = e 0 + 1 := by simpa [succCond] using hc
    have h := squarePairNth_squarePair_succ (e 2) (e 3) (e 0)
    simp only [squarePair] at h
    simp [squarePairNthSucc, hc', h]

lemma provable_equatesBvar :
    T ∪ S.Con ⊢ ∀¹* ((Rew.subst (fun i ↦ #(i.castAdd 3)) ▹ bvarCond.val) 🡒 equatesBvar S) :=
  provable_imp_of_models_henkin S T _ _ fun _ _ _ hS hcons e hc ↦ by
    have hc' : e 0 = ^#(e 1) ∧ e 1 < e 2 := by simpa [bvarCond] using hc
    suffices e 4 = squarePairNth (e 3) (e 1) → HenkinEq S (e 5) (e 4) →
        ∀ z, IsRepresentative S z → z = e 5 → HenkinEquates S (e 0) (e 2) (e 3) z by
      simpa [equatesBvar] using this
    rintro hy hx z - rfl
    rw [hc'.1, henkinEquates_bvar_iff hc'.2, ← hy]
    exact HenkinEq.symm S hS hcons hx

end representatives

end facts


end FFL.FirstOrder.Arithmetic
