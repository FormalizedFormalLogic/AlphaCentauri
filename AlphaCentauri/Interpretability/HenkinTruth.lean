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

omit [L.Eq] in
variable (L) in
noncomputable def andCond : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “a b c n. !(isSemiformula L).sigma n a ∧ !(isSemiformula L).sigma n b ∧ !qqAndDef c a b”

omit [L.Eq] in
noncomputable def satisfiesAnd : ArithmeticSemisentence 5 :=
  “a b c n s. !(henkinSatisfiesDef S).val c n s ↔
    (!(henkinSatisfiesDef S).val a n s ∧ !(henkinSatisfiesDef S).val b n s)”

omit [L.Eq] [𝗘𝗤 L ⪯ S] in
lemma provable_satisfiesAnd :
    T ∪ S.Con ⊢ ∀¹* ((Rew.subst (fun i ↦ #(i.castAdd 1)) ▹ (andCond L).val) 🡒 satisfiesAnd S) :=
  provable_imp_of_models_henkin S T _ _ fun W _ _ hS hcons e hc ↦ by
    simp [andCond] at hc
    simp [satisfiesAnd]
    sorry

end facts

section internal

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] (S : Theory L) [S.Δ₁]
  [Theory.Δ₁.Sentential S] [𝗘𝗤 L ⪯ S] (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔 ⪯ T]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open Bootstrapping.Arithmetic

/-- The satisfaction of the coded formula `a` with `n` bound variables at the list `s`, as an
internal formula. -/
noncomputable def satisfiesT (a n : V) (s : Bootstrapping.Term V ℒₒᵣ) :
    Bootstrapping.Formula V ℒₒᵣ :=
  (⌜(henkinSatisfiesDef S).val⌝ : Bootstrapping.Semiformula V ℒₒᵣ 3).subst ![𝕹 a, 𝕹 n, s]

omit [L.Eq] [𝗘𝗤 L ⪯ S] in
lemma tprovable_satisfies_and {n p q : V} (hp : IsSemiformula L n p) (hq : IsSemiformula L n q)
    (s : Bootstrapping.Term V ℒₒᵣ) :
    (T ∪ S.Con).internalize V ⊢
      satisfiesT S (p ^⋏ q) n s 🡘 satisfiesT S p n s ⋏ satisfiesT S q n s := by
  have h := tprovable_subst_of_provable_imp (m := 1) (andCond L) (satisfiesAnd S)
    (provable_satisfiesAnd S T)
    (w := ![p, q, p ^⋏ q, n]) (by simp [andCond, hp, hq]) ![𝕹 p, 𝕹 q, 𝕹 (p ^⋏ q), 𝕹 n, s]
    (by simp [Fin.forall_fin_succ])
  rw [satisfiesAnd] at h
  simpa [typed_quote_rew_subst, Bootstrapping.Semiformula.substs_substs, satisfiesT,
    Matrix.vecHead, Matrix.vecTail] using h

end internal

end FFL.FirstOrder.Arithmetic
