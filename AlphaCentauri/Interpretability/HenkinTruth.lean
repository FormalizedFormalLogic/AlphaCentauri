module

public import AlphaCentauri.Bootstrapping.HenkinSatisfaction
public import AlphaCentauri.Bootstrapping.Interpretability.TypedTranslation
public import AlphaCentauri.Interpretability.Henkin
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.InternalTSchema

/-!
# The formalized truth lemma of the Henkin translation

The truth lemma of the Henkin translation, formalized in arithmetic.

## References

- [Vis90, §6.2.2.1]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open Bootstrapping.Arithmetic _root_.FFL.Entailment

private lemma forall_vec_two_iff {α : Type*} {P : (Fin 2 → α) → Prop} {D : α → Prop}
    {Q : Fin 2 → α → Prop} : (∀ z : Fin 2 → α, (∀ j, D (z j) ∧ Q j (z j)) → P z) ↔
      ∀ x y, D y → Q 0 y → D x → Q 1 x → P ![y, x] := by
  constructor
  · intro h x y hy hy' hx hx'
    exact h ![y, x] (by simp [Fin.forall_fin_two, *])
  · intro h z hz
    have e : z = ![z 0, z 1] := by funext i; cases i using Fin.cases <;> simp
    rw [e]
    exact h (z 1) (z 0) (hz 0).1 (hz 0).2 (hz 1).1 (hz 1).2

section formulas

variable (S : ArithmeticTheory) [S.Δ₁] {V : Type*} [ORingStructure V]

/-- The first `n` entries of the list coded by `s` are representatives of the Henkin set of `S`. -/
noncomputable def henkinListDef : ArithmeticSemisentence 2 :=
  “n s. ∃ l, !decGraph.val l s ∧ ∀ i < n, ∃ x, !nthDef.val x l i ∧ !(henkinDomainDef S).val x”

section

variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] {k : ℕ} (R : (ℒₒᵣ).Rel k) (F : (ℒₒᵣ).Func k) (y : V) (v : Fin k → V)

@[simp]
lemma eval_henkinListDef (v : Fin 2 → V) :
    V ⊧/v (henkinListDef S) ↔ ∀ i < v 0, IsRepresentative S (dec (v 1)).[i] := by
  simp [henkinListDef]

lemma eval_henkinRelDef : V ⊧/v (henkinRelDef S R).val ↔
      HenkinSet S (Semiformula.rel R (fun i ↦ Semiterm.fvar (v i)) : Formula V ℒₒᵣ).val :=
  henkinRel_val S R v

lemma eval_henkinFuncDef : V ⊧/(y :> v) (henkinFuncDef S F).val ↔
      HenkinSet S (Semiformula.equal (Semiterm.func F (fun i ↦ Semiterm.fvar (v i)))
        (Semiterm.fvar y) : Formula V ℒₒᵣ).val :=
  henkinFunc_val S F y v

end

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {m m' : ℕ} (w : SemitermVec V ℒₒᵣ m m')
  (s z : Semiterm V ℒₒᵣ m) (p t n : V)

/-- The internal formula that the code `p` with `n` bound variables is satisfied in the Henkin set
of `S` along the list `s`. -/
noncomputable def henkinSatisfiesF : Semiformula V ℒₒᵣ m :=
  (⌜(henkinSatisfiesDef S).val⌝ : Semiformula V ℒₒᵣ 3).subst ![𝕹 p, 𝕹 n, s]

/-- The internal formula that the code `t` of a term with `n` bound variables equates to `z` in the
Henkin set of `S` along the list `s`. -/
noncomputable def henkinEquatesF : Semiformula V ℒₒᵣ m :=
  (⌜(henkinEquatesDef S).val⌝ : Semiformula V ℒₒᵣ 4).subst ![𝕹 t, 𝕹 n, s, z]

/-- The internal formula that the first `n` entries of `s` are representatives. -/
noncomputable def henkinListF : Semiformula V ℒₒᵣ m :=
  (⌜henkinListDef S⌝ : Semiformula V ℒₒᵣ 2).subst ![𝕹 n, s]

/-- The internal domain formula of the Henkin translation. -/
noncomputable def henkinDomainF : Semiformula V ℒₒᵣ 1 := ⌜(henkinDomainDef S).val⌝

variable {S}

@[simp]
lemma subst_henkinSatisfiesF :
    (henkinSatisfiesF S s p n).subst w = henkinSatisfiesF S (s.subst w) p n := by
  simp [henkinSatisfiesF, Semiformula.substs_substs]

@[simp]
lemma shift_henkinSatisfiesF :
    (henkinSatisfiesF S s p n).shift = henkinSatisfiesF S s.shift p n := by
  simp [henkinSatisfiesF, Semiformula.shift_substs, typed_quote_shift]

end formulas

section clauses


variable (S : ArithmeticTheory) [S.Δ₁] [Theory.Δ₁.Sentential S]
  (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔 ⪯ T]
  {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance : 𝗜𝚺₁ ⪯ T ∪ S.Con :=
  Entailment.WeakerThan.trans (inferInstance : 𝗜𝚺₁ ⪯ 𝗣𝗔) (inferInstance : 𝗣𝗔 ⪯ T ∪ S.Con)

/-- A clause `φ` that holds in every model of $\mathsf{PA}$ in which `S` is consistent under a
$\Sigma_1$ condition on its first `k` variables is internally provable from `T ∪ S.Con` at every
vector of terms whose first `k` entries are the numerals of elements satisfying the condition. -/
lemma tprovable_subst_of_models_henkin {k m : ℕ} (c : 𝚺ᴬ₁.Semisentence k)
    (φ : ArithmeticSemisentence (k + m))
    (H : ∀ (W : Type) [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗣𝗔],
      (∀ p ∈ S.Δ₁Class (V := W), (ℒₒᵣ).IsSentence p) → S.Consistent W →
        ∀ e : Fin (k + m) → W, W ⊧/(fun i ↦ e (i.castAdd m)) c.val → W ⊧/e φ)
    {w : Fin k → V} (hw : V ⊧/w c.val) (v : SemitermVec V ℒₒᵣ (k + m) 0)
    (hv : ∀ i, v (i.castAdd m) = 𝕹 (w i)) :
    (T ∪ S.Con).internalize V ⊢ (⌜φ⌝ : Semiformula V ℒₒᵣ (k + m)).subst v := by
  have h : T ∪ S.Con ⊢ ∀¹* ((Rew.subst (fun i ↦ #(i.castAdd m)) ▹ c.val) 🡒 φ) :=
    provable_of_models_henkin S T _ fun W _ _ hS hcons ↦ by
      simpa [models_iff, Semiformula.eval_rew, Function.comp_def] using H W hS hcons
  have h₁ := tprovable_subst_of_allClosure (T ∪ S.Con) v (internal_provable_of_outer_provable h)
  have e : ((Semiterm.subst v)⨟ fun i ↦
      (⌜(Rew.emb (#(i.castAdd m) : ArithmeticSemiterm Empty (k + m)) :
        SyntacticSemiterm ℒₒᵣ (k + m))⌝ : Semiterm V ℒₒᵣ (k + m))) = fun i ↦ 𝕹 (w i) := by
    funext i
    simp [hv]
  rw [LCWQIsoGödelQuote.imply, Semiformula.substs_imp, typed_quote_rew_subst,
    Semiformula.substs_substs, e] at h₁
  exact h₁ ⨀ bold_sigma_one_complete _ c.sigma_prop hw


variable {p q t u : V} (x : Term V ℒₒᵣ) (R : (ℒₒᵣ).Rel 2) (D : Semiformula V ℒₒᵣ 1)
  (A : Fin 2 → Semiformula V ℒₒᵣ 1) (s : Term V ℒₒᵣ) {n : V}

/-! ### Lists of representatives -/

lemma tprovable_henkinListF_zero : (T ∪ S.Con).internalize V ⊢ henkinListF S s 0 := by
  have h := tprovable_subst_of_models_henkin S T (k := 1) (m := 1) (.mkSigma “n. n = 0”)
    (henkinListDef S) (by
      intro W _ _ _ _ e he
      have h : e 0 = 0 := by simpa using he
      simp [h])
    (w := ![(0 : V)]) (by simp) ![𝕹 0, s] (by simp)
  exact h

private noncomputable def listSucc : ArithmeticSemisentence 4 :=
  (henkinListDef S)/[#1, ‘(#2 + #3) * (#2 + #3) + #3 + 1’] 🡘
    (henkinDomainDef S).val/[#2] ⋏ (henkinListDef S)/[#0, #3]

section

variable (n)

lemma tprovable_henkinListF_succ : (T ∪ S.Con).internalize V ⊢ henkinListF S (pTerm x s) (n + 1) 🡘
      (henkinDomainF S).subst ![x] ⋏ henkinListF S s n := by
  have h := tprovable_subst_of_models_henkin S T (k := 2) (m := 2) (.mkSigma “n m. m = n + 1”)
    (listSucc S) (by
      intro W _ _ _ _ e he
      have h : e 1 = e 0 + 1 := by simpa using he
      suffices (∀ i < e 0 + 1, IsRepresentative S (dec (ppair (e 2) (e 3))).[i]) ↔
          IsRepresentative S (e 2) ∧ ∀ i < e 0, IsRepresentative S (dec (e 3)).[i] by
        simpa [listSucc, h, ppair] using this
      constructor
      · intro h
        and_intros
        · simpa using h 0 (by simp)
        · intro i hi
          simpa using h (i + 1) (by simpa using hi)
      · rintro ⟨h₀, h₁⟩ i hi
        rcases zero_or_succ i with rfl | ⟨i, rfl⟩
        · simpa using h₀
        · simpa using h₁ i (by simpa using hi))
    (w := ![n, n + 1]) (by simp) ![𝕹 n, 𝕹 (n + 1), x, s] (by simp [Fin.forall_fin_succ])
  simpa [listSucc, henkinListF, henkinDomainF, pTerm, typed_quote_rew_subst,
    Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail,
    Matrix.constant_eq_singleton] using h

/-! ### Formulas -/

lemma tprovable_henkinSatisfiesF_verum : (T ∪ S.Con).internalize V ⊢ henkinSatisfiesF S s ^⊤ n :=
  tprovable_subst_of_models_henkin S T (k := 2) (m := 1) (.mkSigma “c n. !qqVerumDef c”)
    (henkinSatisfiesDef S).val (by
      intro W _ _ _ _ e he
      have h : e 0 = ^⊤ := by simpa using he
      simp [h, henkinSatisfies_verum])
    (w := ![(^⊤ : V), n]) (by simp) ![𝕹 ^⊤, 𝕹 n, s] (by simp [Fin.forall_fin_succ])

lemma tprovable_henkinSatisfiesF_falsum :
    (T ∪ S.Con).internalize V ⊢ ∼henkinSatisfiesF S s ^⊥ n := by
  have h := tprovable_subst_of_models_henkin S T (k := 2) (m := 1) (.mkSigma “c n. !qqFalsumDef c”)
    (∼(henkinSatisfiesDef S).val) (by
      intro W _ _ hS hcons e he
      have h : e 0 = ^⊥ := by simpa using he
      simp [h, not_henkinSatisfies_falsum hS hcons])
    (w := ![(^⊥ : V), n]) (by simp) ![𝕹 ^⊥, 𝕹 n, s] (by simp [Fin.forall_fin_succ])
  simpa [henkinSatisfiesF] using h

end

private noncomputable def satAnd : ArithmeticSemisentence 5 :=
  (henkinSatisfiesDef S).val/[#2, #3, #4] 🡘
    (henkinSatisfiesDef S).val/[#0, #3, #4] ⋏ (henkinSatisfiesDef S).val/[#1, #3, #4]

lemma tprovable_henkinSatisfiesF_and (hp : IsSemiformula ℒₒᵣ n p) (hq : IsSemiformula ℒₒᵣ n q) :
    (T ∪ S.Con).internalize V ⊢ henkinSatisfiesF S s (p ^⋏ q) n 🡘
      henkinSatisfiesF S s p n ⋏ henkinSatisfiesF S s q n := by
  have h := tprovable_subst_of_models_henkin S T (k := 4) (m := 1)
    (.mkSigma “a b c n. !(isSemiformula ℒₒᵣ).sigma n a ∧ !(isSemiformula ℒₒᵣ).sigma n b ∧
      !qqAndDef c a b”) (satAnd S) (by
      intro W _ _ hS hcons e he
      have h : IsSemiformula ℒₒᵣ (e 3) (e 0) ∧ IsSemiformula ℒₒᵣ (e 3) (e 1) ∧
        e 2 = e 0 ^⋏ e 1 := by simpa using he
      simpa [satAnd, h.2.2] using henkinSatisfies_and_iff hS hcons h.1 h.2.1 (e 4))
    (w := ![p, q, p ^⋏ q, n]) (by simp [hp, hq]) ![𝕹 p, 𝕹 q, 𝕹 (p ^⋏ q), 𝕹 n, s]
    (by simp [Fin.forall_fin_succ])
  simpa [satAnd, henkinSatisfiesF, typed_quote_rew_subst, Semiformula.substs_substs,
    Matrix.vecHead, Matrix.vecTail] using h

private noncomputable def satOr : ArithmeticSemisentence 5 :=
  (henkinSatisfiesDef S).val/[#2, #3, #4] 🡘
    (henkinSatisfiesDef S).val/[#0, #3, #4] ⋎ (henkinSatisfiesDef S).val/[#1, #3, #4]

lemma tprovable_henkinSatisfiesF_or (hp : IsSemiformula ℒₒᵣ n p) (hq : IsSemiformula ℒₒᵣ n q) :
    (T ∪ S.Con).internalize V ⊢ henkinSatisfiesF S s (p ^⋎ q) n 🡘
      henkinSatisfiesF S s p n ⋎ henkinSatisfiesF S s q n := by
  have h := tprovable_subst_of_models_henkin S T (k := 4) (m := 1)
    (.mkSigma “a b c n. !(isSemiformula ℒₒᵣ).sigma n a ∧ !(isSemiformula ℒₒᵣ).sigma n b ∧
      !qqOrDef c a b”) (satOr S) (by
      intro W _ _ hS hcons e he
      have h : IsSemiformula ℒₒᵣ (e 3) (e 0) ∧ IsSemiformula ℒₒᵣ (e 3) (e 1) ∧
        e 2 = e 0 ^⋎ e 1 := by simpa using he
      simpa [satOr, h.2.2] using henkinSatisfies_or_iff hS hcons h.1 h.2.1 (e 4))
    (w := ![p, q, p ^⋎ q, n]) (by simp [hp, hq]) ![𝕹 p, 𝕹 q, 𝕹 (p ^⋎ q), 𝕹 n, s]
    (by simp [Fin.forall_fin_succ])
  simpa [satOr, henkinSatisfiesF, typed_quote_rew_subst, Semiformula.substs_substs,
    Matrix.vecHead, Matrix.vecTail] using h

private noncomputable def satNeg : ArithmeticSemisentence 4 :=
  (henkinSatisfiesDef S).val/[#1, #2, #3] 🡘 ∼(henkinSatisfiesDef S).val/[#0, #2, #3]

lemma tprovable_henkinSatisfiesF_neg (hp : IsSemiformula ℒₒᵣ n p) :
    (T ∪ S.Con).internalize V ⊢ henkinSatisfiesF S s (neg ℒₒᵣ p) n 🡘
      ∼henkinSatisfiesF S s p n := by
  have h := tprovable_subst_of_models_henkin S T (k := 3) (m := 1)
    (.mkSigma “a c n. !(isSemiformula ℒₒᵣ).sigma n a ∧ !(negGraph ℒₒᵣ) c a”) (satNeg S) (by
      intro W _ _ hS hcons e he
      have h : IsSemiformula ℒₒᵣ (e 2) (e 0) ∧ e 1 = neg ℒₒᵣ (e 0) := by simpa using he
      simpa [satNeg, h.2] using henkinSatisfies_neg_iff hS hcons h.1 (e 3))
    (w := ![p, neg ℒₒᵣ p, n]) (by simp [hp]) ![𝕹 p, 𝕹 (neg ℒₒᵣ p), 𝕹 n, s]
    (by simp [Fin.forall_fin_succ])
  simpa [satNeg, henkinSatisfiesF, typed_quote_rew_subst, Semiformula.substs_substs,
    Matrix.vecHead, Matrix.vecTail] using h

lemma tprovable_henkinSatisfiesF_axiom (hp : p ∈ S.Δ₁Class)
    (hf : IsFormula ℒₒᵣ p) : (T ∪ S.Con).internalize V ⊢ henkinSatisfiesF S s p 0 :=
  tprovable_subst_of_models_henkin S T (k := 2) (m := 1)
    (.mkSigma “a n. !(S.Δ₁ch).sigma a ∧ !(isSemiformula ℒₒᵣ).sigma 0 a ∧ n = 0”)
    (henkinSatisfiesDef S).val (by
      intro W _ _ _ _ e he
      have h : e 0 ∈ S.Δ₁Class ∧ IsFormula ℒₒᵣ (e 0) ∧ e 1 = 0 := by simpa using he
      suffices HenkinSatisfies S (e 0) 0 (e 2) by simpa [h.2.2] using this
      exact (henkinSatisfies_zero_iff h.2.1 (e 2)).mpr (HenkinSet.of_provable S h.2.1
        (Derivable.by_axm (by simp [h.2.1]) _ (by simp) h.1).toProvable))
    (w := ![p, 0]) (by simp [hp, hf]) ![𝕹 p, 𝕹 0, s] (by simp [Fin.forall_fin_succ])

variable [𝗘𝗤 ℒₒᵣ ⪯ S]

private noncomputable def satAll : ArithmeticSemisentence 5 :=
  (henkinSatisfiesDef S).val/[#1, #2, #4] 🡘 ∀¹ ((henkinDomainDef S).val/[#0] 🡒
    (henkinSatisfiesDef S).val/[#1, #4, ‘(#0 + #5) * (#0 + #5) + #5 + 1’])

lemma tprovable_henkinSatisfiesF_all (hp : IsSemiformula ℒₒᵣ (n + 1) p) :
    (T ∪ S.Con).internalize V ⊢ henkinSatisfiesF S s (^∀ p) n 🡘
      ∀¹ (henkinDomainF S 🡒 henkinSatisfiesF S (pTerm (Semiterm.bvar 0) s.bShift) p (n + 1)) := by
  have h := tprovable_subst_of_models_henkin S T (k := 4) (m := 1)
    (.mkSigma “a b n m. !(isSemiformula ℒₒᵣ).sigma m a ∧ m = n + 1 ∧ !qqAllDef b a”) (satAll S) (by
      intro W _ _ hS hcons e he
      have h : IsSemiformula ℒₒᵣ (e 3) (e 0) ∧ e 3 = e 2 + 1 ∧ e 1 = ^∀ e 0 := by simpa using he
      simpa [satAll, h.2, ppair] using
        henkinSatisfies_all_iff_isRepresentative hS hcons (h.2.1 ▸ h.1) (e 4))
    (w := ![p, ^∀ p, n, n + 1]) (by simp [hp]) ![𝕹 p, 𝕹 (^∀ p), 𝕹 n, 𝕹 (n + 1), s]
    (by simp [Fin.forall_fin_succ])
  simpa [satAll, henkinSatisfiesF, henkinDomainF, pTerm, typed_quote_rew_subst,
    Semiformula.substs_substs, SemitermVec.q, Matrix.vecHead, Matrix.vecTail,
    Matrix.constant_eq_singleton] using h

private noncomputable def satExs : ArithmeticSemisentence 5 :=
  (henkinSatisfiesDef S).val/[#1, #2, #4] 🡘 ∃¹ ((henkinDomainDef S).val/[#0] ⋏
    (henkinSatisfiesDef S).val/[#1, #4, ‘(#0 + #5) * (#0 + #5) + #5 + 1’])

lemma tprovable_henkinSatisfiesF_exs (hp : IsSemiformula ℒₒᵣ (n + 1) p) :
    (T ∪ S.Con).internalize V ⊢ henkinSatisfiesF S s (^∃ p) n 🡘
      ∃¹ (henkinDomainF S ⋏ henkinSatisfiesF S (pTerm (Semiterm.bvar 0) s.bShift) p (n + 1)) := by
  have h := tprovable_subst_of_models_henkin S T (k := 4) (m := 1)
    (.mkSigma “a b n m. !(isSemiformula ℒₒᵣ).sigma m a ∧ m = n + 1 ∧ !qqExsDef b a”) (satExs S) (by
      intro W _ _ hS hcons e he
      have h : IsSemiformula ℒₒᵣ (e 3) (e 0) ∧ e 3 = e 2 + 1 ∧ e 1 = ^∃ e 0 := by simpa using he
      simpa [satExs, h.2, ppair] using
        henkinSatisfies_exs_iff_isRepresentative hS hcons (h.2.1 ▸ h.1) (e 4))
    (w := ![p, ^∃ p, n, n + 1]) (by simp [hp]) ![𝕹 p, 𝕹 (^∃ p), 𝕹 n, 𝕹 (n + 1), s]
    (by simp [Fin.forall_fin_succ])
  simpa [satExs, henkinSatisfiesF, henkinDomainF, pTerm, typed_quote_rew_subst,
    Semiformula.substs_substs, SemitermVec.q, Matrix.vecHead, Matrix.vecTail,
    Matrix.constant_eq_singleton] using h

private noncomputable def satRel : ArithmeticSemisentence 5 :=
  (∀¹ ∀¹ (((henkinDomainDef S).val/[#0] ⋏ (henkinEquatesDef S).val/[#2, #5, #6, #0]) ⋏
      ((henkinDomainDef S).val/[#1] ⋏ (henkinEquatesDef S).val/[#3, #5, #6, #1]) ⋏ ⊤ 🡒
    (henkinRelDef S R).val/[#0, #1])) 🡘 (henkinSatisfiesDef S).val/[#2, #3, #4]

@[simp]
lemma relativizedImp_two (C : Semiformula V ℒₒᵣ 2) :
    relativizedImp D A (C.subst fun i ↦ Semiterm.bvar (i.addCast 0)) =
      ∀¹ ∀¹ ((D.subst ![Semiterm.bvar 0] ⋏ (A 0).subst ![Semiterm.bvar 0]) ⋏
        (D.subst ![Semiterm.bvar 1] ⋏ (A 1).subst ![Semiterm.bvar 1]) ⋏ ⊤ 🡒
          C.subst ![Semiterm.bvar 0, Semiterm.bvar 1]) := by
  rfl

lemma tprovable_henkinSatisfiesF_rel (ht : IsSemiterm ℒₒᵣ n t) (hu : IsSemiterm ℒₒᵣ n u) :
    (T ∪ S.Con).internalize V ⊢
      relativizedImp (henkinDomainF S)
        (fun i ↦ henkinEquatesF S s.bShift (Semiterm.bvar 0) (![t, u] i) n)
        ((⌜(henkinRelDef S R).val⌝ : Semiformula V ℒₒᵣ 2).subst
          fun i ↦ Semiterm.bvar (i.addCast 0)) 🡘
      henkinSatisfiesF S s (^rel 2 ⌜R⌝ ?[t, u]) n := by
  have h := tprovable_subst_of_models_henkin S T (k := 4) (m := 1)
    (.mkSigma “a b c n. !(isSemiterm ℒₒᵣ).sigma n a ∧ !(isSemiterm ℒₒᵣ).sigma n b ∧
      ∃ v, !mkVec₂Def v a b ∧ !qqRelDef c 2 ↑(Encodable.encode R) v”) (satRel S R) (by
      intro W _ _ hS hcons e he
      have h : IsSemiterm ℒₒᵣ (e 3) (e 0) ∧ IsSemiterm ℒₒᵣ (e 3) (e 1) ∧
          e 2 = ^rel 2 (Encodable.encode R : W) ?[e 0, e 1] := by
        simpa [numeral_eq_natCast] using he
      have h₁ := henkinSatisfies_rel_iff_forall hS hcons R (t := ![e 0, e 1]) (n := e 3)
        (by simp [Fin.forall_fin_succ, h]) (e 4)
      rw [forall_vec_two_iff] at h₁
      have h₂ : e 2 = ^rel ((2 : ℕ) : W) ⌜R⌝ (matrixToVec ![e 0, e 1]) := by rw [h.2.2]; simp; rfl
      rw [← h₂] at h₁
      simpa [satRel, eval_henkinRelDef, -Semiformula.rel_val] using h₁)
    (w := ![t, u, ^rel 2 ⌜R⌝ ?[t, u], n]) (by simp [ht, hu, numeral_eq_natCast]; rfl)
    ![𝕹 t, 𝕹 u, 𝕹 (^rel 2 ⌜R⌝ ?[t, u]), 𝕹 n, s]
    (by simp [Fin.forall_fin_succ])
  rw [relativizedImp_two]
  simpa [satRel, henkinSatisfiesF, henkinEquatesF, henkinDomainF, typed_quote_rew_subst,
    Semiformula.substs_substs, SemitermVec.q, Matrix.vecHead, Matrix.vecTail,
    Matrix.constant_eq_singleton, Semiterm.bShift_eq_subst_nil, Semiterm.bShift_subst_nil,
    Semiterm.subst_nil_subst] using h

/-! ### Terms -/

private noncomputable def equatesBvar : ArithmeticSemisentence 5 :=
  tvDef.val/[#3, #4, #0] 🡒 (henkinListDef S)/[#2, #4] 🡒
    ∀¹ ((henkinDomainDef S).val/[#0] 🡒 (“#0 = #4” 🡘 (henkinEquatesDef S).val/[#1, #3, #5, #0]))

lemma tprovable_henkinEquatesF_bvar {i : V} (hi : i < n) :
    (T ∪ S.Con).internalize V ⊢ tvF x s (^#i) 🡒 henkinListF S s n 🡒
      ∀¹ (henkinDomainF S 🡒 (Semiformula.equal (Semiterm.bvar 0) x.bShift 🡘
        henkinEquatesF S s.bShift (Semiterm.bvar 0) (^#i) n)) := by
  have h := tprovable_subst_of_models_henkin S T (k := 3) (m := 2)
    (.mkSigma “c i n. !qqBvarDef c i ∧ i < n”) (equatesBvar S) (by
      intro W _ _ hS hcons e he
      have h : e 0 = ^#(e 1) ∧ e 1 < e 2 := by simpa using he
      suffices e 3 = (dec (e 4)).[e 1] → (∀ i < e 2, IsRepresentative S (dec (e 4)).[i]) →
          ∀ z, IsRepresentative S z → (z = e 3 ↔ HenkinEquates S (^#(e 1)) (e 2) (e 4) z) by
        simpa [equatesBvar, h.1] using this
      intro hx hl z hz
      rw [henkinEquates_bvar_iff h.2, hx, eq_comm]
      exact (henkinSet_equal_fvar_iff S hS hcons (hl _ h.2) hz).symm)
    (w := ![^#i, i, n]) (by simp [hi]) ![𝕹 (^#i), 𝕹 i, 𝕹 n, x, s] (by simp [Fin.forall_fin_succ])
  simpa [equatesBvar, tvF, henkinListF, henkinEquatesF, henkinDomainF, typed_quote_rew_subst,
    Semiformula.substs_substs, SemitermVec.q, Matrix.vecHead, Matrix.vecTail,
    Matrix.constant_eq_singleton] using h

lemma funcGraph_zero (A : Fin 0 → Semiformula V ℒₒᵣ 1) (C : Semiformula V ℒₒᵣ 1) :
    funcGraph D A C = (⊤ 🡒 C.subst ![Semiterm.bvar 0]) := by
  rfl

lemma funcGraph_two (C : Semiformula V ℒₒᵣ 3) : funcGraph D A C =
      ∀¹ ∀¹ ((D.subst ![Semiterm.bvar 0] ⋏ (A 0).subst ![Semiterm.bvar 0]) ⋏
        (D.subst ![Semiterm.bvar 1] ⋏ (A 1).subst ![Semiterm.bvar 1]) ⋏ ⊤ 🡒
          C.subst ![Semiterm.bvar 2, Semiterm.bvar 0, Semiterm.bvar 1]) := by
  rfl

section

variable (F : (ℒₒᵣ).Func 0) (s : Term V ℒₒᵣ) (n : V) (A : Fin 0 → Semiformula V ℒₒᵣ 1)

private noncomputable def equatesConst : ArithmeticSemisentence 3 :=
  ∀¹ ((henkinDomainDef S).val/[#0] 🡒
    ((⊤ 🡒 (henkinFuncDef S F).val/[#0]) 🡘 (henkinEquatesDef S).val/[#1, #2, #3, #0]))

lemma tprovable_henkinEquatesF_const : (T ∪ S.Con).internalize V ⊢ ∀¹ (henkinDomainF S 🡒
      (funcGraph (henkinDomainF S) A ⌜(henkinFuncDef S F).val⌝ 🡘
        henkinEquatesF S s.bShift (Semiterm.bvar 0) (^func 0 ⌜F⌝ 0) n)) := by
  have h := tprovable_subst_of_models_henkin S T (k := 2) (m := 1)
    (.mkSigma “c n. !qqFuncDef c 0 ↑(Encodable.encode F) 0”) (equatesConst S F) (by
      intro W _ _ hS hcons e he
      have h : e 0 = ^func 0 (Encodable.encode F : W) 0 := by simpa [numeral_eq_natCast] using he
      have h₁ (y : W) := henkinEquates_func_iff_forall hS hcons F (t := ![]) (n := e 1)
        (by simp) (e 2) y
      have h₂ : e 0 = ^func ((0 : ℕ) : W) ⌜F⌝ (matrixToVec ![]) := by rw [h]; simp; rfl
      rw [← h₂] at h₁
      have h₃ (y : W) (_ : IsRepresentative S y) :
          W ⊧/![y] (henkinFuncDef S F).val ↔ HenkinEquates S (e 0) (e 1) (e 2) y :=
        (eval_henkinFuncDef S F y ![]).trans <| by
          rw [← h₁ y]
          simp [Matrix.empty_eq]
      simpa [equatesConst] using h₃)
    (w := ![^func 0 ⌜F⌝ 0, n]) (by simp [numeral_eq_natCast]; rfl)
    ![𝕹 (^func 0 ⌜F⌝ 0), 𝕹 n, s] (by simp [Fin.forall_fin_succ])
  rw [funcGraph_zero]
  simpa [equatesConst, henkinEquatesF, henkinDomainF, typed_quote_rew_subst,
    Semiformula.substs_substs, SemitermVec.q, Matrix.vecHead, Matrix.vecTail,
    Matrix.constant_eq_singleton] using h

end

section

variable (F : (ℒₒᵣ).Func 2) (s : Term V ℒₒᵣ)

private noncomputable def equatesFunc : ArithmeticSemisentence 5 :=
  ∀¹ ((henkinDomainDef S).val/[#0] 🡒
    ((∀¹ ∀¹ (((henkinDomainDef S).val/[#0] ⋏ (henkinEquatesDef S).val/[#3, #6, #7, #0]) ⋏
        ((henkinDomainDef S).val/[#1] ⋏ (henkinEquatesDef S).val/[#4, #6, #7, #1]) ⋏ ⊤ 🡒
      (henkinFuncDef S F).val/[#2, #0, #1])) 🡘 (henkinEquatesDef S).val/[#3, #4, #5, #0]))

lemma tprovable_henkinEquatesF_func (ht : IsSemiterm ℒₒᵣ n t) (hu : IsSemiterm ℒₒᵣ n u) :
    (T ∪ S.Con).internalize V ⊢ ∀¹ (henkinDomainF S 🡒
      (funcGraph (henkinDomainF S)
          (fun i ↦ henkinEquatesF S s.bShift (Semiterm.bvar 0) (![t, u] i) n)
          ⌜(henkinFuncDef S F).val⌝ 🡘
        henkinEquatesF S s.bShift (Semiterm.bvar 0) (^func 2 ⌜F⌝ ?[t, u]) n)) := by
  have h := tprovable_subst_of_models_henkin S T (k := 4) (m := 1)
    (.mkSigma “a b c n. !(isSemiterm ℒₒᵣ).sigma n a ∧ !(isSemiterm ℒₒᵣ).sigma n b ∧
      ∃ v, !mkVec₂Def v a b ∧ !qqFuncDef c 2 ↑(Encodable.encode F) v”) (equatesFunc S F) (by
      intro W _ _ hS hcons e he
      have h : IsSemiterm ℒₒᵣ (e 3) (e 0) ∧ IsSemiterm ℒₒᵣ (e 3) (e 1) ∧
          e 2 = ^func 2 (Encodable.encode F : W) ?[e 0, e 1] := by
        simpa [numeral_eq_natCast] using he
      have h₁ (y : W) := henkinEquates_func_iff_forall hS hcons F (t := ![e 0, e 1]) (n := e 3)
        (by simp [Fin.forall_fin_succ, h]) (e 4) y
      simp only [forall_vec_two_iff] at h₁
      have h₂ : e 2 = ^func ((2 : ℕ) : W) ⌜F⌝ (matrixToVec ![e 0, e 1]) := by rw [h.2.2]; simp; rfl
      rw [← h₂] at h₁
      simpa [equatesFunc, eval_henkinFuncDef] using fun y _ ↦ h₁ y)
    (w := ![t, u, ^func 2 ⌜F⌝ ?[t, u], n]) (by simp [ht, hu, numeral_eq_natCast]; rfl)
    ![𝕹 t, 𝕹 u, 𝕹 (^func 2 ⌜F⌝ ?[t, u]), 𝕹 n, s]
    (by simp [Fin.forall_fin_succ])
  rw [funcGraph_two]
  simpa [equatesFunc, henkinEquatesF, henkinDomainF, typed_quote_rew_subst,
    Semiformula.substs_substs, SemitermVec.q, Matrix.vecHead, Matrix.vecTail,
    Matrix.constant_eq_singleton, Semiterm.bShift_eq_subst_nil, Semiterm.bShift_subst_nil,
    Semiterm.subst_nil_subst] using h

end

end clauses

/-! ## The truth lemma -/

section truth

variable (S : ArithmeticTheory) [S.Δ₁] (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔 ⪯ T]
  {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {tbl n p q t u : V}

variable (hT : IsTable ℒₒᵣ ℒₒᵣ tbl)

/-- The internal formula that the translation of the term `t` and its value in the Henkin set
agree at the free variables `&i`. -/
noncomputable def henkinTermEquiv (ht : (ℒₒᵣ).IsClosedSemiterm n t) : Formula V ℒₒᵣ :=
  henkinListF S (assignment n) n 🡒 ∀¹ (henkinDomainF S 🡒 (varEqualT hT (instTerm n t ht) 🡘
    henkinEquatesF S (assignment n).bShift (Semiterm.bvar 0) t n))

variable (tbl n p t)

/-- The code of `henkinTermEquiv`. -/
noncomputable def henkinTermEquivCode : V :=
  imp ℒₒᵣ (subst ℒₒᵣ ?[numeral n, assignmentCode n] ⌜henkinListDef S⌝)
    (^∀ (imp ℒₒᵣ ⌜(henkinDomainDef S).val⌝
      (iff ℒₒᵣ (varEqual ℒₒᵣ ℒₒᵣ tbl (termSubst ℒₒᵣ (fvarVec n) t))
        (subst ℒₒᵣ ?[numeral t, numeral n, termBShift ℒₒᵣ (assignmentCode n), ^#0]
          ⌜(henkinEquatesDef S).val⌝))))

/-- The code of `henkinEquiv`. -/
noncomputable def henkinEquivCode : V :=
  imp ℒₒᵣ (subst ℒₒᵣ ?[numeral n, assignmentCode n] ⌜henkinListDef S⌝)
    (iff ℒₒᵣ (translate ℒₒᵣ ℒₒᵣ tbl (subst ℒₒᵣ (fvarVec n) p))
      (subst ℒₒᵣ ?[numeral p, numeral n, assignmentCode n] ⌜(henkinSatisfiesDef S).val⌝))

/-- The matrix of a quantified formula with the bound variables `#(i + 1)` replaced by `&i`. -/
noncomputable def instMatrix (hp : IsSemiformula ℒₒᵣ (n + 1) p) : Semiformula V ℒₒᵣ 1 :=
  ⟨subst ℒₒᵣ (qVec ℒₒᵣ (fvarVec n)) p, by
    simpa using hp.subst (isSemitermVec_fvarVec n 0).qVec⟩

variable {tbl n p t}

lemma val_henkinTermEquiv (ht : (ℒₒᵣ).IsClosedSemiterm n t) :
    (henkinTermEquiv S hT ht).val = henkinTermEquivCode S tbl n t := by
  simp [henkinTermEquiv, henkinTermEquivCode, henkinListF, henkinDomainF, henkinEquatesF, instTerm,
    Sentence.quote_eq]

/-- The internal formula that the translation of the formula `p` and its satisfaction in the Henkin
set agree at the free variables `&i`. -/
noncomputable def henkinEquiv (hp : IsSemiformula ℒₒᵣ n p) : Formula V ℒₒᵣ :=
  henkinListF S (assignment n) n 🡒
    (hT.transT (instFormula n p hp) 🡘 henkinSatisfiesF S (assignment n) p n)

lemma val_henkinEquiv (hp : IsSemiformula ℒₒᵣ n p) :
    (henkinEquiv S hT hp).val = henkinEquivCode S tbl n p := by
  simp [henkinEquiv, henkinEquivCode, henkinListF, henkinSatisfiesF, instFormula,
    Sentence.quote_eq]

variable [Theory.Δ₁.Sentential S]

lemma tprovable_henkinEquiv_neg (hp : IsSemiformula ℒₒᵣ n p)
    (hp' : IsSemiformula ℒₒᵣ n (neg ℒₒᵣ p))
    (h : (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT hp) :
    (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT hp' := by
  have e : instFormula n (neg ℒₒᵣ p) hp' = ∼instFormula n p hp := by
    ext; simp [instFormula, substs_neg hp (isSemitermVec_fvarVec n 0)]
  have h₁ := tprovable_henkinSatisfiesF_neg S T (assignment n) hp
  rw [henkinEquiv] at h ⊢
  rw [e, IsTable.transT_neg]
  cl_prover [h, h₁]

lemma tprovable_henkinEquiv_and (hp : IsSemiformula ℒₒᵣ n p) (hq : IsSemiformula ℒₒᵣ n q)
    (h : IsSemiformula ℒₒᵣ n (p ^⋏ q)) (h₁ : (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT hp)
    (h₂ : (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT hq) :
    (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT h := by
  have e : instFormula n (p ^⋏ q) h = instFormula n p hp ⋏ instFormula n q hq := by
    ext; simp [instFormula, hp.isUFormula, hq.isUFormula]
  have h₃ := tprovable_henkinSatisfiesF_and S T (assignment n) hp hq
  rw [henkinEquiv] at h₁ h₂ ⊢
  rw [e, IsTable.transT_and]
  cl_prover [h₁, h₂, h₃]

lemma tprovable_henkinEquiv_or (hp : IsSemiformula ℒₒᵣ n p) (hq : IsSemiformula ℒₒᵣ n q)
    (h : IsSemiformula ℒₒᵣ n (p ^⋎ q)) (h₁ : (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT hp)
    (h₂ : (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT hq) :
    (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT h := by
  have e : instFormula n (p ^⋎ q) h = instFormula n p hp ⋎ instFormula n q hq := by
    ext; simp [instFormula, hp.isUFormula, hq.isUFormula]
  have h₃ := tprovable_henkinSatisfiesF_or S T (assignment n) hp hq
  rw [henkinEquiv] at h₁ h₂ ⊢
  rw [e, IsTable.transT_or]
  cl_prover [h₁, h₂, h₃]

lemma tprovable_list_imp_all_iff (hp : (ℒₒᵣ).IsSemisentence (n + 1) p)
    (h : (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT hp.isSemiformula) :
    (T ∪ S.Con).internalize V ⊢ henkinListF S (assignment n) n 🡒
      ∀¹ (henkinDomainF S 🡒 (hT.transT (instMatrix n p hp.isSemiformula) 🡘
        henkinSatisfiesF S (pTerm (Semiterm.bvar 0) (assignment n).bShift) p (n + 1))) := by
  apply TProof.generalize_imp
  have e₁ : (hT.transT (instMatrix n p hp.isSemiformula)).free =
      hT.transT (instFormula (n + 1) p hp.isSemiformula) := by
    rw [← IsTable.transT_free]
    congr 1
    ext; simp [instMatrix, instFormula, free_subst_qVec_fvarVec hp]
  have e₂ : (henkinSatisfiesF S (pTerm (Semiterm.bvar 0) (assignment n).bShift) p (n + 1)).free =
      henkinSatisfiesF S (assignment (n + 1)) p (n + 1) := by
    rw [assignment_succ]; simp [Semiformula.free, ← Semiterm.bShift_shift_comm]
  have e₃ : (henkinListF S (assignment n) n).shift = henkinListF S (assignment n).shift n := by
    simp [henkinListF, Semiformula.shift_substs, typed_quote_shift]
  have e₄ : (henkinDomainF S : Semiformula V ℒₒᵣ 1).free =
      (henkinDomainF S).subst ![Semiterm.fvar 0] := by
    simp [henkinDomainF, Semiformula.free, typed_quote_shift]
  have h₁ := tprovable_henkinListF_succ S T (Semiterm.fvar 0) (assignment n).shift n
  rw [← assignment_succ] at h₁
  rw [henkinEquiv] at h
  rw [Semiformula.free_imp, Semiformula.free_iff, e₁, e₂, e₃, e₄]
  cl_prover [h, h₁]

variable [𝗘𝗤 ℒₒᵣ ⪯ S]

lemma tprovable_henkinTermEquiv_bvar {i : V} (hi : i < n)
    (h : (ℒₒᵣ).IsClosedSemiterm n (^#i : V)) :
    (T ∪ S.Con).internalize V ⊢ henkinTermEquiv S hT h := by
  have e : instTerm n (^#i) h = Semiterm.fvar i := by ext; simp [instTerm, nth_fvarVec n i hi]
  have h₁ := tprovable_henkinEquatesF_bvar S T (Semiterm.fvar i) (assignment n) hi
  have h₂ := tprovable_tvF_fvar_assignment (T := T ∪ S.Con) n i hi
  rw [henkinTermEquiv, e, varEqualT_fvar]
  simp only [Semiterm.bShift_fvar] at h₁
  exact h₁ ⨀ h₂

variable (hd : hT.domT = henkinDomainF S)
  (hR : ∀ R : (ℒₒᵣ).Rel 2, hT.relT R = ⌜(henkinRelDef S R).val⌝)
  (hF : ∀ {k : ℕ} (F : (ℒₒᵣ).Func k), hT.funcT F = ⌜(henkinFuncDef S F).val⌝)

include hd hF in
lemma tprovable_henkinTermEquiv_const (F : (ℒₒᵣ).Func 0)
    (h : (ℒₒᵣ).IsClosedSemiterm n (^func 0 ⌜F⌝ 0 : V)) :
    (T ∪ S.Con).internalize V ⊢ henkinTermEquiv S hT h := by
  have hf : (ℒₒᵣ).IsFunc ((0 : ℕ) : V) ⌜F⌝ := codeIn_func_quote F
  rw [Nat.cast_zero] at hf
  have e : instTerm n (^func 0 ⌜F⌝ 0) h = Semiterm.func F ![] := by
    ext; simp [instTerm, hf]
  rw [henkinTermEquiv, e, varEqualT_func, hd, hF]
  have h₁ := tprovable_henkinEquatesF_const S T F (assignment n) n fun i ↦ varEqualT hT (![] i)
  cl_prover [h₁]

include hd hF in
lemma tprovable_henkinTermEquiv_func (F : (ℒₒᵣ).Func 2) (ht : (ℒₒᵣ).IsClosedSemiterm n t)
    (hu : (ℒₒᵣ).IsClosedSemiterm n u)
    (h : (ℒₒᵣ).IsClosedSemiterm n (^func 2 ⌜F⌝ ?[t, u] : V))
    (h₁ : (T ∪ S.Con).internalize V ⊢ henkinTermEquiv S hT ht)
    (h₂ : (T ∪ S.Con).internalize V ⊢ henkinTermEquiv S hT hu) :
    (T ∪ S.Con).internalize V ⊢ henkinTermEquiv S hT h := by
  have hf : (ℒₒᵣ).IsFunc ((2 : ℕ) : V) ⌜F⌝ := codeIn_func_quote F
  rw [Nat.cast_ofNat] at hf
  have e : instTerm n (^func 2 ⌜F⌝ ?[t, u]) h =
      Semiterm.func F ![instTerm n t ht, instTerm n u hu] := by
    ext
    simp [instTerm, hf, ht.isSemiterm.isUTerm, hu.isSemiterm.isUTerm]
  have h₃ := funcGraph_congr (T := T ∪ S.Con) (henkinDomainF S)
    (fun i ↦ varEqualT hT (![instTerm n t ht, instTerm n u hu] i))
    (fun i ↦ henkinEquatesF S (assignment n).bShift (Semiterm.bvar 0) (![t, u] i) n)
    ⌜(henkinFuncDef S F).val⌝
  have h₄ := tprovable_all_iff_imp_all_imp_iff (A := funcGraph (henkinDomainF S)
    (fun i ↦ varEqualT hT (![instTerm n t ht, instTerm n u hu] i)) ⌜(henkinFuncDef S F).val⌝) <|
    tprovable_henkinEquatesF_func S T F (assignment n) ht.isSemiterm hu.isSemiterm
  rw [henkinTermEquiv] at h₁ h₂
  rw [henkinTermEquiv, e, varEqualT_func, hd, hF]
  simp only [Matrix.conj, Matrix.cons_val_zero, Matrix.vecTail, Function.comp_apply,
    Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h₃
  cl_prover [h₁, h₂, h₃, h₄]

include hd hF in
lemma provable_henkinTermEquivCode (ht : (ℒₒᵣ).IsClosedSemiterm n t) :
    Provable (T ∪ S.Con) (henkinTermEquivCode S tbl n t) := by
  apply IsSemiterm.induction 𝚺 (P := fun t ↦ termShift ℒₒᵣ t = t →
    Provable (T ∪ S.Con) (henkinTermEquivCode S tbl n t)) ?_ ?_ ?_ ?_ t
    ht.isSemiterm ht.termShift_eq
  · unfold henkinTermEquivCode
    definability
  · intro z hz hs
    have h : (ℒₒᵣ).IsClosedSemiterm n (^#z : V) := .of_termShift_eq (by simp [hz]) hs
    simpa [val_henkinTermEquiv] using
      tprovable_iff_provable.mp (tprovable_henkinTermEquiv_bvar S T hT hz h)
  · intro x h
    simp at h
  · intro k f v hf hv ih hs
    have hc : (ℒₒᵣ).IsClosedSemiterm n (^func k f v : V) :=
      .of_termShift_eq (by simp [hf, hv]) hs
    have hconst (F : (ℒₒᵣ).Func 0) (hf' : f = ⌜F⌝) (hk : k = 0) :
        Provable (T ∪ S.Con) (henkinTermEquivCode S tbl n (^func k f v)) := by
      subst hf' hk
      obtain rfl : v = 0 := by simpa using hv
      simpa [val_henkinTermEquiv] using
        tprovable_iff_provable.mp (tprovable_henkinTermEquiv_const S T hT hd hF F hc)
    have hfunc (F : (ℒₒᵣ).Func 2) (hf' : f = ⌜F⌝) (hk : k = 2) :
        Provable (T ∪ S.Con) (henkinTermEquivCode S tbl n (^func k f v)) := by
      subst hf' hk
      obtain ⟨a, b, ha, hb, rfl⟩ := IsUTermVec.two_iff.mp hv.isUTerm
      have hab : termShift ℒₒᵣ a = a ∧ termShift ℒₒᵣ b = b := by simpa [hf, ha, hb] using hs
      have ha' : (ℒₒᵣ).IsClosedSemiterm n a :=
        .of_termShift_eq (by simpa using hv.nth (i := 0) (by simp)) hab.1
      have hb' : (ℒₒᵣ).IsClosedSemiterm n b :=
        .of_termShift_eq (by simpa using hv.nth (i := 1) (by simp)) hab.2
      have h₁ : (T ∪ S.Con).internalize V ⊢ henkinTermEquiv S hT ha' :=
        tprovable_iff_provable.mpr <| by
          simpa [val_henkinTermEquiv] using ih 0 (by simp) (by simpa using hab.1)
      have h₂ : (T ∪ S.Con).internalize V ⊢ henkinTermEquiv S hT hb' :=
        tprovable_iff_provable.mpr <| by
          simpa [val_henkinTermEquiv] using ih 1 (by simp) (by simpa using hab.2)
      simpa [val_henkinTermEquiv] using tprovable_iff_provable.mp
        (tprovable_henkinTermEquiv_func S T hT hd hF F ha' hb' hc h₁ h₂)
    rcases Arithmetic.isFunc_iff_LOR.mp hf with ⟨hk, hf'⟩ | ⟨hk, hf'⟩ | ⟨hk, hf'⟩ | ⟨hk, hf'⟩
    · exact hconst _ hf' hk
    · exact hconst _ hf' hk
    · exact hfunc _ hf' hk
    · exact hfunc _ hf' hk

include hd hF in
lemma tprovable_henkinTermEquiv (ht : (ℒₒᵣ).IsClosedSemiterm n t) :
    (T ∪ S.Con).internalize V ⊢ henkinTermEquiv S hT ht :=
  tprovable_iff_provable.mpr <| by
    simpa [val_henkinTermEquiv] using provable_henkinTermEquivCode S T hT hd hF ht

include hd hF hR in
lemma tprovable_henkinEquiv_rel (R : (ℒₒᵣ).Rel 2) (ht : (ℒₒᵣ).IsClosedSemiterm n t)
    (hu : (ℒₒᵣ).IsClosedSemiterm n u) (h : IsSemiformula ℒₒᵣ n (^rel 2 ⌜R⌝ ?[t, u] : V)) :
    (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT h := by
  have hr : (ℒₒᵣ).IsRel ((2 : ℕ) : V) ⌜R⌝ := codeIn_rel_quote R
  rw [Nat.cast_ofNat] at hr
  have e : hT.transT (instFormula n (^rel 2 ⌜R⌝ ?[t, u]) h) =
      relativizedImp (henkinDomainF S)
        (fun i ↦ varEqualT hT (![instTerm n t ht, instTerm n u hu] i))
        ((⌜(henkinRelDef S R).val⌝ : Semiformula V ℒₒᵣ 2).subst
          fun i ↦ Semiterm.bvar (i.addCast 0)) := by
    have e₁ : instFormula n (^rel 2 ⌜R⌝ ?[t, u]) h =
        Semiformula.rel R ![instTerm n t ht, instTerm n u hu] := by
      ext
      simp [instFormula, instTerm, hr, ht.isSemiterm.isUTerm, hu.isSemiterm.isUTerm]
    rw [e₁, IsTable.transT_rel, hd, hR]
  have h₁ := tprovable_henkinTermEquiv S T hT hd hF ht
  have h₂ := tprovable_henkinTermEquiv S T hT hd hF hu
  have h₃ := relativizedImp_congr (T := T ∪ S.Con) (henkinDomainF S)
    (fun i ↦ varEqualT hT (![instTerm n t ht, instTerm n u hu] i))
    (fun i ↦ henkinEquatesF S (assignment n).bShift (Semiterm.bvar 0) (![t, u] i) n)
    ((⌜(henkinRelDef S R).val⌝ : Semiformula V ℒₒᵣ 2).subst fun i ↦ Semiterm.bvar (i.addCast 0))
  have h₄ := tprovable_henkinSatisfiesF_rel S T R (assignment n) ht.isSemiterm hu.isSemiterm
  rw [henkinTermEquiv] at h₁ h₂
  rw [henkinEquiv, e]
  generalize relativizedImp (henkinDomainF S)
    (fun i ↦ varEqualT hT (![instTerm n t ht, instTerm n u hu] i)) _ = X at h₃ ⊢
  generalize relativizedImp (henkinDomainF S)
    (fun i ↦ henkinEquatesF S (assignment n).bShift (Semiterm.bvar 0) (![t, u] i) n) _ = Y at h₃ h₄
  simp only [Matrix.conj, Matrix.cons_val_zero, Matrix.vecTail, Function.comp_apply,
    Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h₃
  cl_prover [h₁, h₂, h₃, h₄]

include hd in
lemma tprovable_henkinEquiv_all (hp : (ℒₒᵣ).IsSemisentence (n + 1) p)
    (h' : IsSemiformula ℒₒᵣ n (^∀ p))
    (h : (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT hp.isSemiformula) :
    (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT h' := by
  have e : instFormula n (^∀ p) h' = ∀¹ instMatrix n p hp.isSemiformula := by
    ext; simp [instFormula, instMatrix, hp.isSemiformula.isUFormula]
  have h₁ := tprovable_list_imp_all_iff S T hT hp h
  have h₂ := tprovable_henkinSatisfiesF_all S T (assignment n) hp.isSemiformula
  have h₃ := tprovable_all_imp_iff_all_domain (T := T ∪ S.Con) (henkinDomainF S)
    (hT.transT (instMatrix n p hp.isSemiformula))
    (henkinSatisfiesF S (pTerm (Semiterm.bvar 0) (assignment n).bShift) p (n + 1))
  rw [henkinEquiv, e, IsTable.transT_all, hd, Semiformula.subst_eq_self₁]
  cl_prover [h₁, h₂, h₃]

include hd in
lemma tprovable_henkinEquiv_exs (hp : (ℒₒᵣ).IsSemisentence (n + 1) p)
    (h' : IsSemiformula ℒₒᵣ n (^∃ p))
    (h : (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT hp.isSemiformula) :
    (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT h' := by
  have e : instFormula n (^∃ p) h' = ∃¹ instMatrix n p hp.isSemiformula := by
    ext; simp [instFormula, instMatrix, hp.isSemiformula.isUFormula]
  have h₁ := tprovable_list_imp_all_iff S T hT hp h
  have h₂ := tprovable_henkinSatisfiesF_exs S T (assignment n) hp.isSemiformula
  have h₃ := tprovable_all_imp_iff_exs_domain (T := T ∪ S.Con) (henkinDomainF S)
    (hT.transT (instMatrix n p hp.isSemiformula))
    (henkinSatisfiesF S (pTerm (Semiterm.bvar 0) (assignment n).bShift) p (n + 1))
  rw [henkinEquiv, e, IsTable.transT_exs, hd, Semiformula.subst_eq_self₁]
  cl_prover [h₁, h₂, h₃]

include hd hF hR in
lemma provable_henkinEquivCode (hp : (ℒₒᵣ).IsSemisentence n p) :
    Provable (T ∪ S.Con) (henkinEquivCode S tbl n p) := by
  have hrel {n k r v : V} (hr : (ℒₒᵣ).IsRel k r) (hv : IsSemitermVec ℒₒᵣ k n v)
      (hs : shift ℒₒᵣ (^rel k r v) = ^rel k r v) (h : IsSemiformula ℒₒᵣ n (^rel k r v)) :
      (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT h := by
    have hbin (R : (ℒₒᵣ).Rel 2) (hr' : r = ⌜R⌝) (hk : k = 2) :
        (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT h := by
      subst hr' hk
      obtain ⟨a, b, ha, hb, rfl⟩ := IsUTermVec.two_iff.mp hv.isUTerm
      have hab : termShift ℒₒᵣ a = a ∧ termShift ℒₒᵣ b = b := by simpa [hr, ha, hb] using hs
      exact tprovable_henkinEquiv_rel S T hT hd hR hF R
        (.of_termShift_eq (by simpa using hv.nth (i := 0) (by simp)) hab.1)
        (.of_termShift_eq (by simpa using hv.nth (i := 1) (by simp)) hab.2) h
    rcases Arithmetic.isRel_iff_LOR.mp hr with ⟨hk, hr'⟩ | ⟨hk, hr'⟩
    · exact hbin _ hr' hk
    · exact hbin _ hr' hk
  have of_code {n p : V} {hp : IsSemiformula ℒₒᵣ n p}
      (h : Provable (T ∪ S.Con) (henkinEquivCode S tbl n p)) :
      (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT hp :=
    tprovable_iff_provable.mpr <| by rwa [val_henkinEquiv]
  have to_code {n p : V} {hp : IsSemiformula ℒₒᵣ n p}
      (h : (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT hp) :
      Provable (T ∪ S.Con) (henkinEquivCode S tbl n p) := by
    simpa [val_henkinEquiv] using tprovable_iff_provable.mp h
  apply IsSemiformula.sigma1_structural_induction (L := ℒₒᵣ) (P := fun n p ↦ shift ℒₒᵣ p = p →
    Provable (T ∪ S.Con) (henkinEquivCode S tbl n p)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    hp.isSemiformula hp.shift_eq
  · unfold henkinEquivCode
    definability
  · intro n k r v hr hv hs
    exact to_code (hrel hr hv hs (by simp [hr, hv]))
  · intro n k r v hr hv hs
    have hs' : shift ℒₒᵣ (^rel k r v) = ^rel k r v := by
      simpa [hr, hv.isUTerm] using hs
    have h : IsSemiformula ℒₒᵣ n (^rel k r v) := by simp [hr, hv]
    have e : neg ℒₒᵣ (^rel k r v) = ^nrel k r v := by simp [hr, hv.isUTerm]
    rw [← e]
    exact to_code (tprovable_henkinEquiv_neg S T hT h h.neg (hrel hr hv hs' h))
  · intro n _
    have e : instFormula n ^⊤ (by simp) = ⊤ := by ext; simp [instFormula]
    apply to_code (hp := by simp)
    have h₁ := tprovable_henkinSatisfiesF_verum S T (assignment n) n
    rw [henkinEquiv, e, IsTable.transT_verum]
    cl_prover [h₁]
  · intro n _
    have e : instFormula n ^⊥ (by simp) = ⊥ := by ext; simp [instFormula]
    apply to_code (hp := by simp)
    have h₁ := tprovable_henkinSatisfiesF_falsum S T (assignment n) n
    rw [henkinEquiv, e, IsTable.transT_falsum]
    cl_prover [h₁]
  · intro n p q hp hq ihp ihq hs
    have hpq := Language.IsSemisentence.and_iff.mp (.of_shift_eq (n := n) (by simp [hp, hq]) hs)
    exact to_code <| tprovable_henkinEquiv_and S T hT hp hq (by simp [hp, hq])
      (of_code (ihp hpq.1.shift_eq)) (of_code (ihq hpq.2.shift_eq))
  · intro n p q hp hq ihp ihq hs
    have hpq := Language.IsSemisentence.or_iff.mp (.of_shift_eq (n := n) (by simp [hp, hq]) hs)
    exact to_code <| tprovable_henkinEquiv_or S T hT hp hq (by simp [hp, hq])
      (of_code (ihp hpq.1.shift_eq)) (of_code (ihq hpq.2.shift_eq))
  · intro n p hp ih hs
    have hs' : shift ℒₒᵣ p = p := by simpa [hp.isUFormula] using hs
    exact to_code <| tprovable_henkinEquiv_all S T hT hd (.of_shift_eq hp hs') (by simp [hp])
      (of_code (ih hs'))
  · intro n p hp ih hs
    have hs' : shift ℒₒᵣ p = p := by simpa [hp.isUFormula] using hs
    exact to_code <| tprovable_henkinEquiv_exs S T hT hd (.of_shift_eq hp hs') (by simp [hp])
      (of_code (ih hs'))

end truth

end FFL.FirstOrder.Arithmetic.Bootstrapping

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping FFL.Entailment

/-- In every model of $\mathsf{I}\Sigma_1$, along a table of the Henkin translation of `S`, every
axiom of `S` translates to a formula provable from `T` and the consistency of `S`.
- [Vis90, §6.2.2.1] -/
theorem provable_translate_henkinTranslation (S : ArithmeticTheory) [S.Δ₁]
    [Theory.Δ₁.Sentential S] [𝗘𝗤 ℒₒᵣ ⪯ S] (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔 ⪯ T]
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {tbl : V} (h : IsTableOf (henkinTranslation S T) tbl) {p : V} (hp : p ∈ S.Δ₁Class)
    (hf : IsFormula ℒₒᵣ p) : Provable (T ∪ S.Con) (translate ℒₒᵣ ℒₒᵣ tbl p) := by
  have hT : IsTable ℒₒᵣ ℒₒᵣ tbl := h.isTable Language.SymbolsStandard.oRing
  have h₁ : (T ∪ S.Con).internalize V ⊢ henkinEquiv S hT hf :=
    tprovable_iff_provable.mpr <| by
      rw [val_henkinEquiv]
      exact provable_henkinEquivCode S T hT (n := 0) (p := p)
        (Bootstrapping.Semiformula.ext h.domain)
        (fun R ↦ Bootstrapping.Semiformula.ext (h.rel R))
        (fun F ↦ Bootstrapping.Semiformula.ext (h.func F))
        (Theory.Δ₁.Sentential.forall_isSentence (V := V) S p hp)
  have h₂ := tprovable_henkinListF_zero S T (V := V) (assignment 0)
  have h₃ := tprovable_henkinSatisfiesF_axiom S T (assignment (0 : V)) hp hf
  have e : instFormula 0 p hf = ⟨p, hf⟩ := by
    ext; simp [instFormula, subst_eq_self hf (w := 0) (by simp) (by simp)]
  rw [henkinEquiv, e] at h₁
  have h₄ : (T ∪ S.Con).internalize V ⊢ hT.transT ⟨p, hf⟩ := by cl_prover [h₁, h₂, h₃]
  simpa using tprovable_iff_provable.mp h₄

end FFL.FirstOrder.Arithmetic
