module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Bootstrapping.InternalTSchema
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.Prenex

/-!
# Disjunctions of internal prenex sentences

`prenexSatDef Γ n` is the standard formula saying that a code `p` of a bounded formula is satisfied
under the assignment `a` extended by `n` alternating quantifiers starting with polarity `Γ`. Over a
theory containing $\mathsf{I}\Sigma_1$, every internal prenex $\Gamma_n$ formula is internally
equivalent to `prenexSatDef Γ n` at the code of its matrix, and `prenexSatDef Γ (n + 1)` is
equivalent in every model of $\mathsf{I}\Sigma_1$ to a prenex $\Gamma_{n + 1}$ formula. Hence the
disjunction of two internal prenex $\Gamma_n$ sentences is internally equivalent to an internal
prenex $\Gamma_n$ sentence.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

noncomputable def prenexSatDef : Polarity → ℕ → ArithmeticSemisentence 2
  | _, 0 => psatDef.val
  | 𝚺, n + 1 => “a p. ∃ x, !(prenexSatDef 𝚷 n) ((x + a) * (x + a) + a + 1) p”
  | 𝚷, n + 1 => “a p. ∀ x, !(prenexSatDef 𝚺 n) ((x + a) * (x + a) + a + 1) p”

open Bootstrapping in
noncomputable def prenexSatPiOneDef : ArithmeticSemisentence 2 :=
  “a p. ∀ x, ∀ s, !decGraph s ((x + a) * (x + a) + a + 1) → !boundedSatisfied.pi s p”

section

open Bootstrapping

variable {W : Type} [ORingStructure W]

@[simp] lemma eval_prenexSatDef_zero [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (Γ : Polarity) (e : Fin 2 → W) :
    W ⊧/e (prenexSatDef Γ 0) ↔ BoundedSatisfied (dec (e 0)) (e 1) := by
  simp [prenexSatDef]

@[simp] lemma eval_prenexSatDef_sigma (n : ℕ) (e : Fin 2 → W) :
    W ⊧/e (prenexSatDef .sigma (n + 1)) ↔
      ∃ x, W ⊧/![(x + e 0) * (x + e 0) + e 0 + 1, e 1] (prenexSatDef .pi n) := by
  simp [prenexSatDef]

@[simp] lemma eval_prenexSatDef_pi (n : ℕ) (e : Fin 2 → W) :
    W ⊧/e (prenexSatDef .pi (n + 1)) ↔
      ∀ x, W ⊧/![(x + e 0) * (x + e 0) + e 0 + 1, e 1] (prenexSatDef .sigma n) := by
  simp [prenexSatDef]

lemma eval_prenexSatPiOneDef [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin 2 → W) :
    W ⊧/e prenexSatPiOneDef ↔ W ⊧/e (prenexSatDef .pi 1) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, eval_prenexSatDef_pi]
  simp [prenexSatPiOneDef]

end

lemma exists_prenex_eval_iff_prenexSatDef :
    ∀ (Γ : Polarity) (n : ℕ), ∃ G : ℬ[<, ℒₒᵣ].Prenex Γ (n + 1) Empty 2,
      ∀ (W : Type) [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin 2 → W),
        W ⊧/e G.val ↔ W ⊧/e (prenexSatDef Γ (n + 1))
  | .sigma, 0 => by
    obtain ⟨G, hG⟩ := exists_prenex_of_hierarchy 𝗜𝚺₁ (Γ := 𝚺) (s := 1) (φ := prenexSatDef .sigma 1)
      (by simp [prenexSatDef]);
    use (discharger := skip) G;
    intro W _ _ e;
    have := models_of_provable (M := W) inferInstance hG;
    have h := (Semiformula.eval_allClosure (b := ![]) (f := Empty.elim)).mp this e;
    rw [LogicalConnective.HomClass.map_iff] at h;
    exact Iff.intro h.2 h.1
  | .pi, 0 => by
    obtain ⟨G, hG⟩ := exists_prenex_of_hierarchy 𝗜𝚺₁ (Γ := 𝚷) (s := 1) (φ := prenexSatPiOneDef)
      (by simp [prenexSatPiOneDef]);
    use (discharger := skip) G;
    intro W _ _ e;
    have := models_of_provable (M := W) inferInstance hG;
    have h := (Semiformula.eval_allClosure (b := ![]) (f := Empty.elim)).mp this e;
    rw [LogicalConnective.HomClass.map_iff] at h;
    exact (Iff.intro h.2 h.1).trans (eval_prenexSatPiOneDef e)
  | .sigma, n + 1 => by
    obtain ⟨G, hG⟩ := exists_prenex_eval_iff_prenexSatDef .pi n;
    use (discharger := skip) (G.rew (Rew.subst ![‘(#0 + #1) * (#0 + #1) + #1 + 1’, #2])).sigma;
    intro W _ _ e;
    rw [eval_prenexSatDef_sigma];
    simp only [Bounding.Prenex.val_sigma, Bounding.Prenex.val_rew, Semiformula.eval_ex,
      Semiformula.eval_rew, ← hG]
    apply exists_congr
    intro x
    apply iff_of_eq
    congr 2
    funext i
    cases i using Fin.cases <;> simp
  | .pi, n + 1 => by
    obtain ⟨G, hG⟩ := exists_prenex_eval_iff_prenexSatDef .sigma n;
    use (discharger := skip) (G.rew (Rew.subst ![‘(#0 + #1) * (#0 + #1) + #1 + 1’, #2])).pi;
    intro W _ _ e;
    rw [eval_prenexSatDef_pi];
    simp only [Bounding.Prenex.val_pi, Bounding.Prenex.val_rew, Semiformula.eval_all,
      Semiformula.eval_rew, ← hG]
    apply forall_congr'
    intro x
    apply iff_of_eq
    congr 2
    funext i
    cases i using Fin.cases <;> simp

lemma exists_prenex_eval_iff_or_prenexSatDef (Γ : Polarity) (n : ℕ) :
    ∃ F : ℬ[<, ℒₒᵣ].Prenex Γ (n + 1) Empty 3,
      ∀ (W : Type) [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin 3 → W),
        W ⊧/e (((Rew.subst ![#2, #0] ▹ prenexSatDef Γ (n + 1)) ⋎
          (Rew.subst ![#2, #1] ▹ prenexSatDef Γ (n + 1))) 🡘 F.val) := by
  obtain ⟨G, hG⟩ := exists_prenex_eval_iff_prenexSatDef Γ n;
  use (discharger := skip)
    Bounding.Prenex.pairOr (G.rew (Rew.subst ![#2, #0])) (G.rew (Rew.subst ![#2, #1]));
  intro W _ _ e;
  have hG' (b : Fin 2 → W) (f : Empty → W) :
      Semiformula.Eval b f G.val ↔ Semiformula.Eval b f (prenexSatDef Γ (n + 1)) := by
    obtain rfl : f = Empty.elim := funext fun x ↦ x.elim;
    exact hG W b;
  simp only [LogicalConnective.HomClass.map_iff, LogicalConnective.HomClass.map_or,
    Semiformula.eval_rew, Bounding.Prenex.eval_pairOr, Bounding.Prenex.val_rew, hG',
    LogicalConnective.Prop.iff_eq, LogicalConnective.Prop.or_eq]

namespace Bootstrapping

open FirstOrder FFL.Entailment Bootstrapping.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma quote_prenexSatDef_sigma_subst (n : ℕ) (a : Term V ℒₒᵣ) (p : V) :
    (⌜prenexSatDef .sigma (n + 1)⌝ : Semiformula V ℒₒᵣ 2).subst ![a, 𝕹 p] =
      ∃¹ (⌜prenexSatDef .pi n⌝ : Semiformula V ℒₒᵣ 2).subst
        ![pTerm (Semiterm.bvar 0) a.bShift, 𝕹 p] := by
  simp [prenexSatDef, pTerm, typed_quote_rew_subst, Semiformula.substs_substs, SemitermVec.q,
    Matrix.vecHead, Matrix.vecTail]

lemma quote_prenexSatDef_pi_subst (n : ℕ) (a : Term V ℒₒᵣ) (p : V) :
    (⌜prenexSatDef .pi (n + 1)⌝ : Semiformula V ℒₒᵣ 2).subst ![a, 𝕹 p] =
      ∀¹ (⌜prenexSatDef .sigma n⌝ : Semiformula V ℒₒᵣ 2).subst
        ![pTerm (Semiterm.bvar 0) a.bShift, 𝕹 p] := by
  simp [prenexSatDef, pTerm, typed_quote_rew_subst, Semiformula.substs_substs, SemitermVec.q,
    Matrix.vecHead, Matrix.vecTail]

lemma free_quote_prenexSatDef_subst (Γ : Polarity) (n : ℕ) (k p : V) :
    ((⌜prenexSatDef Γ n⌝ : Semiformula V ℒₒᵣ 2).subst
        ![pTerm (Semiterm.bvar 0) (assignment k).bShift, 𝕹 p]).free =
      (⌜prenexSatDef Γ n⌝ : Semiformula V ℒₒᵣ 2).subst ![assignment (k + 1), 𝕹 p] := by
  simp [Semiformula.free, Semiformula.shift_substs, Semiformula.substs_substs, assignment_succ,
    typed_quote_shift, ← Semiterm.bShift_shift_comm]

variable {T : ArithmeticTheory} [T.Δ₁]

lemma TProof.exs_imp_exs_of_free {φ ψ : Semiformula V ℒₒᵣ 1}
    (h : T.internalize V ⊢ φ.free 🡒 ψ.free) : T.internalize V ⊢ ∃¹ φ 🡒 ∃¹ ψ := by
  apply TProof.exs_imp_of_free;
  have h' := TProof.subst_imp_exs (T := T) ψ.shift (Semiterm.fvar 0);
  rw [Semiformula.shift_exs];
  have e : ψ.free = ψ.shift.subst ![Semiterm.fvar 0] := rfl;
  rw [← e] at h';
  cl_prover [h, h']

variable [𝗜𝚺₁ ⪯ T]

lemma tprovable_instFormula_qqToPrenex_iff (Γ : Polarity) (n : ℕ) {θ : V} (hθ : IsBounded θ)
    (k : V) (hk : Language.IsFVFree ℒₒᵣ (k + n) θ) :
    T.internalize V ⊢ instFormula k (qqToPrenex Γ n θ)
        (isSemiformula_qqToPrenex.mpr hk.isSemiformula) 🡘
      (⌜prenexSatDef Γ n⌝ : Semiformula V ℒₒᵣ 2).subst ![assignment k, 𝕹 θ] := by
  induction n generalizing Γ k with
  | zero =>
    have h := (tprovable_instFormula_iff (T := T) (by simpa using hk.isSemiformula)).mpr <|
      provable_iff_psat_of_isBounded (T := T) (k + θ) θ hθ k le_self_add le_rfl
        (by simpa using hk.isSemiformula) hk.shift_eq;
    simpa [prenexSatDef, psatF] using h
  | succ n ih =>
    have hk' : Language.IsFVFree ℒₒᵣ ((k + 1 : V) + (n : V)) θ := by
      simpa [add_assoc, add_comm (1 : V)] using hk;
    have hq : IsSemiformula ℒₒᵣ (k + 1) (qqToPrenex Γ.alt n θ) :=
      isSemiformula_qqToPrenex.mpr hk'.isSemiformula;
    have hqs : shift ℒₒᵣ (qqToPrenex Γ.alt n θ) = qqToPrenex Γ.alt n θ := by
      rw [shift_qqToPrenex hk'.isSemiformula.isUFormula, hk'.shift_eq];
    let L : Semiformula V ℒₒᵣ 1 :=
      ⟨subst ℒₒᵣ (qVec ℒₒᵣ (fvarVec k)) (qqToPrenex Γ.alt n θ),
        hq.subst (isSemitermVec_fvarVec k 0).qVec⟩;
    have hL : L.free = instFormula (k + 1) (qqToPrenex Γ.alt n θ) hq := by
      ext; simp [L, instFormula, free_subst_qVec_fvarVec hq hqs];
    have ih' := ih Γ.alt (k + 1) hk';
    rw [← hL, ← free_quote_prenexSatDef_subst] at ih';
    cases Γ
    · have e : ∀ h, instFormula k (qqToPrenex .sigma (n + 1) θ) h = ∃¹ L := by
        intro h; ext; simp [L, instFormula, hk'.isSemiformula.isUFormula];
      rw [e, quote_prenexSatDef_sigma_subst];
      have h₁ := TProof.exs_imp_exs_of_free (T := T) (K_left ih');
      have h₂ := TProof.exs_imp_exs_of_free (T := T) (K_right ih');
      cl_prover [h₁, h₂]
    · have e : ∀ h, instFormula k (qqToPrenex .pi (n + 1) θ) h = ∀¹ L := by
        intro h; ext; simp [L, instFormula, hk'.isSemiformula.isUFormula];
      rw [e, quote_prenexSatDef_pi_subst];
      have h₁ := TProof.all_imp_all_of_free (T := T) (K_left ih');
      have h₂ := TProof.all_imp_all_of_free (T := T) (K_right ih');
      cl_prover [h₁, h₂]

lemma tprovable_iff_prenexSatDef {Γ : Polarity} {n : ℕ} {φ : Formula V ℒₒᵣ} {θ : V}
    (hφs : φ.shift = φ) (hθ : φ.val = qqToPrenex Γ n θ) (hθb : IsBounded θ) :
    T.internalize V ⊢ φ 🡘 (⌜prenexSatDef Γ n⌝ : Semiformula V ℒₒᵣ 2).subst ![𝕹 0, 𝕹 θ] := by
  have hk : IsSemiformula ℒₒᵣ ((0 : V) + n) θ := by
    simpa [hθ] using φ.isSemiformula;
  have hsh : shift ℒₒᵣ θ = θ := by
    have := congrArg (·.val) hφs;
    simpa [hθ, shift_qqToPrenex hk.isUFormula] using this;
  have h := tprovable_instFormula_qqToPrenex_iff (T := T) Γ n hθb 0 ⟨hk, hsh⟩;
  have e : instFormula 0 (qqToPrenex Γ n θ) (isSemiformula_qqToPrenex.mpr hk) = φ := by
    have e₁ : instFormula 0 (qqToPrenex Γ n θ) (isSemiformula_qqToPrenex.mpr hk) =
        φ.subst (![] : SemitermVec V ℒₒᵣ 0 0) := by
      ext; simp [instFormula, hθ, -Semiformula.subst_nil_eq_self];
    rw [e₁, Semiformula.subst_nil_eq_self];
  rwa [e, assignment_zero] at h

/-- The disjunction of two internal prenex $\Gamma_n$ sentences is internally equivalent to an
internal prenex $\Gamma_n$ sentence. -/
theorem exists_isPrenexHierarchy_tprovable_or_iff {Γ : Polarity} {n : ℕ}
    {φ ψ : Formula V ℒₒᵣ} (hφs : φ.shift = φ) (hψs : ψ.shift = ψ)
    (hφ : IsPrenexHierarchy Γ n φ.val) (hψ : IsPrenexHierarchy Γ n ψ.val) :
    ∃ χ : Formula V ℒₒᵣ, χ.shift = χ ∧ IsPrenexHierarchy Γ n χ.val ∧
      T.internalize V ⊢ φ ⋎ ψ 🡘 χ := by
  cases n with
  | zero =>
    use (discharger := skip) φ ⋎ ψ;
    and_intros;
    · simp [hφs, hψs];
    · simpa [IsPrenexHierarchy] using IsBounded.or_iff.mpr ⟨hφ, hψ⟩;
    · cl_prover;
  | succ n =>
    obtain ⟨θ, hθ, hθb⟩ := isPrenexHierarchy_iff_exists_qqToPrenex.mp hφ;
    obtain ⟨η, hη, hηb⟩ := isPrenexHierarchy_iff_exists_qqToPrenex.mp hψ;
    obtain ⟨F, hF⟩ := exists_prenex_eval_iff_or_prenexSatDef Γ n;
    use (discharger := skip) (⌜F.val⌝ : Semiformula V ℒₒᵣ 3).subst ![𝕹 θ, 𝕹 η, 𝕹 0];
    and_intros;
    · simp [Semiformula.shift_substs, typed_quote_shift];
    · have hF := (isPrenexHierarchy_quote_iff (V := V) F.val).mpr
        Bounding.Prenex.val_prenexHierarchy;
      simpa [Sentence.quote_eq] using IsPrenexHierarchy.subst
        (SemitermVec.isSemitermVec (![𝕹 θ, 𝕹 η, 𝕹 0] : SemitermVec V ℒₒᵣ 3 0))
        (Sentence.quote_isSemiformula F.val) hF;
    · have h₁ := tprovable_iff_prenexSatDef (T := T) hφs hθ hθb;
      have h₂ := tprovable_iff_prenexSatDef (T := T) hψs hη hηb;
      have h₃ : T.internalize V ⊢
          (⌜prenexSatDef Γ (n + 1)⌝ : Semiformula V ℒₒᵣ 2).subst ![𝕹 0, 𝕹 θ] ⋎
            (⌜prenexSatDef Γ (n + 1)⌝ : Semiformula V ℒₒᵣ 2).subst ![𝕹 0, 𝕹 η] 🡘
          (⌜F.val⌝ : Semiformula V ℒₒᵣ 3).subst ![𝕹 θ, 𝕹 η, 𝕹 0] := by
        simpa [typed_quote_rew_subst, Semiformula.substs_substs, Matrix.vecHead,
          Matrix.vecTail] using
          tprovable_subst_of_models (T := T) (fun W _ _ e ↦ hF W e) ![𝕹 θ, 𝕹 η, 𝕹 0];
      cl_prover [h₁, h₂, h₃]

end Bootstrapping
end FFL.FirstOrder.Arithmetic

end
