module

public import AlphaCentauri.InterpretabilityLogic.Verbrugge.Basic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Fintype.Powerset

/-!
# w-bisimulations between generalised Veltman models

w-bisimulations and their finite approximations, $n$-w-bisimulations, between generalised Veltman
models. w-bisimilar worlds force the same formulas, $n$-w-bisimilar worlds force the same formulas
of modal depth at most $n$, and over finitely many propositional variables the converse of the
latter holds.

## References

- [HPV23]
-/

@[expose] public section

namespace FFL.InterpretabilityLogic.Verbrugge.Model

open World

variable {κ κ' α : Type*} [Nonempty κ] [Nonempty κ'] {M : Model κ α} {N : Model κ' α}
  {Z₁ Z₀ : M.World → N.World → Prop} {x : M.World} {y : N.World} {A B : Formula α}

variable (M N) in
/-- The w-forth condition from `Z₁` to `Z₀`: for every `≺`-successor `u` of `x` and every
`Z₁`-related `y`, there is a nonempty set `U` of `≺`-successors of `y`, each `Z₀`-related to `u`,
such that whenever every `u' ∈ U` is given some $u' \mathrel{≺[y]} V'(u')$, some
$u \mathrel{≺[x]} V$ has every element `Z₀`-related to an element of $\bigcup_{u' ∈ U} V'(u')$.

- [HPV23, Definition 2.7, Definition 3.1]
-/
def WForth (Z₁ Z₀ : M.World → N.World → Prop) : Prop :=
  ∀ {x : M.World} {y : N.World} {u : M.World}, Z₁ x y → x ≺ u →
    ∃ U : Set N.World, U.Nonempty ∧ (∀ u' ∈ U, y ≺ u' ∧ Z₀ u u') ∧
      ∀ V' : N.World → Set N.World, (∀ u' ∈ U, u' ≺[y] V' u') →
        ∃ V, u ≺[x] V ∧ ∀ v ∈ V, ∃ u' ∈ U, ∃ v' ∈ V' u', Z₀ v v'

namespace WForth

variable (hZ : WForth M N Z₁ Z₀) (h : Z₁ x y)
include hZ h

lemma forces_box (hA : ∀ u u', Z₀ u u' → (u ⊩[M] A ↔ u' ⊩[N] A)) (hy : y ⊩[N] □A) :
    x ⊩[M] □A := by
  intro u Rxu;
  obtain ⟨U, ⟨u', hu'⟩, hU, -⟩ := hZ h Rxu;
  exact (hA _ _ (hU u' hu').2).mpr <| hy u' (hU u' hu').1;

lemma forces_rhd (hA : ∀ u u', Z₀ u u' → (u ⊩[M] A ↔ u' ⊩[N] A))
    (hB : ∀ v v', Z₀ v v' → (v ⊩[M] B ↔ v' ⊩[N] B)) (hy : y ⊩[N] A ▷ B) : x ⊩[M] A ▷ B := by
  intro u Rxu hu;
  obtain ⟨U, -, hU, hV⟩ := hZ h Rxu;
  choose! V' SV' hV' using fun u' hu' ↦ hy u' (hU u' hu').1 <| (hA _ _ (hU u' hu').2).mp hu;
  obtain ⟨V, SuV, hV⟩ := hV V' SV';
  use V;
  and_intros;
  · exact SuV;
  · intro v hv;
    obtain ⟨u', hu', v', hv', Zvv'⟩ := hV v hv;
    exact (hB _ _ Zvv').mpr <| hV' u' hu' v' hv';

end WForth

variable (M N) in
/-- A w-bisimulation: a relation between worlds that preserves atoms and satisfies the w-forth
and the w-back conditions.

- [HPV23, Definition 2.7]
-/
structure WBisimulation where
  toRel : M.World → N.World → Prop
  atomic {x : M.World} {y : N.World} {a : α} : toRel x y → (M x a ↔ N y a)
  forth : WForth M N toRel toRel
  back : WForth N M (flip toRel) (flip toRel)

instance : CoeFun (WBisimulation M N) fun _ ↦ M.World → N.World → Prop :=
  ⟨WBisimulation.toRel⟩

/-- w-bisimilar worlds force the same formulas.

- [HPV23, Proposition 2.8(a)]
-/
theorem WBisimulation.forces_iff (Z : WBisimulation M N) (h : Z x y) : x ⊩[M] A ↔ y ⊩[N] A := by
  induction A generalizing x y with
  | atom a => exact Z.atomic h;
  | falsum => rfl;
  | imp A B ihA ihB => exact imp_congr (ihA h) (ihB h);
  | box A ih =>
    constructor;
    · exact WForth.forces_box Z.back h fun _ _ h ↦ (ih h).symm;
    · exact WForth.forces_box Z.forth h fun _ _ h ↦ ih h;
  | rhd A B ihA ihB =>
    constructor;
    · exact WForth.forces_rhd Z.back h (fun _ _ h ↦ (ihA h).symm) fun _ _ h ↦ (ihB h).symm;
    · exact WForth.forces_rhd Z.forth h (fun _ _ h ↦ ihA h) fun _ _ h ↦ ihB h;

variable (M N) in
/-- An $n$-w-bisimulation: a sequence $Z_n ⊆ ⋯ ⊆ Z_0$ of relations between worlds such that
$Z_0$ preserves atoms and each $Z_{i + 1}$ satisfies the w-forth and the w-back conditions with
respect to $Z_i$.

- [HPV23, Definition 3.1]
-/
structure NWBisimulation (n : ℕ) where
  toRel : ℕ → M.World → N.World → Prop
  antitone {i : ℕ} {x : M.World} {y : N.World} : i < n → toRel (i + 1) x y → toRel i x y
  atomic {x : M.World} {y : N.World} {a : α} : toRel 0 x y → (M x a ↔ N y a)
  forth {i : ℕ} : i < n → WForth M N (toRel (i + 1)) (toRel i)
  back {i : ℕ} : i < n → WForth N M (flip (toRel (i + 1))) (flip (toRel i))

namespace NWBisimulation

variable {n i : ℕ} (Z : NWBisimulation M N n)

lemma toRel_zero (hi : i ≤ n) (h : Z.toRel i x y) : Z.toRel 0 x y := by
  induction i with
  | zero => exact h;
  | succ i ih => exact ih (by omega) <| Z.antitone (by omega) h;

/-- Worlds related by $Z_i$ in an $n$-w-bisimulation, $i ≤ n$, force the same formulas of modal
depth at most $i$.

- [HPV23, Proposition 3.2]
-/
theorem forces_iff (hi : i ≤ n) (h : Z.toRel i x y) (hA : A.depth ≤ i) :
    x ⊩[M] A ↔ y ⊩[N] A := by
  induction A generalizing i x y with
  | atom a => exact Z.atomic <| Z.toRel_zero hi h;
  | falsum => rfl;
  | imp A B ihA ihB =>
    simp only [Formula.depth_imp, max_le_iff] at hA;
    exact imp_congr (ihA hi h hA.1) (ihB hi h hA.2);
  | box A ih =>
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by simp at hA; omega⟩;
    have ih' {u : M.World} {u' : N.World} (h : Z.toRel j u u') : u ⊩[M] A ↔ u' ⊩[N] A :=
      ih (by omega) h (by simpa using hA);
    constructor;
    · exact WForth.forces_box (Z.back (i := j) (by omega)) h fun _ _ h ↦ (ih' h).symm;
    · exact WForth.forces_box (Z.forth (i := j) (by omega)) h fun _ _ h ↦ ih' h;
  | rhd A B ihA ihB =>
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by simp at hA; omega⟩;
    simp only [Formula.depth_rhd, add_le_add_iff_right, max_le_iff] at hA;
    have ihA' {u : M.World} {u' : N.World} (h : Z.toRel j u u') : u ⊩[M] A ↔ u' ⊩[N] A :=
      ihA (by omega) h hA.1;
    have ihB' {u : M.World} {u' : N.World} (h : Z.toRel j u u') : u ⊩[M] B ↔ u' ⊩[N] B :=
      ihB (by omega) h hA.2;
    constructor;
    · exact WForth.forces_rhd (Z.back (i := j) (by omega)) h (fun _ _ h ↦ (ihA' h).symm)
        fun _ _ h ↦ (ihB' h).symm;
    · exact WForth.forces_rhd (Z.forth (i := j) (by omega)) h (fun _ _ h ↦ ihA' h)
        fun _ _ h ↦ ihB' h;

end NWBisimulation

variable (M N) in
/-- `x` and `y` are $n$-w-bisimilar: some $n$-w-bisimulation relates them by $Z_n$.

- [HPV23, Definition 3.1]
-/
def NWBisimilar (n : ℕ) (x : M.World) (y : N.World) : Prop :=
  ∃ Z : NWBisimulation M N n, Z.toRel n x y

variable (M N) in
/-- `x` and `y` are $n$-modally equivalent: they force the same formulas of modal depth at most
$n$.

- [HPV23, §2]
-/
def ModalEquivalent (n : ℕ) (x : M.World) (y : N.World) : Prop :=
  ∀ A : Formula α, A.depth ≤ n → (x ⊩[M] A ↔ y ⊩[N] A)

lemma flip_modalEquivalent {n : ℕ} : flip (ModalEquivalent M N n) = ModalEquivalent N M n := by
  ext y x;
  exact forall_congr' fun _ ↦ imp_congr_right fun _ ↦ Iff.comm;

/-! ### Definable sets of worlds in a disjoint union of two models -/

section Definable

variable (M N) in
private def SumForces : M.World ⊕ N.World → Formula α → Prop
  | .inl x, A => x ⊩[M] A
  | .inr y, A => y ⊩[N] A

variable {z : M.World ⊕ N.World}

private lemma sumForces_bot : ¬SumForces M N z ⊥ := by cases z <;> exact id;

private lemma sumForces_imp :
    SumForces M N z (A 🡒 B) ↔ (SumForces M N z A → SumForces M N z B) := by
  cases z <;> rfl;

private lemma sumForces_neg : SumForces M N z (∼A) ↔ ¬SumForces M N z A := by cases z <;> rfl;

private lemma sumForces_and :
    SumForces M N z (A ⋏ B) ↔ SumForces M N z A ∧ SumForces M N z B := by
  cases z <;> exact forces_and;

private lemma sumForces_or :
    SumForces M N z (A ⋎ B) ↔ SumForces M N z A ∨ SumForces M N z B := by
  cases z <;> exact forces_or;

private lemma sumForces_box_congr {A' : Formula α}
    (hA : ∀ w, SumForces M N w A ↔ SumForces M N w A') :
    SumForces M N z (□A) ↔ SumForces M N z (□A') := by
  cases z with
  | inl x => exact forall_congr' fun y ↦ imp_congr_right fun _ ↦ hA (.inl y);
  | inr x => exact forall_congr' fun y ↦ imp_congr_right fun _ ↦ hA (.inr y);

private lemma sumForces_rhd_congr {A' B' : Formula α}
    (hA : ∀ w, SumForces M N w A ↔ SumForces M N w A')
    (hB : ∀ w, SumForces M N w B ↔ SumForces M N w B') :
    SumForces M N z (A ▷ B) ↔ SumForces M N z (A' ▷ B') := by
  cases z with
  | inl x =>
    have hA' (y : M.World) : y ⊩[M] A ↔ y ⊩[M] A' := hA (.inl y);
    have hB' (y : M.World) : y ⊩[M] B ↔ y ⊩[M] B' := hB (.inl y);
    simp only [SumForces, forces_rhd, hA', hB'];
  | inr x =>
    have hA' (y : N.World) : y ⊩[N] A ↔ y ⊩[N] A' := hA (.inr y);
    have hB' (y : N.World) : y ⊩[N] B ↔ y ⊩[N] B' := hB (.inr y);
    simp only [SumForces, forces_rhd, hA', hB'];

variable (M N) in
private def Definable (n : ℕ) (S : Set (M.World ⊕ N.World)) : Prop :=
  ∃ A : Formula α, A.depth ≤ n ∧ ∀ z, z ∈ S ↔ SumForces M N z A

variable {n : ℕ} {S T : Set (M.World ⊕ N.World)} {𝒮 : Set (Set (M.World ⊕ N.World))}

private lemma Definable.inter (hS : Definable M N n S) (hT : Definable M N n T) :
    Definable M N n (S ∩ T) := by
  obtain ⟨A, hA, hS⟩ := hS;
  obtain ⟨B, hB, hT⟩ := hT;
  use A ⋏ B;
  and_intros;
  · simpa using ⟨hA, hB⟩;
  · intro z;
    simp [sumForces_and, hS, hT];

private lemma Definable.union (hS : Definable M N n S) (hT : Definable M N n T) :
    Definable M N n (S ∪ T) := by
  obtain ⟨A, hA, hS⟩ := hS;
  obtain ⟨B, hB, hT⟩ := hT;
  use A ⋎ B;
  and_intros;
  · simpa using ⟨hA, hB⟩;
  · intro z;
    simp [sumForces_or, hS, hT];

private lemma Definable.sInter (h𝒮 : 𝒮.Finite) (hS : ∀ S ∈ 𝒮, Definable M N n S) :
    Definable M N n (⋂₀ 𝒮) := by
  induction 𝒮, h𝒮 using Set.Finite.induction_on with
  | empty =>
    use ⊤;
    and_intros;
    · simp;
    · intro z;
      exact iff_of_true (by simp) <| sumForces_imp.mpr id;
  | insert _ _ ih =>
    rw [Set.sInter_insert];
    exact (hS _ <| Set.mem_insert _ _).inter <| ih fun S hS' ↦ hS S <| Set.mem_insert_of_mem _ hS';

private lemma Definable.sUnion (h𝒮 : 𝒮.Finite) (hS : ∀ S ∈ 𝒮, Definable M N n S) :
    Definable M N n (⋃₀ 𝒮) := by
  induction 𝒮, h𝒮 using Set.Finite.induction_on with
  | empty =>
    use ⊥;
    and_intros;
    · simp;
    · intro z;
      exact iff_of_false (by simp) sumForces_bot;
  | insert _ _ ih =>
    rw [Set.sUnion_insert];
    exact (hS _ <| Set.mem_insert _ _).union <| ih fun S hS' ↦ hS S <| Set.mem_insert_of_mem _ hS';

/-- If worlds with the same value of `σ` force the same formulas of modal depth at most `n`, then
there are at most as many sets definable by such formulas as there are sets of values of `σ`. -/
private lemma finite_definable_of_invariant {β : Type*} [Finite β] (σ : M.World ⊕ N.World → β)
    (hσ : ∀ A : Formula α, A.depth ≤ n → ∀ z z', σ z = σ z' →
      (SumForces M N z A ↔ SumForces M N z' A)) :
    {S | Definable M N n S}.Finite := by
  have sub {S T} (hT : Definable M N n T) (hST : σ '' S ⊆ σ '' T) : S ⊆ T := by
    obtain ⟨B, hB, hT⟩ := hT;
    intro z hz;
    obtain ⟨t, ht, htz⟩ := hST ⟨z, hz, rfl⟩;
    exact (hT z).mpr <| (hσ B hB t z htz).mp <| (hT t).mp ht;
  apply Set.Finite.of_finite_image (f := (σ '' ·)) (Set.toFinite _);
  intro S hS T hT hST;
  exact Set.Subset.antisymm (sub hT hST.le) (sub hS hST.ge);

/-- Over finitely many propositional variables, finitely many sets of worlds are definable by
formulas of modal depth at most `n`. -/
private lemma finite_definable [Finite α] (n : ℕ) : {S | Definable M N n S}.Finite := by
  induction n with
  | zero =>
    apply finite_definable_of_invariant fun z ↦ {a : α | SumForces M N z (#a)};
    intro A hA z z' hz;
    induction A with
    | atom a => exact Set.ext_iff.mp hz a;
    | falsum => exact iff_of_false sumForces_bot sumForces_bot;
    | imp A B ihA ihB =>
      simp only [Formula.depth_imp, nonpos_iff_eq_zero, Nat.max_eq_zero_iff] at hA;
      simp only [sumForces_imp, ihA hA.1.le, ihB hA.2.le];
    | box A => simp at hA;
    | rhd A B => simp at hA;
  | succ n ih =>
    have := ih.to_subtype;
    let rep (S : {S | Definable M N n S}) : Formula α := S.2.choose;
    have hrep (S : {S | Definable M N n S}) (z) : z ∈ S.1 ↔ SumForces M N z (rep S) :=
      S.2.choose_spec.2 z;
    apply finite_definable_of_invariant fun z ↦
      ({a : α | SumForces M N z (#a)},
       {S : {S | Definable M N n S} | SumForces M N z (□rep S)},
       {p : {S | Definable M N n S} × {S | Definable M N n S} |
          SumForces M N z (rep p.1 ▷ rep p.2)});
    intro A hA z z' hz;
    simp only [Prod.mk.injEq] at hz;
    obtain ⟨hatom, hbox, hrhd⟩ := hz;
    have hdef {B : Formula α} (hB : B.depth ≤ n) : Definable M N n {w | SumForces M N w B} :=
      ⟨B, hB, fun _ ↦ Iff.rfl⟩;
    induction A with
    | atom a => exact Set.ext_iff.mp hatom a;
    | falsum => exact iff_of_false sumForces_bot sumForces_bot;
    | imp A B ihA ihB =>
      simp only [Formula.depth_imp, max_le_iff] at hA;
      simp only [sumForces_imp, ihA hA.1, ihB hA.2];
    | box A =>
      have hS := hrep ⟨_, hdef (B := A) (by simpa using hA)⟩;
      rw [sumForces_box_congr hS, sumForces_box_congr hS];
      exact Set.ext_iff.mp hbox _;
    | rhd A B =>
      simp only [Formula.depth_rhd, add_le_add_iff_right, max_le_iff] at hA;
      have hS := hrep ⟨_, hdef hA.1⟩;
      have hT := hrep ⟨_, hdef hA.2⟩;
      rw [sumForces_rhd_congr hS hT, sumForces_rhd_congr hS hT];
      exact Set.ext_iff.mp hrhd (_, _);

variable (M N) in
private def SumModalEquivalent (n : ℕ) (z w : M.World ⊕ N.World) : Prop :=
  ∀ A : Formula α, A.depth ≤ n → (SumForces M N z A ↔ SumForces M N w A)

private lemma definable_modalEquivalent_class [Finite α] (n : ℕ) (u : M.World ⊕ N.World) :
    Definable M N n {z | SumModalEquivalent M N n z u} := by
  have : {z | SumModalEquivalent M N n z u} = ⋂₀ {S | Definable M N n S ∧ u ∈ S} := by
    ext z;
    simp only [Set.mem_ofPred_eq, Set.mem_sInter, and_imp];
    constructor;
    · rintro hz S ⟨A, hA, hS⟩ hu;
      exact (hS z).mpr <| (hz A hA).mpr <| (hS u).mp hu;
    · intro hz A hA;
      by_cases hu : SumForces M N u A;
      · exact iff_of_true (hz _ ⟨A, hA, fun _ ↦ Iff.rfl⟩ hu) hu;
      · apply iff_of_false _ hu;
        exact hz {w | ¬SumForces M N w A} ⟨∼A, by simpa, fun _ ↦ sumForces_neg.symm⟩ hu;
  rw [this];
  exact Definable.sInter ((finite_definable n).subset fun _ h ↦ h.1) fun _ h ↦ h.1;

private lemma definable_modalEquivalent_union [Finite α] (n : ℕ) (C : Set (M.World ⊕ N.World)) :
    Definable M N n {z | ∃ c ∈ C, SumModalEquivalent M N n z c} := by
  have : {z | ∃ c ∈ C, SumModalEquivalent M N n z c} =
      ⋃₀ ((fun c ↦ {z | SumModalEquivalent M N n z c}) '' C) := by
    ext z;
    simp;
  rw [this];
  have hC : ∀ S ∈ (fun c ↦ {z | SumModalEquivalent M N n z c}) '' C, Definable M N n S := by
    rintro _ ⟨c, -, rfl⟩;
    exact definable_modalEquivalent_class n c;
  exact Definable.sUnion ((finite_definable n).subset hC) hC;

/-- Over finitely many propositional variables, $(n + 1)$-modal equivalence satisfies the w-forth
condition with respect to $n$-modal equivalence.

- [HPV23, Theorem 4.3, Remark 3.3]
-/
lemma wForth_modalEquivalent [Finite α] (n : ℕ) :
    WForth M N (ModalEquivalent M N (n + 1)) (ModalEquivalent M N n) := by
  intro x y u h Rxu;
  obtain ⟨χ, hχ, hχu⟩ := definable_modalEquivalent_class (M := M) (N := N) n (.inl u);
  have hu : u ⊩[M] χ := (hχu (.inl u)).mp fun _ _ ↦ Iff.rfl;
  obtain ⟨u', Ryu', hu'⟩ := forces_dia.mp <|
    (h (◇χ) (by simpa using hχ)).mp <| forces_dia.mpr ⟨u, Rxu, hu⟩;
  use {u' | y ≺ u' ∧ u' ⊩[N] χ};
  and_intros;
  · use u';
    exact ⟨Ryu', hu'⟩;
  · rintro u' ⟨Ryu', hu'⟩;
    exact ⟨Ryu', fun A hA ↦ ((hχu (.inr u')).mpr hu' A hA).symm⟩;
  · intro V' SV';
    obtain ⟨δ, hδ, hδC⟩ := definable_modalEquivalent_union (M := M) (N := N) n
      {z | ∃ u', (y ≺ u' ∧ u' ⊩[N] χ) ∧ ∃ v' ∈ V' u', z = .inr v'};
    by_contra hne;
    push Not at hne;
    have hx : x ⊮[M] χ ▷ δ := by
      apply not_forces_rhd.mpr;
      use u;
      and_intros;
      · exact Rxu;
      · exact hu;
      · intro V SuV;
        obtain ⟨v, hv, hvC⟩ := hne V SuV;
        use v;
        and_intros;
        · exact hv;
        · intro hvδ;
          obtain ⟨_, ⟨u', hu', v', hv', rfl⟩, hvv'⟩ := (hδC (.inl v)).mpr hvδ;
          exact hvC u' hu' v' hv' hvv';
    obtain ⟨u', Ryu', hu', hV⟩ := not_forces_rhd.mp fun hy ↦
      hx <| (h _ (by simpa using ⟨hχ, hδ⟩)).mpr hy;
    obtain ⟨v', hv', hv'δ⟩ := hV (V' u') (SV' u' ⟨Ryu', hu'⟩);
    exact hv'δ <| (hδC (.inr v')).mp ⟨_, ⟨u', ⟨Ryu', hu'⟩, v', hv', rfl⟩, fun _ _ ↦ Iff.rfl⟩;

end Definable

/-- Over finitely many propositional variables, worlds are $n$-w-bisimilar if and only if they are
$n$-modally equivalent.

- [HPV23, Proposition 3.2, Theorem 4.3]
-/
theorem nWBisimilar_iff_modalEquivalent [Finite α] {n : ℕ} :
    NWBisimilar M N n x y ↔ ModalEquivalent M N n x y := by
  constructor;
  · rintro ⟨Z, h⟩ A hA;
    exact Z.forces_iff le_rfl h hA;
  · intro h;
    use {
      toRel := ModalEquivalent M N
      antitone := fun _ h A hA ↦ h A (by omega)
      atomic := fun {_ _ a} h ↦ h (#a) le_rfl
      forth := fun _ ↦ wForth_modalEquivalent _
      back := by
        intro i _;
        rw [flip_modalEquivalent, flip_modalEquivalent];
        exact wForth_modalEquivalent _
    };

end FFL.InterpretabilityLogic.Verbrugge.Model

end
