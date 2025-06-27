import Mathlib
-- import FaugereF4.MvPolyIdealBasic

-- namespace MvPolynomial

/-!
# Preliminaries on monomial ideals

-/

/- deprecated; use monomial_ideal below
def monomialIdeal {σ R : Type*} [CommSemiring R] (s : Set (σ →₀ ℕ)) :
  Ideal (MvPolynomial σ R) :=
  Ideal.span ((fun s => monomial s (1 : R)) '' s)
-/

/-
def commring_ACC (R : Type*) [CommRing R] :=
  ∀ (iseq : ℕ → Ideal R), (∀ (n m : ℕ), n ≤ m → iseq n ≤ iseq m) →
  ∃ (N : ℕ), ∀ (M : ℕ), N ≤ M → iseq N = iseq M

def commring_MC (R : Type*) [CommRing R] :=
  ∀ (S : Set (Ideal R)), S.Nonempty → ∃ J, Maximal (fun I => I ∈ S) J

/-- An equivalent formulation of Noetherian ring.
[Every ideal is finitely generated] ↔
[Every ascending chain of ideals terminate] ↔
[Every nonempty set of ideals has a maximal element under inclusion]. -/
lemma noeth_FC_impl_ACC (R : Type*) [CommRing R]:
  IsNoetherianRing R →
  ∀ (iseq : ℕ → Ideal R), (∀ (n m : ℕ), n ≤ m → iseq n ≤ iseq m) →
  ∃ (N : ℕ), ∀ (M : ℕ), N ≤ M → iseq N = iseq M := by
  intro noeth iseq iseq_acc
  unfold IsNoetherianRing at noeth
  rw [IsNoetherian_def] at noeth
  sorry
-/

/- `noeth_acc` leads to well-foundedness of the dual order of ideal inclusion.
... this is alrady proved in mathlib, `isNoetherian_iff'` and `IsNoetherian.wf`. -/

/-
theorem Dickson_lemma_fin (n : ℕ) : -- {σ K : Type*} [Field K] :
  ∀ (K : Type*) [Field K], ∀ (A : Set (Fin n →₀ ℕ)), ∃ (s : Finset (Fin n →₀ ℕ)),
  ↑s ⊆ A ∧ (@monomialIdeal (Fin n) K _ ↑s = monomialIdeal A) := by
  intro K instK
  induction n using Nat.strongRecOn with
  | ind n IH =>
    obtain _ | n := n
    · simp_all
      intro A
      have mem_A : ∀ x ∈ A, x = 0 := by
        intro hxA
        rw [← Finsupp.support_eq_empty]
        have fin0_sub_empty : ∀ (S : Set (Fin 0)), S = ∅ :=
          Set.eq_empty_of_isEmpty -- simp_all의 적용을 위해 이 중간단계가 필요
        rw [← Finset.coe_eq_empty]
        simp_all
      by_cases hA : A = ∅
      · exact ⟨∅, by simp, by simp_all⟩
      · have : A = {0} := by
          ext x
          constructor
          · apply mem_A
          · intro hx0
            simp at hx0
            push_neg at hA
            have : ∃ y, y ∈ A := hA
            let ⟨y, hyA⟩ := this
            have : y = 0 := mem_A y hyA
            simp_all
        exact ⟨{0}, by simp_all, by simp_all⟩
    · intro A
      let SubA (d : ℕ) : Set (Fin n →₀ ℕ) :=
        { a | (Finsupp.embDomain (Fin.succEmb n) a).update n d ∈ A }
      let USubA (d : ℕ) : Set (Fin n →₀ ℕ) :=
        ⋃ d' : Fin d, SubA d'
      let Iseq (d : ℕ) := @monomialIdeal (Fin n) K _ (USubA d)
      have USubA_seq : ∀ (d1 d2 : ℕ), d1 ≤ d2 → USubA d1 ⊆ USubA d2 := by
        intro d1 d2 hdc
        unfold USubA
        simp
        intro d1' x hxd1
        simp
        exists Fin.castLEOrderEmb hdc d1'
      have Iseq_seq : ∀ (d1 d2 : ℕ), d1 ≤ d2 → Iseq d1 ≤ Iseq d2 := by
        intro d1 d2 hdc
        unfold Iseq
        unfold monomialIdeal
        apply Ideal.span_mono
        apply Set.image_subset
        exact USubA_seq d1 d2 hdc
      let ⟨N, Iseq_accN⟩ := noeth_acc _ Iseq Iseq_seq
      let fg_exists (d : ℕ) := IH n (by simp) (USubA d)
      let fg_mons (d : ℕ) := (fg_exists d).choose
      let fg_spec (d : ℕ) := (fg_exists d).choose_spec
      /-
      let S : Finset (Fin (n + 1) →₀ ℕ) :=
        Finset.biUnion
          (Fin (N + 1)).toFinset
          (λ d => (λ a => (Finsupp.embDomain (Fin.succEmb n) a).update n d) '' fg_mons d)
          -/
      sorry

/-
finite_iff_exists_equiv_fin : σ ≃ Fin n
Finsupp.equivCongrLeft : (σ →₀ ℕ) ≃ (Fin n →₀ ℕ)
MvPolynomial.renameEquiv : MvPolynomial σ R ≃ₐ[R] MvPolynomial (Fin n) R

-/

theorem Dickson_lemma_finite {σ : Type*} [inst_finite : Finite σ] :
  ∀ (K : Type*) [Field K], ∀ (A : Set (σ →₀ ℕ)), ∃ (s : Finset (σ →₀ ℕ)),
  ↑s ⊆ A ∧ (@monomialIdeal σ K _ ↑s = monomialIdeal A) := by
  let ⟨n, h_eq_dec⟩ := finite_iff_exists_equiv_fin.mp inst_finite
  let σ_fin_equiv := Classical.choice h_eq_dec
  intro K instK A
  let A' := Finsupp.equivMapDomain σ_fin_equiv '' A
  let ⟨s', hcont', hgen'⟩ := @Dickson_lemma_fin n K _ A'
  let s := Finset.map (Finsupp.mapDomainEmbedding σ_fin_equiv.symm.toEmbedding) s'
  exists s
  constructor
  · rw [← Equiv.image_subset (Finsupp.equivCongrLeft σ_fin_equiv) ↑s A]
    have s_eq : s'.toSet = ⇑(Finsupp.equivCongrLeft σ_fin_equiv) '' s.toSet := by
      unfold s
      simp_all
      ext m
      constructor
      · intro hms'
        simp_all
        exact ⟨m, hms', by ext a; simp_all⟩
      · intro hmss
        simp_all
        let ⟨m', hms', hmss'⟩ := hmss
        have : m = m' := by
          subst hmss'
          simp_all only [A', σ_fin_equiv]
          obtain ⟨w, hleft, hright⟩ := hmss
          ext a
          simp_all
        rw [this]
        exact hms'
    have A_eq : A' = ⇑(Finsupp.equivCongrLeft σ_fin_equiv) '' A := by
      unfold A'
      simp_all
    simp_all
  · let mvp_equiv := MvPolynomial.renameEquiv K σ_fin_equiv
    ext f
    have si_mem : mvp_equiv f ∈ monomialIdeal ↑s' ↔ f ∈ monomialIdeal ↑s := by
      unfold s
      unfold monomialIdeal
      -- unfold mvp_equiv
      -- simp_all
      -- rw [Ideal.symm_apply_mem_of_equiv_iff]
      sorry
    /-
    have si_eq : monomialIdeal ↑s = Ideal.map ↑mvp_equiv.symm (monomialIdeal ↑s') := by
      unfold s
      unfold monomialIdeal
      unfold Ideal.map
      unfold Set.image
      simp_all
      -- rw [← Set.image_comp, ← Set.image_comp]
      aesop?
    have Ai_eq : monomialIdeal A = Ideal.map ↑mvp_equiv.symm (monomialIdeal A') := by
      sorry
    -/
    -- unfold Ideal.span
    simp_all
    sorry
-/

def lcm_monomial {σ : Type*} [DecidableEq σ] (m1 m2 : σ →₀ ℕ) : σ →₀ ℕ := {
  support := m1.support ∪ m2.support
  toFun := λ x => max (m1 x) (m2 x)
  mem_support_toFun := by
    intro x
    simp_all
    constructor
    · intro h1 h2
      simp_all
    · intro h
      by_contra h'
      simp_all
}


/-- The maximum monomial of `S : Finset (σ →₀ ℕ)`, under given monomial order `mo`. -/
def max_monomial {σ : Type*} [DecidableEq σ]
  (mo : MonomialOrder σ) (S : Finset (σ →₀ ℕ)) :=
  WithBot.map mo.toSyn.invFun (Finset.map mo.toSyn S).max

/-- A variant of `leading_monomial`: given `S.Nonempty`, the `WithBot` can be peeled off. -/
def max_monomial' {σ : Type*} [DecidableEq σ]
  (mo : MonomialOrder σ) (S : Finset (σ →₀ ℕ)) (hS : S.Nonempty) :=
  mo.toSyn.invFun ((Finset.map mo.toSyn.toEmbedding S).max' (by simp; exact hS))

/-- The maximum monomial is in the original monomial set. -/
lemma maxm'_mem {σ : Type*} [DecidableEq σ]
  (mo : MonomialOrder σ) (S : Finset (σ →₀ ℕ)) (hS : S.Nonempty) :
  max_monomial' mo S hS ∈ S := by
  unfold max_monomial'
  rw [← Finset.mem_map' mo.toSyn.toEmbedding]
  have (x) : mo.toSyn.toEmbedding (mo.toSyn.invFun x) = x := by simp
  rw [this]
  apply Finset.max'_mem

lemma set_eq_impl_maxm'_eq {σ : Type*} [DecidableEq σ]
  (mo : MonomialOrder σ) (S1 S2 : Finset (σ →₀ ℕ))
  (hS1 : S1.Nonempty) (hS2 : S2.Nonempty) (hSeq : S1 = S2) :
  max_monomial' mo S1 hS1 = max_monomial' mo S2 hS2 := by
  subst hSeq
  simp_all

/-- The leading monomial of polynomial `f`, under given monomial order `mo`. -/
def leading_monomial {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) :=
  max_monomial mo f.support

/-- A variant of `leading_monomial`: given `f ≠ 0`, the `WithBot` can be peeled off. -/
def leading_monomial' {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) (f_not_0 : f ≠ 0) :=
  max_monomial' mo f.support (by simp_all)

/-- The leading monomial is in the support of the original polynomial `f`. -/
lemma lm'_mem {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) (f_not_0 : f ≠ 0) :
  leading_monomial' mo f f_not_0 ∈ f.support := by
  unfold leading_monomial'
  apply maxm'_mem

lemma lm'_eq_of_eq {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ R) (f_eq_g : f = g) (f_not_0 : f ≠ 0) :
  leading_monomial' mo f f_not_0 = leading_monomial' mo g (by rw [← f_eq_g]; exact f_not_0) := by
  subst f_eq_g
  simp_all

lemma mem_le_lm' {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) (f_not_0 : f ≠ 0) :
  ∀ m ∈ f.support, mo.toSyn m ≤ mo.toSyn (leading_monomial' mo f f_not_0) := by
  intro m hmf
  unfold leading_monomial' max_monomial'
  rw [← Finset.mem_map' mo.toSyn.toEmbedding] at hmf
  simp only [Equiv.toEmbedding_apply, AddEquiv.toEquiv_eq_coe] at hmf
  simp
  apply Finset.le_max' _ (mo.toSyn m) hmf

lemma lm_smul_eq_lm {σ R : Type*} [DecidableEq σ] [CommSemiring R] [IsDomain R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) (c : R) (c_not_0 : c ≠ 0) :
  leading_monomial mo f = leading_monomial mo (c • f) := by
  unfold leading_monomial
  unfold max_monomial
  simp_all

lemma lm'_smul_eq_lm' {σ R : Type*} [DecidableEq σ] [CommSemiring R] [IsDomain R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) (f_not_0 : f ≠ 0) (c : R) (c_not_0 : c ≠ 0) :
  leading_monomial' mo f f_not_0 = leading_monomial' mo (c • f) (smul_ne_zero c_not_0 f_not_0) := by
  unfold leading_monomial'
  unfold max_monomial'
  simp_all

lemma sub_smul_ne_0 {σ R : Type*} [DecidableEq σ] [CommRing R] [IsDomain R]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ R)
  (hf : f ≠ 0) (hg : g ≠ 0)
  (hfg : mo.toSyn (leading_monomial' mo f hf) < mo.toSyn (leading_monomial' mo g hg))
  (c : R) :
  g - c • f ≠ 0 := by
  by_contra H
  rw [sub_eq_zero] at H
  rcases em (c = 0) with hc0 | hc0
  · rw [hc0] at H
    simp at H
    exact hg H
  · rw [lm'_smul_eq_lm' mo f hf c hc0] at hfg
    subst H
    simp_all

lemma lm_sub_smul_eq_lm {σ R : Type*} [DecidableEq σ] [CommRing R] [IsDomain R]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ R)
  (hf : f ≠ 0) (hg : g ≠ 0)
  (hfg : mo.toSyn (leading_monomial' mo f hf) < mo.toSyn (leading_monomial' mo g hg))
  (c : R) :
  leading_monomial' mo (g - c • f) (sub_smul_ne_0 mo f g hf hg hfg c) = leading_monomial' mo g hg := by
  let lmg := leading_monomial' mo g hg
  have supp_subs : (g - c • f).support ⊆ g.support ∪ f.support := by
    calc
      (g - c • f).support ⊆ g.support ∪ (c • f).support := MvPolynomial.support_sub σ g (c • f)
      _ ⊆ g.support ∪ f.support := by apply Finset.union_subset_union; simp; apply MvPolynomial.support_smul
  have hmg : ∀ m ∈ g.support, mo.toSyn m ≤ mo.toSyn lmg := mem_le_lm' mo g hg
  have hmfg : ∀ m ∈ f.support, mo.toSyn m < mo.toSyn lmg := by
    intro m hmf
    have : mo.toSyn m ≤ mo.toSyn (leading_monomial' mo f hf) := by
      unfold leading_monomial' max_monomial'
      rw [← Finset.mem_map' mo.toSyn.toEmbedding] at hmf
      simp only [Equiv.toEmbedding_apply, AddEquiv.toEquiv_eq_coe] at hmf
      simp
      apply Finset.le_max' _ (mo.toSyn m) hmf
    calc
      mo.toSyn m ≤ mo.toSyn (leading_monomial' mo f hf) := this
      _ < mo.toSyn lmg := by unfold lmg; exact hfg
  have lmg_mem : lmg ∈ (g - c • f).support := by
    simp
    have : f.coeff lmg = 0 := by
      rw [← MvPolynomial.notMem_support_iff]
      by_contra H
      let H' := @ne_of_lt _ _ (mo.toSyn lmg) (mo.toSyn lmg)
      rw [← ne_self_iff_false (mo.toSyn lmg)]
      exact H' (hmfg lmg H)
    rw [this]
    simp
    push_neg
    rw [← MvPolynomial.mem_support_iff]
    exact lm'_mem mo g hg
  rw [← AddEquiv.apply_eq_iff_eq mo.toSyn]
  apply le_antisymm
  · unfold leading_monomial' max_monomial'
    simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
      AddEquiv.apply_symm_apply, Finset.max'_le_iff, Finset.mem_map_equiv, AddEquiv.coe_toEquiv_symm]
    intro y hy
    apply supp_subs at hy
    simp only [Finset.mem_union] at hy
    cases hy with
    | inl mem_g =>
      unfold lmg leading_monomial' max_monomial' at hmg
      simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
        AddEquiv.apply_symm_apply, Finset.max'_le_iff, Finset.mem_map_equiv, AddEquiv.coe_toEquiv_symm] at hmg
      let goal := hmg (mo.toSyn.symm y) mem_g
      simp at goal
      exact goal
    | inr mem_f =>
      apply le_of_lt
      unfold lmg leading_monomial' max_monomial' at hmfg
      simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
        AddEquiv.apply_symm_apply, Finset.max'_le_iff, Finset.mem_map_equiv, AddEquiv.coe_toEquiv_symm] at hmfg
      let goal := hmfg (mo.toSyn.symm y) mem_f
      simp at goal
      exact goal
  · exact mem_le_lm' mo (g - c • f) (sub_smul_ne_0 mo f g hf hg hfg c) lmg lmg_mem


/-- `max_monomial'` of a Finset is type-coerced to `max_monomial`, when `S.Nonempty` is
removed. A monomial order version of `Finset.coe_max'`. -/
lemma maxm_coe_maxm' {σ : Type*} [DecidableEq σ]
  (mo : MonomialOrder σ) (S : Finset (σ →₀ ℕ)) (hS : S.Nonempty) :
  max_monomial mo S = ↑(max_monomial' mo S hS) := by
  unfold max_monomial
  unfold max_monomial'
  apply Eq.symm
  rw [WithBot.some_eq_map_iff]
  simp
  apply Eq.symm
  exact @Finset.coe_max' _ _ (Finset.map mo.toSyn.toEmbedding S) (by simp_all)

/-- `leading_monomial'` of a polynomial is type-coerced to `leading_monomial`, when `f ≠ 0` is
removed. A monomial order version of `Finset.coe_max'`. -/
lemma lm_coe_lm' {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) (f_not_0 : f ≠ 0) :
  leading_monomial mo f = ↑(leading_monomial' mo f f_not_0) := by
  unfold leading_monomial
  unfold leading_monomial'
  exact maxm_coe_maxm' mo f.support (by simp_all)

/-- The leading coefficient of polynomial `f`, under given monomial order `mo`.
That is, the coefficient of leading monomial of `f`. -/
def leading_coeff' {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) (f_not_0 : f ≠ 0) :=
  f.coeff (leading_monomial' mo f f_not_0)

lemma lc_not_zero {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) (f_not_0 : f ≠ 0) :
  leading_coeff' mo f f_not_0 ≠ 0 := by
  unfold leading_coeff'
  rw [← MvPolynomial.mem_support_iff]
  apply lm'_mem


/-- The set of leading monomials of `f ∈ F`,
  under a given monomial order `mo`. -/
def leading_monomials_fin {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (F : Finset (MvPolynomial σ R)) : Finset (σ →₀ ℕ) :=
  F.biUnion (λ (f : MvPolynomial σ R) => (leading_monomial mo f).toFinset)

def leading_monomials {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (F : Set (MvPolynomial σ R)) : Set (σ →₀ ℕ) :=
  ((λ (f : MvPolynomial σ R) => (leading_monomial mo f).toFinset.toSet) '' F).sUnion

def monomial_ideal {σ K : Type*} [DecidableEq σ] [Field K]
  (S : Set (σ →₀ ℕ)) : Ideal (MvPolynomial σ K) :=
  Ideal.span ((fun (s : σ →₀ ℕ) => MvPolynomial.monomial s (1 : K)) '' S)

/-
def leadterm_ideal' {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K]
  (mo : MonomialOrder σ) (S' : Set (MvPolynomial σ K)) (hS' : 0 ∉ S') :=
  have : ∀ f ∈ S', f ≠ 0 := by
    intro f hf hf0
    simp_all
  @monomial_ideal σ K _ _ _ { m : σ →₀ ℕ | ∃ f ∈ S', m = leading_monomial' mo f (this f _) }

def leadterm_ideal {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K]
  (mo : MonomialOrder σ) (S : Set (MvPolynomial σ K)) :=


def leadterm_ideal {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K]
  (mo : MonomialOrder σ) (I : Ideal (MvPolynomial σ K)) :=
  @monomial_ideal σ K _ _ _ { m : σ →₀ ℕ | ∃ f ∈ I, f ≠ 0 ∧ m = leading_monomial' mo f (by trivial) }
-/

/-- The set of entire monomials which appear in one of `f ∈ F`. -/
def monomial_set {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (F : Finset (MvPolynomial σ R)) : Finset (σ →₀ ℕ) :=
  F.biUnion MvPolynomial.support

lemma singleton_monset_eq_support {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (f : MvPolynomial σ R) : monomial_set {f} = f.support := by
  unfold monomial_set
  simp

/-- Shift a monomial‐exponent vector by `m`. -/
noncomputable def add_mon {σ : Type*} (m : σ →₀ ℕ) : (σ →₀ ℕ) ↪ σ →₀ ℕ :=
  ⟨fun n => m + n, by unfold Function.Injective; simp⟩

/-- The monomial set of the product of `f : MvPolynomial σ R` and `monomial m a`
is equal to `f.support` mapped through addition by `m`. -/
@[simp]
theorem monomial_set_mul_monomial {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (f : MvPolynomial σ R) (m : σ →₀ ℕ) (a : R) (ha : IsUnit a) :
  monomial_set {f * MvPolynomial.monomial m a} = f.support.map (addRightEmbedding m) := by
  simp [monomial_set]
  apply AddMonoidAlgebra.support_mul_single (f := f) (r := a) (hr := fun y => by exact IsUnit.mul_left_eq_zero ha) (x := m)


lemma maxm'_monmul_commute {σ : Type*} [DecidableEq σ]
  (mo : MonomialOrder σ) (S : Finset (σ →₀ ℕ)) (hS : S.Nonempty) (m : σ →₀ ℕ) :
  max_monomial' mo (S.map (addRightEmbedding m)) (by simp_all) = max_monomial' mo S hS + m := by
  unfold max_monomial'
  rw [← AddEquiv.apply_eq_iff_eq mo.toSyn, AddEquiv.map_add]
  have h_are_m_S : (Finset.map mo.toSyn.toEmbedding (Finset.map (addRightEmbedding m) S)).Nonempty := by simp_all
  let Sm_syn_max' := (Finset.map mo.toSyn.toEmbedding (Finset.map (addRightEmbedding m) S)).max' h_are_m_S
  let S_syn_max' := (Finset.map mo.toSyn.toEmbedding S).max' (by simp_all)
  have : Sm_syn_max' = S_syn_max' + mo.toSyn m := by
    unfold Sm_syn_max'
    unfold S_syn_max'
    simp_all only [AddEquiv.toEquiv_eq_coe]
    unfold addRightEmbedding
    apply le_antisymm
    · unfold Finset.max'
      simp
      intro b b_in_S
      exists b
    · unfold Finset.max'
      simp
      exists mo.toSyn.symm S_syn_max'
      constructor
      · have (n) : mo.toSyn.symm n ∈ S ↔ n ∈ S.map mo.toSyn.toEmbedding := by
          simp_all only [AddEquiv.toEquiv_eq_coe, Finset.mem_map_equiv, AddEquiv.coe_toEquiv_symm]
        rw [this S_syn_max']
        unfold S_syn_max'
        apply Finset.max'_mem
      · intro b b_in_S
        simp
        unfold S_syn_max'
        have : mo.toSyn b ∈ S.map mo.toSyn.toEmbedding := by
          simp_all only [AddEquiv.toEquiv_eq_coe, Finset.mem_map_equiv, EquivLike.coe_symm_apply_apply]
        unfold Finset.max'
        simp
        exists b
  simp
  unfold Sm_syn_max' at this
  unfold S_syn_max' at this
  exact this

/-
lemma maxm_monmul_commute {σ : Type*} [DecidableEq σ]
  (mo : MonomialOrder σ) (S : Finset (σ →₀ ℕ)) (m : σ →₀ ℕ) :
  max_monomial mo (S.map (addRightEmbedding m)) = max_monomial mo S + ↑m := by
  unfold max_monomial
  by_cases hS : S.Nonempty
  · -- utilize mo.iocam

    sorry
  · simp at hS
    subst hS
    simp_all
-/

lemma mul_mon_nonzero {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (f : MvPolynomial σ K) (f_not_0 : f ≠ 0) (m : σ →₀ ℕ) (a : K) (ha : a ≠ 0) :
  f * MvPolynomial.monomial m a ≠ 0 := by
  have : MvPolynomial.monomial m a ≠ 0 := by
    by_contra mon_0
    simp at mon_0
    subst mon_0
    simp_all
  by_contra mul_0
  have : f = 0 ∨ MvPolynomial.monomial m a = 0 :=
    MvPolynomial.instNoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero mul_0
  simp_all

lemma lm'_monmul_commute {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f : MvPolynomial σ K) (f_not_0 : f ≠ 0) (m : σ →₀ ℕ) (a : K) (ha : a ≠ 0) :
  leading_monomial' mo (f * MvPolynomial.monomial m a) (mul_mon_nonzero f f_not_0 m a ha)
    = leading_monomial' mo f f_not_0 + m := by
  unfold leading_monomial'
  have monset_monmul : monomial_set {f * MvPolynomial.monomial m a} = (f * MvPolynomial.monomial m a).support := by
    unfold monomial_set
    simp
  have : max_monomial' mo (f * (MvPolynomial.monomial m) a).support (by simp_all)
    = max_monomial' mo (monomial_set {f * MvPolynomial.monomial m a}) (by simp_all) := by
    simp_all
  rw [this, ← maxm'_monmul_commute]
  rw [set_eq_impl_maxm'_eq]
  rw [monomial_set_mul_monomial]
  simp_all

  /-
  unfold max_monomial'
  simp [← monset_monmul]
  simp [← AddEquiv.apply_eq_iff_eq mo.toSyn]
  have : monomial_set {f * MvPolynomial.monomial m a} = f.support.map (addRightEmbedding m) := by
    simp_all only [ne_eq, isUnit_iff_ne_zero, not_false_eq_true, monomial_set_mul_monomial]
  have : Finset.map mo.toSyn.toEmbedding (monomial_set {f * MvPolynomial.monomial m a})
    = Finset.map mo.toSyn.toEmbedding (f.support.map (addRightEmbedding m)) := by
    rw [this]
  have : (Finset.map mo.toSyn.toEquiv.toEmbedding (monomial_set {f * MvPolynomial.monomial m a})).max' (by simp_all)
    = (Finset.map mo.toSyn.toEquiv.toEmbedding (f.support.map (addRightEmbedding m))).max' (by simp_all) := by
    simp_all
  /- max_monomial' mo (S.map (addRightEmbedding m)) (by simp_all) = max_monomial' mo S hS + m -/
  simp_all
  simp_all only
  unfold addRightEmbedding
  unfold Finset.map
  simp
  apply mo.lo.le_antisymm
  · simp_all

    sorry
  · apply Finset.le_max'
    simp_all
    exists leading_monomial' mo f f_not_0
    constructor
    · unfold leading_monomial'
      unfold max_monomial'
      sorry
    ·
      sorry
  -/
  /-
  have : (f.support.map mo.toSyn.toEmbedding).max + ↑(mo.toSyn m)
    = ((f.support.map (addRightEmbedding m)).map mo.toSyn.toEmbedding).max := by

    aesop?

  have : WithBot.map mo.toSyn.invFun (f.support.map mo.toSyn.toEmbedding).max + ↑m
    = WithBot.map mo.toSyn.invFun ((f.support.map (addRightEmbedding m)).map mo.toSyn.toEmbedding).max := by

    aesop?
  simp_all only [monomial_set_mul_monomial, AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm]
  -/

/-- The monomial set of some union equals the union of corresponding monomial sets. -/
lemma union_monset_commute {σ R : Type*} [DecidableEq σ] [CommSemiring R] [DecidableEq R]
  (A B : Finset (MvPolynomial σ R)) :
  monomial_set (A ∪ B) = monomial_set A ∪ monomial_set B := by -- autogen by aesop
  unfold monomial_set
  ext a : 1
  simp_all only [Finset.mem_biUnion, Finset.mem_union, MvPolynomial.mem_support_iff, ne_eq]
  apply Iff.intro
  · intro a_1
    obtain ⟨w, h⟩ := a_1
    obtain ⟨left, right⟩ := h
    cases left with
    | inl h =>
      apply Or.inl
      apply Exists.intro
      · apply And.intro
        · exact h
        · simp_all only [not_false_eq_true]
    | inr h_1 =>
      apply Or.inr
      apply Exists.intro
      · apply And.intro
        · exact h_1
        · simp_all only [not_false_eq_true]
  · intro a_1
    cases a_1 with
    | inl h =>
      obtain ⟨w, h⟩ := h
      obtain ⟨left, right⟩ := h
      apply Exists.intro
      · apply And.intro
        · apply Or.inl
          exact left
        · simp_all only [not_false_eq_true]
    | inr h_1 =>
      obtain ⟨w, h⟩ := h_1
      obtain ⟨left, right⟩ := h
      apply Exists.intro
      · apply And.intro
        · apply Or.inr
          exact left
        · simp_all only [not_false_eq_true]

@[simp]
lemma monomial_sub_add {σ : Type*} (m n : σ →₀ ℕ) (hmn : m ≤ n) :
  n - m + m = n := by
  ext s
  simp
  have : m s ≤ n s := by apply hmn
  simp_all only [Nat.sub_add_cancel]

lemma nonzero_lm'_div_impl_lm_div {σ R : Type*} [Finite σ] [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) (f_not_0 : f ≠ 0) (m : σ →₀ ℕ) :
  leading_monomial mo f ≤ m → leading_monomial' mo f f_not_0 ≤ m := by
  intro hfm
  have : leading_monomial mo f = ↑(leading_monomial' mo f f_not_0) := by
    unfold leading_monomial
    unfold max_monomial
    unfold leading_monomial'
    unfold max_monomial'
    rw [← WithBot.map_coe, Finset.coe_max']
    simp_all only [ne_eq, AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm]
  simp_all only [WithBot.coe_le_coe]

lemma lm_mem_supp {σ R : Type*} [Finite σ] [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) (f_not_0 : f ≠ 0) :
  leading_monomial' mo f f_not_0 ∈ f.support := by
  unfold leading_monomial'
  unfold max_monomial'
  rw [← Finset.mem_map' mo.toSyn.toEmbedding]
  -- simp only [Equiv.coe_toEmbedding, mo.toSyn.left_inv, mo.toSyn.right_inv]
  have (m) : mo.toSyn.toEmbedding (mo.toSyn.invFun m) = m := by
    simp_all only [ne_eq, AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
      Equiv.coe_toEmbedding, EquivLike.coe_coe, AddEquiv.apply_symm_apply]
  rw [this]
  apply Finset.max'_mem


/-
noncomputable def add_mon {σ : Type*} [Finite σ] [DecidableEq σ] (m : σ →₀ ℕ)
  : (σ →₀ ℕ) ↪ σ →₀ ℕ := {
    toFun := λ n => m + n
    inj' := by unfold Function.Injective; simp
  }
-/

lemma mvpoly_mul_coeff {σ : Type*} {R : Type*} [Finite σ] [DecidableEq σ] [CommSemiring R] [DecidableEq R]
  (f g : MvPolynomial σ R) (m : σ →₀ ℕ) :
  (f * g).coeff m = ∑ (nf ∈ f.support) (ng ∈ g.support) with nf + ng = m, f.coeff nf * g.coeff ng := by
  rw [MvPolynomial.coeff_mul]
  let antidiag_supp := {x ∈ f.support ×ˢ g.support | match x with | (nf, ng) => nf + ng = m}
  have : antidiag_supp ⊆ Finset.antidiagonal m := by
    unfold antidiag_supp
    intro x
    intro hx
    simp_all only [Finset.mem_filter, Finset.mem_product, MvPolynomial.mem_support_iff, ne_eq,
      Finset.mem_antidiagonal]

  rw [Finset.antidiagonal]
  /-
  rw [@Finsupp.instHasAntidiagonal.mem_antidiagonal m _]

  simp_all
  rw [MvPolynomial.mul_def]
  unfold Finsupp.sum
  rw [MvPolynomial.coeff_sum]

  rw [Fintype.sum_prod_type']
  rw [MvPolynomial.coeff_sum g.support (λ x_1 => (MvPolynomial.monomial (x + x_1)) (f.coeff x * g.coeff x_1)) m]
  -/
  sorry



lemma add_mon_supp {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (f : MvPolynomial σ K) (m : σ →₀ ℕ) :
  -- (f * MvPolynomial.monomial m 1).support = Finset.map (add_mon m) f.support := by
  monomial_set {f * MvPolynomial.monomial m 1} = Finset.map (add_mon m) f.support := by
  have f_mul_mon : f * MvPolynomial.monomial m 1
    = ∑ n ∈ f.support, MvPolynomial.monomial (n + m) (f.coeff n) := by
    rw [MvPolynomial.as_sum f, MvPolynomial.mul_def]
    simp
    unfold Finsupp.sum
    rfl
  have coeff_shift (l) : f.coeff l = (f * MvPolynomial.monomial m 1).coeff (l + m) := by
    rw [MvPolynomial.coeff_mul]
    simp_all only [MvPolynomial.coeff_monomial, mul_ite, mul_one, mul_zero]
    have : ∀ n ∈ Finset.antidiagonal (l + m), (m = n.2) ↔ n = (l, m) := by
      intro n hn
      simp_all only [Finset.mem_antidiagonal]
      obtain ⟨fst, snd⟩ := n
      simp_all only [Prod.mk.injEq]
      constructor
      · intro hm
        subst hm
        simp_all only [add_left_inj, and_self]
      · intro hlm
        simp_all only
    /-
    have : ∑ x ∈ Finset.antidiagonal (l + m), if m = x.2 then MvPolynomial.coeff x.1 f else 0
      = ∑ x ∈ Finset.antidiagonal (l + m), if m = x.2 then MvPolynomial.coeff l f else 0 := by
      aesop?
      -/

    /-
    rw [Finset.sum_ite_zero (Finset.antidiagonal (l + m)) (λ n => m = n.2) this (MvPolynomial.coeff x.1 f)]

    rw [f_mul_mon]
      -/
    by_cases hnf : l ∈ f.support
    · sorry
    · sorry
  /-
  have : Finset.map (add_mon m) f.support = {m + n | n ∈ f.support} := by
    simp_all only [Finset.coe_map, MvPolynomial.mem_support_iff, ne_eq]
    ext x : 1
    simp_all only [Set.mem_image, Finset.mem_coe, MvPolynomial.mem_support_iff, ne_eq, Set.mem_setOf_eq]
    rfl
  have (n) : n ∈ f.support ↔ n + m ∈ (f * MvPolynomial.monomial m 1).support := by
    rw [f_mul_mon]
    constructor
    · intro hnf

      sorry
    ·
      sorry
  have : {m + n | n ∈ f.support} = (f * MvPolynomial.monomial m 1).support := by
    rw [f_mul_mon]
    simp_all
    sorry
  rw [this]
  -/
  sorry


/- m * Mon(f) = Mon(m * f) -/
/- x^αcoeff of f = x^(a+b) coeff of (x^b * f) -/
/-- Taking support of `MvPolynomial` and multiplying a monomial commute. -/
lemma add_mon_supp'' {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (f : MvPolynomial σ K) (m : σ →₀ ℕ) :
  -- (f * MvPolynomial.monomial m 1).support = Finset.map (add_mon m) f.support := by
  monomial_set {f * MvPolynomial.monomial m 1} = Finset.map (add_mon m) f.support := by
  have f_mul_mon : f * MvPolynomial.monomial m 1
    = ∑ n ∈ f.support, MvPolynomial.monomial (n + m) (f.coeff n) := by
    rw [MvPolynomial.as_sum f, MvPolynomial.mul_def]
    simp
    unfold Finsupp.sum
    rfl
  -- rw [f_mul_mon]
  ext m'
  unfold monomial_set
  simp
  push_neg
  constructor
  · rw [f_mul_mon]
    simp
    intro hm'
    have : m ≤ m' := by
      sorry
    unfold add_mon
    simp
    exists m' - m

    sorry
  · sorry

/-
  unfold add_mon
  rw [MvPolynomial.as_sum f, MvPolynomial.mul_def]
  unfold Finset.map
  ext n
  simp

  sorry
-/
lemma add_mon_supp' {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (f : MvPolynomial σ K) (m : σ →₀ ℕ) :
  monomial_set {f * MvPolynomial.monomial m 1} = Finset.map (add_mon m) f.support := by
  unfold monomial_set
  unfold add_mon
  rw [MvPolynomial.as_sum f, MvPolynomial.mul_def]
  unfold Finset.map
  ext n
  simp
  unfold MvPolynomial.coeff
  rw [Finsupp.sum_apply]
  unfold Finsupp.sum
  simp
  push_neg
  constructor
  · intro hn
    apply Finset.exists_ne_zero_of_sum_ne_zero at hn
    let ⟨a, haf, ham⟩ := hn
    exists a
    constructor
    · simp_all
    · rw [← Finsupp.mem_support_iff] at ham
      apply MvPolynomial.support_monomial_subset at ham
      rw [add_comm]
      simp_all
  · intro hn
    let ⟨a, haf, ham⟩ := hn
    rw [add_comm] at ham
    rw [← ham]
    have (x) : x = a ↔ (MvPolynomial.monomial (x + m) (f.toFun x)).toFun (a + m) ≠ 0 := by
      constructor
      · intro hxa
        rw [hxa]
        have : ((MvPolynomial.monomial (a + m)) (f.toFun a)).support = {a + m} := by
          subst hxa ham
          simp_all only [ne_eq]
          obtain ⟨w, h⟩ := hn
          obtain ⟨left, right⟩ := h
          ext a : 1
          simp_all
          apply Iff.intro
          · intro a_1
            simp_all only
          · intro a_1
            subst a_1
            simp_all only [true_and]
            exact haf
        have : a + m ∈ ((MvPolynomial.monomial (a + m)) (f.toFun a)).support := by simp_all
        apply MvPolynomial.mem_support_iff.mp
        exact this
      · intro hnz
        have : a + m ∈ ((MvPolynomial.monomial (x + m)) (f.toFun x)).support :=
          MvPolynomial.mem_support_iff.mpr hnz
        have : ((MvPolynomial.monomial (x + m)) (f.toFun x)).support = {x + m} := by
          subst ham
          simp_all only [ne_eq, MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, add_left_inj,
            ite_eq_right_iff, Classical.not_imp]
          obtain ⟨left, right⟩ := this
          obtain ⟨w, h⟩ := hn
          obtain ⟨left_1, right_1⟩ := h
          subst left
          ext a : 1
          simp_all only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, ne_eq, ite_eq_right_iff,
            imp_false, Decidable.not_not, Finset.mem_singleton]
          apply Iff.intro
          · intro a_1
            subst a_1
            simp_all only
          · intro a_1
            subst a_1
            simp_all only
        have : a + m = x + m := by simp_all
        subst ham
        simp_all
    have (x) : MvPolynomial.coeff (a + m) ((MvPolynomial.monomial (x + m)) (f.toFun x)) = if x = a then f.toFun a else 0 := by
      have heq : x = a → MvPolynomial.coeff (a + m) ((MvPolynomial.monomial (x + m)) (f.toFun x)) = f.toFun a := by
        intro hxa
        rw [hxa]
        simp
      have hne : x ≠ a → MvPolynomial.coeff (a + m) ((MvPolynomial.monomial (x + m)) (f.toFun x)) = 0 := by
        contrapose
        push_neg
        exact (this x).mpr
      subst ham
      simp_all only [ne_eq, MvPolynomial.coeff_monomial, add_left_inj, not_false_eq_true, ↓reduceIte,
        Decidable.not_not, not_true_eq_false, implies_true, ite_not]
      obtain ⟨w, h⟩ := hn
      obtain ⟨left, right⟩ := h
      split
      next h => simp_all only [not_true_eq_false, IsEmpty.forall_iff]
      next h => simp_all only [not_false_eq_true, forall_const]
    have : ∑ x ∈ f.support, MvPolynomial.coeff (a + m) ((MvPolynomial.monomial (x + m)) (f.toFun x)) = f.toFun a := by
      have : ∑ x ∈ f.support, MvPolynomial.coeff (a + m) ((MvPolynomial.monomial (x + m)) (f.toFun x))
        = ∑ x ∈ f.support, if x = a then f.toFun a else 0 := by simp_all
      -- let fthen, felse
      sorry
    unfold MvPolynomial.coeff at this

    have : f.toFun a ≠ 0 := haf

    --aesop?
    sorry
  -- 분배법칙 ㅇㄷ?


/-- The set of leading monomials is contained in the set of entire monomials. -/
lemma monset_sub_lms {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K]
  (mo : MonomialOrder σ) (F : Finset (MvPolynomial σ K))
  : leading_monomials_fin mo F ⊆ monomial_set F := by
  unfold leading_monomials_fin
  unfold monomial_set
  simp_all
  intro x hx m hm
  simp_all
  by_cases hF : F = ∅
  · simp_all
  · by_cases hx0 : x = 0
    · unfold leading_monomial at hm
      unfold max_monomial at hm
      simp [hx0] at hm
    · apply Exists.intro x
      constructor
      · exact hx
      · unfold leading_monomial at hm
        have : m ∈ x.support := by
          apply Iff.mp WithBot.map_eq_some_iff at hm
          let ⟨y, hy1, hy2⟩ := hm
          apply Finset.mem_of_max at hy1
          simp_all
        simp_all
