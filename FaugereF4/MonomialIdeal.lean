/-
Copyright (c) 2025 Dongwook Cheon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dongwook Cheon
-/
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Preliminaries on monomial ideals

This file contains concepts and facts needed for describing Groebner basis
and associated algorithms. Some main definitions and lemmas are:
- leading monomial and leading coefficient of a nonzero polynomial,
- equalities and inequalities on leading monomials, related to polynomial operations, and
- monomial ideal and its membership criterion.
-/

/-- The least common multiple of two monomial exponents. -/
def lcm_monomial {σ : Type*} [DecidableEq σ] (m1 m2 : σ →₀ ℕ) : σ →₀ ℕ :=
{
  support := m1.support ∪ m2.support
  toFun := fun x => max (m1 x) (m2 x)
  mem_support_toFun := by
    intro x
    constructor
    · intro h1 h2
      simp_all
    · intro h
      by_contra h'
      simp_all
}

/-- The LCM of a monomial with itself equals itself. -/
lemma self_lcm_monomial_eq_self {σ : Type*} [DecidableEq σ] (m : σ →₀ ℕ) :
    lcm_monomial m m = m := by
  ext x
  simp [lcm_monomial]

/-- Monomial LCM is divided by both its input monomials. -/
lemma le_lcm_monomial {σ : Type*} [DecidableEq σ] (m1 m2 : σ →₀ ℕ) :
    m1 ≤ lcm_monomial m1 m2 ∧ m2 ≤ lcm_monomial m1 m2 := by
  constructor <;>
    intro _ <;>
    simp [lcm_monomial]

/-- The monomial lcm operation is commutative. -/
lemma lcm_monomial_comm {σ : Type*} [DecidableEq σ] (m1 m2 : σ →₀ ℕ) :
    lcm_monomial m1 m2 = lcm_monomial m2 m1 := by
  unfold lcm_monomial
  rw [Finsupp.mk.injEq]
  constructor
  · exact Finset.union_comm _ _
  · ext x
    exact max_comm _ _

/-- The maximum monomial of `S : Finset (σ →₀ ℕ)`, under given monomial order `mo`. -/
noncomputable def max_monomial {σ : Type*} [DecidableEq σ]
  (mo : MonomialOrder σ) (S : Finset (σ →₀ ℕ)) :=
  WithBot.map mo.toSyn.invFun (Finset.map mo.toSyn S).max

/-- A variant of `leading_monomial`: given `S.Nonempty`, the `WithBot` can be peeled off. -/
def max_monomial' {σ : Type*} [DecidableEq σ]
  (mo : MonomialOrder σ) (S : Finset (σ →₀ ℕ)) (hS : S.Nonempty) :=
  mo.toSyn.invFun
    ((Finset.map mo.toSyn.toEmbedding S).max'
      (by simp only [AddEquiv.toEquiv_eq_coe, Finset.map_nonempty]; exact hS))

/-- The maximum monomial is in the original monomial set. -/
lemma maxm'_mem {σ : Type*} [DecidableEq σ]
  (mo : MonomialOrder σ) (S : Finset (σ →₀ ℕ)) (hS : S.Nonempty) :
    max_monomial' mo S hS ∈ S := by
  unfold max_monomial'
  rw [← Finset.mem_map' mo.toSyn.toEmbedding]
  simp [Finset.max'_mem, -Finset.mem_map_equiv]

/-- Maximum monomials equal if the given two monomial sets equal. -/
lemma set_eq_impl_maxm'_eq {σ : Type*} [DecidableEq σ]
  (mo : MonomialOrder σ) (S1 S2 : Finset (σ →₀ ℕ))
  (hS1 : S1.Nonempty) (hS2 : S2.Nonempty) (hSeq : S1 = S2) :
    max_monomial' mo S1 hS1 = max_monomial' mo S2 hS2 := by
  subst hSeq
  simp_all

/-- The leading monomial of polynomial `f`, under given monomial order `mo`. -/
noncomputable def leading_monomial {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) :=
  max_monomial mo f.support

/-- The leading monomial of zero polynomial is `⊥ : WithBot (σ →₀ ℕ)`. -/
lemma lm_zero_eq_bot {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) :
    leading_monomial mo (0 : MvPolynomial σ R) = ⊥ := by
  unfold leading_monomial max_monomial
  simp

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

/-- The leading monomial of a nonzero monomial is itself without its coefficient. -/
lemma lm'_mon {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (μ : σ →₀ ℕ) (c : R) (c_ne_0 : c ≠ 0) :
    have mon_ne_0 : MvPolynomial.monomial μ c ≠ 0 := by simp [c_ne_0]
    leading_monomial' mo (MvPolynomial.monomial μ c) mon_ne_0 = μ := by
  intro mon_ne_0
  have key := lm'_mem mo (MvPolynomial.monomial μ c) mon_ne_0
  simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, ne_eq,
    ite_eq_right_iff, Classical.not_imp] at key
  exact key.1.symm

/-- The leading monomials equal, given the two monomials equal and one of them
is not zero. -/
lemma lm'_eq_of_eq {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ R) (f_eq_g : f = g) (f_not_0 : f ≠ 0) :
    leading_monomial' mo f f_not_0 =
    leading_monomial' mo g (by rw [← f_eq_g]; exact f_not_0) := by
  subst f_eq_g
  simp_all

/-- Each monomial in a polynomial is never greater than the leading monomial
of the polynomial. -/
lemma mem_le_lm' {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) (f_not_0 : f ≠ 0) :
    ∀ m ∈ f.support, mo.toSyn m ≤ mo.toSyn (leading_monomial' mo f f_not_0) := by
  intro m hmf
  unfold leading_monomial' max_monomial'
  rw [← Finset.mem_map' mo.toSyn.toEmbedding] at hmf
  simp only [Equiv.toEmbedding_apply, AddEquiv.toEquiv_eq_coe] at hmf
  simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
    AddEquiv.apply_symm_apply]
  apply Finset.le_max' _ (mo.toSyn m) hmf

/-- `max_monomial'` of a Finset is type-coerced to `max_monomial`, when `S.Nonempty` is
removed. A monomial order version of `Finset.coe_max'`. -/
lemma maxm_coe_maxm' {σ : Type*} [DecidableEq σ]
  (mo : MonomialOrder σ) (S : Finset (σ →₀ ℕ)) (hS : S.Nonempty) :
    max_monomial mo S = ↑(max_monomial' mo S hS) := by
  unfold max_monomial
  unfold max_monomial'
  apply Eq.symm
  rw [WithBot.some_eq_map_iff]
  simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
    EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
  apply Eq.symm
  apply @Finset.coe_max' _ _ (Finset.map mo.toSyn.toEmbedding S)

/-- `leading_monomial'` of a polynomial is type-coerced to `leading_monomial`, when `f ≠ 0` is
removed. A monomial order version of `Finset.coe_max'`. -/
lemma lm_coe_lm' {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) (f_not_0 : f ≠ 0) :
  leading_monomial mo f = ↑(leading_monomial' mo f f_not_0) := by
  unfold leading_monomial
  unfold leading_monomial'
  apply maxm_coe_maxm' mo f.support

/-- The leading coefficient of polynomial `f`, under given monomial order `mo`.
That is, the coefficient of leading monomial of `f`. -/
def leading_coeff' {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) (f_not_0 : f ≠ 0) :=
  f.coeff (leading_monomial' mo f f_not_0)

/-- The leading coefficient of any nonzero polynomial is not zero. -/
lemma lc_not_zero {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) (f_not_0 : f ≠ 0) :
    leading_coeff' mo f f_not_0 ≠ 0 := by
  unfold leading_coeff'
  rw [← MvPolynomial.mem_support_iff]
  apply lm'_mem

/-- If LM(g) precedes LM(f), then the coefficient of f at LM(g) is zero. -/
lemma coeff_zero_of_lt_lm {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ R) (g_ne_0 : g ≠ 0) :
    let lmg := leading_monomial' mo g g_ne_0
    WithBot.map mo.toSyn (leading_monomial mo f) < mo.toSyn lmg → f.coeff lmg = 0 := by
  intro lmg lmf_lt_lmg
  cases em (f = 0) with
  | inl f_eq_0 => simp [f_eq_0]
  | inr f_ne_0 =>
    simp only [lm_coe_lm' mo f f_ne_0, WithBot.map_coe, WithBot.coe_lt_coe] at lmf_lt_lmg
    have supp_f_lt_lmg : ∀ α ∈ f.support, mo.toSyn α < mo.toSyn lmg := by
      intro α hαf
      have : mo.toSyn α ≤ mo.toSyn (leading_monomial' mo f f_ne_0) := by
        apply mem_le_lm' mo f f_ne_0
        exact hαf
      exact lt_of_le_of_lt this lmf_lt_lmg
    rw [← MvPolynomial.notMem_support_iff]
    by_contra HC
    exact Eq.not_lt rfl (supp_f_lt_lmg lmg HC)

/-- A polynomial and its nonzero scalar multiple has the same leading monomial. -/
lemma lm_smul_eq_lm {σ R : Type*} [DecidableEq σ] [CommSemiring R] [IsDomain R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) (c : R) (c_not_0 : c ≠ 0) :
    leading_monomial mo f = leading_monomial mo (c • f) := by
  unfold leading_monomial
  unfold max_monomial
  simp_all

/-- A polynomial and its nonzero scalar multiple has the same leading monomial.
A nonzero-polynomial variant of `lm_smul_eq_lm`. -/
lemma lm'_smul_eq_lm' {σ R : Type*} [DecidableEq σ] [CommSemiring R] [IsDomain R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) (f_not_0 : f ≠ 0) (c : R) (c_not_0 : c ≠ 0) :
    leading_monomial' mo f f_not_0 =
    leading_monomial' mo (c • f) (smul_ne_zero c_not_0 f_not_0) := by
  unfold leading_monomial'
  unfold max_monomial'
  simp_all

/-- Polynomial negation fixes its leading monomial. -/
lemma lm_neg_eq_lm {σ R : Type*} [DecidableEq σ] [CommRing R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) :
    leading_monomial mo f = leading_monomial mo (-f) := by
  unfold leading_monomial
  unfold max_monomial
  simp_all

/-- Polynomial negation fixes its leading monomial. A nonzero-polynomial variant
of `lm_neg_eq_lm`. -/
lemma lm'_neg_eq_lm' {σ R : Type*} [DecidableEq σ] [CommRing R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) (f_not_0 : f ≠ 0) :
    leading_monomial' mo f f_not_0 = leading_monomial' mo (-f) (neg_ne_zero.mpr f_not_0) := by
  unfold leading_monomial'
  unfold max_monomial'
  simp_all

/-- `g - c • f ≠ 0`, given that `f` and `g` are nonzero and the leading monomial of `g`
precedes that of `f`. A partial step for `lm_sub_smul_eq_lm`. -/
lemma sub_smul_ne_0 {σ R : Type*} [DecidableEq σ] [CommRing R] [IsDomain R]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ R)
  (hf : f ≠ 0) (hg : g ≠ 0)
  (hfg : mo.toSyn (leading_monomial' mo f hf) < mo.toSyn (leading_monomial' mo g hg))
  (c : R) :
    g - c • f ≠ 0 := by
  -- If g - c • f was equal to 0, i.e. g = c • f...
  by_contra H
  rw [sub_eq_zero] at H
  rcases em (c = 0) with hc0 | hc0
  · -- case 1: c = 0. This makes g = 0, contradictory to hg : g ≠ 0.
    rw [hc0] at H
    simp at H
    exact hg H
  · -- case 2: c ≠ 0. Then g and f have the same support...
    -- contradictory to hfg : LM(f) < LM(g).
    rw [lm'_smul_eq_lm' mo f hf c hc0] at hfg
    subst H
    simp_all

/-- The leading monomials of `g` and `g - c • f` equal, given that `f` and `g` are
nonzero and the leading monomial of `g` precedes that of `f`. -/
lemma lm_sub_smul_eq_lm {σ R : Type*} [DecidableEq σ] [CommRing R] [IsDomain R]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ R)
  (hf : f ≠ 0) (hg : g ≠ 0)
  (hfg : mo.toSyn (leading_monomial' mo f hf) < mo.toSyn (leading_monomial' mo g hg))
  (c : R) :
    leading_monomial' mo (g - c • f) (sub_smul_ne_0 mo f g hf hg hfg c) =
    leading_monomial' mo g hg := by
  let lmg := leading_monomial' mo g hg
  -- Fact 1: each monomial in g - c • f is a monomial of either g or f.
  have supp_subs : (g - c • f).support ⊆ g.support ∪ f.support := by
    calc
      (g - c • f).support ⊆ g.support ∪ (c • f).support :=
        MvPolynomial.support_sub σ g (c • f)
      _ ⊆ g.support ∪ f.support := by
        apply Finset.union_subset_union
        · exact subset_refl g.support
        · apply MvPolynomial.support_smul
  -- Fact 2: by definition of LM, each monomial in g doesn't exceed LM(g).
  have hmg : ∀ m ∈ g.support, mo.toSyn m ≤ mo.toSyn lmg := mem_le_lm' mo g hg
  -- Fact 3: each monomial in f strictly precedes LM(g).
  have hmfg : ∀ m ∈ f.support, mo.toSyn m < mo.toSyn lmg := by
    intro m hmf
    -- Chaining m ≤ LM(f) with hfg directly gives this fact.
    calc
      mo.toSyn m ≤ mo.toSyn (leading_monomial' mo f hf) := mem_le_lm' mo f hf m hmf
      _ < mo.toSyn lmg := by exact hfg
  -- Fact 4: subtracting c • f from g doesn't erase LM(g).
  have lmg_mem : lmg ∈ (g - c • f).support := by
    simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub,
      MvPolynomial.coeff_smul, smul_eq_mul]
    -- f doesn't have LM(g) as its monomial, according to Fact 3 above.
    have : f.coeff lmg = 0 := by
      rw [← MvPolynomial.notMem_support_iff]
      by_contra H
      let H' := @ne_of_lt _ _ (mo.toSyn lmg) (mo.toSyn lmg)
      rw [← ne_self_iff_false (mo.toSyn lmg)]
      exact H' (hmfg lmg H)
    rw [this]
    simp only [mul_zero, sub_zero]
    -- Conclude by leading coefficient of g not being zero.
    exact lc_not_zero mo g hg
  rw [← AddEquiv.apply_eq_iff_eq mo.toSyn]
  -- Split the goal into less-eq part and greater-eq part.
  apply le_antisymm
  · -- Goal 1: (≤)
    conv in (occs := 1) leading_monomial' _ _ _ => unfold leading_monomial' max_monomial'
    -- The goal is equivalent to:
    -- each monomial in g - c • f doesn't exceed LM(g).
    simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
      AddEquiv.apply_symm_apply, Finset.max'_le_iff, Finset.mem_map_equiv,
      AddEquiv.coe_toEquiv_symm]
    intro y hy
    -- Fact 1 above allows to split the cases: y in g, or y in f.
    apply supp_subs at hy
    simp only [Finset.mem_union] at hy
    cases hy with
    | inl mem_g => -- Case 1: y is a monomial in g. Fact 2 directly proves this case.
      let goal := hmg (mo.toSyn.symm y) mem_g
      rw [AddEquiv.apply_symm_apply] at goal
      exact goal
    | inr mem_f => -- Case 2: y is a monomial in f. Fact 3 directly proves this case.
      apply le_of_lt
      let goal := hmfg (mo.toSyn.symm y) mem_f
      rw [AddEquiv.apply_symm_apply] at goal
      exact goal
  · -- Goal 2: (≥)
    -- Fact 4 proves it: as a monomial of g - c • f, LM(g) cannot exceed LM(g - c • f).
    exact mem_le_lm' mo (g - c • f) (sub_smul_ne_0 mo f g hf hg hfg c) lmg lmg_mem

/-- If the LMs of two polynomials `f1` and `f2` don't exceed the LM of `g`,
then so does the LM of `f1 + f2`. This proves the special case where all the
polynomials involved are nonzero. This leads to `lm_add_le_of_both_lm_le`. -/
lemma lm'_add_le_of_both_lm'_le {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f1 f2 g : MvPolynomial σ R)
  (f1_ne_0 : f1 ≠ 0) (f2_ne_0 : f2 ≠ 0) (fadd_ne_0 : f1 + f2 ≠ 0) (g_ne_0 : g ≠ 0)
  (hf1g :
    mo.toSyn (leading_monomial' mo f1 f1_ne_0) ≤
    mo.toSyn (leading_monomial' mo g g_ne_0))
  (hf2g :
    mo.toSyn (leading_monomial' mo f2 f2_ne_0) ≤
    mo.toSyn (leading_monomial' mo g g_ne_0)) :
    mo.toSyn (leading_monomial' mo (f1 + f2) fadd_ne_0) ≤
    mo.toSyn (leading_monomial' mo g g_ne_0) := by
  simp_all only [leading_monomial', max_monomial',
    AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
    AddEquiv.apply_symm_apply, Finset.max'_le_iff, Finset.mem_map_equiv,
    MvPolynomial.mem_support_iff, MvPolynomial.coeff_add]
  intro μ' f_μ'_coeff_add_ne_0
  let μ := mo.toSyn.symm μ'
  have f_coeff_ne_0 : f1.coeff μ ≠ 0 ∨ f2.coeff μ ≠ 0 := by
    by_contra f_coeff_eq_0
    push_neg at f_coeff_eq_0
    rcases f_coeff_eq_0 with ⟨f1_coeff_eq_0, f2_coeff_eq_0⟩
    subst μ
    rw [f1_coeff_eq_0, f2_coeff_eq_0] at f_μ'_coeff_add_ne_0
    simp at f_μ'_coeff_add_ne_0
  cases f_coeff_ne_0 with
  | inl f1_coeff_ne_0 =>
    exact hf1g μ' f1_coeff_ne_0
  | inr f2_coeff_ne_0 =>
    exact hf2g μ' f2_coeff_ne_0

/-- If the LMs of two polynomials `f1` and `f2` don't exceed the LM of `g`,
then so does the LM of `f1 + f2`. This generalizes `lm'_add_le_of_both_lm'_le`,
to cases in which some polynomials are zero. -/
lemma lm_add_le_of_both_lm_le {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f1 f2 g : MvPolynomial σ R)
  (hf1g :
    WithBot.map mo.toSyn (leading_monomial mo f1) ≤
    WithBot.map mo.toSyn (leading_monomial mo g))
  (hf2g :
    WithBot.map mo.toSyn (leading_monomial mo f2) ≤
    WithBot.map mo.toSyn (leading_monomial mo g)) :
    WithBot.map mo.toSyn (leading_monomial mo (f1 + f2)) ≤
    WithBot.map mo.toSyn (leading_monomial mo g) := by
  cases em (f1 = 0) with
  | inl f1_eq_0 =>
    subst f1
    rw [zero_add]
    exact hf2g
  | inr f1_ne_0 =>
    push_neg at f1_ne_0
    have g_ne_0 : g ≠ 0 := by
      simp only [lm_coe_lm' mo f1 f1_ne_0, WithBot.map_coe] at hf1g
      by_contra g_eq_0
      subst g
      simp [lm_zero_eq_bot] at hf1g
    cases em (f2 = 0) with
    | inl f2_eq_0 =>
      subst f2
      rw [add_zero]
      exact hf1g
    | inr f2_ne_0 =>
      cases em (f1 + f2 = 0) with
      | inl fadd_eq_0 =>
        simp [fadd_eq_0, lm_zero_eq_bot]
      | inr fadd_ne_0 =>
        push_neg at f2_ne_0 fadd_ne_0
        simp only [lm_coe_lm' mo f1 f1_ne_0] at hf1g
        simp only [lm_coe_lm' mo f2 f2_ne_0] at hf2g
        simp_all only [lm_coe_lm' mo (f1 + f2) fadd_ne_0, WithBot.map_coe,
          lm_coe_lm' mo g g_ne_0, WithBot.coe_le_coe]
        exact lm'_add_le_of_both_lm'_le mo f1 f2 g f1_ne_0 f2_ne_0 fadd_ne_0 g_ne_0 hf1g hf2g

/-- If the LMs of two polynomials `f1` and `f2` don't exceed `δ`,
then so does the LM of `f1 + f2`. This is equivalent to `lm_add_le_of_both_lm_le`
with LHS nonzero. -/
lemma lm_add_le_of_both_lm_le_mon {σ R : Type*} [DecidableEq σ] [CommSemiring R] [Nontrivial R]
  (mo : MonomialOrder σ) (f1 f2 : MvPolynomial σ R) (δ : σ →₀ ℕ)
  (hf1g : WithBot.map mo.toSyn (leading_monomial mo f1) ≤ mo.toSyn δ)
  (hf2g : WithBot.map mo.toSyn (leading_monomial mo f2) ≤ mo.toSyn δ) :
    WithBot.map mo.toSyn (leading_monomial mo (f1 + f2)) ≤ mo.toSyn δ := by
  let g := MvPolynomial.monomial δ (1 : R)
  have g_ne_0 : g ≠ 0 := by simp [g]
  have lmg_eq_δ := lm'_mon mo δ (1 : R) one_ne_zero
  have lmg_eq_δ_syn : WithBot.map mo.toSyn (leading_monomial mo g) = mo.toSyn δ := by
    rw [lm_coe_lm' mo _ g_ne_0]
    subst g
    rw [lmg_eq_δ]
    simp only [WithBot.map_coe]
  rw [← lmg_eq_δ_syn] at hf1g hf2g
  rw [← lmg_eq_δ_syn]
  exact lm_add_le_of_both_lm_le mo f1 f2 g hf1g hf2g

/-- A generalization of `lm_add_le_of_both_lm_le_mon` to finite sum. -/
lemma lm_sum_le_of_all_lm_le {σ R ι : Type*}
  [DecidableEq σ] [CommSemiring R] [Nontrivial R] [DecidableEq ι]
  (mo : MonomialOrder σ) (s : Finset ι) (φ : ι → MvPolynomial σ R) (δ : σ →₀ ℕ)
  (hφδ : ∀ i ∈ s, WithBot.map mo.toSyn (leading_monomial mo (φ i)) ≤ mo.toSyn δ) :
    WithBot.map mo.toSyn (leading_monomial mo (∑ i ∈ s, φ i)) ≤ mo.toSyn δ := by
  apply
    Finset.sum_induction φ
      (fun f => WithBot.map mo.toSyn (leading_monomial mo f) ≤ mo.toSyn δ)
      (lm_add_le_of_both_lm_le_mon mo · · δ)
  · simp [lm_zero_eq_bot]
  · exact hφδ

/-- If the LMs of two polynomials `f1` and `f2` strictly precede the LM of `g`,
then so does the LM of `f1 + f2`. This proves the special case where all the
polynomials involved are nonzero. This leads to `lm_add_lt_of_both_lm_lt`. -/
lemma lm'_add_lt_of_both_lm'_lt {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f1 f2 g : MvPolynomial σ R)
  (f1_ne_0 : f1 ≠ 0) (f2_ne_0 : f2 ≠ 0) (fadd_ne_0 : f1 + f2 ≠ 0) (g_ne_0 : g ≠ 0)
  (hf1g :
    mo.toSyn (leading_monomial' mo f1 f1_ne_0) <
    mo.toSyn (leading_monomial' mo g g_ne_0))
  (hf2g :
    mo.toSyn (leading_monomial' mo f2 f2_ne_0) <
    mo.toSyn (leading_monomial' mo g g_ne_0)) :
    mo.toSyn (leading_monomial' mo (f1 + f2) fadd_ne_0) <
    mo.toSyn (leading_monomial' mo g g_ne_0) := by
  simp_all only [leading_monomial', max_monomial', AddEquiv.toEquiv_eq_coe,
    Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, AddEquiv.apply_symm_apply,
    Finset.max'_lt_iff, Finset.mem_map_equiv, MvPolynomial.mem_support_iff,
    MvPolynomial.coeff_add]
  intro μ' f_μ'_coeff_add_ne_0
  let μ := mo.toSyn.symm μ'
  have f_coeff_ne_0 : f1.coeff μ ≠ 0 ∨ f2.coeff μ ≠ 0 := by
    by_contra f_coeff_eq_0
    push_neg at f_coeff_eq_0
    rcases f_coeff_eq_0 with ⟨f1_coeff_eq_0, f2_coeff_eq_0⟩
    subst μ
    rw [f1_coeff_eq_0, f2_coeff_eq_0] at f_μ'_coeff_add_ne_0
    simp at f_μ'_coeff_add_ne_0
  cases f_coeff_ne_0 with
  | inl f1_coeff_ne_0 =>
    exact hf1g μ' f1_coeff_ne_0
  | inr f2_coeff_ne_0 =>
    exact hf2g μ' f2_coeff_ne_0

/-- If the LMs of two polynomials `f1` and `f2` strictly precede the LM of `g`,
then so does the LM of `f1 + f2`. This generalizes `lm'_add_lt_of_both_lm'_lt`,
to cases in which some polynomials are zero. -/
lemma lm_add_lt_of_both_lm_lt {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (f1 f2 g : MvPolynomial σ R)
  (hf1g :
    WithBot.map mo.toSyn (leading_monomial mo f1) <
    WithBot.map mo.toSyn (leading_monomial mo g))
  (hf2g :
    WithBot.map mo.toSyn (leading_monomial mo f2) <
    WithBot.map mo.toSyn (leading_monomial mo g)) :
    WithBot.map mo.toSyn (leading_monomial mo (f1 + f2)) <
    WithBot.map mo.toSyn (leading_monomial mo g) := by
  cases em (f1 = 0) with
  | inl f1_eq_0 =>
    subst f1
    rw [zero_add]
    exact hf2g
  | inr f1_ne_0 =>
    push_neg at f1_ne_0
    have g_ne_0 : g ≠ 0 := by
      simp only [lm_coe_lm' mo f1 f1_ne_0, WithBot.map_coe] at hf1g
      by_contra g_eq_0
      subst g
      simp [lm_zero_eq_bot] at hf1g
    cases em (f2 = 0) with
    | inl f2_eq_0 =>
      subst f2
      rw [add_zero]
      exact hf1g
    | inr f2_ne_0 =>
      cases em (f1 + f2 = 0) with
      | inl fadd_eq_0 =>
        simp [fadd_eq_0, lm_zero_eq_bot, lm_coe_lm' mo g g_ne_0]
      | inr fadd_ne_0 =>
        push_neg at f2_ne_0 fadd_ne_0
        simp only [lm_coe_lm' mo f1 f1_ne_0] at hf1g
        simp only [lm_coe_lm' mo f2 f2_ne_0] at hf2g
        simp_all only [lm_coe_lm' mo (f1 + f2) fadd_ne_0, WithBot.map_coe,
          lm_coe_lm' mo g g_ne_0, WithBot.coe_lt_coe]
        exact lm'_add_lt_of_both_lm'_lt mo f1 f2 g f1_ne_0 f2_ne_0 fadd_ne_0 g_ne_0 hf1g hf2g

/-- If the LMs of two polynomials `f1` and `f2` strictly precede `δ`,
then so does the LM of `f1 + f2`. This is equivalent to `lm_add_lt_of_both_lm_lt`
with LHS nonzero. -/
lemma lm_add_lt_of_both_lm_lt_mon {σ R : Type*} [DecidableEq σ] [CommSemiring R] [Nontrivial R]
  (mo : MonomialOrder σ) (f1 f2 : MvPolynomial σ R) (δ : σ →₀ ℕ)
  (hf1g : WithBot.map mo.toSyn (leading_monomial mo f1) < mo.toSyn δ)
  (hf2g : WithBot.map mo.toSyn (leading_monomial mo f2) < mo.toSyn δ) :
    WithBot.map mo.toSyn (leading_monomial mo (f1 + f2)) < mo.toSyn δ := by
  let g := MvPolynomial.monomial δ (1 : R)
  have g_ne_0 : g ≠ 0 := by simp [g]
  have lmg_eq_δ := lm'_mon mo δ (1 : R) one_ne_zero
  have lmg_eq_δ_syn : WithBot.map mo.toSyn (leading_monomial mo g) = mo.toSyn δ := by
    rw [lm_coe_lm' mo _ g_ne_0]
    subst g
    rw [lmg_eq_δ]
    simp only [WithBot.map_coe]
  rw [← lmg_eq_δ_syn] at hf1g hf2g
  rw [← lmg_eq_δ_syn]
  exact lm_add_lt_of_both_lm_lt mo f1 f2 g hf1g hf2g

/-- A generalization of `lm_add_lt_of_both_lm_lt_mon` to finite sum. -/
lemma lm_sum_lt_of_all_lm_lt {σ R ι : Type*}
  [DecidableEq σ] [CommSemiring R] [Nontrivial R] [DecidableEq ι]
  (mo : MonomialOrder σ) (s : Finset ι) (φ : ι → MvPolynomial σ R) (δ : σ →₀ ℕ)
  (hφδ : ∀ i ∈ s, WithBot.map mo.toSyn (leading_monomial mo (φ i)) < mo.toSyn δ) :
    WithBot.map mo.toSyn (leading_monomial mo (∑ i ∈ s, φ i)) < mo.toSyn δ := by
  apply
    Finset.sum_induction φ
      (fun f => WithBot.map mo.toSyn (leading_monomial mo f) < mo.toSyn δ)
      (lm_add_lt_of_both_lm_lt_mon mo · · δ)
  · simp [lm_zero_eq_bot]
  · exact hφδ

/-- For two monomials `m1` and `m2` which add up to `LM(f) + LM(g)`,
`(m1, m2) = (LM(f), LM(g))` exactly when the coefficient of `m1` in `f` and
that of `m2` in `g` don't multiply up to zero. A substep for `lm'_mul_commute`. -/
lemma lm_lm_antidiag_only_nonzero_coeff {σ R : Type*} [DecidableEq σ] [CommSemiring R] [IsDomain R]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ R) (f_not_0 : f ≠ 0) (g_not_0 : g ≠ 0) :
    let lmf := leading_monomial' mo f f_not_0
    let lmg := leading_monomial' mo g g_not_0
    ∀ mp ∈ Finset.antidiagonal (lmf + lmg),
      (f.coeff mp.1 * g.coeff mp.2 ≠ 0 ↔ mp = (lmf, lmg)) := by
  intro lmf lmg ⟨mf, mg⟩ mem_lmfg_ad
  simp only [Finset.mem_antidiagonal] at mem_lmfg_ad -- rewrites to `m1 + m2 = LM(f) + LM(g)`
  simp only [mul_ne_zero_iff, Prod.mk.injEq]
  -- The goal is translated to:
  -- coeff of `m1` in `f` ≠ 0 and coeff of `m2` in `g` ≠ 0 iff `m1 = LM(f)` and `m2 = LM(g)`
  constructor -- We make use of mo.lo & mo.iocam from here!
  · -- Goal 1: (==>). Suppose both coeffs are nonzero.
    intro ⟨cf_ne_0, cg_ne_0⟩
    -- Suppose at least one of `m1 = LM(f)` and `m2 = LM(g)` doesn't hold.
    by_contra m_ne_lm
    push_neg at m_ne_lm
    cases em (mf = lmf) with
    | inl mf_eq_lmf => -- Case 1: `m1 = LM(f)`
      -- This directly contradicts to `m1 + m2 = LM(f) + LM(g)`.
      subst mf
      simp_all
    | inr mf_ne_lmf => -- Case 2: `m1 ≠ LM(f)`
      have mf_supp_f : mf ∈ f.support := by simp [cf_ne_0]
      have mg_supp_g : mg ∈ g.support := by simp [cg_ne_0]
      -- m1 < LM(f) and m2 ≤ LM(g).
      have mf_lt_lmf : mo.toSyn mf < mo.toSyn lmf := by
        apply lt_of_le_of_ne
        · exact mem_le_lm' mo f f_not_0 mf mf_supp_f
        · simp [mf_ne_lmf]
      have mg_le_lmg : mo.toSyn mg ≤ mo.toSyn lmg :=
        mem_le_lm' mo g g_not_0 mg mg_supp_g
      -- Adding these two inequality results in `m1 + m2 < LM(f) + LM(g)`.
      -- This contradicts to `m1 + m2 = LM(f) + LM(g)`.
      -- Refine the goal to obtain the contradiction.
      rw [← AddEquiv.apply_eq_iff_eq mo.toSyn] at mem_lmfg_ad
      simp only [map_add] at mem_lmfg_ad
      absurd mem_lmfg_ad
      apply ne_of_lt
      calc
        mo.toSyn mf + mo.toSyn mg < mo.toSyn lmf + mo.toSyn mg :=
          add_lt_add_right mf_lt_lmf (mo.toSyn mg)
        _ ≤ mo.toSyn lmf + mo.toSyn lmg :=
          add_le_add_left mg_le_lmg (mo.toSyn lmf)
  · -- Goal 2: (<==). Suppose `m1 = LM(f)` and `m2 = LM(g)`.
    intro ⟨mf_eq_lmf, mg_eq_lmg⟩
    subst mf mg
    -- Then the coeffs are leading coeffs of f and g respectively, which are nonzero.
    exact ⟨lc_not_zero mo f f_not_0, lc_not_zero mo g g_not_0⟩

/-- The LM of `f * g` equals the product of LMs of `f` and `g`. -/
lemma lm'_mul_commute {σ R : Type*} [DecidableEq σ] [CommSemiring R] [IsDomain R]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ R) (f_not_0 : f ≠ 0) (g_not_0 : g ≠ 0) :
    have fg_not_0 : f * g ≠ 0 := mul_ne_zero f_not_0 g_not_0
    let lmf := leading_monomial' mo f f_not_0
    let lmg := leading_monomial' mo g g_not_0
    let lmfg := leading_monomial' mo (f * g) fg_not_0
    lmf + lmg = lmfg := by
  intro fg_not_0 lmf lmg lmfg
  simp only [leading_monomial', max_monomial', AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe,
    AddEquiv.coe_toEquiv_symm, lmf, lmg, lmfg]
  -- Rewrite the goal into terms of mo.syn.
  rw [← AddEquiv.map_add mo.toSyn.symm, AddEquiv.apply_eq_iff_eq]
  symm
  rw [Finset.max'_eq_iff] -- requires mathlib v4.22.0-rc4 or later
  constructor
  -- This splits the goal LM(f) + LM(g) = LM(f * g) into two goals.
  · -- Goal 1: LM(f) + LM(g) is among the monomials of f * g.
    --         i.e. the coefficient of LM(f) + LM(g) in f * g is not zero.
    rw [Finset.mem_map_equiv, MvPolynomial.mem_support_iff]
    -- Such the coefficient equals the coeff products over the antidiagonal of LM(f) + LM(g).
    simp only [AddEquiv.coe_toEquiv_symm, map_add, MvPolynomial.coeff_mul]
    -- We show the goal by showing that the only nonzero summand is that on (LM(f), LM(g)).
    -- Step 1: an equivalence condition for a pair in the antidiagonal of LM(f) + LM(g)
    --         to equal (LM(f), LM(g))
    have only_fg_term_combi :
        ∀ mp ∈ Finset.antidiagonal (lmf + lmg),
          (f.coeff mp.1 * g.coeff mp.2 ≠ 0 ↔ mp = (lmf, lmg)) :=
      lm_lm_antidiag_only_nonzero_coeff mo f g f_not_0 g_not_0
    -- Step 2: all the summands but on (LM(f), LM(g)) are zero, hence sum up to zero.
    have sum_except_eq_zero :
        ∑ mp ∈ (Finset.antidiagonal (lmf + lmg)).erase (lmf, lmg),
          f.coeff mp.1 * g.coeff mp.2 = 0 := by
      apply Finset.sum_eq_zero
      intro mp mp_mem_erase
      rw [Finset.mem_erase] at mp_mem_erase
      rcases mp_mem_erase with ⟨mp_ne_pair, mp_mem⟩
      have key := only_fg_term_combi mp mp_mem
      simp only [ne_eq, ← key] at mp_ne_pair
      push_neg at mp_ne_pair
      exact mp_ne_pair
    -- Step 3: the antidiagonal sum of coeff products equals LC(f) * LC(g).
    have final_sum_eq :=
      @Finset.sum_insert _ _ _ _ _
        (fun mp => f.coeff mp.1 * g.coeff mp.2) _
        (Finset.notMem_erase (lmf, lmg) (Finset.antidiagonal (lmf + lmg)))
    rw [Finset.insert_erase (Finset.mem_antidiagonal.mpr rfl), sum_except_eq_zero] at final_sum_eq
    simp only [leading_monomial', max_monomial', AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe,
      AddEquiv.coe_toEquiv_symm, add_zero, lmf, lmg] at final_sum_eq
    -- LC(f) * LC(g) ≠ 0 finishes the goal.
    rw [final_sum_eq]
    exact (only_fg_term_combi (lmf, lmg) (Finset.mem_antidiagonal.mpr rfl)).mpr rfl
  · -- Goal 2: each monomial in f * g is not greater than LM(f) + LM(g).
    intro mfg' mfg'_supp_fg
    -- Refine the monomial membership in f * g, using `(f * g).support ⊆ f.support + g.support`.
    simp only [Finset.mem_map_equiv, AddEquiv.coe_toEquiv_symm] at mfg'_supp_fg
    apply MvPolynomial.support_mul at mfg'_supp_fg
    rw [← AddEquiv.coe_toEquiv_symm, ← Finset.mem_map_equiv] at mfg'_supp_fg
    simp only [Finset.mem_map, Equiv.coe_toEmbedding, EquivLike.coe_coe] at mfg'_supp_fg
    rcases mfg'_supp_fg with ⟨mfg, mfg_supp_add, mfg_eq_mfg'⟩
    -- Some monomial pair, each in f and g, multiplies up to a monomial of f * g.
    rw [Finset.mem_add] at mfg_supp_add
    rcases mfg_supp_add with ⟨mf, mf_supp_f, mg, mg_supp_g, mf_add_mg⟩
    -- Each monomial in f and g is not greater than LM(f) and LM(g) respectively.
    -- Hence so is the sum, compared to LM(f) + LM(g).
    simp only [← AddEquiv.apply_eq_iff_eq mo.toSyn, map_add] at mf_add_mg
    rw [← mfg_eq_mfg', ← mf_add_mg]
    apply add_le_add
    · exact Finset.le_max' _ (mo.toSyn mf) (by simp [mf_supp_f])
    · exact Finset.le_max' _ (mo.toSyn mg) (by simp [mg_supp_g])

/-- Excluding the leading term of a polynomial gives a strictly smaller leading monomial. -/
lemma lm_sub_leadterm_lt_lm {σ R : Type*} [DecidableEq σ] [CommRing R] [Nontrivial R]
  (mo : MonomialOrder σ) (f : MvPolynomial σ R) (f_ne_0 : f ≠ 0)
  : let lmf := leading_monomial' mo f f_ne_0
    let lcf := f.coeff lmf
    let ltf := MvPolynomial.monomial lmf lcf
    WithBot.map mo.toSyn (leading_monomial mo (f - ltf)) < mo.toSyn lmf := by
  intro lmf lcf ltf
  have lcf_ne_0 : lcf ≠ 0 := lc_not_zero mo f f_ne_0
  apply lt_of_le_of_ne
  · rw [sub_eq_add_neg]
    apply lm_add_le_of_both_lm_le_mon
    · simp [lmf, lm_coe_lm' mo f f_ne_0, WithBot.map_coe]
    · simp only [← lm_neg_eq_lm, ltf]
      rw [
        lm_coe_lm' mo _
        (by simp only [ne_eq, MvPolynomial.monomial_eq_zero]; exact lcf_ne_0)
      ]
      simp [WithBot.map_coe, lm'_mon mo lmf lcf lcf_ne_0]
  · rw [← WithBot.map_coe]
    by_contra lm_sub_ltf_eq_lm
    unfold leading_monomial max_monomial at lm_sub_ltf_eq_lm
    simp only [WithBot.map, AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
      Option.map_map, AddEquiv.self_comp_symm, Option.map_id, id_eq] at lm_sub_ltf_eq_lm
    apply Finset.mem_of_max at lm_sub_ltf_eq_lm
    simp [ltf, lcf] at lm_sub_ltf_eq_lm

/-- The finite set of leading monomials of `f ∈ F` for finite `F`,
  under a given monomial order `mo`. -/
noncomputable def leading_monomials_fin {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (F : Finset (MvPolynomial σ R)) : Finset (σ →₀ ℕ) :=
  F.biUnion (fun (f : MvPolynomial σ R) => (leading_monomial mo f).toFinset)

/-- The set of leading monomials of `f ∈ F`,
  under a given monomial order `mo`. -/
def leading_monomials {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (F : Set (MvPolynomial σ R)) : Set (σ →₀ ℕ) :=
  ((fun (f : MvPolynomial σ R) => SetLike.coe (leading_monomial mo f).toFinset) '' F).sUnion

/-- A monomial ideal is a polynomial ideal generated by some set of monomials. -/
def monomial_ideal {σ : Type*} (K : Type*) [DecidableEq σ] [Field K]
  (S : Set (σ →₀ ℕ)) : Ideal (MvPolynomial σ K) :=
  Ideal.span ((fun (s : σ →₀ ℕ) => MvPolynomial.monomial s (1 : K)) '' S)

/-- The set of entire monomials which appear in one of `f ∈ F`. -/
def monomial_set {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (F : Finset (MvPolynomial σ R)) : Finset (σ →₀ ℕ) :=
  F.biUnion MvPolynomial.support

/-- The monomial set of a singleton is exactly the support of the element. -/
lemma singleton_monset_eq_support {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (f : MvPolynomial σ R) :
    monomial_set {f} = f.support := by
  unfold monomial_set
  simp

/-- Taking monomial set and taking union of polynomial sets commute. -/
lemma monomial_set_union_distrib {σ R : Type*} [DecidableEq σ] [CommSemiring R] [DecidableEq R]
  (F G : Finset (MvPolynomial σ R)) :
    monomial_set (F ∪ G) = monomial_set F ∪ monomial_set G := by
  unfold monomial_set
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_biUnion] at hx
    rcases hx with ⟨f, hf, hx⟩
    rw [Finset.mem_union] at hf
    simp only [Finset.mem_union, Finset.mem_biUnion]
    cases hf with
    | inl hfF =>
      apply Or.inl
      exists f
    | inr hfG =>
      apply Or.inr
      exists f
  · intro hx
    simp only [Finset.mem_union, Finset.mem_biUnion]
    simp only [Finset.mem_biUnion, Finset.mem_union] at hx
    rcases hx with (⟨f, hfF, hx⟩ | ⟨g, hgG, hx⟩)
    · exact ⟨f, Or.inl hfF, hx⟩
    · exact ⟨g, Or.inr hgG, hx⟩

/-- Zero polynomial doesn't affect a monomial set. -/
lemma monomial_set_erase_zero {σ R : Type*} [DecidableEq σ] [CommSemiring R] [DecidableEq R]
  (F : Finset (MvPolynomial σ R)) :
    monomial_set (F.erase 0) = monomial_set F := by
  unfold monomial_set
  cases (em (0 ∈ F)) with
  | inl zero_mem =>
    conv_rhs => rw [← Finset.insert_erase zero_mem]
    simp
  | inr zero_not_mem =>
    simp [zero_not_mem]

/-- Taking leading monomial of a polynomial and multiplying a monomial commutes.
This is a corollary of `lm'_mul_commute`. -/
lemma lm'_monmul_commute {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f : MvPolynomial σ K) (f_not_0 : f ≠ 0)
  (m : σ →₀ ℕ) (a : K) (ha : a ≠ 0) :
    leading_monomial' mo (f * MvPolynomial.monomial m a) (mul_ne_zero f_not_0 (by simp [ha])) =
    leading_monomial' mo f f_not_0 + m := by
  have key := lm'_mul_commute mo f (MvPolynomial.monomial m a) f_not_0 (by simp [ha])
  simp only at key
  rw [← key, add_right_inj]
  exact lm'_mon mo m a ha

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

/-- Cancelation rule of monomial division and multiplication. -/
@[simp]
lemma monomial_sub_add {σ : Type*} (m n : σ →₀ ℕ) (hmn : m ≤ n) :
    n - m + m = n := by
  ext s
  simp
  have : m s ≤ n s := by apply hmn
  simp_all only [Nat.sub_add_cancel]

/-- `WithBot`-coercion can be peeled off in divisibility relation, given the
less-eq side is nonzero. -/
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

/-- The set of leading monomials is contained in the set of entire monomials. -/
lemma lms_subset_monset {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K]
  (mo : MonomialOrder σ) (F : Finset (MvPolynomial σ K)) :
    leading_monomials_fin mo F ⊆ monomial_set F := by
  unfold leading_monomials_fin
  unfold monomial_set
  simp_all
  intro x hx m hm
  simp_all only [Option.mem_toFinset, Option.mem_def, Finset.mem_biUnion,
    MvPolynomial.mem_support_iff]
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

/-- A monomial `μ` divides `ν`, if and only if there exists a polynomial `f`
such that the `μ`-multiple of `f` has `ν` as a monomial. -/
lemma mem_monmul_supp_iff {σ : Type*} {K : Type*} [DecidableEq σ] [Field K]
  {μ ν : σ →₀ ℕ} :
    μ ≤ ν ↔ ∃ f : MvPolynomial σ K, ν ∈ (f * (MvPolynomial.monomial μ) 1).support := by
  constructor
  · intro hμν
    exists (MvPolynomial.monomial (ν - μ)) 1
    simp_all [monomial_sub_add]
  · intro ⟨f, hνf⟩
    cases (em (f = 0)) with
    | inl hf0 => simp_all
    | inr hfn0 =>
      simp only [MvPolynomial.mem_support_iff, ne_eq] at hνf
      simp only [MvPolynomial.coeff_mul_monomial', mul_one, ite_eq_right_iff,
        Classical.not_imp] at hνf
      exact hνf.1

/-- A monomial `ν` is in a monomial ideal `⟨M⟩`,
exactly when some basis element `μ` divides the monomial `ν`. -/
lemma mon_mem_moni_iff {σ : Type*} {K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (ν : σ →₀ ℕ) (M : Set (σ →₀ ℕ)) :
    MvPolynomial.monomial ν 1 ∈ monomial_ideal K M ↔ ∃ μ ∈ M, μ ≤ ν := by
  constructor
  · -- Goal 1: (==>)
    unfold monomial_ideal
    unfold Ideal.span
    -- Membership in a span ↔ sum of ring element multiple of basis elements
    rw [Submodule.mem_span_iff_exists_finset_subset]
    intro ⟨φ, S, hSM, hφS, hsumS⟩
    -- `hsumS : ∑ a ∈ S, φ a • a = (MvPolynomial.monomial ν) 1`. Both side have the same support.
    have ν_sum_supp :
        ν ∈ (∑ a ∈ S, φ a • a).support := by
      rw [hsumS, MvPolynomial.support_monomial]
      simp
    -- auxiliary steps to apply MvPolynomial.support_sum
    let sum_fun (a : MvPolynomial σ K) := φ a • a
    have : ∑ a ∈ S, φ a • a = ∑ a ∈ S, sum_fun a := by unfold sum_fun; rfl
    rw [this] at ν_sum_supp
    -- membership in the support of a sum → membership in the union of supports of summands
    apply MvPolynomial.support_sum at ν_sum_supp
    simp only [smul_eq_mul, Finset.mem_biUnion, sum_fun] at ν_sum_supp
    let ⟨f, hfS, hνf⟩ := ν_sum_supp
    apply hSM at hfS
    rw [Set.mem_image] at hfS
    let ⟨μ, hμM, hμf⟩ := hfS
    rw [← hμf] at hνf
    -- Now we have membership of `ν` in the support of some polynomial multiple of `μ`.
    -- Use 'μ' to show the result.
    exists μ
    constructor
    · exact hμM
    · rw [@mem_monmul_supp_iff σ K]
      exists φ ((MvPolynomial.monomial μ) 1)
  · -- Goal 2: (<==)
    intro ⟨μ, hμ, hμν⟩
    let δ := ν - μ
    -- key step: `ν` is a product of `μ` and `ν - μ`
    have ν_eq_μδ
      : (MvPolynomial.monomial ν) (1 : K)
      = (MvPolynomial.monomial μ) 1 * (MvPolynomial.monomial δ) 1 := by
      simp_all only [MvPolynomial.monomial_mul, add_tsub_cancel_of_le, mul_one, δ]
    rw [ν_eq_μδ, monomial_ideal]
    -- Take a singleton subset `{μ}` of the basis
    have μ_mem_basis :
        {(MvPolynomial.monomial μ) (1 : K)} ⊆ (fun s ↦ (MvPolynomial.monomial s) 1) '' ↑M := by
      simp_all
    apply Ideal.span_mono μ_mem_basis
    -- Membership in an ideal generated by a singleton is equivalent to divisibility
    -- by the singleton element.
    -- We are done, since the key step above shows the divisibility.
    rw [Ideal.mem_span_singleton]
    exists (MvPolynomial.monomial δ) 1

/-- A monomial `ν` with any nonzero coefficient is in a monomial ideal `⟨M⟩`,
exactly when some basis element `μ` divides the monomial `ν`. -/
lemma term_mem_moni_iff {σ : Type*} {K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (ν : σ →₀ ℕ) (M : Set (σ →₀ ℕ)) (c : K) (hc : c ≠ 0)
  : MvPolynomial.monomial ν c ∈ monomial_ideal K M ↔ ∃ μ ∈ M, μ ≤ ν := by
  rw [← @mon_mem_moni_iff σ K]
  constructor
  · intro mc_mem
    apply Ideal.mul_mem_left (monomial_ideal K M) (MvPolynomial.C c⁻¹) at mc_mem
    simp only [MvPolynomial.C_mul_monomial, ne_eq, hc, not_false_eq_true,
      inv_mul_cancel₀] at mc_mem
    exact mc_mem
  · intro m1_mem
    apply Ideal.mul_mem_left (monomial_ideal K M) (MvPolynomial.C c) at m1_mem
    simp only [MvPolynomial.C_mul_monomial, mul_one] at m1_mem
    exact m1_mem

/-- A characterization lemma on membership in a monomial ideal.
A polynomial `f` is in a monomial ideal `⟨M⟩`, exactly when each monomial of `f`
is divisible by a basis monomial in `M`. -/
lemma mem_moni_iff {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (f : MvPolynomial σ K) (M : Set (σ →₀ ℕ))
  : f ∈ monomial_ideal K M ↔ ∀ ν ∈ f.support, ∃ μ ∈ M, μ ≤ ν := by
  constructor
  · -- Goal 1: (==>)
    intro f_mem_IM ν ν_supp_f
    unfold monomial_ideal at f_mem_IM
    rw [Ideal.span, Submodule.mem_span_iff_exists_finset_subset] at f_mem_IM
    rcases f_mem_IM with ⟨φ, F, F_subs_M, φ_supp_F, φ_sum_f⟩
    -- Now we have a (MvPolynomial σ K)-linear combination rep'n, ∑ a ∈ F, φ a • a = f,
    -- over a finite subset F of M.
    rw [← φ_sum_f] at ν_supp_f
    apply MvPolynomial.support_sum at ν_supp_f
    -- Then a monomial ν in f is also in some φ mμ • mμ, for some mμ ∈ F.
    simp only [smul_eq_mul, Finset.mem_biUnion] at ν_supp_f
    rcases ν_supp_f with ⟨mμ, mμ_mem_F, ν_supp_φμμ⟩
    -- Extract the exponent μ of mμ to obtain μ ∈ M, and apply it to existential quantifier.
    apply F_subs_M at mμ_mem_F
    rw [Set.mem_image] at mμ_mem_F
    rcases mμ_mem_F with ⟨μ, μ_mem_M, μ_eq_mμ⟩
    exists μ, μ_mem_M
    -- It remains to show μ \le ν, which directly comes from `mem_monmul_supp_iff`.
    rw [@mem_monmul_supp_iff σ K]
    exists φ mμ
    rw [μ_eq_mμ]
    exact ν_supp_φμμ
  · -- Goal 2: (<==)
    intro M_div_mon_f
    -- It suffices to show that each term in f is in the monomial ideal ⟨M⟩ of M.
    rw [← MvPolynomial.support_sum_monomial_coeff f]
    apply Ideal.sum_mem
    intro ν ν_supp_f
    -- Translate the termwise membership in ⟨M⟩ into the monomial divisibility condition.
    rw [term_mem_moni_iff ν M (f.coeff ν) (MvPolynomial.mem_support_iff.mp ν_supp_f)]
    -- This is exactly what we have as the assumption.
    exact M_div_mon_f ν ν_supp_f
