import Mathlib
import FaugereF4.GroebnerBasis

/-!
# Faugere F4 algorithm

This file formalizes Faugere's F4 algorithm, which computes
a Groebner basis of any finite-variable polynomial ideal,
given a finite generator set.

## Reference
* [Cox, Little and O'Shea, *Ideals, varieties, and algorithms*][coxlittleoshea1997]
-/

open Classical
-- universe u v
-- variable {σ : Type u} {K : Type v} [Finite σ] [DecidableEq σ] [Field K]

/-- WellFoundedRelation instance on the `WithTop syn` type of a monomial order;
this is needed for termination proof of symbolic preprocessing. -/
instance {σ : Type*} (mo : MonomialOrder σ) : WellFoundedRelation (WithTop mo.syn) :=
  WellFoundedLT.toWellFoundedRelation

/-- The struct to iterate through symbolic preprocessing. -/
structure SymbProcStruct
  (σ : Type*) (K : Type*) (mo : MonomialOrder σ)
  [Finite σ] [DecidableEq σ] [Field K] where
  H : Finset (MvPolynomial σ K)
  done_mons : Finset (σ →₀ ℕ) -- the set of monomials considered until then
  done_sub_H : done_mons ⊆ monomial_set H
  last_mon : WithTop mo.syn
  h_last_mon (not_top : last_mon ≠ ⊤) :
    mo.toSyn.invFun (last_mon.get (by
      cases last_mon with
      | top => simp_all
      | coe lmon => simp_all; rfl
    )) ∈ done_mons

/-- Symbolic preprocessing subroutine in F4. This returns a finite superset `H'`
of a given `H : Finset (MvPolynomial σ K)`, which satisfies the following:
for any `m ∈ monomial_set H` which has some `f ∈ H` whose leading monomial
divides `m`, this `H` has the monomial multiple of `f` whose leading monomial is
adjusted to be `m`. -/
noncomputable def symbolic_preprocess_rec {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K]
  (mo : MonomialOrder σ)
  (G : Finset (MvPolynomial σ K))
  (sps : SymbProcStruct σ K mo) :=
  let mon_H := monomial_set sps.H
  if hmons : sps.done_mons = mon_H
    then -- no more monomials to be considered
      sps
    else
      have monset_nonempty : (Finset.map mo.toSyn.toEmbedding (mon_H \ sps.done_mons)).Nonempty := by
        have : sps.done_mons ⊂ mon_H := by
          apply ssubset_iff_subset_ne.mpr
          exact ⟨sps.done_sub_H, hmons⟩
        have : (mon_H \ sps.done_mons).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          simp
          exact not_subset_of_ssubset this
        exact Finset.map_nonempty.mpr this
      let b' := @Finset.max' _ mo.lo (Finset.map mo.toSyn (mon_H \ sps.done_mons)) monset_nonempty -- done_sub_H is needed for this
      let b := mo.toSyn.invFun b'
      let done_mons := {b} ∪ sps.done_mons
      have b_mem_mon_H : b ∈ mon_H := by
        unfold b
        simp
        have : ∃ b'' ∈ mon_H, mo.toSyn b'' = b' := by
          exists b
          constructor
          · unfold b
            apply (Finset.mem_map' mo.toSyn.toEmbedding).mp
            have : b' = mo.toSyn.toEmbedding (mo.toSyn.invFun b') := by simp
            rw [← this]
            unfold mon_H
            unfold b'
            have : Finset.map mo.toSyn.toEmbedding (mon_H \ sps.done_mons)
              ⊆ Finset.map mo.toSyn.toEmbedding mon_H := by simp_all
            apply this
            exact Finset.max'_mem _ _
          · unfold b
            simp_all
        let ⟨b'', mem_b'', syn_b''⟩ := this
        have : b = b'' := by
          unfold b
          rw [← syn_b'']
          simp
        subst this
        simp_all only [Equiv.invFun_as_coe, AddEquiv.toEquiv_eq_coe,
          AddEquiv.coe_toEquiv_symm, AddEquiv.apply_symm_apply, mon_H, b', b]
      have done_sub_H : done_mons ⊆ mon_H := by
        unfold done_mons
        intro c
        simp_all
        intro c_mem
        cases c_mem with
        | inl hcb =>
          subst hcb
          exact b_mem_mon_H
        | inr hcH =>
          apply sps.done_sub_H
          exact hcH
      let SubG := {f ∈ G | f ≠ 0 ∧ leading_monomial mo f ≤ b}
      have b'_notin_last_done : mo.toSyn.invFun b' ∉ sps.done_mons := by
        sorry
      have b'_mem_done : mo.toSyn.invFun b' ∈ done_mons := by
        sorry
      have b'_lt_lmon : b' < sps.last_mon := by -- termination proof
        induction sps.last_mon
        case top =>
          apply WithTop.coe_lt_top _
        case coe lmon =>
          apply WithTop.coe_lt_coe.mpr
          sorry
      symbolic_preprocess_rec mo G (
        if h_div_able : SubG ≠ ∅
          then
            have : SubG.Nonempty := by
              rw [Finset.nonempty_iff_ne_empty]
              exact h_div_able
            let f := this.choose -- noncomputable from here
            let hf' := this.choose_spec
            have hf : f ≠ 0 ∧ leading_monomial mo f ≤ b := by
              have : f ∈ SubG := by
                unfold f
                exact hf'
              unfold SubG at this
              simp_all
            -- let ⟨f, hf⟩ := @Finset.Nonempty.exists_mem _ SubG this -- goal이 Prop이 아니면 이렇게 쓸 수 없다
            let H := {f * MvPolynomial.monomial (b - leading_monomial' mo f hf.1) 1} ∪ sps.H
            {
              H := H
              done_mons := done_mons
              done_sub_H := by
                have : monomial_set sps.H ⊆ monomial_set H := by
                  unfold monomial_set
                  have : sps.H ⊆ H := by unfold H; simp
                  exact Finset.biUnion_subset_biUnion_of_subset_left _ this
                unfold mon_H at done_sub_H
                exact subset_trans done_sub_H this
              last_mon := ↑b'
              h_last_mon := sorry
            }
          else
            {
              H := sps.H
              done_mons := done_mons
              done_sub_H := done_sub_H
              last_mon := ↑b'
              h_last_mon := sorry
            }
      )
termination_by sps.last_mon -- b'_lt_lmon
decreasing_by
  -- exact b'_lt_lmon
  sorry
/-
done_mons의 원소가 모두 mon_H \ done_mons의 원소보다 크다
b'는 mon_H \ done_mons에서 뽑아낸 최대원소
lmon은? 바로 앞단계 iter의 mon_H \ done_mons에서 뽑아낸 최대원소
lmon을 나누는 f가 G 안에...
있었다 => H에 f*~(s.t. lmon이 max mon)을 더함 (=> mon_H 단조증가)
없었다 => H 그대로 유지
-/

noncomputable def symbolic_preprocess {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K]
  (mo : MonomialOrder σ)
  (G : Finset (MvPolynomial σ K))
  (H : Finset (MvPolynomial σ K)) :=
  (symbolic_preprocess_rec mo G {
    H := H
    done_mons := ∅
    done_sub_H := by simp
    last_mon := ⊤
    h_last_mon := by simp
  }).H

-- def



structure F4Struct (σ : Type*) (K : Type*) [Finite σ] [DecidableEq σ] [Field K] where
  G : Finset (MvPolynomial σ K)
  size : ℕ
  pairs : Finset (Finset ℕ)

-- def F4_iter_step (m : MonomialOrder σ)

def F4 {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K]
  (F : Finset (MvPolynomial σ K)) : Finset (MvPolynomial σ K) :=
  sorry
