import FaugereF4.GaussianElim
import FaugereF4.GroebnerBasis
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.List.ToFinsupp
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Faugere F4 algorithm

This file formalizes Faugere's F4 algorithm, which computes
a Groebner basis of any finite-variable polynomial ideal,
given a finite generator set.
-/

/-! ## Symbolic preprocessing -/

/-- WellFoundedRelation instance on the `WithTop syn` type of a monomial order;
this is needed for termination proof of symbolic preprocessing. -/
instance withtop_mo_syn_wf {σ : Type*} (mo : MonomialOrder σ) :
    WellFoundedRelation (WithTop mo.syn) :=
  WellFoundedLT.toWellFoundedRelation

/-- The struct to iterate through symbolic preprocessing. -/
structure SymbProcStruct
  (σ : Type*) (K : Type*)
  [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (G H0 : Finset (MvPolynomial σ K)) where
  /-- Increasing set of polynomials, to which several polynomials of the form $x^αg$
  for $g ∈ G$ would be inserted. -/
  H : Finset (MvPolynomial σ K)
  /-- H contains the starting set H0. -/
  H0_sub_H : H0 ⊆ H
  /-- Every element in H is a monomial multiple of some element in G. -/
  H_sub_monmul_G : ↑H ⊆ {mg | ∃ g ∈ G, ∃ α : σ →₀ ℕ, ∃ c : K, mg = g * MvPolynomial.monomial α c}
  /-- This H is always contained in the span of G. -/
  H_sub_ideal_G : ↑H ⊆ (Ideal.span G : Ideal (MvPolynomial σ K)).carrier
  /-- H doesn't have zero as an element -/
  zero_not_mem_H : 0 ∉ H
  /-- The set of monomials considered until then -/
  done_mons : Finset (σ →₀ ℕ)
  /-- `done_mons` is contained in Mon(H) in each step -/
  done_sub_H : done_mons ⊆ monomial_set H
  /-- ⊤, or most recently considered monomial.
  This strictly decreases in `symbolic_preprocess_rec`. -/
  last_mon : WithTop mo.syn
  /-- `last_mon` must be in `done_mons`, except for the first loop -/
  lmon_done (not_top : last_mon ≠ ⊤) :
    mo.toSyn.invFun (last_mon.get (by
      cases last_mon with
      | top => simp_all
      | coe lmon => simp_all; rfl
    )) ∈ done_mons
  /-- Any "not-done" monomial is less than last_mon -/
  nd_lt_lmon (ndm : σ →₀ ℕ) :
    ndm ∈ monomial_set H \ done_mons → mo.toSyn ndm < last_mon
  /-- If a monomial m ∈ monomial_set H is divisible by LM(g), for some g ∈ G of
  current (initial, or possibly extended) basis set, then H itself has
  n * g (∃ monomial n) where LM(n * g) = m.
  Since the recursion continues while done_mons ⊊ Mon(H), it suffices to check
  in each step that (2) holds for monomials in done_mons. -/
  div_then_cont_mult :
    ∀ m ∈ done_mons,
      (¬∃ g ∈ G, leading_monomial mo g ≤ m) ∨
      (∃ g ∈ G, ∃ α : σ →₀ ℕ,
        (MvPolynomial.monomial α 1) * g ∈ H ∧
        leading_monomial mo ((MvPolynomial.monomial α 1) * g) = m)

set_option maxHeartbeats 400000 in
-- the definition requires more than 200000 heartbeats
/-- One step of symbolic preprocessing. This loop continues until the monomial set
of `sps.H` is fully processed, i.e. each monomial in `sps.H` satisfies
`sps.div_then_cont_mult`. -/
noncomputable def symbolic_preprocess_step {σ K : Type*}
  [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (G H0 : Finset (MvPolynomial σ K)) (hG : 0 ∉ G)
  (sps : SymbProcStruct σ K mo G H0)
  (hmons : ¬sps.done_mons = monomial_set sps.H) : SymbProcStruct σ K mo G H0 :=
  let mon_H := monomial_set sps.H
  have monset_nonempty : (Finset.map mo.toSyn.toEmbedding (mon_H \ sps.done_mons)).Nonempty := by
    have : sps.done_mons ⊂ mon_H := by
      apply ssubset_iff_subset_ne.mpr
      exact ⟨sps.done_sub_H, hmons⟩
    have : (mon_H \ sps.done_mons).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      simp only [ne_eq, Finset.sdiff_eq_empty_iff_subset]
      exact not_subset_of_ssubset this
    exact Finset.map_nonempty.mpr this
  -- ...then the max mon can be taken; this requires done_sub_H
  let b' := @Finset.max' _ mo.lo (Finset.map mo.toSyn (mon_H \ sps.done_mons)) monset_nonempty
  let b := mo.toSyn.invFun b' -- actual monomial type
  let done_mons := {b} ∪ sps.done_mons -- include b into done
  -- this b is taken from a subset of mon_H, hence is a member of mon_H
  have b_mem_mon_H : b ∈ mon_H := by
    unfold b
    simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm]
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
    simp_all only [Finset.mem_union, Finset.mem_singleton]
    intro c_mem
    cases c_mem with
    | inl hcb =>
      subst hcb
      exact b_mem_mon_H
    | inr hcH =>
      apply sps.done_sub_H
      exact hcH
  let SubG := {f ∈ G | leading_monomial mo f ≤ b}
  have b_notin_last_done : b ∉ sps.done_mons := by
    unfold b
    have : b' ∈ Finset.map mo.toSyn.toEmbedding (mon_H \ sps.done_mons) := by
      unfold b'
      exact Finset.max'_mem _ _
    simp_all
  have b_in_done : b ∈ done_mons := by
    unfold done_mons
    simp
  have nd_lt_b (ndm : σ →₀ ℕ) : -- proof of nd_lt_lmon
    ndm ∈ mon_H \ done_mons → (mo.toSyn ndm) < b' := by
    have lem_1 : mon_H \ done_mons = (mon_H \ sps.done_mons).erase b := by -- autogenerated by aesop
      simp_all only [Equiv.invFun_as_coe, AddEquiv.toEquiv_eq_coe,
        AddEquiv.coe_toEquiv_symm, Finset.mem_union, Finset.mem_singleton,
        or_false, b, mon_H, b', done_mons]
      ext a
      simp_all only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton,
        not_or, Finset.mem_erase, ne_eq]
      constructor
      · intro a_1
        simp_all only [not_false_eq_true, and_self]
      · intro a_1
        simp_all only [not_false_eq_true, and_self]
    have lem_2 :
      Finset.map mo.toSyn.toEmbedding (mon_H \ done_mons) =
      (Finset.map mo.toSyn.toEmbedding (mon_H \ sps.done_mons)).erase b' := by
      have :
        Finset.map mo.toSyn.toEmbedding (mon_H \ done_mons) =
        (Finset.map mo.toSyn.toEmbedding ((mon_H \ sps.done_mons).erase b)) := by
        simp_all
      have :
        (Finset.map mo.toSyn.toEmbedding ((mon_H \ sps.done_mons).erase b)) =
        (Finset.map mo.toSyn.toEmbedding (mon_H \ sps.done_mons)).erase b' := by
        unfold b'
        simp_all only [Equiv.invFun_as_coe, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv_symm,
          Finset.mem_union, Finset.mem_singleton, or_false, Finset.map_erase,
          Equiv.coe_toEmbedding, EquivLike.coe_coe, AddEquiv.apply_symm_apply,
          b, mon_H, done_mons, b']
      simp_all
    intro ndm_mem
    have lem_3 :
      mo.toSyn ndm ∈ (Finset.map mo.toSyn.toEmbedding (mon_H \ sps.done_mons)).erase b' := by
      rw [← lem_2]
      have : mo.toSyn ndm = mo.toSyn.toEmbedding ndm := by simp
      rw [this]
      simp only [Finset.mem_map', ndm_mem]
    unfold b'
    unfold b' at lem_3
    exact Finset.lt_max'_of_mem_erase_max'
      (Finset.map mo.toSyn.toEmbedding (mon_H \ sps.done_mons))
      monset_nonempty
      lem_3
  if h_div_able : SubG ≠ ∅
    then
      have SubG_occ : SubG.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        exact h_div_able
      let f := SubG_occ.choose -- noncomputable from here
      let hf' := SubG_occ.choose_spec
      have f_mem_SubG : f ∈ SubG := by
        unfold f
        exact hf'
      have f_mem_G : f ∈ G := by
        simp_all only [ne_eq, Equiv.invFun_as_coe,
          AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv_symm,
          Finset.mem_union, Finset.mem_singleton, or_false, Finset.mem_sdiff,
          not_or, and_imp, Finset.mem_filter, mon_H, done_mons, b, b', SubG, f]
      have f_not_0 : f ≠ 0 := by
        simp_all [mon_H, SubG, done_mons, b, f, b']
        apply Aesop.BuiltinRules.not_intro
        intro a
        simp_all
      let lmf := leading_monomial' mo f f_not_0
      have lmf_div_b : lmf ≤ b := by
        unfold lmf
        unfold SubG at SubG_occ
        have : leading_monomial mo f ≤ b := by
          simp_all [mon_H, b, b', done_mons, SubG, f]
        apply nonzero_lm'_div_impl_lm_div
        exact this
      let mulf := f * MvPolynomial.monomial (b - lmf) (1 : K)
      have lm_mulf :
        leading_monomial' mo mulf (by
          simp_all [SubG, b', f, b, mon_H, done_mons, lmf, mulf]
        ) = b := by
        unfold mulf
        rw [lm'_monmul_commute mo f f_not_0 _ _ (by simp)]
        rw [add_comm]
        apply monomial_sub_add
        exact lmf_div_b
      let H := {mulf} ∪ sps.H
      {
        H := H
        H0_sub_H := by
          unfold H
          intro h h_mem_H0
          rw [Finset.mem_union]
          exact Or.inr (sps.H0_sub_H h_mem_H0)
        H_sub_monmul_G := by
          unfold H
          simp only [Finset.coe_union, Set.union_subset_iff]
          constructor
          · simp only [Finset.coe_singleton, Set.singleton_subset_iff, Set.mem_setOf_eq]
            exists f, f_mem_G, b - lmf, 1
          · exact sps.H_sub_monmul_G
        H_sub_ideal_G := by
          unfold H
          simp only [Finset.coe_union, Set.union_subset_iff]
          constructor
          · rw [Finset.coe_singleton, Set.singleton_subset_iff]
            unfold mulf
            have : Ideal.span {f} ≤ Ideal.span G := by
              apply Ideal.span_mono
              simp only [Set.singleton_subset_iff, Finset.mem_coe]
              exact f_mem_G
            apply this
            rw [Ideal.mem_span_singleton]
            simp
          · exact sps.H_sub_ideal_G
        zero_not_mem_H := by
          unfold H
          simp only [Finset.mem_union, Finset.mem_singleton, not_or, ne_eq]
          constructor
          · simp_all [SubG, b', f, b, mon_H, done_mons, lmf, mulf]
          · exact sps.zero_not_mem_H
        done_mons := done_mons
        done_sub_H := by
          have : monomial_set sps.H ⊆ monomial_set H := by
            unfold monomial_set
            have : sps.H ⊆ H := by unfold H; simp
            exact Finset.biUnion_subset_biUnion_of_subset_left _ this
          unfold mon_H at done_sub_H
          exact subset_trans done_sub_H this
        last_mon := ↑b'
        lmon_done := by
          intro not_top
          simp_all only [Equiv.invFun_as_coe, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv_symm,
            Finset.mem_union, Finset.mem_singleton, or_false, Finset.mem_sdiff, not_or, and_imp,
            ne_eq, Finset.mem_filter, true_and, EmbeddingLike.apply_eq_iff_eq, mon_H, b, b',
            done_mons, SubG, f]
          apply Or.inl
          rfl
        nd_lt_lmon := by
          unfold mon_H at nd_lt_b
          simp only [Finset.mem_sdiff, WithTop.coe_lt_coe, and_imp]
          simp only [Finset.mem_sdiff, and_imp] at nd_lt_b
          intro ndm ndm_mem_mon_H
          have mon_H_union : monomial_set H = monomial_set {mulf} ∪ monomial_set sps.H := by
            unfold H
            exact union_monset_commute {mulf} sps.H
          have ndm_mem_cases : ndm ∈ monomial_set {mulf} ∨ ndm ∈ monomial_set sps.H := by
            rw [mon_H_union] at ndm_mem_mon_H
            exact Finset.mem_union.mp ndm_mem_mon_H
          -- case 1: ndm ∈ monomial_set sps.H
          ---- direct by nd_lt_b
          -- case 2: ndm ∈ monomial_set H \ monomial_set sps.H
          ---- then ndm ∈ monomial_set {mulf}
          cases ndm_mem_cases with
          | inl ndm_mem_mulf =>
            rw [singleton_monset_eq_support] at ndm_mem_mulf
            -- unfold mulf at ndm_mem_mulf
            -- rw [monomial_set_mul_monomial] at ndm_mem_mulf
            intro ndm_not_done
            have ndm_ne_b : ndm ≠ b := (ne_of_mem_of_not_mem b_in_done ndm_not_done).symm
            have syn_ndm_ne_b : mo.toSyn ndm ≠ b' := by
              unfold b at ndm_ne_b
              have : mo.toSyn ndm ≠ mo.toSyn (mo.toSyn.invFun b') := by
                by_contra nconc
                rw [AddEquiv.apply_eq_iff_eq] at nconc
                exact ndm_ne_b nconc
              simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
                AddEquiv.apply_symm_apply, ne_eq] at this
              exact this
            have syn_ndm_le_b : mo.toSyn ndm ≤ b' := by
              unfold leading_monomial' at lm_mulf
              unfold max_monomial' at lm_mulf
              unfold b at lm_mulf
              rw [← AddEquiv.apply_eq_iff_eq mo.toSyn] at lm_mulf
              simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
                AddEquiv.apply_symm_apply] at lm_mulf
              rw [← lm_mulf]
              apply Finset.le_max'
              simp_all
            exact lt_iff_le_and_ne.mpr ⟨syn_ndm_le_b, syn_ndm_ne_b⟩
          | inr ndm_mem_prev_mon_H =>
            exact nd_lt_b ndm ndm_mem_prev_mon_H
        div_then_cont_mult := by
          intro m m_done
          by_cases m_eq_b : m = b
          · apply Or.inr
            exists f
            constructor
            · exact f_mem_G
            · exists b - lmf
              subst m
              constructor
              · simp [H, mulf, mul_comm]
              · unfold mulf at lm_mulf
                conv_lhs => rw [mul_comm]
                conv_rhs => rw [← lm_mulf]
                apply lm_coe_lm'
          · have : m ∈ sps.done_mons := by
              unfold done_mons at m_done
              simp_all
            cases (sps.div_then_cont_mult m this) with
            | inl h_div_able =>
              apply Or.inl
              push_neg
              intro g g_mem_G
              simp only [not_exists, not_and] at h_div_able
              exact h_div_able g g_mem_G
            | inr h_cont_mult =>
              apply Or.inr
              let ⟨g, g_mem_G, α, g_mmul_mem_sps_H, lm_g_mmul_eq_m⟩ := h_cont_mult
              exists g, g_mem_G, α
              constructor
              · unfold H
                apply Finset.mem_union_right
                exact g_mmul_mem_sps_H
              · exact lm_g_mmul_eq_m
      }
    else
      {
        H := sps.H
        H0_sub_H := sps.H0_sub_H
        H_sub_monmul_G := sps.H_sub_monmul_G
        H_sub_ideal_G := sps.H_sub_ideal_G
        zero_not_mem_H := sps.zero_not_mem_H
        done_mons := done_mons
        done_sub_H := done_sub_H
        last_mon := ↑b'
        lmon_done := by
          intro _
          apply b_in_done
        nd_lt_lmon := by
          unfold mon_H at nd_lt_b
          simp_all
        div_then_cont_mult := by
          intro m m_done
          by_cases m_eq_b : m = b
          · apply Or.inl
            push_neg
            intro g g_G
            simp only [ne_eq, Decidable.not_not] at h_div_able
            let g_not_in_SubG :=
              (@Finset.eq_empty_iff_forall_notMem (MvPolynomial σ K) SubG).mp h_div_able g
            unfold SubG at g_not_in_SubG
            simp only [Finset.mem_filter, not_and] at g_not_in_SubG
            rw [m_eq_b]
            exact g_not_in_SubG g_G
          · have : m ∈ sps.done_mons := by
              unfold done_mons at m_done
              simp_all
            exact sps.div_then_cont_mult m this
      }

/-- Termination proof for symbolic preprocessing. The monomial processed in each
step decreases under the specified monomial order `mo`. -/
lemma sps_last_mon_decr {σ K : Type*}
  [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (G H0 : Finset (MvPolynomial σ K)) (hG : 0 ∉ G)
  (sps : SymbProcStruct σ K mo G H0)
  (hmons : ¬sps.done_mons = monomial_set sps.H) :
    (symbolic_preprocess_step mo G H0 hG sps hmons).last_mon < sps.last_mon := by
  let mon_H := monomial_set sps.H
  have monset_nonempty : (Finset.map mo.toSyn.toEmbedding (mon_H \ sps.done_mons)).Nonempty := by
    have : sps.done_mons ⊂ mon_H := by
      apply ssubset_iff_subset_ne.mpr
      exact ⟨sps.done_sub_H, hmons⟩
    have : (mon_H \ sps.done_mons).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      simp only [ne_eq, Finset.sdiff_eq_empty_iff_subset]
      exact not_subset_of_ssubset this
    exact Finset.map_nonempty.mpr this
  let b' := @Finset.max' _ mo.lo (Finset.map mo.toSyn (mon_H \ sps.done_mons)) monset_nonempty
  let b := mo.toSyn.invFun b'
  have b_mem_mon_H : b ∈ mon_H := by
    unfold b
    simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm]
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
  let SubG := {f ∈ G | leading_monomial mo f ≤ b}
  have b_notin_last_done : b ∉ sps.done_mons := by
    unfold b
    have : b' ∈ Finset.map mo.toSyn.toEmbedding (mon_H \ sps.done_mons) := by
      unfold b'
      exact Finset.max'_mem _ _
    simp_all
  have b'_lt_lmon : b' < sps.last_mon := by -- termination proof
    by_cases init_or_step : sps.last_mon = ⊤
    · rw [init_or_step]
      exact WithTop.coe_lt_top b'
    · have b_mem : b ∈ mon_H \ sps.done_mons := by simp_all
      unfold mon_H at b_mem
      have concl : ↑(mo.toSyn b) < sps.last_mon := sps.nd_lt_lmon b b_mem
      have : mo.toSyn b = b' := by
        unfold b
        simp
      rw [this] at concl
      trivial
  unfold symbolic_preprocess_step
  unfold b' at b'_lt_lmon
  simp_all only [Equiv.invFun_as_coe, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv_symm,
    ne_eq, dite_not, gt_iff_lt, mon_H, b, b']
  split
  next h => simp_all
  next h => simp_all

/-- Recursive definition of symbolic preprocessing. -/
noncomputable def symbolic_preprocess_rec {σ K : Type*}
  [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (G H0 : Finset (MvPolynomial σ K)) (hG : 0 ∉ G)
  (sps : SymbProcStruct σ K mo G H0) :
    SymbProcStruct σ K mo G H0 :=
  let mon_H := monomial_set sps.H
  if hmons : sps.done_mons = mon_H
    then -- no more monomials to be considered
      sps
    else -- one or more monomials are left to be considered
      symbolic_preprocess_rec mo G H0 hG (symbolic_preprocess_step mo G H0 hG sps hmons)
termination_by sps.last_mon
decreasing_by
  unfold WellFoundedRelation.rel withtop_mo_syn_wf -- WellFoundedLT.toWellFoundedRelation
  apply sps_last_mon_decr

/-- Initial `SymbProcStruct` object to iterate through `symbolic_preprocess_rec`. -/
def sps_init {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (G : Finset (MvPolynomial σ K))
  (H0 : Finset (MvPolynomial σ K)) (hH0 : 0 ∉ H0)
  (hGH0 : ↑H0 ⊆ {mg | ∃ g ∈ G, ∃ α : σ →₀ ℕ, ∃ c : K, mg = g * MvPolynomial.monomial α c}) :
    SymbProcStruct σ K mo G H0 :=
  {
    H := H0
    H0_sub_H := by rfl
    H_sub_monmul_G := hGH0
    H_sub_ideal_G := by
      intro h hhH0
      apply hGH0 at hhH0
      simp only [Set.mem_setOf_eq] at hhH0
      rcases hhH0 with ⟨g, hgG, α, c, hlgαc⟩
      rw [hlgαc]
      have : Ideal.span {g} ≤ Ideal.span G := by
        apply Ideal.span_mono
        simp [hgG]
      apply this
      simp [Ideal.mem_span_singleton]
    zero_not_mem_H := hH0
    done_mons := ∅
    done_sub_H := by simp
    last_mon := ⊤
    lmon_done := by simp
    nd_lt_lmon := by simp
    div_then_cont_mult := by simp
  }

/-- Wrapper definition of symbolic preprocessing. -/
noncomputable def symbolic_preprocess {σ : Type*} {K : Type*}
  [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G)
  (H0 : Finset (MvPolynomial σ K)) (hH0 : 0 ∉ H0)
  (hGH0 : ↑H0 ⊆ {mg | ∃ g ∈ G, ∃ α : σ →₀ ℕ, ∃ c : K, mg = g * MvPolynomial.monomial α c}) :
    SymbProcStruct σ K mo G H0 :=
  symbolic_preprocess_rec mo G H0 hG (sps_init mo G H0 hH0 hGH0)

/-- Auxiliary induction argument for `symbolic_preprocess_done_mons`. -/
lemma symbolic_preprocess_rec_done_mons {σ K : Type*}
  [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (G H0 : Finset (MvPolynomial σ K)) (hG : 0 ∉ G)
  (last_mon : WithTop mo.syn) :
    ∀ sps : SymbProcStruct σ K mo G H0,
      sps.last_mon = last_mon →
      let sps' := symbolic_preprocess_rec mo G H0 hG sps
      sps'.done_mons = monomial_set sps'.H := by
  induction last_mon using WellFounded.induction (withtop_mo_syn_wf mo).wf with
  | h μ IH =>
    rw [WellFoundedRelation.rel, withtop_mo_syn_wf] at IH
    intro sps μ_eq_lm
    cases (em (sps.done_mons = monomial_set sps.H)) with
    | inl mons_eq =>
      rw [symbolic_preprocess_rec]
      split_ifs
      exact mons_eq
    | inr mons_ne =>
      subst μ
      let sps' := symbolic_preprocess_step mo G H0 hG sps mons_ne
      have lm'_lt_lm : sps'.last_mon < sps.last_mon := by
        apply sps_last_mon_decr
      let IH' := IH sps'.last_mon lm'_lt_lm sps' (by rfl)
      simp only at IH'
      have sp_idem :
        symbolic_preprocess_rec mo G H0 hG sps' = symbolic_preprocess_rec mo G H0 hG sps := by
        unfold sps'
        conv_rhs => unfold symbolic_preprocess_rec
        simp only [right_eq_dite_iff]
        intro mons_eq
        by_contra _
        exact mons_ne mons_eq
      simp only [← sp_idem]
      exact IH'

/-- The termination condition of `symbolic_preprocess`. -/
lemma symbolic_preprocess_done_mons {σ K : Type*}
  [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G)
  (H0 : Finset (MvPolynomial σ K)) (hH0 : 0 ∉ H0)
  (hGH0 : ↑H0 ⊆ {mg | ∃ g ∈ G, ∃ α : σ →₀ ℕ, ∃ c : K, mg = g * MvPolynomial.monomial α c}) :
    let sps := symbolic_preprocess mo G hG H0 hH0 hGH0
    sps.done_mons = monomial_set sps.H := by
  simp only [symbolic_preprocess]
  exact symbolic_preprocess_rec_done_mons mo G H0 hG ⊤ (sps_init mo G H0 hH0 hGH0) (by rfl)

lemma span_ge_symb_proc_red_0_induction {σ K : Type*}
  [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G)
  (L : Finset (MvPolynomial σ K)) (hL : 0 ∉ L)
  (hGL : ↑L ⊆ {mg | ∃ g ∈ G, ∃ α : σ →₀ ℕ, ∃ c : K, mg = g * MvPolynomial.monomial α c}) :
    let sp_L := symbolic_preprocess mo G hG L hL hGL
    let ge_L' := gaussian_elim mo sp_L.H
    let N := ge_L'.SO
    let N' := N.filter (fun n => ∀ l ∈ sp_L.H, ¬leading_monomial mo l ≤ leading_monomial mo n)
    let V : Submodule K (MvPolynomial σ K) := Submodule.span K sp_L.H
    ∀ μ' : mo.syn, ∀ f ∈ V,
      (f_ne_0 : f ≠ 0) →
      leading_monomial' mo f f_ne_0 = mo.toSyn.invFun μ' →
      reduces_to_zero mo f f_ne_0 (G ∪ N') := by
  intro sp_L ge_L' N N' V μ'
  induction μ' using WellFounded.induction (@wellFounded_lt _ _ mo.wf) with
  | h μ'_ IH =>
    intro f f_mem_V f_ne_0 lmf_eq_μ
    unfold V at f_mem_V
    rw [← ge_L'.span_V] at f_mem_V
    have : ge_L'.SI = ∅ := gaussian_elim_SI_empty mo sp_L.H
    simp only [this, Finset.coe_empty, Set.empty_union] at f_mem_V
    let f_mem_V_ := f_mem_V
    apply mem_span_ge_exists_same_lm_mem mo sp_L.H at f_mem_V_
    rcases f_mem_V_ f_ne_0 with ⟨n, hn, lmf_eq_lmn⟩
    have n_ne_0 : n ≠ 0 := ne_of_mem_of_not_mem hn ge_L'.zero_not_mem_SO
    let f' := f - f.coeff (leading_monomial' mo n n_ne_0) • n
    have f'_mem_V : f' ∈ V := by
      have f_n_subset_V : {f, n} ⊆ V.carrier := by
        rw [Set.pair_subset_iff]
        unfold V
        rw [← ge_L'.span_V, gaussian_elim_SI_empty mo sp_L.H]
        simp only [Finset.coe_empty, Set.empty_union, Submodule.carrier_eq_coe, SetLike.mem_coe]
        constructor
        · exact f_mem_V
        · unfold ge_L'
          apply Submodule.subset_span
          exact hn
      unfold f'
      apply @Submodule.span_mono K at f_n_subset_V
      unfold V at f_n_subset_V
      conv_rhs at f_n_subset_V => rw [Submodule.carrier_eq_coe, Submodule.span_span]
      apply f_n_subset_V
      rw [Submodule.mem_span_pair]
      exists 1, -f.coeff (leading_monomial' mo n n_ne_0)
      simp only [one_smul, neg_smul]
      ring
    have f'_eq_0_or_lmf'_lt_lmf (f'_ne_0 : f' ≠ 0) :
      mo.toSyn (leading_monomial' mo f' f'_ne_0) < mo.toSyn (leading_monomial' mo f f_ne_0) := by
      conv_lhs => unfold leading_monomial' max_monomial'
      simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
        AddEquiv.apply_symm_apply, Finset.max'_lt_iff, Finset.mem_map_equiv]
      intro α' α_supp_f'
      apply lt_of_le_of_ne
      · unfold f' at α_supp_f'
        rw [sub_eq_add_neg] at α_supp_f'
        apply MvPolynomial.support_add at α_supp_f'
        rw [Finset.mem_union] at α_supp_f'
        cases α_supp_f' with
        | inl α_supp_f =>
          unfold leading_monomial' max_monomial'
          simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
            AddEquiv.apply_symm_apply]
          apply Finset.le_max'
          simp_all
        | inr α_supp_n =>
          rw [← neg_smul (f.coeff (leading_monomial' mo n n_ne_0)) n] at α_supp_n
          apply MvPolynomial.support_smul at α_supp_n
          rw [lmf_eq_lmn]
          unfold leading_monomial' max_monomial'
          simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
            AddEquiv.apply_symm_apply]
          apply Finset.le_max'
          simp_all
      · simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
        smul_eq_mul, ne_eq, f'] at α_supp_f'
        contrapose α_supp_f'
        simp only [ne_eq, Decidable.not_not] at α_supp_f'
        subst α'
        simp only [AddEquiv.symm_apply_apply, sub_eq_zero, Decidable.not_not]
        conv_rhs => rw [lmf_eq_lmn]
        have lcn_eq_1 := ge_L'.out_lc_one n hn
        unfold leading_coeff' at lcn_eq_1
        simp [lcn_eq_1, lmf_eq_lmn]
    rw [← AddEquiv.apply_eq_iff_eq mo.toSyn] at lmf_eq_μ
    simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
      AddEquiv.apply_symm_apply] at lmf_eq_μ
    subst μ'_
    cases em (n ∈ N') with
    | inl n_mem_N' =>
      cases em (f' = 0) with
      | inl f'_eq_0 =>
        subst f'
        rw [sub_eq_zero] at f'_eq_0
        let lmn := leading_monomial' mo n n_ne_0
        let cf := f.coeff lmn
        let A : MvPolynomial σ K → MvPolynomial σ K :=
          fun x => if x = n then MvPolynomial.C cf else 0
        exists A
        subst A
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_union, Or.inr n_mem_N',
          ↓reduceIte, ne_eq, ite_eq_right_iff, mul_eq_zero, map_eq_zero, Classical.not_imp, not_or]
        constructor
        · rw [f'_eq_0]
          apply MvPolynomial.smul_eq_C_mul
        · intro g g_mem_basis' ⟨g_eq_n, cf_ne_0, g_ne_0⟩
          subst g
          simp only [↓reduceIte, ge_iff_le]
          apply le_of_eq
          rw [AddEquiv.apply_eq_iff_eq]
          apply lm'_eq_of_eq mo (MvPolynomial.C cf * n) f
          rw [f'_eq_0]
          rw [MvPolynomial.smul_eq_C_mul n cf]
      | inr f'_ne_0 =>
        have IH' := IH _ (f'_eq_0_or_lmf'_lt_lmf f'_ne_0) f' f'_mem_V f'_ne_0 (by simp)
        have key :=
          mul_basis_add_red_0 mo (G ∪ N')
            n (by rw [Finset.mem_union]; exact Or.inr n_mem_N') n_ne_0
            f' f'_ne_0 IH'
            0 (f.coeff (leading_monomial' mo n n_ne_0)) (by rw [← lmf_eq_lmn]; apply lc_not_zero)
            (by
              simp only [MvPolynomial.monomial_zero', gt_iff_lt]
              rw [← lm'_eq_of_eq mo
                ((f.coeff (leading_monomial' mo n n_ne_0)) • n)
                (MvPolynomial.C (f.coeff (leading_monomial' mo n n_ne_0)) * n)
                (MvPolynomial.smul_eq_C_mul n _)
                (by
                  apply smul_ne_zero
                  · rw [← lmf_eq_lmn]
                    apply lc_not_zero
                  · exact n_ne_0)]
              rw [← lm'_smul_eq_lm' mo n n_ne_0 _ (by rw [← lmf_eq_lmn]; apply lc_not_zero)]
              rw [← lmf_eq_lmn]
              exact f'_eq_0_or_lmf'_lt_lmf f'_ne_0)
        simp only [MvPolynomial.monomial_zero'] at key
        have : f = f' + MvPolynomial.C (f.coeff (leading_monomial' mo n n_ne_0)) * n := by
          simp [f', MvPolynomial.smul_eq_C_mul]
        have key' := red_0_of_eq mo f _ this f_ne_0 (G ∪ N')
        exact key'.mpr key
    | inr n_not_mem_N' =>
      simp only [Finset.mem_filter, not_and, not_forall, Decidable.not_not, N'] at n_not_mem_N'
      rcases n_not_mem_N' hn with ⟨l, l_mem_L', lml_le_lmn⟩
      have l_ne_0 : l ≠ 0 := ne_of_mem_of_not_mem l_mem_L' sp_L.zero_not_mem_H
      have key := sp_L.div_then_cont_mult
      have lmn_mem_monset_L' : leading_monomial' mo n n_ne_0 ∈ sp_L.done_mons := by
        rw [symbolic_preprocess_done_mons mo G hG L hL hGL]
        rw [← ge_L'.monset_fixed, gaussian_elim_SI_empty mo sp_L.H]
        simp only [Finset.empty_union]
        unfold monomial_set
        rw [Finset.mem_biUnion]
        exists n
        exact ⟨hn, lm'_mem mo n n_ne_0⟩
      have key := key _ lmn_mem_monset_L'
      have l_eq_g_monmul := sp_L.H_sub_monmul_G l_mem_L'
      simp only [Set.mem_setOf_eq] at l_eq_g_monmul
      rcases l_eq_g_monmul with ⟨g, g_mem_G, α, c, hlgαc⟩
      have g_ne_0 : g ≠ 0 := ne_of_mem_of_not_mem g_mem_G hG
      have c_ne_0 : c ≠ 0 := by
        by_contra c_eq_0
        simp only [c_eq_0, MvPolynomial.monomial_zero, mul_zero] at hlgαc
        exact l_ne_0 hlgαc
      have lmg_le_lml : leading_monomial mo g ≤ leading_monomial mo l := by
        simp only [lm_coe_lm' mo g g_ne_0, lm_coe_lm' mo l l_ne_0, WithBot.coe_le_coe]
        rw [lm'_eq_of_eq mo l _ hlgαc l_ne_0]
        rw [lm'_monmul_commute mo g g_ne_0 α c c_ne_0]
        simp only [le_add_iff_nonneg_right, zero_le]
      rw [← imp_iff_not_or, ← lm_coe_lm' mo n n_ne_0] at key
      have key := key ⟨g, g_mem_G, le_trans lmg_le_lml lml_le_lmn⟩
      rcases key with ⟨g, g_mem_G, α, αg_mem_L', lmαg_eq_lmn⟩
      have g_ne_0 : g ≠ 0 := ne_of_mem_of_not_mem g_mem_G hG
      have αg_ne_0 : (MvPolynomial.monomial α) 1 * g ≠ 0 :=
        ne_of_mem_of_not_mem αg_mem_L' sp_L.zero_not_mem_H
      simp only [lm_coe_lm' mo _ αg_ne_0, lm_coe_lm' mo n n_ne_0, WithBot.coe_inj] at lmαg_eq_lmn
      let f'' :=
        f -
          (MvPolynomial.monomial α) (f.coeff (leading_monomial' mo f f_ne_0) *
            (g.coeff (leading_monomial' mo g g_ne_0))⁻¹) * g
      have f''_mem_V : f'' ∈ V := by
        unfold f''
        rw [
          ← mul_one
            (f.coeff (leading_monomial' mo f f_ne_0) *
              (g.coeff (leading_monomial' mo g g_ne_0))⁻¹),
          ← smul_eq_mul
            (f.coeff (leading_monomial' mo f f_ne_0) *
              (g.coeff (leading_monomial' mo g g_ne_0))⁻¹) 1,
          ← MvPolynomial.smul_monomial
            (f.coeff (leading_monomial' mo f f_ne_0) *
              (g.coeff (leading_monomial' mo g g_ne_0))⁻¹),
          smul_mul_assoc
        ]
        have αg_mem_V := (@Submodule.subset_span K (MvPolynomial σ K) _ _ _ sp_L.H) αg_mem_L'
        rw [← ge_L'.span_V] at αg_mem_V
        simp only [gaussian_elim_SI_empty mo sp_L.H, Finset.coe_empty, Set.empty_union,
          SetLike.mem_coe, ge_L'] at αg_mem_V
        have f_αg_subset_V : {f, (MvPolynomial.monomial α) 1 * g} ⊆ V.carrier := by
          rw [Set.pair_subset_iff]
          unfold V
          rw [← ge_L'.span_V, gaussian_elim_SI_empty mo sp_L.H]
          simp only [Finset.coe_empty, Set.empty_union, Submodule.carrier_eq_coe, SetLike.mem_coe]
          exact ⟨f_mem_V, αg_mem_V⟩
        apply @Submodule.span_mono K at f_αg_subset_V
        unfold V at f_αg_subset_V
        conv_rhs at f_αg_subset_V => rw [Submodule.carrier_eq_coe, Submodule.span_span]
        apply f_αg_subset_V
        rw [Submodule.mem_span_pair]
        exists
          1,
          -(f.coeff (leading_monomial' mo f f_ne_0) *
            (g.coeff (leading_monomial' mo g g_ne_0))⁻¹)
        simp only [one_smul, neg_smul]
        ring
      have f''_eq_0_or_lmf''_lt_lmf (f''_ne_0 : f'' ≠ 0) :
        mo.toSyn (leading_monomial' mo f'' f''_ne_0) <
        mo.toSyn (leading_monomial' mo f f_ne_0) := by
        conv_lhs => unfold leading_monomial' max_monomial'
        simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
          AddEquiv.apply_symm_apply, Finset.max'_lt_iff, Finset.mem_map_equiv]
        intro β' β_supp_f''
        apply lt_of_le_of_ne
        · unfold f'' at β_supp_f''
          rw [sub_eq_add_neg] at β_supp_f''
          apply MvPolynomial.support_add at β_supp_f''
          rw [Finset.mem_union] at β_supp_f''
          cases β_supp_f'' with
          | inl β_supp_f =>
            unfold leading_monomial' max_monomial'
            simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
              AddEquiv.apply_symm_apply]
            apply Finset.le_max'
            simp_all
          | inr β_supp_αg =>
            rw [
              ← mul_one
                (f.coeff (leading_monomial' mo f f_ne_0) *
                  (g.coeff (leading_monomial' mo g g_ne_0))⁻¹),
              ← smul_eq_mul
                (f.coeff (leading_monomial' mo f f_ne_0) *
                  (g.coeff (leading_monomial' mo g g_ne_0))⁻¹) 1,
              ← MvPolynomial.smul_monomial
                (f.coeff (leading_monomial' mo f f_ne_0) *
                  (g.coeff (leading_monomial' mo g g_ne_0))⁻¹),
              smul_mul_assoc,
              ← neg_smul
                (f.coeff (leading_monomial' mo f f_ne_0) *
                  (g.coeff (leading_monomial' mo g g_ne_0))⁻¹) _
            ] at β_supp_αg
            apply MvPolynomial.support_smul at β_supp_αg
            rw [lmf_eq_lmn, ← lmαg_eq_lmn]
            unfold leading_monomial' max_monomial'
            simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
              AddEquiv.apply_symm_apply]
            apply Finset.le_max'
            simp_all
        · simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, ne_eq,
            f''] at β_supp_f''
          contrapose β_supp_f''
          simp only [ne_eq, Decidable.not_not] at β_supp_f''
          subst β'
          simp only [AddEquiv.symm_apply_apply, sub_eq_zero, Decidable.not_not]
          rw [
            ← mul_one
              (f.coeff (leading_monomial' mo f f_ne_0) *
                (g.coeff (leading_monomial' mo g g_ne_0))⁻¹),
            ← smul_eq_mul
              (f.coeff (leading_monomial' mo f f_ne_0) *
                (g.coeff (leading_monomial' mo g g_ne_0))⁻¹) 1,
            ← MvPolynomial.smul_monomial
              (f.coeff (leading_monomial' mo f f_ne_0) *
                (g.coeff (leading_monomial' mo g g_ne_0))⁻¹),
            smul_mul_assoc
          ]
          simp only [MvPolynomial.coeff_smul, smul_eq_mul]
          rw [mul_assoc]
          rw [left_eq_mul₀ (by exact lc_not_zero mo f f_ne_0)]
          rw [inv_mul_eq_one₀ (by exact lc_not_zero mo g g_ne_0)]
          conv_rhs =>
            rw [lmf_eq_lmn, ← lmαg_eq_lmn]
            rw [lm'_eq_of_eq mo _ _ (mul_comm (MvPolynomial.monomial α 1) g) αg_ne_0]
            rw [lm'_monmul_commute mo g g_ne_0 α 1 (by simp)]
            rw [add_comm]
          simp
      cases em (f'' = 0) with
      | inl f''_eq_0 =>
        subst f''
        rw [sub_eq_zero] at f''_eq_0
        let A : MvPolynomial σ K → MvPolynomial σ K := fun x =>
          if x = g
            then
              (MvPolynomial.monomial α)
                (f.coeff (leading_monomial' mo f f_ne_0) *
                  (g.coeff (leading_monomial' mo g g_ne_0))⁻¹)
            else 0
        exists A
        subst A
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_union, Or.inl g_mem_G,
          ↓reduceIte, ne_eq, ite_eq_right_iff, mul_eq_zero, MvPolynomial.monomial_eq_zero,
          inv_eq_zero, Classical.not_imp, not_or]
        constructor
        · exact f''_eq_0
        · intro g' g'_mem_basis ⟨g'_eq_g, _, g'_ne_0⟩
          subst g'
          simp only [↓reduceIte, ge_iff_le]
          apply le_of_eq
          rw [AddEquiv.apply_eq_iff_eq]
          rw [lm'_eq_of_eq mo _ _ (mul_comm _ g) _]
          rw [
            lm'_monmul_commute mo g g_ne_0 α _
              (by
                simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]
                exact ⟨lc_not_zero mo f f_ne_0, lc_not_zero mo g g_ne_0⟩)]
          rw [lmf_eq_lmn, ← lmαg_eq_lmn]
          rw [lm'_eq_of_eq mo _ _ (mul_comm _ g) _]
          rw [lm'_monmul_commute mo g g_ne_0 α 1 (by simp)]
      | inr f''_ne_0 =>
        have lmf''_lt_lmf := f''_eq_0_or_lmf''_lt_lmf f''_ne_0
        have IH' := IH _ lmf''_lt_lmf f'' f''_mem_V f''_ne_0 (by simp)
        have key :=
          mul_basis_add_red_0 mo (G ∪ N')
            g (by rw [Finset.mem_union]; exact Or.inl g_mem_G) g_ne_0
            f'' f''_ne_0 IH'
            α
            (f.coeff (leading_monomial' mo f f_ne_0) * (g.coeff (leading_monomial' mo g g_ne_0))⁻¹)
            (by
              simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]
              exact ⟨lc_not_zero mo f f_ne_0, lc_not_zero mo g g_ne_0⟩)
            (by
              rw [
                lm'_eq_of_eq mo _ _ (mul_comm _ g) _,
                lm'_monmul_commute mo g g_ne_0 α _
                  (by
                    simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]
                    exact ⟨lc_not_zero mo f f_ne_0, lc_not_zero mo g g_ne_0⟩)]
              rw [
                lmf_eq_lmn, ← lmαg_eq_lmn,
                lm'_eq_of_eq mo _ _ (mul_comm _ g) _,
                lm'_monmul_commute mo g g_ne_0 α 1 (by simp)
              ] at lmf''_lt_lmf
              exact lmf''_lt_lmf)
        simp only at key
        have :
          f =
            f'' +
              (MvPolynomial.monomial α)
                (f.coeff (leading_monomial' mo f f_ne_0) *
                  (g.coeff (leading_monomial' mo g g_ne_0))⁻¹) *
              g := by
          simp [f'']
        have key' := red_0_of_eq mo f _ this f_ne_0 (G ∪ N')
        exact key'.mpr key

/-- A key step for `F4Struct.sat_buchberger`. Suppose the setting of F4 where:
- $G$: basis set in previous step
- $L$: a finite subset of $\{x^\alpha g \mid g \in G, \alpha \in \mathbb{Z}_{\ge 0}^i\}$
- $L'$: the result of symbolic preprocess on $L$;
  this is still a finite subset of $\{x^\alpha g \mid g \in G, \alpha \in \mathbb{Z}_{\ge 0}^i\}$.
- $N$: the Gaussian elimination result of $L'$
- $N'$: $\{n ∈ N ∣ \exist\, l ∈ L', \mathrm{LM}(l) \mid \mathrm{LM}(n)\}$

Then any nonzero $f \in \left< L' \right>_K = \left< N \right>_K$ reduces to 0
over $G \cup N'$. -/
lemma span_ge_symb_proc_red_0 {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G)
  (L : Finset (MvPolynomial σ K)) (hL : 0 ∉ L)
  (hGL : ↑L ⊆ {mg | ∃ g ∈ G, ∃ α : σ →₀ ℕ, ∃ c : K, mg = g * MvPolynomial.monomial α c}) :
    let sp_L := symbolic_preprocess mo G hG L hL hGL
    let ge_L' := gaussian_elim mo sp_L.H
    let N := ge_L'.SO
    let N' := N.filter (fun n => ∀ l ∈ sp_L.H, ¬leading_monomial mo l ≤ leading_monomial mo n)
    let V : Submodule K (MvPolynomial σ K) := Submodule.span K sp_L.H
    ∀ f ∈ V, (f_ne_0 : f ≠ 0) → reduces_to_zero mo f f_ne_0 (G ∪ N') := by
  intro sp_L ge_L' N N' V f f_mem_span f_ne_0
  exact
    span_ge_symb_proc_red_0_induction mo G hG L hL hGL
      (mo.toSyn (leading_monomial' mo f f_ne_0))
      f f_mem_span f_ne_0 (by simp)

/-! ## F4 algorithm -/

/-- The struct to iterate through F4. -/
structure F4Struct {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (I : Ideal (MvPolynomial σ K)) where
  /-- Extension of basis set, written in `List` -/
  G : List (MvPolynomial σ K)
  /-- Size of current basis set -/
  size : ℕ
  /-- The length of `G` equals `size` -/
  G_len_eq_size : G.length = size
  /-- All the elements in `G` are distinct -/
  G_inj_on_supp (i) (hi : i < G.length) (j) (hj : j < G.length) :
    G[i] = G[j] → i = j
  /-- `G` doesn't have 0 as an element -/
  zero_not_mem_G : 0 ∉ G
  /-- `G` doesn't have 0 as an element; a paraphrased version of `zero_not_mem_G` -/
  zero_not_mem_G' (i) (hi : i < G.length) : G[i] ≠ 0
  /-- Full set of index pairs, from (0, 1) to (size - 2, size - 1) -/
  i_pairs : Finset (Fin size × Fin size)
  /-- Currently processed subset of i_pairs -/
  i_pairs_proc : Finset (Fin size × Fin size)
  /-- The set of processed pairs are contained in the full set of pairs -/
  i_pairs_proc_subs : i_pairs_proc ⊆ i_pairs
  /-- For `(i, j) ∈ i_pairs`, `i < j`; hence all the index pairs are considered exactly once -/
  i_pairs_lt (ip) : ip ∈ i_pairs ↔ ip.fst.val < ip.snd.val
  /-- The size of `i_pairs`; used for termination proof -/
  i_pairs_card : i_pairs.card = size * (size - 1) / 2
  /-- Ideal spanned by `G` is invariant -/
  span_ideal : I = Ideal.span (G.toFinset)
  /-- Any S-polynomial of currently processed pair has standard reprentation over current `G`.
  Since `i_pairs = i_pairs_proc` after termination of F4, the resulting `G` satisfies
  Buchberger's refined criterion. -/
  sat_buchberger (ip) (ip_mem : ip ∈ i_pairs_proc) :
    let sip :=
      S_poly mo G[ip.fst] G[ip.snd]
        (zero_not_mem_G' ip.fst (by rw [G_len_eq_size]; exact ip.fst.isLt))
        (zero_not_mem_G' ip.snd (by rw [G_len_eq_size]; exact ip.snd.isLt))
    (hsip : sip ≠ 0) → reduces_to_zero mo sip hsip (G.toFinset)

/-- Same sets generate same ideals. Auxiliary lemma for `F4Struct.span_ideal`. -/
lemma ideal_span_eq_of_eq {α : Type*} [Semiring α] {s t : Set α} :
    s = t → Ideal.span s = Ideal.span t := by
  intro heq
  subst heq
  simp_all only

/-- The full set of pairs (i, j) with i < j. This defines `F4Struct.i_pairs` in each step. -/
def pair_set {τ : Type*} [LinearOrder τ] (S : Finset τ) : Finset (τ × τ) :=
  (S ×ˢ S).filter (fun ⟨x, y⟩ => x < y)

/-- Lemma on the elements of `pair_set (insert e S)` appended to `pair_set S`.
Auxilliary lemma for `pair_set_insert_card`. -/
lemma pair_set_insert {τ : Type*} [LinearOrder τ] (e : τ) (S : Finset τ) (heS : e ∉ S) :
    pair_set (insert e S) =
    pair_set S ∪ (S.filter (· < e)) ×ˢ {e} ∪ {e} ×ˢ (S.filter (· > e)) := by
  ext ⟨p, q⟩
  simp_all [pair_set]
  aesop

/-- Insertion of an element `e` not in the original set `S` increases the size of `pair_set`
by the size of `S`. Auxiliary lemma for `pair_set_card_ind`. -/
lemma pair_set_insert_card {τ : Type*} [LinearOrder τ] (e : τ) (S : Finset τ) (heS : e ∉ S) :
    (pair_set (insert e S)).card = (pair_set S).card + S.card := by
  rw [pair_set_insert e _ heS]
  have disj_1 : Disjoint (pair_set S) ((S.filter (· < e)) ×ˢ {e}) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext ⟨p, q⟩
    constructor
    · intro hpq
      simp only [pair_set, Finset.product_singleton, Finset.mem_inter, Finset.mem_filter,
        Finset.mem_product, Finset.mem_map, Function.Embedding.coeFn_mk, Prod.mk.injEq, existsAndEq,
        true_and] at hpq
      simp_all only [not_true_eq_false]
    · simp
  have disj_2 : Disjoint (pair_set S ∪ (S.filter (· < e)) ×ˢ {e}) ({e} ×ˢ (S.filter (· > e))) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext ⟨p, q⟩
    constructor
    · intro hpq
      simp only [pair_set, Finset.product_singleton, gt_iff_lt, Finset.singleton_product,
        Finset.mem_inter, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_map,
        Function.Embedding.coeFn_mk, Prod.mk.injEq, existsAndEq, true_and,
        exists_eq_right_right] at hpq
      simp_all only [Finset.product_singleton, false_and, or_self]
    · simp
  rw [Finset.card_union_of_disjoint disj_2, Finset.card_union_of_disjoint disj_1]
  rw [add_assoc, add_left_cancel_iff]
  have S_union : S = (S.filter (· < e)) ∪ (S.filter (e < ·)) := by aesop
  have disj_3 : Disjoint (S.filter (· < e)) (S.filter (e < ·)) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext s
    constructor
    · simp only [Finset.mem_inter, Finset.mem_filter, Finset.notMem_empty, imp_false, not_and,
        not_lt, and_imp]
      intro _ lt _
      exact le_of_lt lt
    · intro hs
      absurd hs
      simp
  simp only [Finset.product_singleton, Finset.card_map, gt_iff_lt, Finset.singleton_product]
  conv_rhs => rw [S_union]
  rw [Finset.card_union_of_disjoint disj_3]

/-- The product of two consecutive number is even. Auxiliary lemma for `pair_set_card_ind`. -/
lemma consec_nat_prod_even (n : ℕ) : 2 ∣ (n + 1) * n := by
  let ⟨k, hnk⟩ := Nat.even_or_odd' n
  cases hnk with
  | inl even =>
    rw [even]
    exists k * (2 * k + 1)
    ring
  | inr odd =>
    rw [odd]
    exists (2 * k + 1) * (k + 1)
    ring

/-- Auxiliary lemma for `pair_set_card`, shown by induction. -/
lemma pair_set_card_ind {τ : Type*} [LinearOrder τ] :
    ∀ n : ℕ, ∀ S : Finset τ, S.card = n →
      (pair_set S).card = S.card * (S.card - 1) / 2 := by
  intro n
  induction n with
  | zero =>
    intro S hS
    rw [Finset.card_eq_zero] at hS
    simp [pair_set, hS]
  | succ n ih =>
    intro S hS
    have S_nonempty : S.Nonempty := by rw [← Finset.one_le_card, hS]; simp
    let maxS := S.max' S_nonempty
    have max_mem_S : maxS ∈ S := by unfold maxS; exact S.max'_mem S_nonempty
    have S_eq_max_ie : S = insert maxS (S.erase maxS) := by
      conv_lhs => rw [← Finset.insert_erase max_mem_S]
    conv_lhs => rw [S_eq_max_ie]
    rw [pair_set_insert_card maxS (S.erase maxS) (by simp)]
    have card_1 : (S.erase maxS).card = n := by
      apply Finset.card_erase_of_mem at max_mem_S
      simp only [hS, add_tsub_cancel_right] at max_mem_S
      exact max_mem_S
    have card_2 : (pair_set (S.erase maxS)).card = n * (n - 1) / 2 := by
      rw [← card_1]
      exact ih (S.erase maxS) card_1
    rw [card_1, card_2, hS]
    cases n with
    | zero => simp
    | succ m =>
      apply @Nat.eq_of_mul_eq_mul_right _ 2 _ (by simp)
      simp only [Nat.add_sub_cancel, Nat.right_distrib _ _ 2]
      rw [
        Nat.div_mul_cancel (consec_nat_prod_even m),
        Nat.div_mul_cancel (consec_nat_prod_even (m + 1))]
      ring

/-- A formula for the size of `F4Struct.pair_set`. The termination proof of F4
uses this fact. -/
lemma pair_set_card {τ : Type*} [LinearOrder τ] (S : Finset τ) :
    (pair_set S).card = S.card * (S.card - 1) / 2 :=
  pair_set_card_ind S.card S rfl

/-- Well-foundedness of lexicographical join of increase in ideal and decrease in ℕ. -/
instance imv_nat_wf {σ K : Type*} [Finite σ] [Field K] :
    WellFoundedRelation (Ideal (MvPolynomial σ K) × ℕ) :=
  @Prod.Lex.instIsWellFounded (Ideal (MvPolynomial σ K)) ℕ (· > ·) (· < ·) _ _
    |>.toWellFoundedRelation
/-- An object defined by the fields within `F4Struct`, which is well-founded by
`imv_nat_wf` under the F4 algorithm. -/
def f4s_lex_prod {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (I : Ideal (MvPolynomial σ K)) (f4s : F4Struct mo I) :
    Ideal (MvPolynomial σ K) × ℕ :=
  (monomial_ideal K (leading_monomials_fin mo f4s.G.toFinset),
    (f4s.i_pairs \ f4s.i_pairs_proc).card)

set_option maxHeartbeats 400000 in
-- the definition requires more than 200000 heartbeats
/-- One step of F4. The loop continues as long as `f4s.i_pairs ≠ f4s.i_pairs_proc`,
i.e. there still exists a pair of polynomials whose S-pair isn't processed yet. -/
noncomputable def F4_step {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
  (f4s : F4Struct mo I) (full_proc : ¬f4s.i_pairs = f4s.i_pairs_proc) :
    F4Struct mo I :=
  have pairs_diff_nonempty : (f4s.i_pairs \ f4s.i_pairs_proc).Nonempty := by
    push_neg at full_proc
    rw [Finset.sdiff_nonempty]
    apply not_subset_of_ssubset
    exact ssubset_of_subset_of_ne f4s.i_pairs_proc_subs (full_proc.symm)
  have pairs_choosable : ((f4s.i_pairs \ f4s.i_pairs_proc).powerset.erase ∅).Nonempty := by
    rw [Finset.erase_eq, Finset.sdiff_nonempty]
    by_contra H
    simp only [Finset.subset_singleton_iff, Finset.powerset_eq_singleton_empty,
      Finset.sdiff_eq_empty_iff_subset] at H
    cases H with
    | inl H =>
      let H' := (f4s.i_pairs \ f4s.i_pairs_proc).powerset_nonempty
      rw [Finset.nonempty_iff_ne_empty] at H'
      exact H' H
    | inr H =>
      rw [Finset.sdiff_nonempty] at pairs_diff_nonempty
      exact pairs_diff_nonempty H
  let i_pairs_new := Classical.choose (Finset.Nonempty.exists_mem pairs_choosable)
  have i_pairs_new_spec : i_pairs_new ≠ ∅ ∧ i_pairs_new ⊆ f4s.i_pairs \ f4s.i_pairs_proc := by
    let spec := Classical.choose_spec (Finset.Nonempty.exists_mem pairs_choosable)
    simp only [Finset.mem_erase, ne_eq, Finset.mem_powerset] at spec
    exact spec
  have i_pairs_proc_new_disj : Disjoint i_pairs_new f4s.i_pairs_proc :=
    (Finset.subset_sdiff.mp i_pairs_new_spec.2).2
  let ip_to_spair : Fin f4s.size × Fin f4s.size → Finset (MvPolynomial σ K) :=
    (fun ⟨i, j⟩ =>
      let s_pair := S_pair mo
        (f4s.G[i]'(by rw [f4s.G_len_eq_size]; exact i.isLt))
        (f4s.G[j]'(by rw [f4s.G_len_eq_size]; exact j.isLt))
        (f4s.zero_not_mem_G' i (by rw [f4s.G_len_eq_size]; exact i.isLt))
        (f4s.zero_not_mem_G' j (by rw [f4s.G_len_eq_size]; exact j.isLt))
      { s_pair.fst, s_pair.snd })
  let L := Finset.biUnion i_pairs_new ip_to_spair
  have zero_not_mem_L : 0 ∉ L := by
    simp only [S_pair, Fin.getElem_fin, Finset.mem_biUnion, Finset.mem_insert, zero_eq_mul,
      MvPolynomial.monomial_eq_zero, inv_eq_zero, Finset.mem_singleton, Prod.exists, not_exists,
      not_and, not_or, ne_eq, L, ip_to_spair]
    intro i j ij_mem_new
    have gi_ne_0 : f4s.G[i.val]'(by rw [f4s.G_len_eq_size]; exact i.isLt) ≠ 0 :=
      f4s.zero_not_mem_G' i.val _
    have gj_ne_0 : f4s.G[j.val]'(by rw [f4s.G_len_eq_size]; exact j.isLt) ≠ 0 :=
      f4s.zero_not_mem_G' j.val _
    constructor
    · exact ⟨gi_ne_0, lc_not_zero mo _ gi_ne_0⟩
    · exact ⟨gj_ne_0, lc_not_zero mo _ gj_ne_0⟩
  have L_sub_monmul_G :
    ↑L ⊆
      {mg | ∃ g ∈ f4s.G.toFinset, ∃ α : σ →₀ ℕ, ∃ c : K,
        mg = g * MvPolynomial.monomial α c} := by
    intro p p_mem_L
    simp only [List.mem_toFinset, Set.mem_setOf_eq]
    simp only [Finset.coe_biUnion, Finset.mem_coe, Set.mem_iUnion, exists_prop, Prod.exists,
      L] at p_mem_L
    let ⟨i, j, hij, hpij⟩ := p_mem_L
    simp only [Fin.getElem_fin, Finset.mem_insert, Finset.mem_singleton, ip_to_spair] at hpij
    let fi := f4s.G[i]'(by rw [f4s.G_len_eq_size]; exact i.isLt)
    let fj := f4s.G[j]'(by rw [f4s.G_len_eq_size]; exact j.isLt)
    have fi_mem_G : fi ∈ f4s.G := by simp [fi]
    have fj_mem_G : fj ∈ f4s.G := by simp [fj]
    have fi_ne_0 := f4s.zero_not_mem_G' i (by rw [f4s.G_len_eq_size]; exact i.isLt)
    have fj_ne_0 := f4s.zero_not_mem_G' j (by rw [f4s.G_len_eq_size]; exact j.isLt)
    let lmfi := leading_monomial' mo fi fi_ne_0
    let lmfj := leading_monomial' mo fj fj_ne_0
    cases hpij with
    | inl hpij1 =>
      exists fi, fi_mem_G, (lcm_monomial lmfi lmfj - lmfi), (fi.coeff lmfi)⁻¹
    | inr hpij2 =>
      exists fj, fj_mem_G, (lcm_monomial lmfi lmfj - lmfj), (fj.coeff lmfj)⁻¹
  let symb_proc_L :=
    symbolic_preprocess mo
      f4s.G.toFinset
      (by rw [List.mem_toFinset]; exact f4s.zero_not_mem_G)
      L zero_not_mem_L L_sub_monmul_G
  let L' := symb_proc_L.H
  let ge_L' := gaussian_elim mo L'
  let N := ge_L'.SO
  let N' := N.filter (fun n => ∀ l ∈ L', ¬leading_monomial mo l ≤ leading_monomial mo n)
  have mem_N'_not_mem_f4s_G (n) (hnN' : n ∈ N') : n ∉ f4s.G := by
    intro hnG
    simp only [Finset.mem_filter, N'] at hnN'
    rcases hnN' with ⟨hnN, hnL'⟩
    have n_ne_0 : n ≠ 0 := ne_of_mem_of_not_mem hnG f4s.zero_not_mem_G
    let ν := leading_monomial' mo n n_ne_0
    have ν_done : ν ∈ symb_proc_L.done_mons := by
      rw [
        symbolic_preprocess_done_mons mo
          f4s.G.toFinset (by rw [List.mem_toFinset]; exact f4s.zero_not_mem_G)
          L zero_not_mem_L L_sub_monmul_G,
        ← ge_L'.monset_fixed,
        gaussian_elim_SI_empty mo L',
        Finset.empty_union]
      unfold N at hnN
      rw [← Finset.insert_erase hnN, Finset.insert_eq, monomial_set_union_distrib]
      simp only [Finset.mem_union]
      apply Or.inl
      rw [singleton_monset_eq_support]
      exact lm'_mem mo n n_ne_0
    let key := symb_proc_L.div_then_cont_mult ν ν_done
    rw [← imp_iff_not_or] at key
    have key' : leading_monomial mo n ≤ ν := by
      unfold ν
      rw [lm_coe_lm' mo n n_ne_0]
    let key := key ⟨n, List.mem_toFinset.mpr hnG, key'⟩
    unfold L' at hnL'
    rcases key with ⟨f, hfG, μ, μcf_mul_mem, μcf_mul_lm⟩
    let hnL' := hnL' _ μcf_mul_mem
    unfold ν at μcf_mul_lm
    rw [← lm_coe_lm' mo n n_ne_0] at μcf_mul_lm
    exact hnL' (le_of_eq μcf_mul_lm)
  have N'_subs_N : N' ⊆ N := by
    unfold N'
    apply Finset.filter_subset
  let i_pairs_ext :
    (Fin f4s.size × Fin f4s.size) ↪ (Fin (f4s.size + N'.card) × Fin (f4s.size + N'.card)) :=
  {
    toFun (ip) := (Fin.castAdd N'.card ip.fst, Fin.castAdd N'.card ip.snd)
    inj' := by simp [Function.Injective]
  }
  let size := f4s.size + N'.card
  let G := f4s.G ++ N'.toList
  let i_pairs := pair_set (@Finset.univ (Fin (f4s.size + N'.card)) _)
  let i_pairs_proc := (f4s.i_pairs_proc ∪ i_pairs_new).map i_pairs_ext
  have i_pairs_proc_subs : i_pairs_proc ⊆ i_pairs := by
    simp only [Finset.map_union, pair_set, Finset.univ_product_univ, Finset.union_subset_iff,
      i_pairs_proc, i_pairs]
    constructor
    · intro ⟨i', j'⟩
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Prod.mk.injEq, Prod.exists,
        Finset.mem_filter, Finset.mem_univ, true_and, forall_exists_index, and_imp, i_pairs_ext]
      intro i j hij hii' hjj'
      simp only [← hii', ← hjj']
      apply f4s.i_pairs_proc_subs at hij
      exact (f4s.i_pairs_lt (i, j)).mp hij
    · intro ⟨i', j'⟩
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Prod.mk.injEq, Prod.exists,
        Finset.mem_filter, Finset.mem_univ, true_and, forall_exists_index, and_imp, i_pairs_ext]
      intro i j hij hii' hjj'
      simp only [← hii', ← hjj']
      apply i_pairs_new_spec.2 at hij
      apply Finset.sdiff_subset at hij
      exact (f4s.i_pairs_lt (i, j)).mp hij
  have i_pairs_card : i_pairs.card = size * (size - 1) / 2 := by
    have : (@Finset.univ (Fin (f4s.size + N'.card)) _).card = size := by simp [size]
    rw [pair_set_card (@Finset.univ (Fin (f4s.size + N'.card)) _), this]
  {
    size := size
    G := G
    G_len_eq_size := by
      simp only [List.length_append, Finset.length_toList, Nat.add_right_cancel_iff, G, size]
      exact f4s.G_len_eq_size
    G_inj_on_supp := by
      simp only [List.length_append, Finset.length_toList, G]
      intro i hi j hj
      simp only [List.getElem_append]
      have G_N'_mem_ne (g) (hg : g ∈ f4s.G) (n) (hn : n ∈ N'.toList) : g ≠ n :=
        ne_of_mem_of_not_mem hg (mem_N'_not_mem_f4s_G n (Finset.mem_toList.mp hn))
      split_ifs with hi' hj' hj'
      · exact f4s.G_inj_on_supp i hi' j hj'
      · contrapose
        intro _
        apply G_N'_mem_ne
        · simp
        · simp
      · contrapose
        intro _
        push_neg
        apply Ne.symm
        apply G_N'_mem_ne
        · simp
        · simp
      · intro hij
        rw [List.Nodup.getElem_inj_iff (Finset.nodup_toList N')] at hij
        simp_all only [ne_eq, Finset.mem_toList, Finset.forall_mem_not_eq, not_lt]
        rw [← add_left_inj f4s.G.length] at hij
        simp_all only [Nat.sub_add_cancel]
    zero_not_mem_G := by
      simp only [List.mem_append, Finset.mem_toList, not_or, G]
      constructor
      · exact f4s.zero_not_mem_G
      · have : 0 ∉ N := ge_L'.zero_not_mem_SO
        revert this
        unfold N'
        contrapose
        simp only [Finset.mem_filter, not_and, not_forall, Decidable.not_not, not_exists]
        intro ⟨h0N, _⟩
        exact h0N
    zero_not_mem_G' := by -- 사실상 zero_not_mem_G와 동치
      intro i hi
      rw [List.getElem_append]
      split_ifs with hi'
      · exact f4s.zero_not_mem_G' i hi'
      · have zero_not_mem_N' : 0 ∉ N'.toList := by
          rw [Finset.mem_toList]
          unfold N'
          simp only [Finset.mem_filter, not_and, not_forall, Decidable.not_not]
          intro HN
          by_contra _
          exact ge_L'.zero_not_mem_SO HN
        exact ne_of_mem_of_not_mem (N'.toList.getElem_mem _) zero_not_mem_N'
    i_pairs := i_pairs
    i_pairs_proc := i_pairs_proc
    i_pairs_proc_subs := i_pairs_proc_subs
    i_pairs_lt := by
      simp only [Fin.val_fin_lt, Prod.forall, i_pairs]
      intro i j
      simp [pair_set]
    i_pairs_card := i_pairs_card
    span_ideal := by
      let prev_span_ideal := f4s.span_ideal
      conv_lhs => rw [prev_span_ideal]
      conv_rhs => unfold G
      apply Submodule.span_eq_span
      · simp only [List.coe_toFinset, List.toFinset_append, Finset.toList_toFinset,
          Finset.coe_union, Ideal.submodule_span_eq]
        intro p hp
        apply @Ideal.subset_span _ _ ({a | a ∈ f4s.G} ∪ ↑N')
        apply Or.inl hp
      · simp only [List.toFinset_append, Finset.toList_toFinset, Finset.coe_union,
          List.coe_toFinset, Ideal.submodule_span_eq, Set.union_subset_iff]
        constructor
        · exact Ideal.subset_span
        · intro p hp
          apply N'_subs_N at hp
          unfold N at hp
          have ge_L'_SI_empty : ge_L'.SI = ∅ := gaussian_elim_SI_empty mo L'
          have ge_L'_K_span :
            (Submodule.span K (ge_L'.SI ∪ ge_L'.SO) : Submodule K (MvPolynomial σ K)) =
            Submodule.span K L' := by
            apply ge_L'.span_V
          simp only [ge_L'_SI_empty, Finset.coe_empty, Set.empty_union] at ge_L'_K_span
          have submod_span_subs :
            (Submodule.span K L' : Submodule K (MvPolynomial σ K)).carrier ⊆
            (Ideal.span L' : Ideal (MvPolynomial σ K)).carrier := by
            unfold Ideal.span
            apply Submodule.span_subset_span
          have ideal_span_subs :
            Ideal.span L' ≤ Ideal.span {a | a ∈ f4s.G} := by
            rw [Ideal.span_le]
            unfold L'
            let key := symb_proc_L.H_sub_ideal_G
            simp only [List.coe_toFinset, Submodule.carrier_eq_coe] at key
            exact key
          apply ideal_span_subs
          apply submod_span_subs
          rw [← ge_L'_K_span]
          simp only [Submodule.carrier_eq_coe, SetLike.mem_coe]
          rw [← Finset.mem_coe] at hp
          exact Submodule.subset_span hp
    sat_buchberger := by
      unfold G
      intro ⟨i, j⟩ ij_proc spoly_ij spoly_ij_ne_0
      simp only [Finset.mem_map, Finset.mem_union, Prod.exists, i_pairs_proc] at ij_proc
      rcases ij_proc with ⟨i', j', ij'_mem, ext_ij'_eq_ij⟩
      simp only [DFunLike.coe, Prod.mk.injEq, i_pairs_ext] at ext_ij'_eq_ij
      simp only [List.toFinset_append, Finset.toList_toFinset]
      have i_eq_i' : i.val = i'.val := by rw [← ext_ij'_eq_ij.1]; simp
      have j_eq_j' : j.val = j'.val := by rw [← ext_ij'_eq_ij.2]; simp
      have i_ran : i.val < f4s.G.length := by rw [i_eq_i', f4s.G_len_eq_size]; simp
      have j_ran : j.val < f4s.G.length := by rw [j_eq_j', f4s.G_len_eq_size]; simp
      have len_le : f4s.G.length ≤ (f4s.G ++ N'.toList).length := by simp
      have get_i_eq :
        (f4s.G ++ N'.toList)[i.val]'(lt_of_lt_of_le i_ran len_le) = f4s.G[i.val]'i_ran := by
        exact List.getElem_append_left i_ran
      have get_j_eq :
        (f4s.G ++ N'.toList)[j.val]'(lt_of_lt_of_le j_ran len_le) = f4s.G[j.val]'j_ran := by
        exact List.getElem_append_left j_ran
      have gi_ne_0 : f4s.G[i.val] ≠ 0 := f4s.zero_not_mem_G' i.val i_ran
      have gj_ne_0 : f4s.G[j.val] ≠ 0 := f4s.zero_not_mem_G' j.val j_ran
      let spair_ij := S_pair mo f4s.G[i.val] f4s.G[j.val] gi_ne_0 gj_ne_0
      let sij := spair_ij.1
      let sji := spair_ij.2
      have spoly_ij_eq : spoly_ij = sij - sji := by
        simp [spoly_ij, S_poly, sij, sji, spair_ij, get_i_eq, get_j_eq]
      have sij_ne_0 : sij ≠ 0 := by
        simp only [S_pair, ne_eq, mul_eq_zero, MvPolynomial.monomial_eq_zero, inv_eq_zero, not_or,
          sij, spair_ij]
        exact ⟨gi_ne_0, lc_not_zero mo f4s.G[i.val] gi_ne_0⟩
      have sji_ne_0 : sji ≠ 0 := by
        simp only [S_pair, ne_eq, mul_eq_zero, MvPolynomial.monomial_eq_zero, inv_eq_zero, not_or,
          sji, spair_ij]
        exact ⟨gj_ne_0, lc_not_zero mo f4s.G[j.val] gj_ne_0⟩
      cases ij'_mem with
      | inl ij'_mem_proc =>
        apply red_0_on_extension mo spoly_ij spoly_ij_ne_0 f4s.G.toFinset N'
        have key :=
          f4s.sat_buchberger (i', j') ij'_mem_proc
            (by
              simp only [S_poly, Fin.getElem_fin, ← i_eq_i', ← j_eq_j', ne_eq]
              simp only [spoly_ij_eq, ne_eq] at spoly_ij_ne_0
              exact spoly_ij_ne_0)
        simp at key
        have gi_eq_gi' : f4s.G[i.val] = f4s.G[i'.val] := by simp_all
        have gj_eq_gj' : f4s.G[j.val] = f4s.G[j'.val] := by simp_all
        have spoly_eq_spoly' :
          spoly_ij =
          S_poly mo f4s.G[i'.val] f4s.G[j'.val]
            (by rw [← gi_eq_gi']; exact gi_ne_0)
            (by rw [← gj_eq_gj']; exact gj_ne_0) := by
          simp only [S_poly, S_pair, Fin.getElem_fin, get_i_eq, get_j_eq, spoly_ij]
          conv_lhs =>
            rw [lm'_eq_of_eq mo _ _ gi_eq_gi' gi_ne_0, lm'_eq_of_eq mo _ _ gj_eq_gj' gj_ne_0]
          simp [gi_eq_gi', gj_eq_gj']
        have key' := red_0_of_eq mo spoly_ij _ spoly_eq_spoly' spoly_ij_ne_0 f4s.G.toFinset
        exact key'.mpr key
      | inr ij'_mem_new =>
        have spair_ij_in_L : {sij, sji} ⊆ L := by
          unfold L
          have key := Finset.subset_biUnion_of_mem ip_to_spair ij'_mem_new
          simp only [Fin.getElem_fin, ← i_eq_i', ← j_eq_j', ip_to_spair] at key
          exact key
        have spair_ij_in_L' : {sij, sji} ⊆ L' := subset_trans spair_ij_in_L symb_proc_L.H0_sub_H
        have spoly_ij_mem_V : spoly_ij ∈ Submodule.span K L' := by
          have span_spair_le_V : Submodule.span K {sij, sji} ≤ Submodule.span K L' := by
            exact
              @Submodule.span_mono K (MvPolynomial σ K) _ _ _ {sij, sji} L'
                (by rw [← Finset.coe_pair]; exact Finset.coe_subset.mpr spair_ij_in_L')
          apply span_spair_le_V
          rw [spoly_ij_eq]
          rw [Submodule.mem_span_pair]
          exists 1, -1
          simp only [one_smul, neg_smul]
          ring
        exact span_ge_symb_proc_red_0 mo
          f4s.G.toFinset (by rw [List.mem_toFinset]; exact f4s.zero_not_mem_G)
          L zero_not_mem_L L_sub_monmul_G
          spoly_ij spoly_ij_mem_V spoly_ij_ne_0
  }

/-- Termination proof for F4. `f4s_lex_prod` decreases strictly after each step
of F4, i.e. the ideal generated leading monomials of `f4s.G` increases monotonely;
if it doesn't change, then the size of `f4s.i_pairs \ f4s.i_pairs_proc` decreases strictly. -/
lemma f4s_moni_ipcard_lex_decr {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
  (f4s : F4Struct mo I) (full_proc : ¬f4s.i_pairs = f4s.i_pairs_proc) :
    let f4s' := F4_step mo I f4s full_proc
    /-
    let lmi : Ideal (MvPolynomial σ K) :=
      monomial_ideal K (leading_monomials_fin mo f4s.G.toFinset)
    let lmi' : Ideal (MvPolynomial σ K) :=
      monomial_ideal K (leading_monomials_fin mo f4s'.G.toFinset)
    lmi < lmi' ∨
    lmi' = lmi ∧ (f4s'.i_pairs \ f4s'.i_pairs_proc).card < (f4s.i_pairs \ f4s.i_pairs_proc).card
    -/
    Prod.Lex (· > ·) (· < ·) (f4s_lex_prod mo I f4s') (f4s_lex_prod mo I f4s) := by
  have pairs_diff_nonempty : (f4s.i_pairs \ f4s.i_pairs_proc).Nonempty := by
    push_neg at full_proc
    rw [Finset.sdiff_nonempty]
    apply not_subset_of_ssubset
    exact ssubset_of_subset_of_ne f4s.i_pairs_proc_subs (full_proc.symm)
  have pairs_choosable : ((f4s.i_pairs \ f4s.i_pairs_proc).powerset.erase ∅).Nonempty := by
    rw [Finset.erase_eq, Finset.sdiff_nonempty]
    by_contra H
    simp only [Finset.subset_singleton_iff, Finset.powerset_eq_singleton_empty,
      Finset.sdiff_eq_empty_iff_subset] at H
    cases H with
    | inl H =>
      let H' := (f4s.i_pairs \ f4s.i_pairs_proc).powerset_nonempty
      rw [Finset.nonempty_iff_ne_empty] at H'
      exact H' H
    | inr H =>
      rw [Finset.sdiff_nonempty] at pairs_diff_nonempty
      exact pairs_diff_nonempty H
  let i_pairs_new := Classical.choose (Finset.Nonempty.exists_mem pairs_choosable)
  have i_pairs_new_spec : i_pairs_new ≠ ∅ ∧ i_pairs_new ⊆ f4s.i_pairs \ f4s.i_pairs_proc := by
    let spec := Classical.choose_spec (Finset.Nonempty.exists_mem pairs_choosable)
    simp only [Finset.mem_erase, ne_eq, Finset.mem_powerset] at spec
    exact spec
  have i_pairs_proc_new_disj : Disjoint i_pairs_new f4s.i_pairs_proc :=
    (Finset.subset_sdiff.mp i_pairs_new_spec.2).2
  let ip_to_spair : Fin f4s.size × Fin f4s.size → Finset (MvPolynomial σ K) :=
    (fun ⟨i, j⟩ =>
      let s_pair := S_pair mo
        (f4s.G[i]'(by rw [f4s.G_len_eq_size]; exact i.isLt))
        (f4s.G[j]'(by rw [f4s.G_len_eq_size]; exact j.isLt))
        (f4s.zero_not_mem_G' i (by rw [f4s.G_len_eq_size]; exact i.isLt))
        (f4s.zero_not_mem_G' j (by rw [f4s.G_len_eq_size]; exact j.isLt))
      { s_pair.fst, s_pair.snd })
  let L := Finset.biUnion i_pairs_new ip_to_spair
  have zero_not_mem_L : 0 ∉ L := by
    simp [L, Finset.mem_biUnion, ip_to_spair, S_pair]
    intro i j ij_mem_new
    have gi_ne_0 : f4s.G[i.val]'(by rw [f4s.G_len_eq_size]; exact i.isLt) ≠ 0 := f4s.zero_not_mem_G' i.val _
    have gj_ne_0 : f4s.G[j.val]'(by rw [f4s.G_len_eq_size]; exact j.isLt) ≠ 0 := f4s.zero_not_mem_G' j.val _
    constructor
    · exact ⟨gi_ne_0, lc_not_zero mo _ gi_ne_0⟩
    · exact ⟨gj_ne_0, lc_not_zero mo _ gj_ne_0⟩
  have L_sub_monmul_G : ↑L ⊆ {mg | ∃ g ∈ f4s.G.toFinset, ∃ α : σ →₀ ℕ, ∃ c : K, mg = g * MvPolynomial.monomial α c} := by
    intro p p_mem_L
    simp
    simp [L] at p_mem_L
    let ⟨i, j, hij, hpij⟩ := p_mem_L
    simp [ip_to_spair] at hpij
    let fi := f4s.G[i]'(by rw [f4s.G_len_eq_size]; exact i.isLt)
    let fj := f4s.G[j]'(by rw [f4s.G_len_eq_size]; exact j.isLt)
    have fi_mem_G : fi ∈ f4s.G := by simp [fi]
    have fj_mem_G : fj ∈ f4s.G := by simp [fj]
    have fi_ne_0 := f4s.zero_not_mem_G' i (by rw [f4s.G_len_eq_size]; exact i.isLt)
    have fj_ne_0 := f4s.zero_not_mem_G' j (by rw [f4s.G_len_eq_size]; exact j.isLt)
    let lmfi := leading_monomial' mo fi fi_ne_0
    let lmfj := leading_monomial' mo fj fj_ne_0
    cases hpij with
    | inl hpij1 =>
      exists fi, fi_mem_G, (lcm_monomial lmfi lmfj - lmfi), (fi.coeff lmfi)⁻¹
    | inr hpij2 =>
      exists fj, fj_mem_G, (lcm_monomial lmfi lmfj - lmfj), (fj.coeff lmfj)⁻¹
  let symb_proc_L :=
    symbolic_preprocess mo
      f4s.G.toFinset
      (by rw [List.mem_toFinset]; exact f4s.zero_not_mem_G)
      L zero_not_mem_L L_sub_monmul_G
  let L' := symb_proc_L.H
  let ge_L' := gaussian_elim mo L'
  let N := ge_L'.SO
  let N' := N.filter (fun n => ∀ l ∈ L', ¬leading_monomial mo l ≤ leading_monomial mo n)
  have N'_subs_N : N' ⊆ N := by
    unfold N'
    apply Finset.filter_subset
  let i_pairs_ext : (Fin f4s.size × Fin f4s.size) ↪ (Fin (f4s.size + N'.card) × Fin (f4s.size + N'.card)) := {
    toFun (ip) := (Fin.castAdd N'.card ip.fst, Fin.castAdd N'.card ip.snd)
    inj' := by unfold Function.Injective; simp
  }
  let size := f4s.size + N'.card
  let G := f4s.G ++ N'.toList
  let i_pairs := pair_set (@Finset.univ (Fin (f4s.size + N'.card)) _)
  let i_pairs_proc := (f4s.i_pairs_proc ∪ i_pairs_new).map i_pairs_ext
  have i_pairs_proc_subs : i_pairs_proc ⊆ i_pairs := by
    simp [i_pairs, i_pairs_proc, pair_set, Finset.map_union, Finset.union_subset_iff]
    constructor
    · intro ⟨i', j'⟩
      simp [i_pairs_ext]
      intro i j hij hii' hjj'
      simp [← hii', ← hjj']
      apply f4s.i_pairs_proc_subs at hij
      exact (f4s.i_pairs_lt (i, j)).mp hij
    · intro ⟨i', j'⟩
      simp [i_pairs_ext]
      intro i j hij hii' hjj'
      simp [← hii', ← hjj']
      apply i_pairs_new_spec.2 at hij
      apply Finset.sdiff_subset at hij
      exact (f4s.i_pairs_lt (i, j)).mp hij
  have i_pairs_card : i_pairs.card = size * (size - 1) / 2 := by
    have : (@Finset.univ (Fin (f4s.size + N'.card)) _).card = size := by simp [size]
    rw [pair_set_card (@Finset.univ (Fin (f4s.size + N'.card)) _), this]
  -- main proof
  simp
  let lmi : Ideal (MvPolynomial σ K) := monomial_ideal K (leading_monomials_fin mo f4s.G.toFinset)
  let lmi' : Ideal (MvPolynomial σ K) := monomial_ideal K (leading_monomials_fin mo G.toFinset)
  have f4s_moni_ipcard_lex_decr' :
    lmi < lmi' ∨
    lmi' = lmi ∧ (i_pairs \ i_pairs_proc).card < (f4s.i_pairs \ f4s.i_pairs_proc).card := by
    cases (em (N' = ∅)) with
    | inl N'_empty =>
      have N'_list_empty : N'.toList = [] := by simp; exact N'_empty
      have N'_card_0 : N'.card = 0 := by rw [N'_empty]; simp
      apply Or.inr
      constructor
      · unfold lmi' lmi G
        simp [N'_list_empty]
      · rw [Finset.card_sdiff i_pairs_proc_subs, Finset.card_sdiff f4s.i_pairs_proc_subs]
        have hc1 : i_pairs.card = f4s.i_pairs.card := by
          have : size = f4s.size := by simp [size, N'_card_0]
          rw [i_pairs_card, f4s.i_pairs_card, this]
        simp [hc1, i_pairs_proc]
        apply Nat.sub_lt_sub_left
        · apply Finset.card_lt_card
          rw [ssubset_iff_subset_ne]
          constructor
          · exact f4s.i_pairs_proc_subs
          · push_neg at full_proc
            exact full_proc.symm
        · rw [Finset.card_union_of_disjoint i_pairs_proc_new_disj.symm]
          apply lt_add_of_pos_right
          exact Finset.Nonempty.card_pos (Finset.nonempty_of_ne_empty i_pairs_new_spec.1)
    | inr N'_nonempty =>
      apply Or.inl
      rw [lt_iff_le_and_ne]
      constructor
      · unfold lmi lmi' monomial_ideal
        apply Ideal.span_mono
        apply Set.image_mono -- (fun s => (MvPolynomial.monomial s) 1)
        rw [Finset.coe_subset]
        unfold leading_monomials_fin
        apply Finset.biUnion_subset_biUnion_of_subset_left
        simp [G]
      · have zero_not_mem_N' : 0 ∉ N' := Finset.notMem_mono N'_subs_N ge_L'.zero_not_mem_SO
        have lm_N'_mem_not_mem (n) (hnN' : n ∈ N')
          : let lmn := leading_monomial' mo n (ne_of_mem_of_not_mem hnN' zero_not_mem_N')
            let xlmn := MvPolynomial.monomial lmn (1 : K)
            xlmn ∈ lmi' ∧ xlmn ∉ lmi := by
          constructor
          · unfold lmi' monomial_ideal
            have lm'_n_mem
              : leading_monomial' mo n (ne_of_mem_of_not_mem hnN' zero_not_mem_N')
              ∈ leading_monomials_fin mo G.toFinset := by
              simp [leading_monomials_fin]
              exists n
              constructor
              · simp [G]
                exact Or.inr hnN'
              · simp [lm_coe_lm' mo n (ne_of_mem_of_not_mem hnN' zero_not_mem_N'), WithBot.some_eq_coe]
            rw [← Finset.mem_coe] at lm'_n_mem
            apply Set.mem_image_of_mem (fun s => (MvPolynomial.monomial s) (1 : K)) at lm'_n_mem
            apply Ideal.subset_span
            exact lm'_n_mem
          · by_contra lm'_n_mem
            simp [
              lmi,
              mon_mem_moni_iff (leading_monomial' mo n (ne_of_mem_of_not_mem hnN' zero_not_mem_N')) (leading_monomials_fin mo f4s.G.toFinset)
            ] at lm'_n_mem
            let ⟨μ, hμG, hμn⟩ := lm'_n_mem
            simp [leading_monomials_fin] at hμG
            let ⟨g, hgG, hgμ⟩ := hμG
            have g_ne_0 : g ≠ 0 := ne_of_mem_of_not_mem hgG f4s.zero_not_mem_G
            have μ_eq_lm_g : μ = leading_monomial' mo g g_ne_0 := by
              simp [lm_coe_lm' mo g g_ne_0, WithBot.some_eq_coe] at hgμ
              rw [WithBot.coe_inj] at hgμ
              exact hgμ.symm
            have n_ne_0 : n ≠ 0 := ne_of_mem_of_not_mem hnN' zero_not_mem_N'
            have hnN : n ∈ N := N'_subs_N hnN'
            let ν := leading_monomial' mo n n_ne_0
            have ν_done : ν ∈ symb_proc_L.done_mons := by
              rw [symbolic_preprocess_done_mons mo
                  f4s.G.toFinset (by rw [List.mem_toFinset]; exact f4s.zero_not_mem_G)
                  L zero_not_mem_L L_sub_monmul_G,
                  ← ge_L'.monset_fixed, gaussian_elim_SI_empty mo L']
              simp
              unfold N at hnN
              rw [← Finset.insert_erase hnN, Finset.insert_eq, monomial_set_union_distrib]
              simp
              apply Or.inl
              rw [singleton_monset_eq_support]
              exact lm'_mem mo n n_ne_0
            let key := symb_proc_L.div_then_cont_mult ν ν_done
            rw [← imp_iff_not_or] at key
            have key' : leading_monomial mo g ≤ ν := by
              unfold ν
              rw [← lm_coe_lm' mo n n_ne_0]
              rw [μ_eq_lm_g, ← WithBot.coe_le_coe,
                  ← lm_coe_lm' mo g g_ne_0, ← lm_coe_lm' mo n n_ne_0] at hμn
              exact hμn
            let key := key ⟨g, List.mem_toFinset.mpr hgG, key'⟩
            rcases key with ⟨f, hfG, π, πcf_mul_mem, πcf_mul_lm⟩
            simp [N', L'] at hnN'
            let hnL' := hnN'.2 _ πcf_mul_mem
            rw [πcf_mul_lm] at hnL'
            unfold ν at hnL'
            rw [← lm_coe_lm' mo n n_ne_0] at hnL'
            exact hnL' le_rfl
        let n := Classical.choose (Finset.Nonempty.exists_mem (Finset.nonempty_of_ne_empty N'_nonempty))
        have hn : n ∈ N' := Classical.choose_spec (Finset.Nonempty.exists_mem (Finset.nonempty_of_ne_empty N'_nonempty))
        let ⟨key_1, key_2⟩ := lm_N'_mem_not_mem n hn
        exact (ne_of_mem_of_not_mem' key_1 key_2).symm
  unfold f4s_lex_prod
  rw [Prod.lex_def]
  simp
  have G_eq : (F4_step mo I f4s full_proc).G = G := by
    unfold F4_step
    simp [G, N', N, L', ge_L', symb_proc_L, L, i_pairs_new, ip_to_spair]
  have card_eq
    : ((F4_step mo I f4s full_proc).i_pairs \ (F4_step mo I f4s full_proc).i_pairs_proc).card
    = (i_pairs \ i_pairs_proc).card := by
    unfold F4_step i_pairs i_pairs_proc i_pairs_ext
    simp [N', N, L', ge_L', symb_proc_L, L, i_pairs_new, ip_to_spair]
  rw [G_eq, card_eq]
  unfold lmi lmi' at f4s_moni_ipcard_lex_decr'
  exact f4s_moni_ipcard_lex_decr'

noncomputable def F4_rec {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
  (f4s : F4Struct mo I) : F4Struct mo I :=
  if full_proc : f4s.i_pairs = f4s.i_pairs_proc
    then f4s -- terminates when all the index pairs are processed
    else F4_rec mo I (F4_step mo I f4s full_proc)
termination_by
  ((monomial_ideal K (leading_monomials_fin mo f4s.G.toFinset) : Ideal (MvPolynomial σ K)),
   Finset.card (f4s.i_pairs \ f4s.i_pairs_proc))
decreasing_by
  unfold WellFoundedRelation.rel imv_nat_wf IsWellFounded.toWellFoundedRelation
  simp
  apply f4s_moni_ipcard_lex_decr mo I f4s full_proc

/-- Initial `F4Struct` object to iterate through `F4_rec`. -/
noncomputable def F4_init {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (F : Finset (MvPolynomial σ K)) (hF : 0 ∉ F) :
    F4Struct mo (Ideal.span F : Ideal (MvPolynomial σ K)) :=
  let init_i_pairs := pair_set (@Finset.univ (Fin F.card) _)
  let I : Ideal (MvPolynomial σ K) := Ideal.span F
  have supp_G_le_size : F.toList.toFinsupp.support = Finset.range F.toList.length := by
    unfold List.toFinsupp Finset.range
    ext x
    constructor
    · intro hx
      simp_all
    · intro hx
      simp_all only [Finset.length_toList, Finset.mem_mk, Multiset.mem_range,
        List.getD_eq_getElem?_getD, ne_eq, Finset.mem_filter, getElem?_pos, Option.getD_some,
        true_and]
      rw [← Finset.length_toList] at hx
      have : F.toList[x]'hx ∈ F := by rw [← Finset.mem_toList]; simp
      exact ne_of_mem_of_not_mem this hF
  {
    size := F.card
    G := F.toList
    G_len_eq_size := by simp
    G_inj_on_supp := by
      intro i hi j hj hij
      rw [List.Nodup.getElem_inj_iff (Finset.nodup_toList F)] at hij
      exact hij
    zero_not_mem_G := by
      rw [← Finset.mem_toList] at hF
      exact hF
    zero_not_mem_G' := by
      intro i hi
      rw [← Finset.mem_toList] at hF
      exact ne_of_mem_of_not_mem (F.toList.getElem_mem _) hF
    i_pairs := init_i_pairs
    i_pairs_proc := ∅
    i_pairs_proc_subs := by simp
    i_pairs_lt := by
      intro ⟨i, j⟩
      unfold init_i_pairs pair_set
      simp_all
    i_pairs_card := by
      have : (@Finset.univ (Fin F.card) _).card = F.card := by simp
      rw [pair_set_card (@Finset.univ (Fin F.card) _), this]
    span_ideal := by
      apply ideal_span_eq_of_eq
      simp
    sat_buchberger := by
      intro _ H
      by_contra _
      exact Finset.notMem_empty _ H
  }

/-- Wrapper definition of F4 algorithm. -/
noncomputable def F4 {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (F : Finset (MvPolynomial σ K)) (hF : 0 ∉ F) :
    F4Struct mo (Ideal.span F : Ideal (MvPolynomial σ K)) :=
  F4_rec mo (Ideal.span F : Ideal (MvPolynomial σ K)) (F4_init mo F hF)

/-- Auxiliary induction argument for `F4_full_proc`. -/
lemma F4_rec_full_proc {σ K : Type*} [hσ : Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (I : Ideal (MvPolynomial σ K)) :
    ∀ f4s_lexp : Ideal (MvPolynomial σ K) × ℕ,
    ∀ f4s : F4Struct mo I,
      f4s_lex_prod mo I f4s = f4s_lexp →
      (F4_rec mo I f4s).i_pairs = (F4_rec mo I f4s).i_pairs_proc := by
  intro f4s_lexp
  induction f4s_lexp using WellFounded.induction imv_nat_wf.wf with
  | h f4s_lexp' IH =>
    intro f4s lexp_eq
    subst f4s_lexp'
    rw [F4_rec]
    cases (em (f4s.i_pairs = f4s.i_pairs_proc)) with
    | inl full_proc =>
      rw [dif_pos full_proc]
      exact full_proc
    | inr full_proc =>
      rw [dif_neg full_proc]
      let f4s' := F4_step mo I f4s full_proc
      apply IH (f4s_lex_prod mo I f4s')
      · exact f4s_moni_ipcard_lex_decr mo I f4s full_proc
      · rfl
  | _ => exact hσ

/-- The termination condition of `F4`. -/
lemma F4_full_proc {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (F : Finset (MvPolynomial σ K)) (hF : 0 ∉ F) :
    (F4 mo F hF).i_pairs = (F4 mo F hF).i_pairs_proc := by
  unfold F4
  let I : Ideal (MvPolynomial σ K) := Ideal.span F
  let f4s_init := F4_init mo F hF
  exact F4_rec_full_proc mo I (f4s_lex_prod mo I f4s_init) f4s_init (by rfl)

/-- The main theorem on F4 algorithm. The resulting extended basis of F4 satisfies
the refined Buchberger criterion, hence is a Groebner basis of the ideal spanned
by the original basis set. -/
theorem F4_groebner {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (F : Finset (MvPolynomial σ K)) (hF : 0 ∉ F) :
    let f4F := F4 mo F hF
    is_groebner mo f4F.G.toFinset (Ideal.span F) := by
  intro f4F
  have ideal_eq := f4F.span_ideal
  rw [
    groebner_iff_groebner_ideal_eq mo f4F.G.toFinset
      (Ideal.span ↑F) (Ideal.span ↑f4F.G.toFinset) ideal_eq]
  rw [refined_buchberger mo f4F.G.toFinset (by rw [List.mem_toFinset]; exact f4F.zero_not_mem_G)]
  unfold every_S_poly_red_0
  intro f1 f1_mem_G f2 f2_mem_G spoly spoly_ne_0
  have f1_ne_0 : f1 ≠ 0 :=
    ne_of_mem_of_not_mem (by rw [List.mem_toFinset] at f1_mem_G; exact f1_mem_G) f4F.zero_not_mem_G
  have f2_ne_0 : f2 ≠ 0 :=
    ne_of_mem_of_not_mem (by rw [List.mem_toFinset] at f2_mem_G; exact f2_mem_G) f4F.zero_not_mem_G
  rw [List.mem_toFinset, List.mem_iff_getElem] at f1_mem_G f2_mem_G
  rcases f1_mem_G with ⟨i, i_ran, fi_eq_f1⟩
  rcases f2_mem_G with ⟨j, j_ran, fj_eq_f2⟩
  have i_ne_j : i ≠ j := by
    by_contra i_eq_j
    subst i f1 f2
    have spoly_eq_0 : spoly = 0 := by simp [spoly, S_poly, S_pair]
    exact spoly_ne_0 spoly_eq_0
  let ii : Fin f4F.size := { val := i, isLt := by rw [f4F.G_len_eq_size] at i_ran; exact i_ran }
  let jj : Fin f4F.size := { val := j, isLt := by rw [f4F.G_len_eq_size] at j_ran; exact j_ran }
  cases ne_iff_lt_or_gt.mp i_ne_j with
  | inl i_lt_j =>
    have ii_lt_jj : ii < jj := by simp [ii, jj, i_lt_j]
    have ip_mem_pairs : (ii, jj) ∈ f4F.i_pairs := by
      simp only [f4F.i_pairs_lt (ii, jj), Fin.val_fin_lt]
      exact ii_lt_jj
    rw [F4_full_proc] at ip_mem_pairs
    have key := f4F.sat_buchberger (ii, jj) ip_mem_pairs
    simp only [Fin.getElem_fin, ne_eq, ii, jj] at key
    unfold spoly
    have spoly_eq :=
      eq_S_poly_of_eq_eq mo
        f1 f4F.G[i] f2 f4F.G[j]
        fi_eq_f1.symm fj_eq_f2.symm
        (Or.inl f1_ne_0) (Or.inl f2_ne_0)
    have both_red_0 := red_0_of_eq mo spoly _ spoly_eq spoly_ne_0 f4F.G.toFinset
    simp only [ne_eq, spoly] at both_red_0 spoly_ne_0
    rw [both_red_0]
    apply key
    rw [← spoly_eq]
    exact spoly_ne_0
  | inr i_gt_j =>
    have jj_lt_ii : jj < ii := by simp [ii, jj, i_gt_j]
    have ip_mem_pairs : (jj, ii) ∈ f4F.i_pairs := by
      simp only [f4F.i_pairs_lt (jj, ii), Fin.val_fin_lt]
      exact jj_lt_ii
    rw [F4_full_proc] at ip_mem_pairs
    have key := f4F.sat_buchberger (jj, ii) ip_mem_pairs
    simp only [Fin.getElem_fin, ne_eq, jj, ii] at key
    unfold spoly
    have spoly_eq :=
      eq_S_poly_of_eq_eq mo
        f2 f4F.G[j] f1 f4F.G[i]
        fj_eq_f2.symm fi_eq_f1.symm
        (Or.inl f2_ne_0) (Or.inl f1_ne_0)
    have spoly_neg_red_0 := red_0_iff_neg_red_0 mo _ spoly_ne_0 f4F.G.toFinset
    simp only [spoly] at spoly_neg_red_0
    have spoly_swap := S_poly_neg_of_swap mo f1 f2 f1_ne_0 f2_ne_0
    rw [spoly_neg_red_0]
    have red_0_spoly_eq :=
      red_0_of_eq mo _ _ spoly_swap.symm
        (by
          unfold spoly at spoly_ne_0
          rw [← neg_ne_zero] at spoly_ne_0
          exact spoly_ne_0)
        f4F.G.toFinset
    simp only at red_0_spoly_eq spoly_eq
    rw [red_0_spoly_eq]
    subst spoly f1 f2
    simp only [← neg_eq_iff_eq_neg] at spoly_swap
    rw [← spoly_swap, neg_ne_zero] at spoly_ne_0
    exact key spoly_ne_0
