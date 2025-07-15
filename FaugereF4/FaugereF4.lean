import Mathlib
import FaugereF4.MonomialIdeal
import FaugereF4.GaussianElim
import FaugereF4.GroebnerBasis

/-!
# Faugere F4 algorithm

This file formalizes Faugere's F4 algorithm, which computes
a Groebner basis of any finite-variable polynomial ideal,
given a finite generator set.

## Reference
* [Cox, Little and O'Shea, *Ideals, varieties, and algorithms*][coxlittleoshea1997]
-/

-- open Classical
-- universe u v
-- variable {σ : Type u} {K : Type v} [Finite σ] [DecidableEq σ] [Field K]

/-- WellFoundedRelation instance on the `WithTop syn` type of a monomial order;
this is needed for termination proof of symbolic preprocessing. -/
instance withtop_mo_syn_wf {σ : Type*} (mo : MonomialOrder σ) : WellFoundedRelation (WithTop mo.syn) :=
  WellFoundedLT.toWellFoundedRelation

/-
What to be shown of the result of symbolic preprocessing:
(1) H is nondecreasing in each step
(2) If a monomial m ∈ monomial_set H is divisible by lm(g), for some g ∈ G of
current (initial, or possibly extended) basis set, then H itself has
n * g (∃ monomial n) where lm(n * g) = m.
Since the recursion continues while done_mons ⊊ Mon(H), it suffices to check
in each step that (2) holds for monomials in done_mons.
-/
/-- The struct to iterate through symbolic preprocessing. -/
structure SymbProcStruct
  (σ : Type*) (K : Type*)
  [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K)) where
  /-- Increasing set of polynomials, to which several polynomials of the form $x^αg$
  for $g ∈ G$ would be inserted. -/
  H : Finset (MvPolynomial σ K)
  /-- This H is always contained in the span of G. -/
  H_sub_ideal_G : ↑H ⊆ (Ideal.span G : Ideal (MvPolynomial σ K)).carrier
  /-- H doesn't have zero as an element -/
  zero_not_mem_H : 0 ∉ H
  /-- The set of monomials considered until then -/
  done_mons : Finset (σ →₀ ℕ)
  /-- `done_mons` is contained in Mon(H) in each step -/
  done_sub_H : done_mons ⊆ monomial_set H
  /-- ⊤, or most recently considered monomial. This strictly decreases in `symbolic_preprocess_rec`. -/
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
      (∃ g ∈ G, ∃ α : σ →₀ ℕ, ∃ c : K,
        c ≠ 0 ∧
        (MvPolynomial.monomial α c) * g ∈ H ∧
        leading_monomial mo ((MvPolynomial.monomial α c) * g) = m)

noncomputable def symbolic_preprocess_step {σ K : Type*}
  [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G)
  (sps : SymbProcStruct σ K mo G)
  (hmons : ¬sps.done_mons = monomial_set sps.H)
  : SymbProcStruct σ K mo G :=
  let mon_H := monomial_set sps.H
  have monset_nonempty : (Finset.map mo.toSyn.toEmbedding (mon_H \ sps.done_mons)).Nonempty := by
    have : sps.done_mons ⊂ mon_H := by
      apply ssubset_iff_subset_ne.mpr
      exact ⟨sps.done_sub_H, hmons⟩
    have : (mon_H \ sps.done_mons).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      simp
      exact not_subset_of_ssubset this
    exact Finset.map_nonempty.mpr this
  -- ...then the max mon can be taken; this requires done_sub_H
  let b' := @Finset.max' _ mo.lo (Finset.map mo.toSyn (mon_H \ sps.done_mons)) monset_nonempty
  let b := mo.toSyn.invFun b' -- actual monomial type
  let done_mons := {b} ∪ sps.done_mons -- include b into done
  have b_mem_mon_H : b ∈ mon_H := by -- this b is taken from a subset of mon_H, hence is a member of mon_H
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
        exact Finset.max'_mem _ _ -- (Finset.map mo.toSyn.toEmbedding (mon_H \ sps.done_mons)) monset_nonempty
      · unfold b
        simp_all
    let ⟨b'', mem_b'', syn_b''⟩ := this
    have : b = b'' := by
      unfold b
      rw [← syn_b'']
      simp
    subst this
    simp_all only [Equiv.invFun_as_coe, AddEquiv.toEquiv_eq_coe, -- autogenerated by aesop
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
      simp_all only [ne_eq, Equiv.invFun_as_coe, AddEquiv.toEquiv_eq_coe,
        AddEquiv.coe_toEquiv_symm, Finset.mem_union, Finset.mem_singleton,
        or_false, b, mon_H, b', done_mons]
      ext a
      simp_all only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton,
        not_or, Finset.mem_erase, ne_eq, b, mon_H, b']
      constructor
      · intro a_1
        simp_all only [not_false_eq_true, and_self, b, mon_H, b']
      · intro a_1
        simp_all only [not_false_eq_true, and_self, b, mon_H, b']
    have lem_2 : Finset.map mo.toSyn.toEmbedding (mon_H \ done_mons)
      = (Finset.map mo.toSyn.toEmbedding (mon_H \ sps.done_mons)).erase b' := by
      have : Finset.map mo.toSyn.toEmbedding (mon_H \ done_mons)
        = (Finset.map mo.toSyn.toEmbedding ((mon_H \ sps.done_mons).erase b)) := by
        simp_all
      have : (Finset.map mo.toSyn.toEmbedding ((mon_H \ sps.done_mons).erase b))
        = (Finset.map mo.toSyn.toEmbedding (mon_H \ sps.done_mons)).erase b' := by
        unfold b'
        simp_all only [ne_eq, Equiv.invFun_as_coe, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv_symm, -- autogenerated by aesop
          Finset.mem_union, Finset.mem_singleton, or_false, Finset.map_erase,
          Equiv.coe_toEmbedding, EquivLike.coe_coe, AddEquiv.apply_symm_apply,
          b, mon_H, done_mons, b']
      simp_all
    intro ndm_mem
    have lem_3 : mo.toSyn ndm ∈ (Finset.map mo.toSyn.toEmbedding (mon_H \ sps.done_mons)).erase b' := by
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
      have f_mem_G : f ∈ G := by -- autogenerated by aesop
        simp_all only [ne_eq, Equiv.invFun_as_coe,
          AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv_symm,
          Finset.mem_union, Finset.mem_singleton, or_false, Finset.mem_sdiff,
          not_or, and_imp, Finset.mem_filter, mon_H, done_mons, b, b', SubG, f]
      have f_not_0 : f ≠ 0 := by
        simp_all [mon_H, SubG, done_mons, b, f, b']
        apply Aesop.BuiltinRules.not_intro
        intro a
        simp_all only [mon_H, SubG, done_mons, b, f, b']
      -- let ⟨f, hf⟩ := @Finset.Nonempty.exists_mem _ SubG SubG_occ -- goal이 Prop이 아니면 이렇게 쓸 수 없다
      let lmf := leading_monomial' mo f f_not_0
      -- let lcf := f.coeff lmf
      have lmf_div_b : lmf ≤ b := by
        unfold lmf
        unfold SubG at SubG_occ
        have : leading_monomial mo f ≤ b := by -- autogenerated by aesop
          simp_all only [Equiv.invFun_as_coe, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv_symm, Finset.mem_union,
            Finset.mem_singleton, or_false, Finset.mem_sdiff, not_or, and_imp, ne_eq, Finset.mem_filter, b', f, b,
            mon_H, SubG, done_mons]
        -- unfold leading_monomial'
        apply nonzero_lm'_div_impl_lm_div
        exact this
      /-
      have lcf_not_0 : lcf ≠ 0 := by
        unfold lcf
        rw [← MvPolynomial.mem_support_iff]
        unfold lmf
        apply lm_mem_supp
        -/
      let mulf := f * MvPolynomial.monomial (b - lmf) (1 : K) -- (1 / lcf) -- adjusting leading coeff to 1 ... or not
      have lm_mulf : leading_monomial' mo mulf (by
          simp_all [SubG, b', f, b, mon_H, done_mons, lmf, /-lcf,-/ mulf]
        ) = b := by
        unfold mulf
        rw [lm'_monmul_commute]
        rw [add_comm]
        apply monomial_sub_add
        · exact lmf_div_b
        · simp
          -- exact lcf_not_0
      let H := {mulf} ∪ sps.H
      {
        H := H
        H_sub_ideal_G := by
          unfold H
          simp only [Finset.coe_union, Set.union_subset_iff]
          constructor
          · rw [Finset.coe_singleton, Set.singleton_subset_iff]
            unfold mulf
            have : Ideal.span {f} ≤ Ideal.span G := by
              apply Ideal.span_mono
              simp
              exact f_mem_G
            apply this
            rw [Ideal.mem_span_singleton]
            simp
          · exact sps.H_sub_ideal_G
        zero_not_mem_H := by
          unfold H
          simp
          constructor
          · simp_all [SubG, b', f, b, mon_H, done_mons, lmf, /-lcf,-/ mulf]
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
        lmon_done := by -- autogenerated by aesop
          intro not_top
          simp_all only [ne_eq, Equiv.invFun_as_coe, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv_symm,
            Finset.mem_union, Finset.mem_singleton, or_false, Finset.mem_sdiff, not_or, and_imp,
            EmbeddingLike.apply_eq_iff_eq, mon_H, SubG, done_mons, b, f, b']
          -- obtain ⟨left, right⟩ := hf
          apply Or.inl
          rfl
        nd_lt_lmon := by
          unfold mon_H at nd_lt_b
          simp
          simp at nd_lt_b
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
              simp at this
              exact this
            have syn_ndm_le_b : mo.toSyn ndm ≤ b' := by
              unfold leading_monomial' at lm_mulf
              unfold max_monomial' at lm_mulf
              unfold b at lm_mulf
              rw [← AddEquiv.apply_eq_iff_eq mo.toSyn] at lm_mulf
              simp at lm_mulf
              rw [← lm_mulf]
              apply Finset.le_max'
              simp_all
            -- simp at ndm_mem_mulf
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
              exists 1
              constructor
              · simp
              · constructor
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
              simp at h_div_able
              exact h_div_able g g_mem_G
            | inr h_cont_mult =>
              apply Or.inr
              let ⟨g, g_mem_G, α, c, c_ne_0, g_mmul_mem_sps_H, lm_g_mmul_eq_m⟩ := h_cont_mult
              exists g, g_mem_G, α, c, c_ne_0
              constructor
              · unfold H
                apply Finset.mem_union_right
                exact g_mmul_mem_sps_H
              · exact lm_g_mmul_eq_m
      }
    else
      {
        H := sps.H
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
            simp at h_div_able
            let g_not_in_SubG := (@Finset.eq_empty_iff_forall_notMem (MvPolynomial σ K) SubG).mp h_div_able g
            unfold SubG at g_not_in_SubG
            simp at g_not_in_SubG
            rw [m_eq_b]
            exact g_not_in_SubG g_G
          · have : m ∈ sps.done_mons := by
              unfold done_mons at m_done
              simp_all
            exact sps.div_then_cont_mult m this
      }

lemma sps_last_mon_decr {σ K : Type*}
  [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G)
  (sps : SymbProcStruct σ K mo G)
  (hmons : ¬sps.done_mons = monomial_set sps.H)
  : (symbolic_preprocess_step mo G hG sps hmons).last_mon < sps.last_mon := by
  let mon_H := monomial_set sps.H
  have monset_nonempty : (Finset.map mo.toSyn.toEmbedding (mon_H \ sps.done_mons)).Nonempty := by
    have : sps.done_mons ⊂ mon_H := by
      apply ssubset_iff_subset_ne.mpr
      exact ⟨sps.done_sub_H, hmons⟩
    have : (mon_H \ sps.done_mons).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      simp
      exact not_subset_of_ssubset this
    exact Finset.map_nonempty.mpr this
  -- ...then the max mon can be taken; this requires done_sub_H
  let b' := @Finset.max' _ mo.lo (Finset.map mo.toSyn (mon_H \ sps.done_mons)) monset_nonempty
  let b := mo.toSyn.invFun b' -- actual monomial type
  have b_mem_mon_H : b ∈ mon_H := by -- this b is taken from a subset of mon_H, hence is a member of mon_H
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
        exact Finset.max'_mem _ _ -- (Finset.map mo.toSyn.toEmbedding (mon_H \ sps.done_mons)) monset_nonempty
      · unfold b
        simp_all
    let ⟨b'', mem_b'', syn_b''⟩ := this
    have : b = b'' := by
      unfold b
      rw [← syn_b'']
      simp
    subst this
    simp_all only [Equiv.invFun_as_coe, AddEquiv.toEquiv_eq_coe, -- autogenerated by aesop
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
  simp_all only [Equiv.invFun_as_coe, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv_symm, Finset.mem_union,
    Finset.mem_singleton, or_false, ne_eq, dite_not, gt_iff_lt, mon_H, b, b']
  split
  next h => simp_all only [mon_H, b', b]
  next h => simp_all only [mon_H, b', b]

noncomputable def symbolic_preprocess_rec {σ K : Type*}
  [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G)
  (sps : SymbProcStruct σ K mo G)
  : SymbProcStruct σ K mo G :=
  let mon_H := monomial_set sps.H
  if hmons : sps.done_mons = mon_H
    then -- no more monomials to be considered
      sps
    else -- one or more monomials are left to be considered
      symbolic_preprocess_rec mo G hG (symbolic_preprocess_step mo G hG sps hmons)
termination_by sps.last_mon
decreasing_by
  unfold WellFoundedRelation.rel withtop_mo_syn_wf -- WellFoundedLT.toWellFoundedRelation
  apply sps_last_mon_decr

/-
done_mons의 원소가 모두 mon_H \ done_mons의 원소보다 크다
b'는 mon_H \ done_mons에서 뽑아낸 최대원소
lmon은? 바로 앞단계 iter의 mon_H \ done_mons에서 뽑아낸 최대원소
이 앞단계에서 lmon를 done_mons에 넣었으므로 lmon ∈ done_mons
lmon을 나누는 f가 G 안에...
있었다 => H에 f*~(s.t. lmon이 max mon)을 더함 (=> mon_H 단조증가)
없었다 => H 그대로 유지
-/

/-
만족할 성질들:
(1) L ⊆ H
증가하는 집합열로서... 귀납적으로...
(2) Mon(H) 안의 단항식들은 모두 G의 어떤 다항식의 LT로 나누어짐
초기 H(=L)은 L의 정의상 ok, 이후 H는 추가하는 원소들의 정의로부터 ok

termination proof 전략:
f*~~에 의해 새로 mon_H에 들어오는 mon들은 b를 제외하면 모두 b보다 작다
이미 b는 mon_H \ sps.done_mons에서 뽑아낸 최대원소
그러니 다음 단계에서 뽑는 b는 지금 뽑는 b보다 작다
-/

def sps_init {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (G : Finset (MvPolynomial σ K))
  (H : Finset (MvPolynomial σ K)) (hH : 0 ∉ H)
  (hGH : ↑H ⊆ (Ideal.span G : Ideal (MvPolynomial σ K)).carrier) : SymbProcStruct σ K mo G :=
  {
    H := H
    H_sub_ideal_G := hGH
    zero_not_mem_H := hH
    done_mons := ∅
    done_sub_H := by simp
    last_mon := ⊤
    lmon_done := by simp
    nd_lt_lmon := by simp
    div_then_cont_mult := by simp
  }

noncomputable def symbolic_preprocess {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G)
  (H : Finset (MvPolynomial σ K)) (hH : 0 ∉ H)
  (hGH : ↑H ⊆ (Ideal.span G : Ideal (MvPolynomial σ K)).carrier) : SymbProcStruct σ K mo G :=
  symbolic_preprocess_rec mo G hG (sps_init mo G H hH hGH)

lemma symbolic_preprocess_rec_done_mons {σ K : Type*}
  [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G)
  (last_mon : WithTop mo.syn)
  : ∀ sps : SymbProcStruct σ K mo G,
    sps.last_mon = last_mon →
    let sps' := symbolic_preprocess_rec mo G hG sps
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
      let sps' := symbolic_preprocess_step mo G hG sps mons_ne
      have lm'_lt_lm : sps'.last_mon < sps.last_mon := by
        apply sps_last_mon_decr
      let IH' := IH sps'.last_mon lm'_lt_lm sps' (by rfl)
      simp at IH'
      have sp_idem : symbolic_preprocess_rec mo G hG sps' = symbolic_preprocess_rec mo G hG sps := by
        unfold sps'
        conv_rhs => unfold symbolic_preprocess_rec
        simp only [right_eq_dite_iff]
        intro mons_eq
        by_contra _
        exact mons_ne mons_eq
      simp [← sp_idem]
      exact IH'

lemma symbolic_preprocess_done_mons {σ K : Type*}
  [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G)
  (H : Finset (MvPolynomial σ K)) (hH : 0 ∉ H)
  (hGH : ↑H ⊆ (Ideal.span G : Ideal (MvPolynomial σ K)).carrier)
  : let sps := symbolic_preprocess mo G hG H hH hGH
    sps.done_mons = monomial_set sps.H := by
  simp [symbolic_preprocess]
  exact symbolic_preprocess_rec_done_mons mo G hG ⊤ (sps_init mo G H hH hGH) (by rfl)


/-- The struct to iterate through F4. -/
structure F4Struct {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (I : Ideal (MvPolynomial σ K)) where
  /-- Extension of basis set, written in `List` -/
  G : List (MvPolynomial σ K)
  -- G : ℕ →₀ MvPolynomial σ K -- extension of basis set, written in `Finsupp`
  /-- Size of current basis set -/
  size : ℕ
  -- supp_G_le_size : G.support = Finset.range size
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
  -- i_pairs_proc_prev : Finset (Fin size × Fin size) -- previously processed subset of i_pairs
  /-- Currently processed subset of i_pairs -/
  i_pairs_proc : Finset (Fin size × Fin size)
  -- i_pairs_proc_prev_subs : i_pairs_proc_prev ⊆ i_pairs_proc
  /-- The set of processed pairs are contained in the full set of pairs -/
  i_pairs_proc_subs : i_pairs_proc ⊆ i_pairs
  -- i_pairs_mem_supp_G : ∀ ip ∈ i_pairs, ip.fst ∈ G.support ∧ ip.snd ∈ G.support
  /-- For `(i, j) ∈ i_pairs`, `i < j`; hence all the index pairs are considered exactly once -/
  i_pairs_lt : ∀ ip ∈ i_pairs, ip.fst.val < ip.snd.val
  /-- The size of `i_pairs`; used for termination proof -/
  i_pairs_card : i_pairs.card = size * (size - 1) / 2
  -- span_ideal : I = Ideal.span (Finset.image G G.support)
  /-- Ideal spanned by `G` is invariant -/
  span_ideal : I = Ideal.span (G.toFinset)
  /-- Any S-polynomial of currently processed pair has standard reprentation over current `G`.
  Since `i_pairs = i_pairs_proc` after termination of F4, the resulting `G` satisfies
  Buchberger's refined criterion. -/
  sat_buchberger (ip) (ip_mem : ip ∈ i_pairs_proc) :
    reduces_to_zero mo
      (S_poly mo G[ip.fst] G[ip.snd]
        (zero_not_mem_G' ip.fst (by rw [G_len_eq_size]; exact ip.fst.isLt))
        (zero_not_mem_G' ip.snd (by rw [G_len_eq_size]; exact ip.snd.isLt)))
      (G.toFinset)
        /-
        (by
          apply Finsupp.mem_support_iff.mp
          rw [supp_G_le_size]
          exact Finset.mem_range.mpr ip.fst.isLt)
        (by
          apply Finsupp.mem_support_iff.mp
          rw [supp_G_le_size]
          exact Finset.mem_range.mpr ip.snd.isLt))
        -/
        /-
        (Finsupp.mem_support_iff.mp
          (i_pairs_mem_supp_G ip
            (Finset.mem_of_subset
              i_pairs_proc_subs
              ip_mem)).1)
        (Finsupp.mem_support_iff.mp
          (i_pairs_mem_supp_G ip
            (Finset.mem_of_subset
              i_pairs_proc_subs
              ip_mem)).2))
        -/
      -- (Finset.image G G.support)

  -- TODO: existence of standard presentation for every S-poly

/-
noncomputable def finset_to_finsupp {τ : Type*} [Zero τ]
  (S : Finset τ) : ℕ →₀ τ :=
  S.toList.toFinsupp
-/
/-
lemma img_ls_fsupp_eq_self {τ : Type*} [Zero τ] (S : Finset τ) (hS : 0 ∉ S)
  : S = Finset.image (⇑S.toList.toFinsupp) S.toList.toFinsupp.support := by
  ext x
  constructor
  · intro hx
    have x_not_0 : x ≠ 0 := ne_of_mem_of_not_mem hx hS
    rw [← Finset.mem_toList, List.mem_iff_getElem] at hx
    let ⟨i, hi, hix⟩ := hx
    rw [Finset.mem_image, List.toFinsupp_support]
    simp only [Finset.length_toList, Finset.mem_filter,
      Finset.mem_range, List.toFinsupp_apply]
    exists i
    constructor
    · constructor
      · rw [← Finset.length_toList S]
        exact hi
      · rw [List.getD_eq_getElem S.toList 0 hi, hix]
        exact x_not_0
    · rw [List.getD_eq_getElem S.toList 0 hi, hix]
  · intro hx
    rw [← Finset.mem_toList]
    rw [Finset.mem_image, List.toFinsupp_support] at hx
    simp only [Finset.length_toList, Finset.mem_filter,
      Finset.mem_range, List.toFinsupp_apply] at hx
    let ⟨i, ⟨i_lt, get_i_ne_0⟩, get_i_eq_x⟩ := hx
    subst get_i_eq_x
    simp_all
-/

/-- Same sets generate same ideals. Auxiliary lemma for `F4Struct.span_ideal`. -/
lemma ideal_span_eq_of_eq {α : Type*} [Semiring α] {s t : Set α} :
  s = t → Ideal.span s = Ideal.span t := by
  intro heq
  subst heq
  simp_all only

/-- The full set of pairs (i, j) with i < j. This defines `F4Struct.i_pairs` in each step. -/
def pair_set {τ : Type*} [LinearOrder τ] (S : Finset τ) : Finset (τ × τ) :=
  (S ×ˢ S).filter (λ ⟨x, y⟩ => x < y)

/-- Lemma on the elements of `pair_set (insert e S)` appended to `pair_set S`.
Auxilliary lemma for `pair_set_insert_card`. -/
lemma pair_set_insert {τ : Type*} [LinearOrder τ] (e : τ) (S : Finset τ) (heS : e ∉ S)
  : pair_set (insert e S) = pair_set S ∪ (S.filter (· < e)) ×ˢ {e} ∪ {e} ×ˢ (S.filter (· > e)) := by
  ext ⟨p, q⟩
  simp_all [pair_set]
  aesop

/-- Insertion of an element `e` not in the original set `S` increases the size of `pair_set`
by the size of `S`. Auxiliary lemma for `pair_set_card_ind`. -/
lemma pair_set_insert_card {τ : Type*} [LinearOrder τ] (e : τ) (S : Finset τ) (heS : e ∉ S)
  : (pair_set (insert e S)).card = (pair_set S).card + S.card := by
  rw [pair_set_insert e _ heS]
  have disj_1 : Disjoint (pair_set S) ((S.filter (· < e)) ×ˢ {e}) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext ⟨p, q⟩
    constructor
    · intro hpq
      simp [pair_set] at hpq
      simp_all only [not_true_eq_false]
    · simp
  have disj_2 : Disjoint (pair_set S ∪ (S.filter (· < e)) ×ˢ {e}) ({e} ×ˢ (S.filter (· > e))) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext ⟨p, q⟩
    constructor
    · intro hpq
      simp [pair_set] at hpq
      simp_all only [Finset.product_singleton, false_and, or_self]
    · simp
  rw [Finset.card_union_of_disjoint disj_2, Finset.card_union_of_disjoint disj_1]
  rw [add_assoc, add_left_cancel_iff]
  have S_union : S = (S.filter (· < e)) ∪ (S.filter (e < ·)) := by aesop
  have disj_3 : Disjoint (S.filter (· < e)) (S.filter (e < ·)) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext s
    constructor
    · simp
      intro _ lt _
      exact le_of_lt lt
    · intro hs
      absurd hs
      simp
  simp [Finset.card_product]
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
lemma pair_set_card_ind {τ : Type*} [LinearOrder τ]
  : ∀ n : ℕ, ∀ S : Finset τ, S.card = n → (pair_set S).card = S.card * (S.card - 1) / 2 := by
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
      simp [hS] at max_mem_S
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
      rw [Nat.div_mul_cancel (consec_nat_prod_even m), Nat.div_mul_cancel (consec_nat_prod_even (m + 1))]
      ring

/-- A formula for the size of `F4Struct.pair_set`. The termination proof of F4
uses this fact. -/
lemma pair_set_card {τ : Type*} [LinearOrder τ] (S : Finset τ)
  : (pair_set S).card = S.card * (S.card - 1) / 2 := pair_set_card_ind S.card S (by rfl)

/-- Well-foundedness of lexicographical join of increase in ideal and decrease in ℕ. -/
instance imv_nat_wf {σ K : Type*} [Finite σ] [Field K]
  : WellFoundedRelation (Ideal (MvPolynomial σ K) × ℕ) :=
  (@Prod.Lex.instIsWellFounded (Ideal (MvPolynomial σ K)) ℕ (· > ·) (· < ·) _ _).toWellFoundedRelation

set_option maxHeartbeats 1000000 -- requires slightly more than 200000 heartbeats
-- #count_heartbeats in
noncomputable def F4_rec {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
  (f4s : F4Struct mo I) : F4Struct mo I :=
  if full_proc : f4s.i_pairs = f4s.i_pairs_proc
    then f4s -- terminates when all the index pairs are processed
    else
      have pairs_diff_nonempty : (f4s.i_pairs \ f4s.i_pairs_proc).Nonempty := by
        push_neg at full_proc
        rw [Finset.sdiff_nonempty]
        apply not_subset_of_ssubset
        exact ssubset_of_subset_of_ne f4s.i_pairs_proc_subs (full_proc.symm)
      have pairs_choosable : ((f4s.i_pairs \ f4s.i_pairs_proc).powerset.erase ∅).Nonempty := by
        rw [Finset.erase_eq, Finset.sdiff_nonempty]
        by_contra H
        simp at H
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
        simp at spec
        exact spec
      have i_pairs_proc_new_disj : Disjoint i_pairs_new f4s.i_pairs_proc :=
        (Finset.subset_sdiff.mp i_pairs_new_spec.2).2
      /-
      have i_isLt' : i < f4s.G.length := by
        rw [← f4s.G_len_eq_size]
        exact i.isLt
      have j_isLt' : j < f4s.G.length := by
        rw [← f4s.G_len_eq_size]
        exact j.isLt
      -/
      let L :=
        Finset.biUnion i_pairs_new
          (λ ⟨i, j⟩ =>
            let s_pair := S_pair mo
              (f4s.G[i]'(by rw [f4s.G_len_eq_size]; exact i.isLt))
              (f4s.G[j]'(by rw [f4s.G_len_eq_size]; exact j.isLt))
              (f4s.zero_not_mem_G' i (by rw [f4s.G_len_eq_size]; exact i.isLt))
              (f4s.zero_not_mem_G' j (by rw [f4s.G_len_eq_size]; exact j.isLt))
              /-
              (by
                apply Finsupp.mem_support_iff.mp
                rw [f4s.supp_G_le_size]
                exact Finset.mem_range.mpr i.isLt)
              (by
                apply Finsupp.mem_support_iff.mp
                rw [f4s.supp_G_le_size]
                exact Finset.mem_range.mpr j.isLt)
              -/
            { s_pair.fst, s_pair.snd })
      have L_sub_ideal_G : ↑(L.erase 0) ⊆ (Ideal.span f4s.G.toFinset : Ideal (MvPolynomial σ K)).carrier := by
        intro p
        simp
        intro p_mem_L p_not_0
        simp [L] at p_mem_L
        let ⟨i, j, hij, hpij⟩ := p_mem_L
        simp [S_pair] at hpij
        cases hpij with
        | inl hpij1 =>
          have : Ideal.span {f4s.G[i]'(by rw [f4s.G_len_eq_size]; exact i.isLt)}
               ≤ Ideal.span {a | a ∈ f4s.G} := by
            apply Ideal.span_mono
            simp
          apply this
          rw [Ideal.mem_span_singleton, hpij1]
          simp
        | inr hpij2 =>
          have : Ideal.span {f4s.G[j]'(by rw [f4s.G_len_eq_size]; exact j.isLt)}
               ≤ Ideal.span {a | a ∈ f4s.G} := by
            apply Ideal.span_mono
            simp
          apply this
          rw [Ideal.mem_span_singleton, hpij2]
          simp
      let symb_proc_L :=
        symbolic_preprocess mo
          f4s.G.toFinset
          (by rw [List.mem_toFinset]; exact f4s.zero_not_mem_G)
          (L.erase 0)
          (by simp)
          L_sub_ideal_G
        -- (symbolic_preprocess mo (f4s.G.support.image f4s.G) (by simp) (L.erase 0) (by simp))
      let L' := symb_proc_L.H
      let ge_L' := gaussian_elim mo L'
      let N := ge_L'.SO
      let N' := N.filter (λ n => ∀ l ∈ L', ¬leading_monomial mo l ≤ leading_monomial mo n)
      have mem_N'_not_mem_f4s_G (n) (hnN' : n ∈ N') : n ∉ f4s.G := by
        intro hnG
        simp [N'] at hnN'
        rcases hnN' with ⟨hnN, hnL'⟩
        have n_ne_0 : n ≠ 0 := ne_of_mem_of_not_mem hnG f4s.zero_not_mem_G
        let ν := leading_monomial' mo n n_ne_0
        have ν_done : ν ∈ symb_proc_L.done_mons := by
          rw [symbolic_preprocess_done_mons mo
              f4s.G.toFinset (by rw [List.mem_toFinset]; exact f4s.zero_not_mem_G)
              (L.erase 0) (by simp)
              L_sub_ideal_G,
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
        have key' : leading_monomial mo n ≤ ν := by
          unfold ν
          rw [lm_coe_lm' mo n n_ne_0]
        let key := key ⟨n, List.mem_toFinset.mpr hnG, key'⟩
        unfold L' at hnL'
        rcases key with ⟨f, hfG, μ, c, c_ne_0, μcf_mul_mem, μcf_mul_lm⟩
        let hnL' := hnL' _ μcf_mul_mem
        unfold ν at μcf_mul_lm
        rw [← lm_coe_lm' mo n n_ne_0] at μcf_mul_lm
        exact hnL' (le_of_eq μcf_mul_lm)
      have N'_subs_N : N' ⊆ N := by
        unfold N'
        apply Finset.filter_subset
      let i_pairs_ext : (Fin f4s.size × Fin f4s.size) ↪ (Fin (f4s.size + N'.card) × Fin (f4s.size + N'.card)) := {
        toFun (ip) := (Fin.addNat ip.fst N'.card, Fin.addNat ip.snd N'.card)
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
          exact f4s.i_pairs_lt (i, j) hij
        · intro ⟨i', j'⟩
          simp [i_pairs_ext]
          intro i j hij hii' hjj'
          simp [← hii', ← hjj']
          apply i_pairs_new_spec.2 at hij
          apply Finset.sdiff_subset at hij
          exact f4s.i_pairs_lt (i, j) hij
      have i_pairs_card : i_pairs.card = size * (size - 1) / 2 := by
        have : (@Finset.univ (Fin (f4s.size + N'.card)) _).card = size := by simp [size]
        rw [pair_set_card (@Finset.univ (Fin (f4s.size + N'.card)) _), this]
      F4_rec mo I {
        size := size
        G := G
        G_len_eq_size := by
          simp [size, G]
          exact f4s.G_len_eq_size
        G_inj_on_supp := by
          simp [G]
          intro i hi j hj
          -- cases for hi & hj, wrt lt or ge f4s.G.length
          -- use List.getElem_append
          simp [List.getElem_append]
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
            simp_all
            rw [← add_left_inj f4s.G.length] at hij
            simp_all only [Nat.sub_add_cancel]
        zero_not_mem_G := by
          simp [G]
          constructor
          · exact f4s.zero_not_mem_G
          · have : 0 ∉ N := ge_L'.zero_not_mem_SO
            revert this
            unfold N'
            contrapose
            simp
            intro H _
            exact H
        zero_not_mem_G' := by -- 사실상 zero_not_mem_G와 동치
          intro i hi
          rw [List.getElem_append]
          split_ifs with hi'
          · exact f4s.zero_not_mem_G' i hi'
          · have zero_not_mem_N' : 0 ∉ N'.toList := by
              rw [Finset.mem_toList]
              unfold N'
              simp
              intro HN
              by_contra _
              exact ge_L'.zero_not_mem_SO HN
            exact ne_of_mem_of_not_mem (N'.toList.getElem_mem _) zero_not_mem_N'
        i_pairs := i_pairs
          -- f4s.i_pairs.map i_pairs_ext
        i_pairs_proc := i_pairs_proc
        i_pairs_proc_subs := i_pairs_proc_subs
          -- apply Finset.union_subset
          /-
          simp [Finset.map_subset_map]
          apply Finset.union_subset
          · exact f4s.i_pairs_proc_subs
          · exact (Finset.subset_sdiff.mp i_pairs_new_spec.2).1
          -/
        i_pairs_lt := by
          simp [i_pairs]
          intro i j hij
          -- simp [i_pairs_ext, Finset.map]
          simp [pair_set] at hij
          exact hij
        i_pairs_card := i_pairs_card
        span_ideal := by
          let prev_span_ideal := f4s.span_ideal
          conv_lhs => rw [prev_span_ideal]
          conv_rhs => unfold G
          apply Submodule.span_eq_span
          · simp
            intro p hp
            apply @Ideal.subset_span _ _ ({a | a ∈ f4s.G} ∪ ↑N')
            apply Or.inl hp
          · simp
            constructor
            · exact Ideal.subset_span
            · intro p hp
              apply N'_subs_N at hp
              unfold N at hp
              have ge_L'_SI_empty : ge_L'.SI = ∅ := gaussian_elim_SI_empty mo L'
              have ge_L'_K_span :
                (Submodule.span K (ge_L'.SI ∪ ge_L'.SO) : Submodule K (MvPolynomial σ K))
                = Submodule.span K L' := by
                apply ge_L'.span_V
              simp [ge_L'_SI_empty] at ge_L'_K_span
              have submod_span_subs :
                (Submodule.span K L' : Submodule K (MvPolynomial σ K)).carrier
                ⊆ (Ideal.span L' : Ideal (MvPolynomial σ K)).carrier := by
                unfold Ideal.span
                apply Submodule.span_subset_span
              have ideal_span_subs :
                Ideal.span L' ≤ Ideal.span {a | a ∈ f4s.G} := by
                rw [Ideal.span_le]
                unfold L'
                let key := symb_proc_L.H_sub_ideal_G
                simp at key
                exact key
              apply ideal_span_subs
              apply submod_span_subs
              rw [← ge_L'_K_span]
              simp
              rw [← Finset.mem_coe] at hp
              exact Submodule.subset_span hp
        sat_buchberger := by
          sorry
      }
termination_by
  ((monomial_ideal K (leading_monomials_fin mo f4s.G.toFinset) : Ideal (MvPolynomial σ K)),
   Finset.card (f4s.i_pairs \ f4s.i_pairs_proc))
decreasing_by
  let lmi_f4s_G : Ideal (MvPolynomial σ K) := monomial_ideal K (leading_monomials_fin mo f4s.G.toFinset)
  let lmi_G : Ideal (MvPolynomial σ K) := monomial_ideal K ↑(leading_monomials_fin mo G.toFinset)
  have f4s_moni_ipcard_lex_decr : -- termination proof
    lmi_f4s_G < lmi_G ∨
    lmi_G = lmi_f4s_G ∧ (i_pairs \ i_pairs_proc).card < (f4s.i_pairs \ f4s.i_pairs_proc).card := by
    cases (em (N' = ∅)) with
    | inl N'_empty =>
      have N'_list_empty : N'.toList = [] := by simp; exact N'_empty
      have N'_card_0 : N'.card = 0 := by rw [N'_empty]; simp
      apply Or.inr
      constructor
      · unfold lmi_G lmi_f4s_G G
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
      · unfold lmi_f4s_G lmi_G monomial_ideal
        apply Ideal.span_mono
        apply Set.image_subset (λ s => (MvPolynomial.monomial s) 1)
        rw [Finset.coe_subset]
        unfold leading_monomials_fin
        apply Finset.biUnion_subset_biUnion_of_subset_left
        simp [G]
      · have zero_not_mem_N' : 0 ∉ N' := Finset.notMem_mono N'_subs_N ge_L'.zero_not_mem_SO
        have lm_N'_mem_not_mem (n) (hnN' : n ∈ N')
          : let lmn := leading_monomial' mo n (ne_of_mem_of_not_mem hnN' zero_not_mem_N')
            let xlmn := MvPolynomial.monomial lmn (1 : K)
            xlmn ∈ lmi_G ∧ xlmn ∉ lmi_f4s_G := by
          constructor
          · unfold lmi_G monomial_ideal
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
            apply Set.mem_image_of_mem (λ s => (MvPolynomial.monomial s) (1 : K)) at lm'_n_mem
            apply Ideal.subset_span
            exact lm'_n_mem
          · by_contra lm'_n_mem
            simp [
              lmi_f4s_G,
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
                  (L.erase 0) (by simp)
                  L_sub_ideal_G,
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
            rcases key with ⟨f, hfG, π, c, c_ne_0, πcf_mul_mem, πcf_mul_lm⟩
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
  unfold WellFoundedRelation.rel imv_nat_wf IsWellFounded.toWellFoundedRelation
  simp
  rw [Prod.lex_def]
  simp only [Prod.fst, Prod.snd, pair_set]
  simp [
    lmi_f4s_G, lmi_G, i_pairs, i_pairs_proc,
    G, N', N, L', ge_L', symb_proc_L, L,
    i_pairs_new, pair_set, i_pairs_ext
  ] at f4s_moni_ipcard_lex_decr
  exact f4s_moni_ipcard_lex_decr

/-
B가 줄거나 ⟨LM(G)⟩가 늘거나
(B가 줄면 G가 extend되지 않았다는 뜻이므로 ⟨LM(G)⟩는 유지됨
B가 늘면 이는 G가 extend되었기 때문으로, 곧 ⟨LM(G)⟩가 커졌음을 의미)

Ideal (⟨LM(G)⟩, w/ inclusion) -- 이쪽이 증가한다
× (Prod.Lex.instIsWellFounded)
Finset (ℕ × ℕ) (i_pairs_r, w/ inclusion | size) -- 그렇지 않다면 이쪽이 감소한다
-/

/- n : ℕ Fin n →₀ α -/

-- set_option maxHeartbeats 5000000
-- #count_heartbeats in
noncomputable def F4 {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (F : Finset (MvPolynomial σ K)) (hF : 0 ∉ F)
  : F4Struct mo
    (Ideal.span F : Ideal (MvPolynomial σ K)) :=
  let init_i_pairs := pair_set (@Finset.univ (Fin F.card) _)
  let I : Ideal (MvPolynomial σ K) := Ideal.span F
  have supp_G_le_size : F.toList.toFinsupp.support = Finset.range F.toList.length := by
    unfold List.toFinsupp Finset.range
    ext x
    constructor
    · intro hx
      simp_all
    · intro hx
      simp_all
      rw [← Finset.length_toList] at hx
      have : F.toList[x]'hx ∈ F := by
        rw [← Finset.mem_toList]
        simp
      exact ne_of_mem_of_not_mem this hF
  F4_rec mo I {
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
      intro ij_mem
      simp_all
    i_pairs_card := by
      have : (@Finset.univ (Fin F.card) _).card = F.card := by simp
      rw [pair_set_card (@Finset.univ (Fin F.card) _), this]
    span_ideal := by
      unfold I
      apply ideal_span_eq_of_eq
      simp
    sat_buchberger := by
      intro _ H
      by_contra _
      exact Finset.notMem_empty _ H
  }
