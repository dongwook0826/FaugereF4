import FaugereF4.DivisionAlgorithm
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.Order.CompletePartialOrder

/-!
# Groebner basis and (refined) Buchberger criterion

This file formalizes Groebner basis and a refined version of Buchberger criterion
to decide whether a basis is Groebner. Some relevant definitions and lemmas are
included, such as:
- S-pair and S-polynomial of two nonzero polynomials, and
- reduction to zero over a basis set.
-/

/-- A finite polynomial set `G` is called a Groebner basis of a polynomial ideal
`I` (under a fixed monomial order `mo`), if `G ⊆ I` and the leading monomials
of `I` and those of `G` generate the same ideal. -/
def is_groebner {σ K : Type*} [DecidableEq σ] [Field K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K))
  (I : Ideal (MvPolynomial σ K)) : Prop :=
  ↑G ⊆ I.carrier ∧
  monomial_ideal K (leading_monomials mo I.carrier) =
  monomial_ideal K (leading_monomials_fin mo G)

/-- A rewrite lemma on `is_groebner` for equal ideals. -/
lemma groebner_iff_groebner_ideal_eq {σ K : Type*} [DecidableEq σ] [Field K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K))
  (I J : Ideal (MvPolynomial σ K)) (hIJ : I = J) :
    is_groebner mo G I ↔ is_groebner mo G J := by
  unfold is_groebner
  rw [hIJ]

theorem mem_ideal_iff_gb_remainder_zero {σ K : Type*}
  [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f : MvPolynomial σ K)
  (G : Finset (MvPolynomial σ K)) (I : Ideal (MvPolynomial σ K))
  (zero_not_mem_G : 0 ∉ G) (G_gb_I : is_groebner mo G I) :
    f ∈ I ↔ remainder_zero mo f G zero_not_mem_G := by
  have spanG_le_I : Ideal.span G ≤ I := by
    rw [← Ideal.span_eq I]
    apply Ideal.span_mono
    exact G_gb_I.1
  constructor
  · intro f_mem_I
    rcases G_gb_I with ⟨G_subs_I, initII_eq_initIG⟩
    cases em (f = 0) with
    | inl f_eq_0 =>
      subst f
      unfold remainder_zero
      exists G.toList, by simp, Finset.nodup_toList G
      exact (div_zero_Qr_zero mo _ _ _).2
    | inr f_ne_0 =>
      unfold remainder_zero
      by_contra mpds_on_r_ne_0
      push_neg at mpds_on_r_ne_0
      let mpds_on
        (LG : List (MvPolynomial σ K)) (G_eq_LG : G = LG.toFinset) (LG_Nodup : LG.Nodup) :=
        mvpoly_division mo f LG
          (by rw [← List.mem_toFinset, ← G_eq_LG]; exact zero_not_mem_G)
          LG_Nodup
      have mpds_on_p_eq_0
        (LG : List (MvPolynomial σ K)) (G_eq_LG : G = LG.toFinset) (LG_Nodup : LG.Nodup) :
          (mpds_on LG G_eq_LG LG_Nodup).p = 0 :=
        mvpoly_division_p_eq_0 mo f LG _ _
      have mpds_on_repn
        (LG : List (MvPolynomial σ K)) (G_eq_LG : G = LG.toFinset) (LG_Nodup : LG.Nodup) :=
        (mpds_on LG G_eq_LG LG_Nodup).f_eq_FQ_r
      simp only [Fin.getElem_fin, mpds_on_p_eq_0, add_zero] at mpds_on_repn
      have mpds_on_r_mem_I
        (LG : List (MvPolynomial σ K)) (G_eq_LG : G = LG.toFinset) (LG_Nodup : LG.Nodup) :
          (mpds_on LG G_eq_LG LG_Nodup).r ∈ I := by
        have mpds_repn := mpds_on_repn LG G_eq_LG LG_Nodup
        rw [add_comm] at mpds_repn
        apply sub_eq_of_eq_add at mpds_repn
        rw [← mpds_repn]
        apply Ideal.sub_mem
        · exact f_mem_I
        · apply spanG_le_I
          apply Ideal.sum_mem
          intro ⟨i, hi⟩
          simp only [Finset.mem_univ, forall_const]
          have LGi_mem_G : {LG[i]} ⊆ G.toSet := by simp [G_eq_LG]
          apply Ideal.span_mono LGi_mem_G
          simp [Ideal.mem_span_singleton]
      have mpds_on_lmr_mem_I
        (LG : List (MvPolynomial σ K)) (G_eq_LG : G = LG.toFinset) (LG_Nodup : LG.Nodup) :
          let mpds := mpds_on LG G_eq_LG LG_Nodup
          ∃ μ ∈ (leading_monomials_fin mo G).toSet,
            μ ≤ leading_monomial' mo mpds.r (mpds_on_r_ne_0 LG G_eq_LG LG_Nodup) := by
        intro mpds
        rw [← @mon_mem_moni_iff σ K, ← initII_eq_initIG]
        unfold monomial_ideal
        apply Ideal.subset_span
        simp only [leading_monomials, Submodule.carrier_eq_coe, Set.sUnion_image, SetLike.mem_coe,
          Set.mem_image, Set.mem_iUnion, Finset.mem_coe, Option.mem_toFinset, Option.mem_def,
          exists_prop, ne_eq, one_ne_zero, not_false_eq_true, MvPolynomial.monomial_left_inj,
          exists_eq_right]
        exists mpds.r, mpds_on_r_mem_I LG G_eq_LG LG_Nodup
        rw [lm_coe_lm' mo mpds.r (mpds_on_r_ne_0 LG G_eq_LG LG_Nodup), WithBot.some_eq_coe]
      have mpds_on_r_not_divisible
        (LG : List (MvPolynomial σ K)) (G_eq_LG : G = LG.toFinset) (LG_Nodup : LG.Nodup) :=
        (mpds_on LG G_eq_LG LG_Nodup).r_not_divisible
      let LG := G.toList
      have G_eq_LG : G = LG.toFinset := by simp [LG]
      have LG_Nodup : LG.Nodup := Finset.nodup_toList G
      have key1 := mpds_on_lmr_mem_I LG G_eq_LG LG_Nodup
      have key2 := mpds_on_r_not_divisible LG G_eq_LG LG_Nodup
      rcases key1 with ⟨ν, ν_mem_lmI, ν_div_lmr⟩
      simp only [leading_monomials_fin, Finset.coe_biUnion, Finset.mem_coe, Set.mem_iUnion,
        Option.mem_toFinset, Option.mem_def, exists_prop] at ν_mem_lmI
      rcases ν_mem_lmI with ⟨g, g_mem_G, lmg_eq_ν⟩
      rw [
        lm_coe_lm' mo g (ne_of_mem_of_not_mem g_mem_G zero_not_mem_G),
        WithBot.some_eq_coe, WithBot.coe_eq_coe
      ] at lmg_eq_ν
      subst ν
      have key2' :=
        key2
          g (by simp [LG, g_mem_G])
          (leading_monomial' mo
            (mpds_on LG G_eq_LG LG_Nodup).r
            (mpds_on_r_ne_0 LG G_eq_LG LG_Nodup))
          (by apply lm'_mem)
      exact key2' ν_div_lmr
  · intro fGr_zero
    unfold remainder_zero at fGr_zero
    rcases fGr_zero with ⟨LG, G_eq_LG, LF_Nodup, fGr_zero⟩
    have zero_not_mem_LG : 0 ∉ LG := by
      rw [← List.mem_toFinset, ← G_eq_LG]
      exact zero_not_mem_G
    let mpds_fG := mvpoly_division mo f LG zero_not_mem_LG LF_Nodup
    have fG_repn := mpds_fG.f_eq_FQ_r
    rw [fGr_zero, mvpoly_division_p_eq_0 mo f LG zero_not_mem_LG] at fG_repn
    simp only [Fin.getElem_fin, add_zero] at fG_repn
    apply spanG_le_I
    rw [fG_repn]
    apply Ideal.sum_mem
    intro ⟨i, hi⟩
    simp only [Finset.mem_univ, forall_const]
    have LGi_mem_G : {LG[i]} ⊆ G.toSet := by simp [G_eq_LG]
    apply Ideal.span_mono LGi_mem_G
    simp [Ideal.mem_span_singleton]

lemma groebner_iff_ideal_leadterm_mem_initI {σ K : Type*}
  [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K)) :
    is_groebner mo G (Ideal.span ↑G) ↔
    ∀ f ∈ Ideal.span ↑G,
      (f_ne_0 : f ≠ 0) →
        let lmf := leading_monomial' mo f f_ne_0
        let lcf := f.coeff lmf
        let ltf := MvPolynomial.monomial lmf lcf
        ltf ∈ monomial_ideal K (leading_monomials_fin mo G) := by
  unfold is_groebner
  constructor
  · intro ⟨G_subs_I, initI_eq⟩ f f_mem_I f_ne_0 lmf lcf ltf
    rw [← initI_eq]
    rw [term_mem_moni_iff lmf _ lcf (lc_not_zero mo f f_ne_0)]
    simp only [leading_monomials, Submodule.carrier_eq_coe, Set.sUnion_image, SetLike.mem_coe,
      Set.mem_iUnion, Finset.mem_coe, Option.mem_toFinset, Option.mem_def, exists_prop]
    exists lmf
    constructor
    · exists f
      constructor
      · exact f_mem_I
      · simp [lmf, lm_coe_lm' mo f f_ne_0, WithBot.some_eq_coe]
    · rfl
  · intro lt_mem_initIG
    constructor
    · exact Ideal.subset_span
    · apply le_antisymm
      · intro f f_mem_initII
        rw [mem_moni_iff] at f_mem_initII
        rw [mem_moni_iff]
        intro ν ν_supp_f
        rcases f_mem_initII ν ν_supp_f with ⟨μ, μ_mem_lmI, μ_div_ν⟩
        simp only [leading_monomials, Submodule.carrier_eq_coe, Set.sUnion_image, SetLike.mem_coe,
          Set.mem_iUnion, Finset.mem_coe, Option.mem_toFinset, Option.mem_def,
          exists_prop] at μ_mem_lmI
        rcases μ_mem_lmI with ⟨g, g_mem_I, lmg_eq_μ⟩
        have g_ne_0 : g ≠ 0 := by
          by_contra g_eq_0
          subst g
          rw [lm_zero_eq_bot, WithBot.some_eq_coe] at lmg_eq_μ
          exact WithBot.bot_ne_coe lmg_eq_μ
        have ltG_mem_initIG := lt_mem_initIG g g_mem_I g_ne_0
        simp only at ltG_mem_initIG
        rw [
          term_mem_moni_iff
            (leading_monomial' mo g g_ne_0)
            (leading_monomials_fin mo G)
            (g.coeff (leading_monomial' mo g g_ne_0))
            (lc_not_zero mo g g_ne_0)
        ] at ltG_mem_initIG
        rw [lm_coe_lm' mo g g_ne_0, WithBot.some_eq_coe, WithBot.coe_inj] at lmg_eq_μ
        rcases ltG_mem_initIG with ⟨κ, κ_mem_lmG, κ_div_μ⟩
        exists κ, κ_mem_lmG
        subst μ
        exact le_trans κ_div_μ μ_div_ν
      · unfold monomial_ideal
        apply Ideal.span_mono
        apply Set.image_mono
        intro μ μ_mem_lmG
        simp only [leading_monomials_fin, Finset.coe_biUnion, Finset.mem_coe, Set.mem_iUnion,
          Option.mem_toFinset, Option.mem_def, exists_prop] at μ_mem_lmG
        rcases μ_mem_lmG with ⟨g, g_mem_G, lmg_eq_μ⟩
        simp only [leading_monomials, Submodule.carrier_eq_coe, Set.sUnion_image, SetLike.mem_coe,
          Set.mem_iUnion, Finset.mem_coe, Option.mem_toFinset, Option.mem_def, exists_prop]
        exists g
        exact ⟨by apply Ideal.subset_span g_mem_G, lmg_eq_μ⟩

/-- Definition of S-pair of two nonzero polynomials. -/
noncomputable def S_pair {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    MvPolynomial σ K × MvPolynomial σ K :=
  let lmf := leading_monomial' mo f hf
  let lcf := f.coeff lmf
  let lmg := leading_monomial' mo g hg
  let lcg := g.coeff lmg
  let lcm_fg := lcm_monomial lmf lmg
  ⟨f * MvPolynomial.monomial (lcm_fg - lmf) lcf⁻¹, g * MvPolynomial.monomial (lcm_fg - lmg) lcg⁻¹⟩

lemma spair_ne_0 {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    (S_pair mo f g hf hg).1 ≠ 0 ∧ (S_pair mo f g hf hg).2 ≠ 0 := by
  simp only [S_pair, ne_eq, mul_eq_zero, MvPolynomial.monomial_eq_zero, inv_eq_zero, not_or]
  constructor
  · constructor
    · exact hf
    · exact lc_not_zero mo f hf
  · constructor
    · exact hg
    · exact lc_not_zero mo g hg

lemma lm_spair_eq_lcm {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    let lmf := leading_monomial' mo f hf
    let lmg := leading_monomial' mo g hg
    let lcmfg := lcm_monomial lmf lmg
    let sp := S_pair mo f g hf hg
    have sp_ne_0 := spair_ne_0 mo f g hf hg
    leading_monomial' mo sp.1 sp_ne_0.1 = lcmfg ∧
    leading_monomial' mo sp.2 sp_ne_0.2 = lcmfg := by
  intro lmf lmg lcmfg sp sp_ne_0
  simp only [S_pair, sp]
  constructor
  · rw [
      lm'_monmul_commute mo f hf (lcmfg - lmf) (f.coeff lmf)⁻¹
        (by exact inv_ne_zero (lc_not_zero mo f hf))]
    rw [add_comm]
    exact monomial_sub_add lmf lcmfg (by intro x; simp [lcmfg, lcm_monomial])
  · rw [
      lm'_monmul_commute mo g hg (lcmfg - lmg) (g.coeff lmg)⁻¹
        (by exact inv_ne_zero (lc_not_zero mo g hg))]
    rw [add_comm]
    exact monomial_sub_add lmg lcmfg (by intro x; simp [lcmfg, lcm_monomial])

/-- Definition of the S-polynomial of two nonzero polynomials. -/
noncomputable def S_poly {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :=
  let ⟨p1, p2⟩ := S_pair mo f g hf hg
  p1 - p2

lemma S_poly_self_eq_zero {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f : MvPolynomial σ K) (hf : f ≠ 0) :
    S_poly mo f f hf hf = 0 := by
  unfold S_poly S_pair
  simp only [sub_self]

/-- A rewrite lemma on `S-poly` for equal pairs of polynomials. -/
lemma eq_S_poly_of_eq_eq {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f1 f2 g1 g2 : MvPolynomial σ K)
  (f_eq : f1 = f2) (g_eq : g1 = g2)
  (f_ne_0 : f1 ≠ 0 ∨ f2 ≠ 0) (g_ne_0 : g1 ≠ 0 ∨ g2 ≠ 0) :
    have f1_ne_0 : f1 ≠ 0 := by subst f2; simp at f_ne_0; exact f_ne_0
    have f2_ne_0 : f2 ≠ 0 := by subst f1; exact f1_ne_0
    have g1_ne_0 : g1 ≠ 0 := by subst g2; simp at g_ne_0; exact g_ne_0
    have g2_ne_0 : g2 ≠ 0 := by subst g1; exact g1_ne_0
    S_poly mo f1 g1 f1_ne_0 g1_ne_0 = S_poly mo f2 g2 f2_ne_0 g2_ne_0 := by
  unfold S_poly S_pair
  subst f2 g2
  simp

/-- Swapping the two polynomial inputs in `S-poly` is equivalent to negating. -/
lemma S_poly_neg_of_swap {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    S_poly mo g f hg hf = -S_poly mo f g hf hg := by
  unfold S_poly S_pair
  simp [lcm_monomial_comm]

lemma lm_spoly_lt_lcm {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    let spoly := S_poly mo f g hf hg
    let lcmfg := lcm_monomial (leading_monomial' mo f hf) (leading_monomial' mo g hg)
    WithBot.map mo.toSyn (leading_monomial mo spoly) < mo.toSyn lcmfg := by
  intro spoly lcmfg
  let lms := leading_monomial mo spoly
  cases em (spoly = 0) with
  | inl spoly_eq_0 =>
    subst spoly
    simp [spoly_eq_0, lm_zero_eq_bot]
  | inr spoly_ne_0 =>
    rw [lm_coe_lm' mo spoly spoly_ne_0]
    simp only [WithBot.map_coe, WithBot.coe_lt_coe, gt_iff_lt]
    apply lt_of_le_of_ne
    · have sp_ne_0 := spair_ne_0 mo f g hf hg
      have lm_sp_eq_lcm := lm_spair_eq_lcm mo f g hf hg
      simp only at lm_sp_eq_lcm
      subst spoly
      simp only [S_poly, S_pair, sub_eq_add_neg, ge_iff_le]
      conv_rhs => rw [← lm'_mon mo lcmfg (1 : K) one_ne_zero]
      have lmsfg_le_lcmfg :
        mo.toSyn (leading_monomial' mo (S_pair mo f g hf hg).1 sp_ne_0.1) ≤
        mo.toSyn (leading_monomial' mo ((MvPolynomial.monomial lcmfg) (1 : K)) (by simp)) := by
        apply le_of_eq
        simp only [lm'_mon mo lcmfg (1 : K) one_ne_zero, EmbeddingLike.apply_eq_iff_eq]
        exact lm_sp_eq_lcm.1
      have lmsgf_le_lcmfg :
        mo.toSyn (leading_monomial' mo (S_pair mo f g hf hg).2 sp_ne_0.2) ≤
        mo.toSyn (leading_monomial' mo ((MvPolynomial.monomial lcmfg) (1 : K)) (by simp)) := by
        apply le_of_eq
        simp only [lm'_mon mo lcmfg (1 : K) one_ne_zero, EmbeddingLike.apply_eq_iff_eq]
        exact lm_sp_eq_lcm.2
      apply
        lm'_add_le_of_both_lm'_le mo
          (S_pair mo f g hf hg).1
          (-(S_pair mo f g hf hg).2)
          (MvPolynomial.monomial lcmfg 1)
          sp_ne_0.1
          (by simp [sp_ne_0.2])
          (by rw [← sub_eq_add_neg]; exact spoly_ne_0)
          (by simp)
          lmsfg_le_lcmfg
          (by rw [← lm'_neg_eq_lm' mo (S_pair mo f g hf hg).2 sp_ne_0.2]; exact lmsgf_le_lcmfg)
    · have lms_mem := lm'_mem mo spoly spoly_ne_0
      simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]
      by_contra HC
      rw [HC, MvPolynomial.mem_support_iff] at lms_mem
      simp only [S_poly, S_pair, MvPolynomial.coeff_sub, ne_eq, spoly] at lms_mem
      absurd lms_mem
      rw [sub_eq_zero]
      unfold lcmfg
      conv_lhs =>
        rw [
          ← monomial_sub_add
            (leading_monomial' mo f hf)
            (lcm_monomial (leading_monomial' mo f hf) (leading_monomial' mo g hg))
            (by intro x; simp [lcm_monomial]),
          add_comm
        ]
        simp only [add_tsub_cancel_left, MvPolynomial.coeff_mul_monomial]
        rw [mul_inv_cancel₀ (by exact lc_not_zero mo f hf)]
      conv_rhs =>
        rw [
          ← monomial_sub_add
            (leading_monomial' mo g hg)
            (lcm_monomial (leading_monomial' mo f hf) (leading_monomial' mo g hg))
            (by intro x; simp [lcm_monomial]),
          add_comm
        ]
        simp only [add_tsub_cancel_left, MvPolynomial.coeff_mul_monomial]
        rw [mul_inv_cancel₀ (by exact lc_not_zero mo g hg)]

lemma smul_spoly {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0)
  (c1 c2 : K) (hc1 : c1 ≠ 0) (hc2 : c2 ≠ 0) :
    S_poly mo f g hf hg =
    S_poly mo (c1 • f) (c2 • g) (smul_ne_zero hc1 hf) (smul_ne_zero hc2 hg) := by
  simp only [S_poly, S_pair,
    ← lm'_smul_eq_lm' mo f hf c1 hc1, ← lm'_smul_eq_lm' mo g hg c2 hc2,
    MvPolynomial.coeff_smul, smul_eq_mul, mul_inv_rev, Algebra.smul_mul_assoc]
  rw [← mul_smul_comm c1 f _, ← mul_smul_comm c2 g _]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul]
  conv in _ * c1⁻¹ => rw [mul_comm]
  conv in c1 * _ => rw [← mul_assoc, mul_inv_cancel₀ hc1, one_mul]
  conv in _ * c2⁻¹ => rw [mul_comm]
  conv in c2 * _ => rw [← mul_assoc, mul_inv_cancel₀ hc2, one_mul]

lemma mul_mon_spoly {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) (α β : σ →₀ ℕ) :
    let lmf := leading_monomial' mo f hf
    let lmg := leading_monomial' mo g hg
    let αf := f * MvPolynomial.monomial α (1 : K)
    let βg := g * MvPolynomial.monomial β (1 : K)
    let αf_ne_0 : αf ≠ 0 := by unfold αf; exact mul_ne_zero hf (by simp)
    let βg_ne_0 : βg ≠ 0 := by unfold βg; exact mul_ne_zero hg (by simp)
    let lcm_fg := lcm_monomial lmf lmg
    let lcm_αfβg := lcm_monomial (α + lmf) (β + lmg)
    let γ := lcm_αfβg - lcm_fg
    S_poly mo αf βg αf_ne_0 βg_ne_0 =
    MvPolynomial.monomial γ (1 : K) * (S_poly mo f g hf hg) := by
  intro lmf lmg αf βg αf_ne_0 βg_ne_0 lcm_fg lcm_αfβg γ
  rw [mul_comm]
  have lcm_le_lcm' : lcm_fg ≤ lcm_αfβg := by
    intro x
    simp only [lcm_monomial, Finsupp.coe_mk, Finsupp.coe_add, Pi.add_apply, le_sup_iff, sup_le_iff,
      le_add_iff_nonneg_left, zero_le, true_and, and_true, lcm_fg, lcm_αfβg]
    cases Nat.le_total (lmf x) (lmg x) with
    | inl lmfx_le_lmgx => exact Or.inr (le_add_of_le_right lmfx_le_lmgx)
    | inr lmgx_le_lmfx => exact Or.inl (le_add_of_le_right lmgx_le_lmfx)
  simp only [S_poly, S_pair]
  rw [mul_sub_right_distrib]
  have lcf_eq_lcαf : f.coeff lmf = αf.coeff (leading_monomial' mo αf αf_ne_0) := by
    simp only [αf]
    rw [lm'_monmul_commute mo f hf _ _ one_ne_zero]
    simp only [MvPolynomial.coeff_mul_monomial, mul_one]
    rfl
  have lcg_eq_lcβg : g.coeff lmg = βg.coeff (leading_monomial' mo βg βg_ne_0) := by
    simp only [βg]
    rw [lm'_monmul_commute mo g hg _ _ one_ne_zero]
    simp only [MvPolynomial.coeff_mul_monomial, mul_one]
    rfl
  have sub_eq_sub_of_eq_eq (a b c d : MvPolynomial σ K) (hab : a = b) (hcd : c = d) :
    a - c = b - d := by simp [hab, hcd]
  have mul_eq_mul_of_eq_eq (a b c d : MvPolynomial σ K) (hab : a = b) (hcd : c = d) :
    a * c = b * d := by simp [hab, hcd]
  apply sub_eq_sub_of_eq_eq
  · unfold γ
    rw [← lcf_eq_lcαf]
    conv in (occs := 1) αf => unfold αf
    conv_lhs => simp [mul_assoc, add_comm]
    conv_rhs => simp [mul_assoc]
    apply mul_eq_mul_of_eq_eq
    · rfl
    · rw [MvPolynomial.monomial_eq_monomial_iff]
      apply Or.inl
      constructor
      · conv_lhs =>
          rw [add_comm]
          rw [
            ← tsub_tsub_assoc
              (le_lcm_monomial _ _).1
              (by
                rw [lm'_monmul_commute mo f hf α 1 one_ne_zero]
                simp only [le_add_iff_nonneg_left, zero_le])
          ]
        nth_rw 2 [lm'_monmul_commute mo f hf α 1 one_ne_zero]
        simp only [add_tsub_cancel_right]
        conv_rhs =>
          rw [tsub_add_eq_add_tsub (le_lcm_monomial lmf lmg).1]
          rw [← add_tsub_assoc_of_le lcm_le_lcm']
          rw [add_comm]
          rw [add_tsub_assoc_of_le (by rfl)]
          simp [lcm_fg]
        rw [lm'_monmul_commute mo f hf α 1 one_ne_zero]
        rw [lm'_monmul_commute mo g hg β 1 one_ne_zero]
        unfold lmf
        simp only [lcm_αfβg]
        rw [add_comm α lmf, add_comm β lmg]
      · rfl
  · unfold γ
    rw [← lcg_eq_lcβg]
    conv in (occs := 1) βg => unfold βg
    conv_lhs => simp [mul_assoc, add_comm]
    conv_rhs => simp [mul_assoc]
    apply mul_eq_mul_of_eq_eq
    · rfl
    · rw [MvPolynomial.monomial_eq_monomial_iff]
      apply Or.inl
      constructor
      · conv_lhs =>
          rw [add_comm]
          rw [
            ← tsub_tsub_assoc
              (le_lcm_monomial _ _).2
              (by
                rw [lm'_monmul_commute mo g hg β 1 one_ne_zero]
                simp only [le_add_iff_nonneg_left, zero_le])
          ]
        nth_rw 2 [lm'_monmul_commute mo g hg β 1 one_ne_zero]
        simp only [add_tsub_cancel_right]
        conv_rhs =>
          rw [tsub_add_eq_add_tsub (le_lcm_monomial lmf lmg).2]
          rw [← add_tsub_assoc_of_le lcm_le_lcm']
          rw [add_comm]
          rw [add_tsub_assoc_of_le (by rfl)]
          simp [lcm_fg]
        rw [lm'_monmul_commute mo f hf α 1 one_ne_zero]
        rw [lm'_monmul_commute mo g hg β 1 one_ne_zero]
        unfold lmg
        simp only [lcm_αfβg]
        rw [add_comm α lmf, add_comm β lmg]
      · rfl

lemma mul_term_spoly {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0)
  (α β : σ →₀ ℕ) (c1 c2 : K) (hc1 : c1 ≠ 0) (hc2 : c2 ≠ 0) :
    let lmf := leading_monomial' mo f hf
    let lmg := leading_monomial' mo g hg
    let c1αf := f * MvPolynomial.monomial α c1
    let c2βg := g * MvPolynomial.monomial β c2
    let c1αf_ne_0 : c1αf ≠ 0 := by unfold c1αf; exact mul_ne_zero hf (by simp [hc1])
    let c2βg_ne_0 : c2βg ≠ 0 := by unfold c2βg; exact mul_ne_zero hg (by simp [hc2])
    let lcm_fg := lcm_monomial lmf lmg
    let lcm_αfβg := lcm_monomial (α + lmf) (β + lmg)
    let γ := lcm_αfβg - lcm_fg
    S_poly mo c1αf c2βg c1αf_ne_0 c2βg_ne_0 =
    MvPolynomial.monomial γ (1 : K) * (S_poly mo f g hf hg) := by
  simp only
  have key := mul_mon_spoly mo f g hf hg α β
  simp only at key
  rw [← key]
  have c1αf_eq :
    f * (MvPolynomial.monomial α) c1 = c1 • (f * (MvPolynomial.monomial α) (1 : K)) := by
    conv_lhs =>
      rw [← mul_one c1, ← smul_eq_mul c1 (1 : K), ← MvPolynomial.smul_monomial c1, mul_smul_comm]
  have c2βg_eq :
    g * (MvPolynomial.monomial β) c2 = c2 • (g * (MvPolynomial.monomial β) (1 : K)) := by
    conv_lhs =>
      rw [← mul_one c2, ← smul_eq_mul c2 (1 : K), ← MvPolynomial.smul_monomial c2, mul_smul_comm]
  rw [
    eq_S_poly_of_eq_eq mo _ _ _ _ c1αf_eq c2βg_eq
      (Or.inl (mul_ne_zero hf (by simp [hc1])))
      (Or.inl (mul_ne_zero hg (by simp [hc2])))
  ]
  apply Eq.symm
  exact smul_spoly mo _ _ _ _ c1 c2 hc1 hc2

private lemma sum_ite_rewrite {α β : Type*} [DecidableEq α] [AddCommMonoid β]
  {s : Finset α} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
  {f g : α → β} (h : ∀ x ∈ s, p x ↔ q x) :
    (∑ x ∈ s, if p x then f x else g x) =
    (∑ x ∈ s, if q x then f x else g x) := by
  apply Finset.sum_congr rfl
  intro x hx
  simp_all

lemma syzygy_lemma {σ K ι : Type*} [DecidableEq σ] [Field K] [DecidableEq K] [DecidableEq ι]
  (mo : MonomialOrder σ) (s : Finset ι) (φ : ι → MvPolynomial σ K) (δ : σ →₀ ℕ)
  (φi_ne_0 : ∀ i ∈ s, φ i ≠ 0)
  (lmφi_eq_δ : ∀ (i : ι) (his : i ∈ s), leading_monomial' mo (φ i) (φi_ne_0 i his) = δ)
  (lm_sum_lt_δ : WithBot.map mo.toSyn (leading_monomial mo (∑ i ∈ s, φ i)) < mo.toSyn δ) :
    ∃ C : ι → ι → K,
      ∑ i ∈ s, φ i =
      ∑ (i ∈ s.attach) (j ∈ s.attach),
        C i.1 j.1 • S_poly mo (φ i.1) (φ j.1) (φi_ne_0 i.1 i.2) (φi_ne_0 j.1 j.2) := by
  have spoly_φ_eq (i j : ι) (his : i ∈ s) (hjs : j ∈ s) :
    S_poly mo (φ i) (φ j) (φi_ne_0 i his) (φi_ne_0 j hjs) =
    ((φ i).coeff (leading_monomial' mo (φ i) (φi_ne_0 i his)))⁻¹ • φ i -
      ((φ j).coeff (leading_monomial' mo (φ j) (φi_ne_0 j hjs)))⁻¹ • φ j := by
    simp only [S_poly, S_pair]
    rw [lmφi_eq_δ i his, lmφi_eq_δ j hjs]
    simp only [self_lcm_monomial_eq_self δ, tsub_self, MvPolynomial.monomial_zero']
    conv in (occs := 1 2) (_ * MvPolynomial.C _) => all_goals rw [mul_comm]
    simp [MvPolynomial.C_mul']
  cases em (s = ∅) with
  | inl s_empty =>
    subst s
    simp
  | inr s_nonempty =>
    push_neg at s_nonempty
    rw [← Finset.nonempty_iff_ne_empty, Finset.Nonempty] at s_nonempty
    rcases s_nonempty with ⟨k, hks⟩
    exists
      fun i j =>
        if his : i ∈ s
          then (if j = k then (φ i).coeff (leading_monomial' mo (φ i) (φi_ne_0 i his)) else 0)
          else 0
    simp only [Finset.coe_mem, ↓reduceDIte, ite_smul, zero_smul]
    rw [
      Finset.sum_product_right' s.attach s.attach
      (fun i j =>
        if j = k
          then (φ i).coeff (leading_monomial' mo (φ i) (by simp [φi_ne_0 i]))
                • S_poly mo (φ i) (φ j) (by simp [φi_ne_0 i]) (by simp [φi_ne_0 j])
          else 0)
    ]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    have s_attach_mem_eq_k_iff : ∀ x ∈ s.attach, x.1 = k ↔ x = ⟨k, hks⟩ := by simp
    rw [sum_ite_rewrite s_attach_mem_eq_k_iff]
    simp only [Finset.sum_ite_eq', Finset.mem_attach, ↓reduceIte]
    have spoly_φ_sum_eq_1 :
      ∑ x ∈ s.attach,
        (φ x.1).coeff (leading_monomial' mo (φ x.1) (φi_ne_0 x.1 x.2)) •
          S_poly mo (φ x.1) (φ k) (φi_ne_0 x.1 x.2) (φi_ne_0 k hks) =
      ∑ x ∈ s.attach,
        (φ x.1).coeff (leading_monomial' mo (φ x.1) (φi_ne_0 x.1 x.2)) •
          (((φ x.1).coeff (leading_monomial' mo (φ x.1) (φi_ne_0 x.1 x.2)))⁻¹ • φ x.1 -
            ((φ k).coeff (leading_monomial' mo (φ k) (φi_ne_0 k hks)))⁻¹ • φ k) := by
      apply Finset.sum_congr rfl
      intro x x_mem_s_att
      rw [spoly_φ_eq x.1 k x.2 hks]
    have spoly_φ_sum_eq_2 :
      ∑ x ∈ s.attach,
        (φ x.1).coeff (leading_monomial' mo (φ x.1) (φi_ne_0 x.1 x.2)) •
          (((φ x.1).coeff (leading_monomial' mo (φ x.1) (φi_ne_0 x.1 x.2)))⁻¹ • φ x.1 -
            ((φ k).coeff (leading_monomial' mo (φ k) (φi_ne_0 k hks)))⁻¹ • φ k) =
      ∑ x ∈ s.attach,
        φ x.1 -
          (∑ x ∈ s.attach, (φ x.1).coeff (leading_monomial' mo (φ x.1) (φi_ne_0 x.1 x.2))) •
            ((φ k).coeff (leading_monomial' mo (φ k) (φi_ne_0 k hks)))⁻¹ •
              φ k := by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x x_mem_s_att
      rw [smul_sub, smul_smul, mul_inv_cancel₀ (lc_not_zero mo _ _), one_smul]
    rw [spoly_φ_sum_eq_1, spoly_φ_sum_eq_2]
    simp only [Finset.sum_attach]
    have sum_lc_eq_0 :
      ∑ x ∈ s.attach, (φ x.1).coeff (leading_monomial' mo (φ x.1) (φi_ne_0 x.1 x.2)) = 0 := by
      calc
        _ = ∑ x ∈ s.attach, (φ x.1).coeff δ := by
          apply Finset.sum_congr rfl
          intro x x_mem_s_att
          rw [lmφi_eq_δ x.1 x.2]
        _ = (∑ x ∈ s.attach, φ x.1).coeff δ := by
          rw [MvPolynomial.coeff_sum]
        _ = (∑ x ∈ s, φ x).coeff δ := by
          rw [Finset.sum_attach]
      by_contra sum_coeff_δ_ne_0
      apply lt_irrefl (WithBot.some (mo.toSyn δ))
      push_neg at sum_coeff_δ_ne_0
      rw [← MvPolynomial.mem_support_iff] at sum_coeff_δ_ne_0
      rw [← Finset.mem_map' mo.toSyn.toEmbedding] at sum_coeff_δ_ne_0
      have : mo.toSyn.toEmbedding δ = mo.toSyn δ := by simp
      rw [this] at sum_coeff_δ_ne_0
      apply Finset.le_max at sum_coeff_δ_ne_0
      have lm_sum_eq :
        (Finset.map mo.toSyn.toEmbedding (∑ x ∈ s, φ x).support).max =
        WithBot.map (⇑mo.toSyn) (leading_monomial mo (∑ i ∈ s, φ i)) := by
        simp [leading_monomial, max_monomial, WithBot.map] -- refer to: Option.map_comp_map
      rw [lm_sum_eq] at sum_coeff_δ_ne_0
      exact lt_of_le_of_lt sum_coeff_δ_ne_0 lm_sum_lt_δ
    rw [sum_lc_eq_0, zero_smul, sub_zero]

/-- A polynomial `f` reduces to zero (or has a standard representation) over
a finite polynomial set `G` (under a fixed monomial order `mo`), if `f` is a
polynomial combination over `G` where the leading monomial of each summand doesn't
exceed that of `f` under `mo`. -/
def reduces_to_zero {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f : MvPolynomial σ K) (f_ne_0 : f ≠ 0) (G : Finset (MvPolynomial σ K)) :=
  ∃ (A : MvPolynomial σ K → MvPolynomial σ K),
    (f = ∑ g ∈ G, (A g) * g) ∧
    ∀ g ∈ G,
      (hgA : (A g) * g ≠ 0) →
        mo.toSyn (leading_monomial' mo ((A g) * g) hgA) ≤
        mo.toSyn (leading_monomial' mo f f_ne_0)

/-- `f` reduces to zero over `G`, iff its negation reduces to zero. -/
lemma red_0_iff_neg_red_0 {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f : MvPolynomial σ K) (f_ne_0 : f ≠ 0) (G : Finset (MvPolynomial σ K)) :
    have neg_f_ne_0 : -f ≠ 0 := neg_ne_zero.mpr f_ne_0
    reduces_to_zero mo f f_ne_0 G ↔ reduces_to_zero mo (-f) neg_f_ne_0 G := by
  intro neg_f_ne_0
  unfold reduces_to_zero
  constructor
  · intro ⟨A, f_sum_A, summand_lm_le_lmf⟩
    exists -A
    simp_all only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, true_and]
    intro g g_mem_G Agg_ne_0
    rw [neg_ne_zero] at Agg_ne_0
    rw [← lm'_neg_eq_lm' mo (A g * g) Agg_ne_0]
    rw [← lm'_neg_eq_lm' mo (∑ g ∈ G, A g * g) (by rw [f_sum_A] at f_ne_0; exact f_ne_0)]
    exact summand_lm_le_lmf g g_mem_G Agg_ne_0
  · intro ⟨A, f_sum_A, summand_lm_le_lmf⟩
    exists -A
    simp_all only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [neg_eq_iff_eq_neg] at f_sum_A
    constructor
    · exact f_sum_A
    · intro g g_mem_G Agg_ne_0
      rw [neg_ne_zero] at Agg_ne_0
      rw [← lm'_neg_eq_lm' mo (A g * g) Agg_ne_0]
      rw [lm'_eq_of_eq mo f _ f_sum_A f_ne_0]
      rw [
        ← lm'_neg_eq_lm' mo (∑ g ∈ G, A g * g)
          (by rw [f_sum_A, neg_ne_zero] at f_ne_0; exact f_ne_0)]
      exact summand_lm_le_lmf g g_mem_G Agg_ne_0

/-- A rewrite lemma on `reduces_to_zero` for equal polynomials. -/
lemma red_0_of_eq {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ K) (f_eq_g : f = g) (f_ne_0 : f ≠ 0)
  (G : Finset (MvPolynomial σ K)) :
    have g_ne_0 : g ≠ 0 := by rw [← f_eq_g]; exact f_ne_0
    reduces_to_zero mo f f_ne_0 G ↔ reduces_to_zero mo g g_ne_0 G := by
  intro g_ne_0
  unfold reduces_to_zero
  rw [lm'_eq_of_eq mo f g f_eq_g f_ne_0]
  subst f
  rfl

/-- If `f` reduces to zero over `G`, then it also reduces to zero over any
extension of `G`. -/
lemma red_0_on_extension {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f : MvPolynomial σ K) (f_ne_0 : f ≠ 0)
  (G G' : Finset (MvPolynomial σ K)) :
    reduces_to_zero mo f f_ne_0 G → reduces_to_zero mo f f_ne_0 (G ∪ G') := by
  unfold reduces_to_zero
  intro ⟨A, f_sum_A, lm_term_le_lmf⟩
  exists fun g => if g ∈ G then A g else 0
  simp only [ite_mul, zero_mul, Finset.sum_ite_mem, Finset.union_inter_cancel_left,
    Finset.mem_union, ne_eq, ite_eq_right_iff, mul_eq_zero, Classical.not_imp, not_or]
  constructor
  · exact f_sum_A
  · simp_all [↓reduceIte]

/-- Suppose `f` already reduces to zero over `G`. Given `g ∈ G`, a monomial
`α` and a nonzero scalar `c` such that the leading monomial of `(monomial α c) * g`
exceeds that of `f`, we have that `f + (monomial α c) * g` also reduces to zero
over `G`. -/
lemma mul_basis_add_red_0 {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K))
  (g : MvPolynomial σ K) (g_mem_G : g ∈ G) (g_ne_0 : g ≠ 0)
  (f : MvPolynomial σ K) (f_ne_0 : f ≠ 0) (f_red_0_G : reduces_to_zero mo f f_ne_0 G)
  (α : σ →₀ ℕ) (c : K) (c_ne_0 : c ≠ 0)
  (lm_g_mul_gt_lmf :
    mo.toSyn (leading_monomial' mo ((MvPolynomial.monomial α c) * g) (by simp_all)) >
    mo.toSyn (leading_monomial' mo f f_ne_0)) :
    let lmgmul := leading_monomial' mo ((MvPolynomial.monomial α c) * g) (by simp_all)
    have f_add_g_mul_ne_0 : f + (MvPolynomial.monomial α c) * g ≠ 0 := by
      rw [MvPolynomial.ne_zero_iff]
      exists lmgmul
      simp only [MvPolynomial.coeff_add, ne_eq]
      have : f.coeff lmgmul = 0 := by
        apply coeff_zero_of_lt_lm
        simp [lm_coe_lm' mo f f_ne_0]
        exact lm_g_mul_gt_lmf
      simp only [this, zero_add, ne_eq]
      exact lc_not_zero mo _ _
    reduces_to_zero mo (f + (MvPolynomial.monomial α c) * g) f_add_g_mul_ne_0 G := by
  intro lmgmul f_add_g_mul_ne_0
  unfold reduces_to_zero
  unfold reduces_to_zero at f_red_0_G
  rcases f_red_0_G with ⟨A, f_sum_A_G, summand_lm_le_lmf⟩
  let A' := A + fun x => if x = g then (MvPolynomial.monomial α) c else 0
  exists A'
  constructor
  · simp only [Pi.add_apply, right_distrib, ite_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq', A']
    conv_rhs => rw [← f_sum_A_G]
    simp_all
  · intro g' g'_mem_G hg'A
    simp only [Pi.add_apply, ne_eq, mul_eq_zero, not_or, A'] at hg'A
    rcases hg'A with ⟨Ag'_ne_0, g'_ne_0⟩
    have lmfadd_eq_lmgmul :
      leading_monomial' mo (f + (MvPolynomial.monomial α) c * g) f_add_g_mul_ne_0 = lmgmul := by
      unfold lmgmul
      conv_rhs =>
        rw [
          ← lm_sub_smul_eq_lm mo f ((MvPolynomial.monomial α) c * g) _ _ lm_g_mul_gt_lmf (-1)]
      simp only [neg_smul, one_smul, sub_neg_eq_add]
      exact lm'_eq_of_eq mo _ _ (add_comm f ((MvPolynomial.monomial α) c * g)) f_add_g_mul_ne_0
    rw [lmfadd_eq_lmgmul]
    simp only [Pi.add_apply, ge_iff_le, A']
    cases em (g' = g) with
    | inl g'_eq_g =>
      subst g'
      simp only [↓reduceIte]
      cases em (A g = 0) with
      | inl Ag_eq_0 =>
        simp [Ag_eq_0, lmgmul]
      | inr Ag_ne_0 =>
        apply le_of_eq
        rw [AddEquiv.apply_eq_iff_eq]
        have Agg_ne_0 : A g * g ≠ 0 := by simp [g'_ne_0, Ag_ne_0]
        rw [
          lm'_eq_of_eq mo
            ((A g + (MvPolynomial.monomial α) c) * g)
            ((MvPolynomial.monomial α) c * g + A g * g)
            (by ring) _]
        have lmAgg_le_lmf := summand_lm_le_lmf g g'_mem_G Agg_ne_0
        have lmAgg_lt_lmgmul := lt_of_le_of_lt lmAgg_le_lmf lm_g_mul_gt_lmf
        have key :=
          lm_sub_smul_eq_lm mo
            (A g * g) ((MvPolynomial.monomial α) c * g)
            Agg_ne_0 _ lmAgg_lt_lmgmul (-1)
        simp only [neg_smul, one_smul, sub_neg_eq_add] at key
        exact key
    | inr g'_ne_g =>
      subst A'
      simp only [g'_ne_g, ↓reduceIte, add_zero]
      simp only [Pi.add_apply, g'_ne_g, ↓reduceIte, add_zero] at hg'A
      calc
        mo.toSyn (leading_monomial' mo (A g' * g') hg'A) ≤
        mo.toSyn (leading_monomial' mo f f_ne_0) := by
          exact summand_lm_le_lmf g' g'_mem_G hg'A
        _ ≤ mo.toSyn lmgmul := by
          exact le_of_lt lm_g_mul_gt_lmf

lemma red_0_of_remainder_0 {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f : MvPolynomial σ K)
  (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G) :
    remainder_zero mo f G hG → (f_ne_0 : f ≠ 0) → reduces_to_zero mo f f_ne_0 G := by
  intro fG_r_0 f_ne_0
  unfold remainder_zero at fG_r_0
  rcases fG_r_0 with ⟨LG, G_eq_LG, LG_Nodup, mpds_fG_r_0⟩
  have hLG : 0 ∉ LG := by
    rw [← List.mem_toFinset, ← G_eq_LG]
    exact hG
  have mpds_fGr_repn := mvpoly_division_repn mo f LG hLG LG_Nodup
  simp only [Fin.getElem_fin, mpds_fG_r_0, add_zero] at mpds_fGr_repn
  let mpds_fG := mvpoly_division mo f LG hLG LG_Nodup
  unfold reduces_to_zero
  let A : MvPolynomial σ K → MvPolynomial σ K :=
    fun p =>
      match LGpi : LG.finIdxOf? p with
      | none => 0
      | some i => mpds_fG.Q[i]'(by rw [← mpds_fG.FQ_len_eq]; exact i.isLt)
  exists A
  have summand_eq (i : Fin LG.length) :
    LG[i] * mpds_fG.Q[i]'(by rw [← mpds_fG.FQ_len_eq]; exact i.isLt) =
    A LG[i] * LG[i] := by
    simp only [Fin.getElem_fin, mul_comm, mul_eq_mul_left_iff]
    apply Or.inl
    simp only [Fin.getElem_fin, A]
    split
    next eq_none =>
      simp only [List.finIdxOf?_eq_none_iff, List.getElem_mem, not_true_eq_false] at eq_none
    next i' eq_some =>
      simp only [List.finIdxOf?_eq_some_iff, Fin.getElem_fin, ne_eq] at eq_some
      rcases eq_some with ⟨LGi'_eq_LGi, _⟩
      have i_eq_i' : i = i' := by
        ext
        exact (List.Nodup.getElem_inj_iff LG_Nodup).mp LGi'_eq_LGi.symm
      rw [i_eq_i']
  constructor
  · simp only [mpds_fGr_repn]
    rw [G_eq_LG, List.sum_toFinset, ← Fin.sum_univ_fun_getElem]
    · unfold mpds_fG at summand_eq
      simp_all only [Fin.getElem_fin] -- how does this end with the goal?
    · exact LG_Nodup -- where did this come from?
  · intro g g_mem_G hgA
    have lm_summand_le := mpds_fG.lm_summand_le_lmf
    have g_eq_LGi : ∃ i : Fin LG.length, g = LG[i] := by
      simp only [G_eq_LG, List.mem_toFinset, List.mem_iff_getElem] at g_mem_G
      rcases g_mem_G with ⟨i, hi, LGi_eq_g⟩
      exact ⟨⟨i, hi⟩, LGi_eq_g.symm⟩
    rcases g_eq_LGi with ⟨⟨i, hi⟩, g_eq_LGi⟩
    subst g
    rw [← summand_eq] at hgA
    have lm_summand_i_le := lm_summand_le ⟨i, hi⟩
    rw [lm_coe_lm' mo _ hgA, lm_coe_lm' mo f f_ne_0] at lm_summand_i_le
    simp only [Fin.getElem_fin, WithBot.map_coe, WithBot.coe_le_coe] at lm_summand_i_le
    rw [lm'_eq_of_eq mo _ _ (summand_eq ⟨i, hi⟩).symm]
    exact lm_summand_i_le

/-- Auxiliary definition for `refined_buchberger`: every S-polynomial from `G`
divides to remainder zero under some order of division algorithm by `G` itself. -/
def every_S_poly_remainder_0 {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G) :=
  ∀ f1, (hf1 : f1 ∈ G) → ∀ f2, (hf2 : f2 ∈ G) →
    let s12 := S_poly mo f1 f2 (ne_of_mem_of_not_mem hf1 hG) (ne_of_mem_of_not_mem hf2 hG)
    remainder_zero mo s12 G hG

/-- Auxiliary definition for `refined_buchberger`: every S-polynomial from `G`
reduces to zero over `G` itself. -/
def every_S_poly_red_0 {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G) :=
  ∀ f1, (hf1 : f1 ∈ G) → ∀ f2, (hf2 : f2 ∈ G) →
    let s12 := S_poly mo f1 f2 (ne_of_mem_of_not_mem hf1 hG) (ne_of_mem_of_not_mem hf2 hG)
    (hs12 : s12 ≠ 0) → reduces_to_zero mo s12 hs12 G

/-- Step 1 for refined Buchberger criterion: if `G` is a Groebner basis
(of its ideal span), then every S-polynomial from `G` divides to remainder zero
by `G`. -/
lemma buchberger_tfae_1 {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G) :
    is_groebner mo G (Ideal.span G) → every_S_poly_remainder_0 mo G hG := by
  unfold every_S_poly_remainder_0
  intro G_groebner f1 f1_mem_G f2 f2_mem_G
  rw [← mem_ideal_iff_gb_remainder_zero mo _ G (Ideal.span G) hG G_groebner]
  simp only [S_poly, S_pair]
  have span_pair_le_I : Ideal.span {f1, f2} ≤ Ideal.span G := by
    apply Ideal.span_mono
    exact Set.pair_subset f1_mem_G f2_mem_G
  apply span_pair_le_I
  rw [Ideal.mem_span_pair]
  -- unfold definitions in S-poly
  have f1_ne_0 : f1 ≠ 0 := ne_of_mem_of_not_mem f1_mem_G hG
  have f2_ne_0 : f2 ≠ 0 := ne_of_mem_of_not_mem f2_mem_G hG
  let lmf1 := leading_monomial' mo f1 f1_ne_0
  let lcf1 := f1.coeff lmf1
  let lmf2 := leading_monomial' mo f2 f2_ne_0
  let lcf2 := f2.coeff lmf2
  let lcm_f12 := lcm_monomial lmf1 lmf2
  exists
    MvPolynomial.monomial (lcm_f12 - lmf1) lcf1⁻¹,
    -MvPolynomial.monomial (lcm_f12 - lmf2) lcf2⁻¹
  rw [mul_comm _ f1, mul_comm _ f2]
  simp only [mul_neg, lcm_f12, lmf1, lmf2, lcf1, lcf2]
  ring

/-- Step 2 for refined Buchberger criterion: if every S-polynomial from `G`
divides to remainder zero by `G`, then every such S-polynomial has a standard
representation over `G`. -/
lemma buchberger_tfae_2 {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G) :
    every_S_poly_remainder_0 mo G hG → every_S_poly_red_0 mo G hG := by
  unfold every_S_poly_remainder_0 every_S_poly_red_0
  intro GS_rem_0 f1 f1_mem_G f2 f2_mem_G s12 s12_ne_0
  exact red_0_of_remainder_0 mo s12 G hG (GS_rem_0 f1 f1_mem_G f2 f2_mem_G) s12_ne_0

/-- Step 3 for refined Buchberger criterion: iff every S-polynomial from `G`
reduces to zero over `G`, then `G` is a Groebner basis (of its ideal span). -/
lemma buchberger_tfae_3 {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G) :
    every_S_poly_red_0 mo G hG → is_groebner mo G (Ideal.span G) := by
  intro GS_red_0'
  cases em (G = ∅) with
  | inl G_empty =>
    subst G
    simp [is_groebner, leading_monomials, leading_monomials_fin, lm_zero_eq_bot,
      ← WithBot.none_eq_bot]
  | inr G_nonempty =>
    push_neg at G_nonempty
    rw [← Finset.nonempty_iff_ne_empty] at G_nonempty
    unfold every_S_poly_red_0 at GS_red_0'
    unfold reduces_to_zero at GS_red_0'
    rw [groebner_iff_ideal_leadterm_mem_initI]
    intro f f_mem_IG f_ne_0 lmf lcf ltf
    rw [Ideal.span, Submodule.mem_span_finset] at f_mem_IG
    simp only [smul_eq_mul] at f_mem_IG
    let fG_repns :=
      { h : MvPolynomial σ K → MvPolynomial σ K
        | h.support ⊆ G ∧ ∑ g ∈ G, h g * g = f }
    have fG_repns_nonempty : fG_repns.Nonempty := by
      simp only [Set.Nonempty, Set.mem_setOf_eq, fG_repns]
      exact f_mem_IG
    let fG_repn_max_lm (h : MvPolynomial σ K → MvPolynomial σ K) :=
      (G.image (fun g => WithBot.map mo.toSyn (leading_monomial mo (h g * g)))).max'
      (by simp only [Finset.image_nonempty, G_nonempty])
    let hδ' := Function.argminOn fG_repn_max_lm fG_repns fG_repns_nonempty
    have hδ_repn_fG : hδ' ∈ fG_repns := by simp [fG_repns, hδ']
    let wbδ' := fG_repn_max_lm hδ'
    have lmf_le_lm_repn :
      ∀ h ∈ fG_repns, WithBot.map mo.toSyn (leading_monomial mo f) ≤ fG_repn_max_lm h := by
      intro h h_mem_fG_repns
      simp only [Set.mem_setOf_eq, fG_repns] at h_mem_fG_repns
      unfold fG_repn_max_lm
      by_contra HC
      push_neg at HC
      simp only [lm_coe_lm' mo f f_ne_0, WithBot.map_coe, Finset.max'_lt_iff, Finset.mem_image,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at HC
      have summand_coeff_lmf_eq_0 :
        ∀ g ∈ G, (h g * g).coeff (leading_monomial' mo f f_ne_0) = 0 := by
        intro g g_mem_G
        have HCg := HC g g_mem_G
        cases em (h g * g = 0) with
        | inl hgg_eq_0 =>
          simp [hgg_eq_0]
        | inr hgg_ne_0 => -- todo
          push_neg at hgg_ne_0
          simp only [lm_coe_lm' mo (h g * g) hgg_ne_0, WithBot.map_coe, WithBot.coe_lt_coe] at HCg
          rw [← MvPolynomial.notMem_support_iff]
          by_contra lmf_supp_hgg
          have HCg' := mem_le_lm' mo (h g * g) hgg_ne_0 _ lmf_supp_hgg
          apply lt_irrefl (mo.toSyn (leading_monomial' mo f f_ne_0))
          exact lt_of_le_of_lt HCg' HCg
      have hgg_sum_coeff_lmf_eq_0 :
        (∑ g ∈ G, h g * g).coeff (leading_monomial' mo f f_ne_0) = 0 := by
        simp only [MvPolynomial.coeff_sum]
        exact Finset.sum_eq_zero summand_coeff_lmf_eq_0
      rw [h_mem_fG_repns.2, ← MvPolynomial.notMem_support_iff] at hgg_sum_coeff_lmf_eq_0
      exact hgg_sum_coeff_lmf_eq_0 (lm'_mem mo f f_ne_0)
    have lmf_le_lm_hδgg := lmf_le_lm_repn hδ' hδ_repn_fG
    have wbδ_ne_bot : wbδ' ≠ ⊥ := by -- 참조: WithBot.ne_bot_iff_exists
      unfold wbδ'
      by_contra wbδ_eq_bot
      simp [wbδ_eq_bot, lm_coe_lm' mo f f_ne_0] at lmf_le_lm_hδgg
    rcases WithBot.ne_bot_iff_exists.mp wbδ_ne_bot with ⟨δ', wbδ_eq_coe_δ⟩
    let δ := mo.toSyn.symm δ'
    subst wbδ'
    simp only [lm_coe_lm' mo f f_ne_0, WithBot.map_coe, ← wbδ_eq_coe_δ,
      WithBot.coe_le_coe] at lmf_le_lm_hδgg
    cases @lt_or_eq_of_le mo.syn _ _ _ lmf_le_lm_hδgg with
    | inl lmf_lt_δ =>
      have hδ_argmin : ∀ h ∈ fG_repns, fG_repn_max_lm hδ' ≤ fG_repn_max_lm h := by
        intro h hh_fG_repn
        unfold hδ'
        exact Function.argminOn_le fG_repn_max_lm fG_repns hh_fG_repn fG_repns_nonempty
      let filG_eq := G.filter (fun g => WithBot.map mo.toSyn (leading_monomial mo (hδ' g * g)) = δ')
      have filG_eq_subs_G : filG_eq ⊆ G := by simp [filG_eq]
      let filG_lt := G \ filG_eq
      have filG_disj : Disjoint filG_eq filG_lt := Finset.disjoint_sdiff
      have G_filG_disjU : G = filG_eq.disjUnion filG_lt filG_disj := by
        simp [filG_lt, filG_eq]
      have mem_filG_lt :
        ∀ g ∈ filG_lt, WithBot.map mo.toSyn (leading_monomial mo (hδ' g * g)) < δ' := by
        intro g g_mem_filG_lt
        simp only [Finset.mem_sdiff, Finset.mem_filter, not_and, filG_lt, filG_eq] at g_mem_filG_lt
        rcases g_mem_filG_lt with ⟨g_mem_G, lmhδgg_ne_δ⟩
        have lmhδgg_ne_δ := lmhδgg_ne_δ g_mem_G
        apply Ne.lt_of_le lmhδgg_ne_δ -- now enough to show (≤)
        rw [wbδ_eq_coe_δ]
        simp only [fG_repn_max_lm]
        apply Finset.le_max'
        simp only [Finset.mem_image]
        exists g
      have ⟨hδ_supp_G, hδG_repn_f⟩ := Set.mem_setOf.mp hδ_repn_fG
      rw [G_filG_disjU, Finset.sum_disjUnion] at hδG_repn_f
      have hδg_ne_0_in_filG_eq (g : MvPolynomial σ K) (hg : g ∈ filG_eq) : hδ' g ≠ 0 := by
        by_contra hδg_eq_0
        simp only [Finset.mem_filter, filG_eq] at hg
        rcases hg with ⟨g_mem_G, lmhδgg_eq_δ⟩
        simp [hδg_eq_0, lm_zero_eq_bot, WithBot.map_bot] at lmhδgg_eq_δ
      have g_ne_0_in_filG_eq (g : MvPolynomial σ K) (hg : g ∈ filG_eq) : g ≠ 0 := by
        apply ne_of_mem_of_not_mem _ hG
        simp [hg, G_filG_disjU]
      have mem_filG_eq_lm_decomp' (g : MvPolynomial σ K) (hg : g ∈ filG_eq) :
        mo.toSyn (leading_monomial' mo (hδ' g) (hδg_ne_0_in_filG_eq g hg)) +
        mo.toSyn (leading_monomial' mo g (g_ne_0_in_filG_eq g hg)) =
        δ' := by
        let hg_ := hg
        simp only [Finset.mem_filter, filG_eq] at hg_
        let hgδ := hg_.2
        rw [
          lm_coe_lm' mo _
            (mul_ne_zero (hδg_ne_0_in_filG_eq g hg) (g_ne_0_in_filG_eq g hg))
        ] at hgδ
        simp only [
          WithBot.map_coe, WithBot.coe_inj,
          ← lm'_mul_commute mo (hδ' g) g (hδg_ne_0_in_filG_eq g hg) (g_ne_0_in_filG_eq g hg),
          map_add
        ] at hgδ
        exact hgδ
      have mem_filG_eq_lm_decomp (g : MvPolynomial σ K) (hg : g ∈ filG_eq) :
        leading_monomial' mo (hδ' g) (hδg_ne_0_in_filG_eq g hg) +
        leading_monomial' mo g (g_ne_0_in_filG_eq g hg) =
        δ := by
        unfold δ
        simp only [AddEquiv.eq_symm_apply mo.toSyn, map_add]
        exact mem_filG_eq_lm_decomp' g hg
      let leadterm_hδ (g : MvPolynomial σ K) (hg : g ∈ filG_eq) : MvPolynomial σ K :=
        let lmhδg := leading_monomial' mo (hδ' g) (hδg_ne_0_in_filG_eq g hg)
        MvPolynomial.monomial lmhδg ((hδ' g).coeff lmhδg)
      have leadterm_hδ_ne_0 (g : MvPolynomial σ K) (hg : g ∈ filG_eq) : leadterm_hδ g hg ≠ 0 := by
        simp only [ne_eq, MvPolynomial.monomial_eq_zero, leadterm_hδ]
        exact lc_not_zero mo (hδ' g) (hδg_ne_0_in_filG_eq g hg)
      rw [← Finset.sum_attach filG_eq (fun g => hδ' g * g)] at hδG_repn_f
      have hδ_filG_eq_split :
        ∑ g ∈ filG_eq.attach, hδ' g.1 * g.1 =
        ∑ g ∈ filG_eq.attach, leadterm_hδ g.1 g.2 * g.1 +
        ∑ g ∈ filG_eq.attach, (hδ' g.1 - leadterm_hδ g.1 g.2) * g.1 := by
        rw [← Finset.sum_add_distrib]
        ring_nf
        apply Finset.sum_congr rfl
        intro ⟨g, hg⟩ mem_filG_eq
        rw [mul_comm]
      rw [hδ_filG_eq_split] at hδG_repn_f
      have filG_eq_sublm_lm_lt_δ :
        ∀ g ∈ filG_eq.attach,
          WithBot.map (⇑mo.toSyn) (leading_monomial mo ((hδ' g.1 - leadterm_hδ g.1 g.2) * g.1)) <
          ↑δ' := by
        intro g g_mem_filG_eq
        cases em (hδ' g.1 - leadterm_hδ g.1 g.2 = 0) with
        | inl sub_lm_eq_0 =>
          simp [sub_lm_eq_0, lm_zero_eq_bot, WithBot.map_bot]
        | inr sub_lm_ne_0 =>
          rw [
            lm_coe_lm' mo
              ((hδ' g.1 - leadterm_hδ g.1 g.2) * g.1)
              (mul_ne_zero sub_lm_ne_0 (g_ne_0_in_filG_eq g.1 g.2))
          ]
          simp only [WithBot.map_coe, WithBot.coe_lt_coe,
            ← lm'_mul_commute mo _ _ sub_lm_ne_0 (g_ne_0_in_filG_eq g.1 g.2), map_add]
          rw [← mem_filG_eq_lm_decomp' g.1 g.2]
          simp only [add_lt_add_iff_right]
          have key := lm_sub_leadterm_lt_lm mo (hδ' g.1) (hδg_ne_0_in_filG_eq g.1 g.2)
          simp only at key
          simp only [gt_iff_lt, leadterm_hδ]
          simp only [leadterm_hδ] at sub_lm_ne_0
          simp only [lm_coe_lm' mo _ sub_lm_ne_0, WithBot.map_coe, WithBot.coe_lt_coe] at key
          exact key
      have sum_filG_eq_sublm_lm_lt_δ :
        WithBot.map mo.toSyn
          (leading_monomial mo (∑ g ∈ filG_eq.attach, (hδ' g.1 - leadterm_hδ g.1 g.2) * g.1)) <
        δ' := by
        have key :=
          lm_sum_lt_of_all_lm_lt mo filG_eq.attach
            (fun g => (hδ' g.1 - leadterm_hδ g.1 g.2) * g.1)
            (mo.toSyn.symm δ')
        simp only [AddEquiv.apply_symm_apply] at key
        apply key
        exact filG_eq_sublm_lm_lt_δ
      have sum_filG_lt_lm_lt_δ :
        WithBot.map mo.toSyn (leading_monomial mo (∑ x ∈ filG_lt, hδ' x * x)) < δ' := by
        have key := lm_sum_lt_of_all_lm_lt mo filG_lt (fun g => hδ' g * g) (mo.toSyn.symm δ')
        simp only [AddEquiv.apply_symm_apply] at key
        apply key
        exact mem_filG_lt
      have sum_filG_eq_lm_lt_δ :
        WithBot.map mo.toSyn
          (leading_monomial mo (∑ g ∈ filG_eq.attach, leadterm_hδ g.1 g.2 * g.1)) <
        δ' := by
        apply eq_add_neg_of_add_eq at hδG_repn_f
        apply eq_add_neg_of_add_eq at hδG_repn_f
        rw [hδG_repn_f]
        conv_rhs => rw [← AddEquiv.apply_symm_apply mo.toSyn δ']
        apply lm_add_lt_of_both_lm_lt_mon
        · apply lm_add_lt_of_both_lm_lt_mon
          · simp [lm_coe_lm' mo f f_ne_0, lmf_lt_δ]
          · simp [← lm_neg_eq_lm, sum_filG_lt_lm_lt_δ]
        · simp [← lm_neg_eq_lm, sum_filG_eq_sublm_lm_lt_δ]
      conv at sum_filG_eq_lm_lt_δ => rw [← AddEquiv.apply_symm_apply mo.toSyn δ']
      apply
        syzygy_lemma mo filG_eq.attach _ _
        (by
          intro ⟨g, hg⟩ _
          apply mul_ne_zero
          · simp only [ne_eq, MvPolynomial.monomial_eq_zero, leadterm_hδ]
            exact lc_not_zero mo (hδ' g) (hδg_ne_0_in_filG_eq g hg)
          · exact g_ne_0_in_filG_eq g hg)
        (by
          intro ⟨g, hg⟩ _
          let hg_ := hg
          simp only [
            Finset.mem_filter,
            lm_coe_lm' mo (hδ' g * g)
              (mul_ne_zero (hδg_ne_0_in_filG_eq g hg) (g_ne_0_in_filG_eq g hg)),
            WithBot.map_coe, WithBot.coe_inj, filG_eq
          ] at hg_
          simp only [← hg_.2, AddEquiv.symm_apply_apply]
          rw [
            ← lm'_mul_commute mo (leadterm_hδ g hg) g
              (leadterm_hδ_ne_0 g hg) (g_ne_0_in_filG_eq g hg),
            ← lm'_mul_commute mo (hδ' g) g
              (hδg_ne_0_in_filG_eq g hg) (g_ne_0_in_filG_eq g hg)
          ]
          simp only [add_left_inj, leadterm_hδ]
          exact lm'_mon mo _ _ (lc_not_zero mo (hδ' g) (hδg_ne_0_in_filG_eq g hg)))
        at sum_filG_eq_lm_lt_δ
      rcases sum_filG_eq_lm_lt_δ with ⟨C_spoly, sum_filG_spoly⟩
      simp only at sum_filG_spoly
      have filG_eq_prod_sum_eq_1 :
        ∑ i ∈ filG_eq.attach, leadterm_hδ i.1 i.2 * i.1 =
        ∑ x ∈ filG_eq.attach ×ˢ filG_eq.attach,
          C_spoly x.1 x.2 •
            S_poly mo (leadterm_hδ x.1.1 x.1.2 * x.1.1) (leadterm_hδ x.2.1 x.2.2 * x.2.1)
              (mul_ne_zero (leadterm_hδ_ne_0 x.1.1 x.1.2) (g_ne_0_in_filG_eq x.1.1 x.1.2))
              (mul_ne_zero (leadterm_hδ_ne_0 x.2.1 x.2.2) (g_ne_0_in_filG_eq x.2.1 x.2.2)) := by
        rw [sum_filG_spoly]
        rw [Finset.sum_product, Finset.sum_product]
        rw [
          Finset.sum_attach filG_eq.attach
            (fun x =>
              ∑ y ∈ filG_eq.attach.attach,
                C_spoly x y.1 •
                  S_poly mo (leadterm_hδ x.1 x.2 * x.1) (leadterm_hδ y.1.1 y.1.2 * y.1.1)
                    (mul_ne_zero (leadterm_hδ_ne_0 x.1 x.2) (g_ne_0_in_filG_eq x.1 x.2))
                    (mul_ne_zero (leadterm_hδ_ne_0 y.1.1 y.1.2) (g_ne_0_in_filG_eq y.1.1 y.1.2)))
        ]
        apply Finset.sum_congr rfl
        intro x _
        rw [
          Finset.sum_attach filG_eq.attach
            (fun y =>
              C_spoly x y •
                S_poly mo (leadterm_hδ x.1 x.2 * x.1) (leadterm_hδ y.1 y.2 * y.1)
                  (mul_ne_zero (leadterm_hδ_ne_0 x.1 x.2) (g_ne_0_in_filG_eq x.1 x.2))
                  (mul_ne_zero (leadterm_hδ_ne_0 y.1 y.2) (g_ne_0_in_filG_eq y.1 y.2)))
        ]
      rw [filG_eq_prod_sum_eq_1] at hδG_repn_f
      have filG_eq_prod_sum_eq_2 :
        ∑ x ∈ filG_eq.attach ×ˢ filG_eq.attach,
          C_spoly x.1 x.2 •
            S_poly mo (leadterm_hδ x.1.1 x.1.2 * x.1.1) (leadterm_hδ x.2.1 x.2.2 * x.2.1)
              (mul_ne_zero (leadterm_hδ_ne_0 x.1.1 x.1.2) (g_ne_0_in_filG_eq x.1.1 x.1.2))
              (mul_ne_zero (leadterm_hδ_ne_0 x.2.1 x.2.2) (g_ne_0_in_filG_eq x.2.1 x.2.2)) =
        ∑ x ∈ filG_eq.attach ×ˢ filG_eq.attach,
          MvPolynomial.monomial
            (δ -
              lcm_monomial
                (leading_monomial' mo x.1.1 (g_ne_0_in_filG_eq x.1.1 x.1.2))
                (leading_monomial' mo x.2.1 (g_ne_0_in_filG_eq x.2.1 x.2.2)))
            (C_spoly x.1 x.2) *
          (S_poly mo x.1.1 x.2.1
            (g_ne_0_in_filG_eq x.1.1 x.1.2) (g_ne_0_in_filG_eq x.2.1 x.2.2)) := by
        apply Finset.sum_congr rfl
        intro ⟨x, y⟩ _
        simp only [leadterm_hδ]
        conv in _ * x.1 => rw [mul_comm]
        conv in _ * y.1 => rw [mul_comm]
        have x_ne_0 := g_ne_0_in_filG_eq x.1 x.2
        have y_ne_0 := g_ne_0_in_filG_eq y.1 y.2
        have hδx_ne_0 := hδg_ne_0_in_filG_eq x.1 x.2
        have hδy_ne_0 := hδg_ne_0_in_filG_eq y.1 y.2
        have key :=
          mul_term_spoly mo x.1 y.1 x_ne_0 y_ne_0
            (leading_monomial' mo (hδ' x.1) hδx_ne_0)
            (leading_monomial' mo (hδ' y.1) hδy_ne_0)
            ((hδ' x.1).coeff (leading_monomial' mo (hδ' x.1) hδx_ne_0))
            ((hδ' y.1).coeff (leading_monomial' mo (hδ' y.1) hδy_ne_0))
            (lc_not_zero mo (hδ' x.1) hδx_ne_0)
            (lc_not_zero mo (hδ' y.1) hδy_ne_0)
        simp only at key
        rw [key]
        rw [mem_filG_eq_lm_decomp x.1 x.2, mem_filG_eq_lm_decomp y.1 y.2]
        rw [self_lcm_monomial_eq_self δ]
        rw [← smul_mul_assoc, MvPolynomial.smul_monomial (C_spoly x y)]
        simp only [smul_eq_mul, mul_one]
      rw [filG_eq_prod_sum_eq_2] at hδG_repn_f
      simp only at GS_red_0'
      have GS_red_0 (g1) (hg1 : g1 ∈ G) (g2) (hg2 : g2 ∈ G) :
        let g1_ne_0 := ne_of_mem_of_not_mem hg1 hG
        let g2_ne_0 := ne_of_mem_of_not_mem hg2 hG
        let s12 := S_poly mo g1 g2 g1_ne_0 g2_ne_0
        ∃ A : MvPolynomial σ K → MvPolynomial σ K,
          s12 = ∑ g ∈ G, A g * g ∧
          ∀ g ∈ G,
            WithBot.map mo.toSyn (leading_monomial mo (A g * g)) ≤
            WithBot.map mo.toSyn (leading_monomial mo s12) := by
        intro g1_ne_0 g2_ne_0 s12
        cases em (s12 = 0) with
        | inl s12_eq_0 =>
          exists 0
          simp [s12_eq_0, lm_zero_eq_bot]
        | inr s12_ne_0 =>
          push_neg at s12_ne_0
          subst s12
          have key := GS_red_0' g1 hg1 g2 hg2 s12_ne_0
          rcases key with ⟨A, A_S_repn, A_S_repn_std⟩
          exists A, A_S_repn
          intro g g_mem_G
          cases em (A g * g = 0) with
          | inl Agg_eq_0 =>
            simp [Agg_eq_0, lm_zero_eq_bot]
          | inr Agg_ne_0 =>
            push_neg at Agg_ne_0
            simp only [
              lm_coe_lm' mo (A g * g) Agg_ne_0, WithBot.map_coe,
              lm_coe_lm' mo (S_poly mo g1 g2 g1_ne_0 g2_ne_0) s12_ne_0, WithBot.coe_le_coe]
            exact A_S_repn_std g g_mem_G Agg_ne_0
      simp only at GS_red_0
      let GSA (g1) (hg1 : g1 ∈ G) (g2) (hg2 : g2 ∈ G) := (GS_red_0 g1 hg1 g2 hg2).choose
      have GSA_spec (g1) (hg1 : g1 ∈ G) (g2) (hg2 : g2 ∈ G) :
        let g1_ne_0 := ne_of_mem_of_not_mem hg1 hG
        let g2_ne_0 := ne_of_mem_of_not_mem hg2 hG
        let s12 := S_poly mo g1 g2 g1_ne_0 g2_ne_0
        s12 = ∑ g ∈ G, (GSA g1 hg1 g2 hg2) g * g ∧
        ∀ g ∈ G,
          WithBot.map (⇑mo.toSyn) (leading_monomial mo ((GSA g1 hg1 g2 hg2) g * g)) ≤
            WithBot.map (⇑mo.toSyn) (leading_monomial mo s12) := by
        simp only [GSA]
        exact (GS_red_0 g1 hg1 g2 hg2).choose_spec
      have filG_eq_prod_sum_eq_3 :
        ∑ x ∈ filG_eq.attach ×ˢ filG_eq.attach,
          MvPolynomial.monomial
            (δ -
              lcm_monomial
                (leading_monomial' mo x.1.1 (g_ne_0_in_filG_eq x.1.1 x.1.2))
                (leading_monomial' mo x.2.1 (g_ne_0_in_filG_eq x.2.1 x.2.2)))
            (C_spoly x.1 x.2) *
          (S_poly mo x.1.1 x.2.1
            (g_ne_0_in_filG_eq x.1.1 x.1.2) (g_ne_0_in_filG_eq x.2.1 x.2.2)) =
        ∑ g ∈ G,
          (∑ x ∈ filG_eq.attach ×ˢ filG_eq.attach,
            MvPolynomial.monomial
              (δ -
                lcm_monomial
                  (leading_monomial' mo x.1.1 (g_ne_0_in_filG_eq x.1.1 x.1.2))
                  (leading_monomial' mo x.2.1 (g_ne_0_in_filG_eq x.2.1 x.2.2)))
              (C_spoly x.1 x.2) *
            GSA x.1.1 (filG_eq_subs_G x.1.2) x.2.1 (filG_eq_subs_G x.2.2) g) * g := by
        calc
          _ =
            ∑ x ∈ filG_eq.attach ×ˢ filG_eq.attach,
              MvPolynomial.monomial
                (δ -
                  lcm_monomial
                    (leading_monomial' mo x.1.1 (g_ne_0_in_filG_eq x.1.1 x.1.2))
                    (leading_monomial' mo x.2.1 (g_ne_0_in_filG_eq x.2.1 x.2.2)))
                (C_spoly x.1 x.2) *
              ∑ g ∈ G, GSA x.1.1 (filG_eq_subs_G x.1.2) x.2.1 (filG_eq_subs_G x.2.2) g * g := by
            apply Finset.sum_congr rfl
            intro ⟨x, y⟩ _
            simp only
            simp only at GSA_spec
            rw [(GSA_spec x.1 (filG_eq_subs_G x.2) y.1 (filG_eq_subs_G y.2)).1]
          _ =
            ∑ x ∈ filG_eq.attach ×ˢ filG_eq.attach, ∑ g ∈ G,
              MvPolynomial.monomial
                (δ -
                  lcm_monomial
                    (leading_monomial' mo x.1.1 (g_ne_0_in_filG_eq x.1.1 x.1.2))
                    (leading_monomial' mo x.2.1 (g_ne_0_in_filG_eq x.2.1 x.2.2)))
                (C_spoly x.1 x.2) *
              GSA x.1.1 (filG_eq_subs_G x.1.2) x.2.1 (filG_eq_subs_G x.2.2) g * g := by
            apply Finset.sum_congr rfl
            intro ⟨x, y⟩ _
            simp only
            rw [Finset.mul_sum G]
            apply Finset.sum_congr rfl
            simp [mul_assoc]
          _ =
            ∑ g ∈ G,
              (∑ x ∈ filG_eq.attach ×ˢ filG_eq.attach,
                MvPolynomial.monomial
                  (δ -
                    lcm_monomial
                      (leading_monomial' mo x.1.1 (g_ne_0_in_filG_eq x.1.1 x.1.2))
                      (leading_monomial' mo x.2.1 (g_ne_0_in_filG_eq x.2.1 x.2.2)))
                  (C_spoly x.1 x.2) *
                GSA x.1.1 (filG_eq_subs_G x.1.2) x.2.1 (filG_eq_subs_G x.2.2) g) * g := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro g g_mem_G
            rw [Finset.sum_mul (filG_eq.attach ×ˢ filG_eq.attach)]
      rw [filG_eq_prod_sum_eq_3] at hδG_repn_f
      let B (g : MvPolynomial σ K) : MvPolynomial σ K :=
        if hfG : g ∈ G
          then
            ∑ x ∈ filG_eq.attach ×ˢ filG_eq.attach,
              MvPolynomial.monomial
                (δ -
                  lcm_monomial
                    (leading_monomial' mo x.1.1 (g_ne_0_in_filG_eq x.1.1 x.1.2))
                    (leading_monomial' mo x.2.1 (g_ne_0_in_filG_eq x.2.1 x.2.2)))
                (C_spoly x.1 x.2) *
              GSA x.1.1 (filG_eq_subs_G x.1.2) x.2.1 (filG_eq_subs_G x.2.2) g +
            if hfG_eq : g ∈ filG_eq
              then hδ' g - leadterm_hδ g hfG_eq
              else hδ' g
          else 0
      absurd hδ_argmin
      push_neg
      exists B
      constructor
      · simp only [Function.support_subset_iff, Finset.mem_coe, Set.mem_setOf_eq, fG_repns]
        constructor
        · intro f
          rw [← not_imp_not]
          simp only [dite_eq_ite, ne_eq, ite_eq_right_iff, Classical.not_imp, not_and,
            Decidable.not_not, B]
          intro f_notin_G f_in_G
          by_contra _
          exact f_notin_G f_in_G
        · simp only [dite_eq_ite, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.inter_self, B]
          calc
            _ =
              ∑ g ∈ G,
                ((∑ x ∈ filG_eq.attach ×ˢ filG_eq.attach,
                  MvPolynomial.monomial
                    (δ -
                      lcm_monomial
                        (leading_monomial' mo x.1.1 (g_ne_0_in_filG_eq x.1.1 x.1.2))
                        (leading_monomial' mo x.2.1 (g_ne_0_in_filG_eq x.2.1 x.2.2)))
                    (C_spoly x.1 x.2) *
                  GSA x.1.1 (filG_eq_subs_G x.1.2) x.2.1 (filG_eq_subs_G x.2.2) g) * g +
                (if hfG_eq : g ∈ filG_eq
                  then hδ' g - leadterm_hδ g hfG_eq
                  else hδ' g) * g) := by
              apply Finset.sum_congr rfl
              intro g g_mem_G
              apply right_distrib
            _ =
              ∑ g ∈ G,
                (∑ x ∈ filG_eq.attach ×ˢ filG_eq.attach,
                  MvPolynomial.monomial
                    (δ -
                      lcm_monomial
                        (leading_monomial' mo x.1.1 (g_ne_0_in_filG_eq x.1.1 x.1.2))
                        (leading_monomial' mo x.2.1 (g_ne_0_in_filG_eq x.2.1 x.2.2)))
                    (C_spoly x.1 x.2) *
                GSA x.1.1 (filG_eq_subs_G x.1.2) x.2.1 (filG_eq_subs_G x.2.2) g) * g +
              ∑ g ∈ G,
                (if hfG_eq : g ∈ filG_eq
                  then hδ' g - leadterm_hδ g hfG_eq
                  else hδ' g) * g := by
              rw [Finset.sum_add_distrib, add_right_cancel_iff]
            _ = f := by
              rw [← hδG_repn_f, add_assoc, add_left_cancel_iff]
              simp only [dite_mul, Finset.sum_dite]
              have filG_eq_type (x : { x // x ∈ {x ∈ G | x ∈ filG_eq} }) : x.1 ∈ filG_eq := by
                have x_prop := x.2
                simp only [Finset.mem_filter] at x_prop
                exact x_prop.2
              have sum_1 :
                ∑ x : { x // x ∈ {x ∈ G | x ∈ filG_eq} },
                  (hδ' x.1 - leadterm_hδ x.1 (filG_eq_type x)) * x.1 =
                ∑ g ∈ filG_eq.attach, (hδ' g.1 - leadterm_hδ g.1 g.2) * g.1 := by
                rw [Finset.sum_coe_sort_eq_attach]
                let e_filG_eq (x : { x // x ∈ {x ∈ G | x ∈ filG_eq} }) : { x // x ∈ filG_eq } :=
                  ⟨x.1, filG_eq_type x⟩
                let e_filG_eq_inv (x : { x // x ∈ filG_eq }) : { x // x ∈ {x ∈ G | x ∈ filG_eq} } :=
                  ⟨x.1, by
                    simp only [Finset.mem_filter, Finset.coe_mem, and_true]
                    exact filG_eq_subs_G x.2⟩
                have e_filG_eq_bij : e_filG_eq.Bijective := by
                  rw [Function.bijective_iff_has_inverse]
                  exists e_filG_eq_inv
                  simp [Function.LeftInverse, Function.RightInverse, e_filG_eq, e_filG_eq_inv]
                apply Finset.sum_bijective e_filG_eq e_filG_eq_bij
                · simp [e_filG_eq]
                · simp [e_filG_eq]
              have filG_lt_type (x : { x // x ∈ {x ∈ G | x ∉ filG_eq} }) : x.1 ∈ filG_lt := by
                simp only [Finset.mem_sdiff, filG_lt]
                have x_prop := x.2
                simp only [Finset.mem_filter] at x_prop
                exact x_prop
              have filG_lt_type_inv (x : { x // x ∈ filG_lt }) : x.1 ∈ {x ∈ G | x ∉ filG_eq} := by
                simp [Finset.mem_filter, ← Finset.mem_sdiff]
              have sum_2 :
                ∑ x : { x // x ∈ {x ∈ G | x ∉ filG_eq} },
                  hδ' ↑x * ↑x = ∑ x ∈ filG_lt, hδ' x * x := by
                conv_lhs => rw [Finset.sum_coe_sort {x ∈ G | x ∉ filG_eq} (fun x => hδ' x * x)]
                apply Finset.sum_congr
                · ext x
                  simp only [Finset.mem_filter, Finset.mem_sdiff, filG_lt]
                · intro _ _
                  rfl
              rw [sum_1, sum_2]
      · simp only [dite_eq_ite, ite_mul, zero_mul, ← wbδ_eq_coe_δ, Finset.max'_lt_iff,
          Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
          fG_repn_max_lm, B]
        intro g g_mem_G
        split
        next _ =>
          rw [right_distrib, ← AddEquiv.apply_symm_apply mo.toSyn δ']
          apply lm_add_lt_of_both_lm_lt_mon mo
          · rw [Finset.sum_mul]
            apply lm_sum_lt_of_all_lm_lt
            intro ⟨g1, g2⟩ _
            simp only [AddEquiv.apply_symm_apply]
            let summand :=
              MvPolynomial.monomial
                (δ -
                  lcm_monomial
                    (leading_monomial' mo g1.1 (ne_of_mem_of_not_mem (filG_eq_subs_G g1.2) hG))
                    (leading_monomial' mo g2.1 (ne_of_mem_of_not_mem (filG_eq_subs_G g2.2) hG)))
                (C_spoly g1 g2) *
              GSA g1.1 (filG_eq_subs_G g1.2) g2.1 (filG_eq_subs_G g2.2) g *
              g
            cases em (summand = 0) with
            | inl summand_eq_0 =>
              unfold summand at summand_eq_0
              simp [summand_eq_0, lm_zero_eq_bot]
            | inr summand_ne_0 =>
              unfold summand at summand_ne_0
              push_neg at summand_ne_0
              conv in _ * _ * g => rw [mul_assoc]
              conv at summand_ne_0 in _ * _ * g => rw [mul_assoc]
              simp only [lm_coe_lm' mo _ summand_ne_0, WithBot.map_coe, WithBot.coe_lt_coe,
                gt_iff_lt]
              rw [mul_ne_zero_iff] at summand_ne_0
              rw [← lm'_mul_commute mo _ _ summand_ne_0.1 summand_ne_0.2]
              rw [lm'_mon mo _ (C_spoly g1 g2) (by simp at summand_ne_0; exact summand_ne_0.1)]
              rw [
                ← add_lt_add_iff_right
                  (mo.toSyn
                    (lcm_monomial
                      (leading_monomial' mo g1.1 (ne_of_mem_of_not_mem (filG_eq_subs_G g1.2) hG))
                      (leading_monomial' mo g2.1 (ne_of_mem_of_not_mem (filG_eq_subs_G g2.2) hG)))),
                ← AddEquiv.map_add,
                add_assoc
              ]
              conv in leading_monomial' _ _ _ + lcm_monomial _ _ => rw [add_comm]
              rw [← add_assoc]
              have lcm_le_δ :
                lcm_monomial
                  (leading_monomial' mo g1.1 (ne_of_mem_of_not_mem (filG_eq_subs_G g1.2) hG))
                  (leading_monomial' mo g2.1 (ne_of_mem_of_not_mem (filG_eq_subs_G g2.2) hG)) ≤
                δ := by
                intro x
                simp only [lcm_monomial, Finsupp.coe_mk, sup_le_iff]
                constructor
                · rw [← mem_filG_eq_lm_decomp g1.1 g1.2]
                  simp
                · rw [← mem_filG_eq_lm_decomp g2.1 g2.2]
                  simp
              rw [monomial_sub_add _ _ lcm_le_δ]
              simp only [AddEquiv.map_add, AddEquiv.apply_symm_apply, add_lt_add_iff_left,
                gt_iff_lt, δ]
              rw [← WithBot.coe_lt_coe, ← WithBot.map_coe, ← WithBot.map_coe]
              calc
                _
                ≤ WithBot.map mo.toSyn
                  (leading_monomial mo
                    (S_poly mo g1.1 g2.1
                      (ne_of_mem_of_not_mem (filG_eq_subs_G g1.2) hG)
                      (ne_of_mem_of_not_mem (filG_eq_subs_G g2.2) hG))) := by
                  rw [← lm_coe_lm' mo]
                  exact (GSA_spec g1.1 (filG_eq_subs_G g1.2) g2.1 (filG_eq_subs_G g2.2)).2 g g_mem_G
                _ < _ := by
                  exact lm_spoly_lt_lcm mo g1.1 g2.1 _ _
          · simp only [AddEquiv.apply_symm_apply]
            split
            next g_mem_filG_eq =>
              exact filG_eq_sublm_lm_lt_δ ⟨g, g_mem_filG_eq⟩ (by simp only [Finset.mem_attach])
            next g_notMem_filG_eq =>
              have g_mem_filG_lt : g ∈ filG_lt := by
                simp only [filG_lt, Finset.mem_sdiff]
                exact ⟨g_mem_G, g_notMem_filG_eq⟩
              exact mem_filG_lt g g_mem_filG_lt
        next g_not_mem_G =>
          by_contra _
          exact g_not_mem_G g_mem_G
    | inr lmf_eq_δ =>
      subst δ'
      unfold fG_repn_max_lm at wbδ_eq_coe_δ
      have key :=
        Finset.max'_mem
          (G.image (fun g => WithBot.map mo.toSyn (leading_monomial mo (hδ' g * g))))
          (by simp only [Finset.image_nonempty, G_nonempty])
      rw [← wbδ_eq_coe_δ, Finset.mem_image] at key
      rcases key with ⟨g, g_mem_G, lmhδgg_eq_lmf⟩
      have g_ne_0 : g ≠ 0 := ne_of_mem_of_not_mem g_mem_G hG
      have hδgg_ne_0 : hδ' g * g ≠ 0 := by
        by_contra hδgg_eq_0
        rw [hδgg_eq_0, lm_zero_eq_bot, WithBot.map_bot] at lmhδgg_eq_lmf
        exact WithBot.coe_ne_bot.symm lmhδgg_eq_lmf
      have hδg_ne_0 : hδ' g ≠ 0 := by
        simp only [ne_eq, mul_eq_zero, not_or] at hδgg_ne_0
        exact hδgg_ne_0.1
      simp only [lm_coe_lm' mo (hδ' g * g) hδgg_ne_0, WithBot.map_coe, WithBot.coe_inj,
        EmbeddingLike.apply_eq_iff_eq] at lmhδgg_eq_lmf
      unfold ltf
      rw [term_mem_moni_iff lmf _ lcf (lc_not_zero mo f f_ne_0)]
      exists leading_monomial' mo g g_ne_0
      constructor
      · simp only [leading_monomials_fin, Finset.coe_biUnion, Finset.mem_coe, Set.mem_iUnion,
          Option.mem_toFinset, Option.mem_def, exists_prop]
        exists g, g_mem_G
        rw [lm_coe_lm' mo g g_ne_0, WithBot.some_eq_coe]
      · unfold lmf
        rw [← lmhδgg_eq_lmf, ← lm'_mul_commute mo (hδ' g) g hδg_ne_0 g_ne_0]
        simp only [le_add_iff_nonneg_left, zero_le]

/-- Buchberger criterion: `G` is a Groebner basis (of its ideal span)
iff every S-polynomial of two distinct polynomials in `G` divides to
remainder zero by `G` itself. -/
theorem buchberger {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G) :
    is_groebner mo G (Ideal.span G) ↔ every_S_poly_remainder_0 mo G hG := by
  constructor
  · exact buchberger_tfae_1 mo G hG
  · exact buchberger_tfae_3 mo G hG ∘ buchberger_tfae_2 mo G hG

/-- Refined Buchberger criterion: `G` is a Groebner basis (of its ideal span)
iff every S-polynomial of two distinct polynomials in `G` reduces to zero over
`G` itself. -/
theorem refined_buchberger {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G) :
    is_groebner mo G (Ideal.span G) ↔ every_S_poly_red_0 mo G hG := by
  constructor
  · exact buchberger_tfae_2 mo G hG ∘ buchberger_tfae_1 mo G hG
  · exact buchberger_tfae_3 mo G hG
