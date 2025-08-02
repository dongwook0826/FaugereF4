import Mathlib
import FaugereF4.MonomialIdeal
import FaugereF4.GaussianElim
import FaugereF4.DivisionAlgorithm

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
  (I J : Ideal (MvPolynomial σ K)) (hIJ : I = J)
  : is_groebner mo G I ↔ is_groebner mo G J := by
  unfold is_groebner
  rw [hIJ]

theorem mem_ideal_iff_gb_remainder_zero {σ K : Type*}
  [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f : MvPolynomial σ K)
  (G : Finset (MvPolynomial σ K)) (I : Ideal (MvPolynomial σ K))
  (zero_not_mem_G : 0 ∉ G) (G_gb_I : is_groebner mo G I)
  : f ∈ I ↔ remainder_zero mo f G zero_not_mem_G := by
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
      let mpds_on (LG : List (MvPolynomial σ K)) (G_eq_LG : G = LG.toFinset) (LG_Nodup : LG.Nodup)
        := mvpoly_division mo f LG (by rw [← List.mem_toFinset, ← G_eq_LG]; exact zero_not_mem_G) LG_Nodup
      have mpds_on_p_eq_0 (LG : List (MvPolynomial σ K)) (G_eq_LG : G = LG.toFinset) (LG_Nodup : LG.Nodup)
        : (mpds_on LG G_eq_LG LG_Nodup).p = 0 := mvpoly_division_p_eq_0 mo f LG _ _
      have mpds_on_repn (LG : List (MvPolynomial σ K)) (G_eq_LG : G = LG.toFinset) (LG_Nodup : LG.Nodup)
        := (mpds_on LG G_eq_LG LG_Nodup).f_eq_FQ_r
      simp [mpds_on_p_eq_0] at mpds_on_repn
      have mpds_on_r_mem_I (LG : List (MvPolynomial σ K)) (G_eq_LG : G = LG.toFinset) (LG_Nodup : LG.Nodup)
        : (mpds_on LG G_eq_LG LG_Nodup).r ∈ I := by
        have mpds_repn := mpds_on_repn LG G_eq_LG LG_Nodup
        rw [add_comm] at mpds_repn
        apply sub_eq_of_eq_add at mpds_repn
        rw [← mpds_repn]
        apply Ideal.sub_mem
        · exact f_mem_I
        · apply spanG_le_I
          apply Ideal.sum_mem
          intro ⟨i, hi⟩
          simp
          have LGi_mem_G : {LG[i]} ⊆ G.toSet := by simp [G_eq_LG]
          apply Ideal.span_mono LGi_mem_G
          simp [Ideal.mem_span_singleton]
      have mpds_on_lmr_mem_I (LG : List (MvPolynomial σ K)) (G_eq_LG : G = LG.toFinset) (LG_Nodup : LG.Nodup)
        : let mpds := mpds_on LG G_eq_LG LG_Nodup
          ∃ μ ∈ (leading_monomials_fin mo G).toSet,
            μ ≤ leading_monomial' mo mpds.r (mpds_on_r_ne_0 LG G_eq_LG LG_Nodup) := by
        intro mpds
        rw [← @mon_mem_moni_iff σ K, ← initII_eq_initIG]
        unfold monomial_ideal
        apply Ideal.subset_span
        simp [leading_monomials]
        exists mpds.r, mpds_on_r_mem_I LG G_eq_LG LG_Nodup
        rw [lm_coe_lm' mo mpds.r (mpds_on_r_ne_0 LG G_eq_LG LG_Nodup), WithBot.some_eq_coe]
      have mpds_on_r_not_divisible (LG : List (MvPolynomial σ K)) (G_eq_LG : G = LG.toFinset) (LG_Nodup : LG.Nodup)
        := (mpds_on LG G_eq_LG LG_Nodup).r_not_divisible
      let LG := G.toList
      have G_eq_LG : G = LG.toFinset := by simp [LG]
      have LG_Nodup : LG.Nodup := Finset.nodup_toList G
      -- let mpds := mpds_on LG G_eq_LG
      have key1 := mpds_on_lmr_mem_I LG G_eq_LG LG_Nodup
      have key2 := mpds_on_r_not_divisible LG G_eq_LG LG_Nodup
      rcases key1 with ⟨ν, ν_mem_lmI, ν_div_lmr⟩
      simp [leading_monomials_fin] at ν_mem_lmI
      rcases ν_mem_lmI with ⟨g, g_mem_G, lmg_eq_ν⟩
      rw [
        lm_coe_lm' mo g (ne_of_mem_of_not_mem g_mem_G zero_not_mem_G),
        WithBot.some_eq_coe, WithBot.coe_eq_coe
      ] at lmg_eq_ν
      subst ν
      have key2' :=
        key2
          g (by simp [LG, g_mem_G])
          (leading_monomial' mo (mpds_on LG G_eq_LG LG_Nodup).r (mpds_on_r_ne_0 LG G_eq_LG LG_Nodup))
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
    simp at fG_repn
    apply spanG_le_I
    rw [fG_repn]
    apply Ideal.sum_mem
    intro ⟨i, hi⟩
    simp
    have LGi_mem_G : {LG[i]} ⊆ G.toSet := by simp [G_eq_LG]
    apply Ideal.span_mono LGi_mem_G
    simp [Ideal.mem_span_singleton]

/-- Definition of S-pair of two nonzero polynomials. -/
noncomputable def S_pair {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0)
  : MvPolynomial σ K × MvPolynomial σ K :=
  let lmf := leading_monomial' mo f hf
  let lcf := f.coeff lmf
  let lmg := leading_monomial' mo g hg
  let lcg := g.coeff lmg
  let lcm_fg := lcm_monomial lmf lmg
  ⟨f * MvPolynomial.monomial (lcm_fg - lmf) lcf⁻¹, g * MvPolynomial.monomial (lcm_fg - lmg) lcg⁻¹⟩

/-- Definition of the S-polynomial of two nonzero polynomials. -/
noncomputable def S_poly {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :=
  let ⟨p1, p2⟩ := S_pair mo f g hf hg
  p1 - p2

/-- A rewrite lemma on `S-poly` for equal pairs of polynomials. -/
lemma eq_S_poly_of_eq_eq {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f1 f2 g1 g2 : MvPolynomial σ K)
  (f_eq : f1 = f2) (g_eq : g1 = g2)
  (f_ne_0 : f1 ≠ 0 ∨ f2 ≠ 0) (g_ne_0 : g1 ≠ 0 ∨ g2 ≠ 0)
  : have f1_ne_0 : f1 ≠ 0 := by subst f2; simp at f_ne_0; exact f_ne_0
    have f2_ne_0 : f2 ≠ 0 := by subst f1; exact f1_ne_0
    have g1_ne_0 : g1 ≠ 0 := by subst g2; simp at g_ne_0; exact g_ne_0
    have g2_ne_0 : g2 ≠ 0 := by subst g1; exact g1_ne_0
    S_poly mo f1 g1 f1_ne_0 g1_ne_0 = S_poly mo f2 g2 f2_ne_0 g2_ne_0 := by
  unfold S_poly S_pair
  subst f2 g2
  simp

/-- Swapping the two polynomial inputs in `S-poly` is equivalent to negating. -/
lemma S_poly_neg_of_swap {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0)
  : S_poly mo g f hg hf = -S_poly mo f g hf hg := by
  unfold S_poly S_pair
  simp [lcm_monomial_comm]

/-- A polynomial `f` reduces to zero (or has a standard representation) over
a finite polynomial set `G` (under a fixed monomial order `mo`), if `f` is a
polynomial combination over `G` where the leading monomial of each summand doesn't
exceed that of `f` under `mo`. -/
def reduces_to_zero {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f : MvPolynomial σ K) (f_ne_0 : f ≠ 0) (G : Finset (MvPolynomial σ K)) :=
  ∃ (A : MvPolynomial σ K → MvPolynomial σ K),
    (f = ∑ g ∈ G, (A g) * g) ∧
    ∀ g ∈ G, (hgA : (A g) * g ≠ 0) →
      mo.toSyn (leading_monomial' mo ((A g) * g) hgA) ≤ mo.toSyn (leading_monomial' mo f f_ne_0)

/-- `f` reduces to zero over `G`, iff its negation reduces to zero. -/
lemma red_0_iff_neg_red_0 {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f : MvPolynomial σ K) (f_ne_0 : f ≠ 0) (G : Finset (MvPolynomial σ K))
  : have neg_f_ne_0 : -f ≠ 0 := neg_ne_zero.mpr f_ne_0
    reduces_to_zero mo f f_ne_0 G ↔ reduces_to_zero mo (-f) neg_f_ne_0 G := by
  intro neg_f_ne_0
  unfold reduces_to_zero
  constructor
  · intro ⟨A, f_sum_A, summand_lm_le_lmf⟩
    exists -A
    simp_all only [not_or, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, true_and]
    intro g g_mem_G Agg_ne_0
    rw [neg_ne_zero] at Agg_ne_0
    rw [← lm'_neg_eq_lm' mo (A g * g) Agg_ne_0]
    rw [← lm'_neg_eq_lm' mo (∑ g ∈ G, A g * g) (by rw [f_sum_A] at f_ne_0; exact f_ne_0)]
    exact summand_lm_le_lmf g g_mem_G Agg_ne_0
  · intro ⟨A, f_sum_A, summand_lm_le_lmf⟩
    exists -A
    simp_all only [not_or, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, true_and]
    rw [neg_eq_iff_eq_neg] at f_sum_A
    constructor
    · exact f_sum_A
    · intro g g_mem_G Agg_ne_0
      rw [neg_ne_zero] at Agg_ne_0
      rw [← lm'_neg_eq_lm' mo (A g * g) Agg_ne_0]
      rw [lm'_eq_of_eq mo f _ f_sum_A f_ne_0]
      rw [← lm'_neg_eq_lm' mo (∑ g ∈ G, A g * g) (by rw [f_sum_A, neg_ne_zero] at f_ne_0; exact f_ne_0)]
      exact summand_lm_le_lmf g g_mem_G Agg_ne_0

/-- A rewrite lemma on `reduces_to_zero` for equal polynomials. -/
lemma red_0_of_eq {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ K) (f_eq_g : f = g) (f_ne_0 : f ≠ 0)
  (G : Finset (MvPolynomial σ K))
  : have g_ne_0 : g ≠ 0 := by rw [← f_eq_g]; exact f_ne_0
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
  (G G' : Finset (MvPolynomial σ K))
  : reduces_to_zero mo f f_ne_0 G → reduces_to_zero mo f f_ne_0 (G ∪ G') := by
  unfold reduces_to_zero
  intro ⟨A, f_sum_A, lm_term_le_lmf⟩
  exists λ g => if g ∈ G then A g else 0
  simp
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
  (lm_g_mul_gt_lmf : mo.toSyn (leading_monomial' mo ((MvPolynomial.monomial α c) * g) (by simp_all)) > mo.toSyn (leading_monomial' mo f f_ne_0))
  : let lmgmul := leading_monomial' mo ((MvPolynomial.monomial α c) * g) (by simp_all)
    have f_add_g_mul_ne_0 : f + (MvPolynomial.monomial α c) * g ≠ 0 := by
      rw [MvPolynomial.ne_zero_iff]
      exists lmgmul
      simp
      have : f.coeff lmgmul = 0 := by
        apply coeff_zero_of_lt_lm
        simp [lm_coe_lm' mo f f_ne_0]
        exact lm_g_mul_gt_lmf
      simp [this]
      exact lc_not_zero mo _ _
    reduces_to_zero mo (f + (MvPolynomial.monomial α c) * g) f_add_g_mul_ne_0 G := by
  intro lmgmul f_add_g_mul_ne_0
  unfold reduces_to_zero
  unfold reduces_to_zero at f_red_0_G
  rcases f_red_0_G with ⟨A, f_sum_A_G, summand_lm_le_lmf⟩
  let A' := A + λ x => if x = g then (MvPolynomial.monomial α) c else 0
  exists A'
  constructor
  · simp [A', right_distrib, Finset.sum_add_distrib]
    conv_rhs => rw [← f_sum_A_G]
    simp_all
  · intro g' g'_mem_G hg'A
    simp [A'] at hg'A
    rcases hg'A with ⟨Ag'_ne_0, g'_ne_0⟩
    have lmfadd_eq_lmgmul : leading_monomial' mo (f + (MvPolynomial.monomial α) c * g) f_add_g_mul_ne_0 = lmgmul := by
      unfold lmgmul
      conv_rhs => rw [← lm_sub_smul_eq_lm mo f ((MvPolynomial.monomial α) c * g) _ _ lm_g_mul_gt_lmf (-1)]
      simp
      exact lm'_eq_of_eq mo _ _ (add_comm f ((MvPolynomial.monomial α) c * g)) f_add_g_mul_ne_0
    rw [lmfadd_eq_lmgmul]
    simp [A']
    cases em (g' = g) with
    | inl g'_eq_g =>
      subst g'
      simp
      cases em (A g = 0) with
      | inl Ag_eq_0 =>
        simp [Ag_eq_0, lmgmul]
      | inr Ag_ne_0 =>
        apply le_of_eq
        rw [AddEquiv.apply_eq_iff_eq]
        have Agg_ne_0 : A g * g ≠ 0 := by simp [g'_ne_0, Ag_ne_0]
        rw [lm'_eq_of_eq mo ((A g + (MvPolynomial.monomial α) c) * g) ((MvPolynomial.monomial α) c * g + A g * g) (by ring) _]
        have lmAgg_le_lmf := summand_lm_le_lmf g g'_mem_G Agg_ne_0
        have lmAgg_lt_lmgmul := lt_of_le_of_lt lmAgg_le_lmf lm_g_mul_gt_lmf
        have key := lm_sub_smul_eq_lm mo (A g * g) ((MvPolynomial.monomial α) c * g) Agg_ne_0 _ lmAgg_lt_lmgmul (-1)
        simp at key
        exact key
    | inr g'_ne_g =>
      subst A'
      simp [g'_ne_g]
      simp only [Pi.add_apply, g'_ne_g, ↓reduceIte, add_zero] at hg'A
      calc
        mo.toSyn (leading_monomial' mo (A g' * g') hg'A) ≤ mo.toSyn (leading_monomial' mo f f_ne_0) := by
          exact summand_lm_le_lmf g' g'_mem_G hg'A
        _ ≤ mo.toSyn lmgmul := by
          exact le_of_lt lm_g_mul_gt_lmf

lemma red_0_of_remainder_0 {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f : MvPolynomial σ K)
  (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G)
  : remainder_zero mo f G hG → (f_ne_0 : f ≠ 0) → reduces_to_zero mo f f_ne_0 G := by
  intro fG_r_0 f_ne_0
  unfold remainder_zero at fG_r_0
  rcases fG_r_0 with ⟨LG, G_eq_LG, LG_Nodup, mpds_fG_r_0⟩
  have hLG : 0 ∉ LG := by
    rw [← List.mem_toFinset, ← G_eq_LG]
    exact hG
  have mpds_fGr_repn := mvpoly_division_repn mo f LG hLG LG_Nodup
  simp [mpds_fG_r_0] at mpds_fGr_repn
  let mpds_fG := mvpoly_division mo f LG hLG LG_Nodup
  unfold reduces_to_zero
  let A : MvPolynomial σ K → MvPolynomial σ K :=
    λ p =>
      match LGpi : LG.finIdxOf? p with
      | none => 0
      | some i => mpds_fG.Q[i]'(by rw [← mpds_fG.FQ_len_eq]; exact i.isLt)
  exists A
  have summand_eq (i : Fin LG.length)
    : LG[i] * mpds_fG.Q[i]'(by rw [← mpds_fG.FQ_len_eq]; exact i.isLt)
    = A LG[i] * LG[i] := by
    simp [mul_comm]
    apply Or.inl
    simp [A]
    split
    next eq_none =>
      simp at eq_none
    next i' eq_some =>
      simp at eq_some
      rcases eq_some with ⟨LGi'_eq_LGi, _⟩
      have i_eq_i' : i = i' := by
        ext
        exact (List.Nodup.getElem_inj_iff LG_Nodup).mp LGi'_eq_LGi.symm
      rw [i_eq_i']
  constructor
  · simp [mpds_fGr_repn]
    rw [G_eq_LG, List.sum_toFinset, ← Fin.sum_univ_fun_getElem]
    · unfold mpds_fG at summand_eq
      simp_all only [Fin.getElem_fin] -- how does this end with the goal?
    · exact LG_Nodup -- where did this come from?
  · intro g g_mem_G hgA
    have lm_summand_le := mpds_fG.lm_summand_le_lmf
    have g_eq_LGi : ∃ i : Fin LG.length, g = LG[i] := by
      simp [G_eq_LG, List.mem_iff_getElem] at g_mem_G
      rcases g_mem_G with ⟨i, hi, LGi_eq_g⟩
      exact ⟨⟨i, hi⟩, LGi_eq_g.symm⟩
    rcases g_eq_LGi with ⟨⟨i, hi⟩, g_eq_LGi⟩
    subst g
    rw [← summand_eq] at hgA
    have lm_summand_i_le := lm_summand_le ⟨i, hi⟩
    rw [lm_coe_lm' mo _ hgA, lm_coe_lm' mo f f_ne_0] at lm_summand_i_le
    simp at lm_summand_i_le
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
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G)
  : is_groebner mo G (Ideal.span G) → every_S_poly_remainder_0 mo G hG := by
  unfold every_S_poly_remainder_0
  intro G_groebner f1 f1_mem_G f2 f2_mem_G
  rw [← mem_ideal_iff_gb_remainder_zero mo _ G (Ideal.span G) hG G_groebner]
  simp [S_poly, S_pair]
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
  exists MvPolynomial.monomial (lcm_f12 - lmf1) lcf1⁻¹, -MvPolynomial.monomial (lcm_f12 - lmf2) lcf2⁻¹
  rw [mul_comm _ f1, mul_comm _ f2]
  simp [lcm_f12, lcf1, lcf2, lmf1, lmf2]
  ring

/-- Step 2 for refined Buchberger criterion: if every S-polynomial from `G`
divides to remainder zero by `G`, then every such S-polynomial has a standard
representation over `G`. -/
lemma buchberger_tfae_2 {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G)
  : every_S_poly_remainder_0 mo G hG → every_S_poly_red_0 mo G hG := by
  unfold every_S_poly_remainder_0 every_S_poly_red_0
  intro GS_rem_0 f1 f1_mem_G f2 f2_mem_G s12 s12_ne_0
  exact red_0_of_remainder_0 mo s12 G hG (GS_rem_0 f1 f1_mem_G f2 f2_mem_G) s12_ne_0

/-- Step 3 for refined Buchberger criterion: iff every S-polynomial from `G`
reduces to zero over `G`, then `G` is a Groebner basis (of its ideal span). -/
lemma buchberger_tfae_3 {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G)
  : every_S_poly_red_0 mo G hG → is_groebner mo G (Ideal.span G) := by
  sorry

/-- Refined Buchberger criterion: `G` is a Groebner basis (of its ideal span)
iff every S-polynomial of two distinct polynomials in `G` reduces to zero over
`G` itself. -/
theorem refined_buchberger {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G) :
  is_groebner mo G (Ideal.span G) ↔ every_S_poly_red_0 mo G hG := by
  constructor
  · exact buchberger_tfae_2 mo G hG ∘ buchberger_tfae_1 mo G hG
  · exact buchberger_tfae_3 mo G hG
