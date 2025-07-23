import Mathlib
import FaugereF4.MonomialIdeal
import FaugereF4.GaussianElim

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

/-- Auxiliary definition for `refined_buchberger`. -/
def every_S_poly_red_0 {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G) :=
  ∀ f1, (hf1 : f1 ∈ G) → ∀ f2, (hf2 : f2 ∈ G) →
    let s12 := S_poly mo f1 f2 (ne_of_mem_of_not_mem hf1 hG) (ne_of_mem_of_not_mem hf2 hG)
    (hs12 : s12 ≠ 0) → reduces_to_zero mo s12 hs12 G

/-- Refined Buchberger criterion: `G` is a Groebner basis (of its ideal span)
iff every S-polynomial of two distinct polynomials in `G` reduces to zero over
`G` itself. -/
theorem refined_buchberger {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G) :
  is_groebner mo G (Ideal.span G) ↔ every_S_poly_red_0 mo G hG := by
  sorry
