import Mathlib
-- import FaugereF4.MvPolyIdealBasic
import FaugereF4.MonomialIdeal

def is_groebner {σ K : Type*} [DecidableEq σ] [Field K] -- [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K))
  (I : Ideal (MvPolynomial σ K)) /-(hI : I ≠ 0)-/ : Prop :=
  ↑G ⊆ I.carrier ∧
  monomial_ideal (leading_monomials mo I.carrier) =
  @monomial_ideal σ K _ _ (leading_monomials_fin mo G)

noncomputable def S_pair {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0)
  : MvPolynomial σ K × MvPolynomial σ K :=
  let lmf := leading_monomial' mo f hf
  let lcf := f.coeff lmf
  let lmg := leading_monomial' mo g hg
  let lcg := g.coeff lmg
  let lcm_fg := lcm_monomial lmf lmg
  ⟨f * MvPolynomial.monomial (lcm_fg - lmf) lcf⁻¹, g * MvPolynomial.monomial (lcm_fg - lmg) lcg⁻¹⟩

noncomputable def S_poly {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :=
  let ⟨p1, p2⟩ := S_pair mo f g hf hg
  p1 - p2

def reduces_to_zero {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f : MvPolynomial σ K) (G : Finset (MvPolynomial σ K)) :=
  ∃ (A : MvPolynomial σ K → MvPolynomial σ K),
    (f = ∑ g ∈ G, (A g) * g) ∧ ∀ g ∈ G, (A g) * g ≠ 0 → leading_monomial mo ((A g) * g) ≤ leading_monomial mo f

/-
TODO:
  Multivariate division algorithm -- mathlib
  Definition of standard representation
  Proof of refined Buchberger's criterion, done by proving...
  TFAE:
    G is Groebner basis of I =>
    ∀ f ∈ I, the residue of f by division algorithm over G is 0 =>
    ∀ f ∈ I, f has a standard representation by G => !!!
    G is Groebner basis of I
Observation:
  Groebner property of a set doesn't necessarily depend on the generated ideal
-/
/-
theorem groebner_iff_S_poly_red_0 {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K)) :
  is_groebner mo G :=
-/
