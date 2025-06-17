import Mathlib
import FaugereF4.MvPolyIdealBasic
import FaugereF4.MonomialIdeal

def is_groebner {σ K : Type*} [DecidableEq σ] [Field K] -- [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K))
  (I : Ideal (MvPolynomial σ K)) (hI : I ≠ 0) :=
  monomial_ideal (leading_monomials mo I) = monomial_ideal (leading_monomials_fin mo G)

/-
def S_poly {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :=
  let
  f * leading_coeff'
-/

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
-/
