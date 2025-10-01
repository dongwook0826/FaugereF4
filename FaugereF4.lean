/-
Copyright (c) 2025 Dongwook Cheon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Dongwook Cheon
-/
import FaugereF4.MonomialIdeal
import FaugereF4.DivisionAlgorithm
import FaugereF4.GaussianElim
import FaugereF4.GroebnerBasis
import FaugereF4.FaugereF4

recall is_groebner {σ K : Type*} [DecidableEq σ] [Field K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K))
  (I : Ideal (MvPolynomial σ K)) : Prop :=
  ↑G ⊆ I.carrier ∧
  monomial_ideal K (leading_monomials mo I.carrier) =
  monomial_ideal K (leading_monomials_fin mo G)

recall refined_buchberger {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (G : Finset (MvPolynomial σ K)) (hG : 0 ∉ G) :
    is_groebner mo G (Ideal.span G) ↔ every_S_poly_red_0 mo G hG

recall F4_groebner {σ K : Type*} [Finite σ] [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (F : Finset (MvPolynomial σ K)) (hF : 0 ∉ F) :
    let f4F := F4 mo F hF
    is_groebner mo f4F.G.toFinset (Ideal.span F)
