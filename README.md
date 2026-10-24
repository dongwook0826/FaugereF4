# Formalizing Faugère's F4 Algorithm in Lean 4

This repository contains the first complete formalization of Faugère's $F_4$ algorithm using the Lean 4 proof assistant and its mathematical library, `Mathlib`. The project verifies both the algorithmic correctness and the non-trivial termination of batch-processing S-polynomials via multivariate polynomial linear reduction (Gaussian elimination).

## Project Structure & Correspondence

* [`MonomialIdeal.lean`](./FaugereF4/MonomialIdeal.lean): Preliminaries on monomial ideals, leading monomials, leading coefficients, and their membership criteria.
* [`DivisionAlgorithm.lean`](./FaugereF4/DivisionAlgorithm.lean): Classical multivariate polynomial division by a list of polynomials under a chosen monomial order, complete with loop invariants.
* [`GaussianElim.lean`](./FaugereF4/GaussianElim.lean): Implementation and verification of the row-reduction state machine (`MvPolyGEState`) acting on finite sets of polynomials.
* [`GroebnerBasis.lean`](./FaugereF4/GroebnerBasis.lean): Formal definitions of Gröbner bases and the verification of the refined Buchberger criterion.
* [`FaugereF4.lean`](./FaugereF4/FaugereF4.lean): The main $F_4$ loop infrastructure, including symbolic preprocessing (`SymbProcStruct`) and the top-level termination and correctness proofs.

## Documentation

* [Lean blueprint](https://dongwook0826.github.io/FaugereF4/)

## License

This project is licensed under the terms of the Apache License 2.0.
