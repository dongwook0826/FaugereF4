import Mathlib

/-- The leading monomial of polynomial `f`, under given monomial order `mo`. -/
def leading_monomial {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K]
  (mo : MonomialOrder σ) (f : MvPolynomial σ K) :=
  -- @Finset.max _ mo.lo (Finset.map mo.toSyn f.support)
  WithBot.map mo.toSyn.invFun (@Finset.max _ mo.lo (Finset.map mo.toSyn f.support))

/-- A variant of `leading_monomial`: given `f ≠ 0`, the `WithBot` can be peeled off. -/
def leading_monomial' {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K]
  (mo : MonomialOrder σ) (f : MvPolynomial σ K) (hf : f ≠ 0) :=
  mo.toSyn.invFun (
    @Finset.max' _ mo.lo
      (Finset.map mo.toSyn f.support)
      (by
        have : f.support.Nonempty := by simp_all
        simp_all
      )
    )

/-- The set of leading monomials of `f ∈ F`,
  under a given monomial order `mo`. -/
def leading_monomials {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K]
  (mo : MonomialOrder σ) (F : Finset (MvPolynomial σ K)) :=
  F.biUnion (λ f => (leading_monomial mo f).toFinset)

def monomial_ideal {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K]
  (s : Set (σ →₀ ℕ)) : Ideal (MvPolynomial σ K) :=
  Ideal.span ((fun s => MvPolynomial.monomial s (1 : K)) '' s)

/-
def leadterm_ideal' {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K]
  (mo : MonomialOrder σ) (S' : Set (MvPolynomial σ K)) (hS' : 0 ∉ S') :=
  have : ∀ f ∈ S', f ≠ 0 := by
    intro f hf hf0
    simp_all
  @monomial_ideal σ K _ _ _ { m : σ →₀ ℕ | ∃ f ∈ S', m = leading_monomial' mo f (this f _) }

def leadterm_ideal {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K]
  (mo : MonomialOrder σ) (S : Set (MvPolynomial σ K)) :=


def leadterm_ideal {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K]
  (mo : MonomialOrder σ) (I : Ideal (MvPolynomial σ K)) :=
  @monomial_ideal σ K _ _ _ { m : σ →₀ ℕ | ∃ f ∈ I, f ≠ 0 ∧ m = leading_monomial' mo f (by trivial) }
-/

/-- The set of entire monomials which appear in one of `f ∈ F`. -/
def monomial_set {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K]
  (F : Finset (MvPolynomial σ K)) :=
  F.biUnion (λ f => f.support)

/-- The set of leading monomials is contained in the set of entire monomials. -/
lemma monset_sub_lms {σ : Type*} {K : Type*} [Finite σ] [DecidableEq σ] [Field K]
  (mo : MonomialOrder σ) (F : Finset (MvPolynomial σ K))
  : leading_monomials mo F ⊆ monomial_set F := by
  unfold leading_monomials
  unfold monomial_set
  simp_all
  intro x hx m hm
  simp_all
  by_cases hF : F = ∅
  · simp_all
  · by_cases hx0 : x = 0
    · unfold leading_monomial at hm
      simp [hx0] at hm
    · apply Exists.intro x
      constructor
      · exact hx
      · unfold leading_monomial at hm
        have : m ∈ x.support := by
          apply Iff.mp WithBot.map_eq_some_iff at hm
          let ⟨y, hy1, hy2⟩ := hm
          apply Finset.mem_of_max at hy1
          simp_all
        simp_all
