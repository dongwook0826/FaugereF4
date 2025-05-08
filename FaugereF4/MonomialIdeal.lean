import Mathlib

namespace MvPolynomial

/-!
# Preliminaries on monomial ideals

## TODO

- Show the ascending chain condition version of Noetherian property
-/

def monomialIdeal {σ R : Type*} [CommSemiring R] (s : Set (σ →₀ ℕ)) :
  Ideal (MvPolynomial σ R) :=
  Ideal.span ((fun s => monomial s (1 : R)) '' s)

lemma noeth_acc (R : Type*) [Semiring R] [IsNoetherianRing R] :
  ∀ (iseq : ℕ → Ideal R), (∀ (n m : ℕ), n ≤ m → iseq n ≤ iseq m) →
  ∃ (N : ℕ), ∀ (M : ℕ), N ≤ M → iseq N = iseq M := by
  sorry

theorem Dickson_lemma_fin (n : ℕ) : -- {σ K : Type*} [Field K] :
  ∀ (K : Type*) [Field K], ∀ (A : Set (Fin n →₀ ℕ)), ∃ (s : Finset (Fin n →₀ ℕ)),
  ↑s ⊆ A ∧ (@monomialIdeal (Fin n) K _ ↑s = monomialIdeal A) := by
  intro K instK
  induction n using Nat.strongRecOn with
  | ind n IH =>
    obtain _ | n := n
    · simp_all
      intro A
      have mem_A : ∀ x ∈ A, x = 0 := by
        intro hxA
        rw [← Finsupp.support_eq_empty]
        have fin0_sub_empty : ∀ (S : Set (Fin 0)), S = ∅ :=
          Set.eq_empty_of_isEmpty -- simp_all의 적용을 위해 이 중간단계가 필요
        rw [← Finset.coe_eq_empty]
        simp_all
      by_cases hA : A = ∅
      · exact ⟨∅, by simp, by simp_all⟩
      · have : A = {0} := by
          ext x
          constructor
          · apply mem_A
          · intro hx0
            simp at hx0
            push_neg at hA
            have : ∃ y, y ∈ A := hA
            let ⟨y, hyA⟩ := this
            have : y = 0 := mem_A y hyA
            simp_all
        exact ⟨{0}, by simp_all, by simp_all⟩
    · intro A
      let SubA (d : ℕ) : Set (Fin n →₀ ℕ) :=
        { a | (Finsupp.embDomain (Fin.succEmb n) a).update n d ∈ A }
      let USubA (d : ℕ) : Set (Fin n →₀ ℕ) :=
        ⋃ d' : Fin d, SubA d'
      let Iseq (d : ℕ) := @monomialIdeal (Fin n) K _ (USubA d)
      have USubA_seq : ∀ (d1 d2 : ℕ), d1 ≤ d2 → USubA d1 ⊆ USubA d2 := by
        intro d1 d2 hdc
        unfold USubA
        simp
        intro d1' x hxd1
        simp
        exists Fin.castLEOrderEmb hdc d1'
      have Iseq_seq : ∀ (d1 d2 : ℕ), d1 ≤ d2 → Iseq d1 ≤ Iseq d2 := by
        intro d1 d2 hdc
        unfold Iseq
        unfold monomialIdeal
        apply Ideal.span_mono
        apply Set.image_subset
        exact USubA_seq d1 d2 hdc
      let ⟨N, Iseq_accN⟩ := noeth_acc _ Iseq Iseq_seq
      let fg_exists (d : ℕ) := IH n (by simp) (USubA d)
      let fg_mons (d : ℕ) := (fg_exists d).choose
      let fg_spec (d : ℕ) := (fg_exists d).choose_spec
      /-
      let S : Finset (Fin (n + 1) →₀ ℕ) :=
        Finset.biUnion
          (Fin (N + 1)).toFinset
          (λ d => (λ a => (Finsupp.embDomain (Fin.succEmb n) a).update n d) '' fg_mons d)
          -/
      sorry

/-
finite_iff_exists_equiv_fin : σ ≃ Fin n
Finsupp.equivCongrLeft : (σ →₀ ℕ) ≃ (Fin n →₀ ℕ)
MvPolynomial.renameEquiv : MvPolynomial σ R ≃ₐ[R] MvPolynomial (Fin n) R

-/

theorem Dickson_lemma_finite {σ : Type*} [inst_finite : Finite σ] :
  ∀ (K : Type*) [Field K], ∀ (A : Set (σ →₀ ℕ)), ∃ (s : Finset (σ →₀ ℕ)),
  ↑s ⊆ A ∧ (@monomialIdeal σ K _ ↑s = monomialIdeal A) := by
  let ⟨n, h_eq_dec⟩ := finite_iff_exists_equiv_fin.mp inst_finite
  let σ_fin_equiv := Classical.choice h_eq_dec
  intro K instK A
  let A' := Finsupp.equivMapDomain σ_fin_equiv '' A
  let ⟨s', hcont', hgen'⟩ := @Dickson_lemma_fin n K _ A'
  let s := Finset.map (Finsupp.mapDomainEmbedding σ_fin_equiv.symm.toEmbedding) s'
  exists s
  constructor
  · rw [← Equiv.image_subset (Finsupp.equivCongrLeft σ_fin_equiv) ↑s A]
    have s_eq : s'.toSet = ⇑(Finsupp.equivCongrLeft σ_fin_equiv) '' s.toSet := by
      unfold s
      simp_all
      ext m
      constructor
      · intro hms'
        simp_all
        exact ⟨m, hms', by ext a; simp_all⟩
      · intro hmss
        simp_all
        let ⟨m', hms', hmss'⟩ := hmss
        have : m = m' := by
          subst hmss'
          simp_all only [A', σ_fin_equiv]
          obtain ⟨w, hleft, hright⟩ := hmss
          ext a
          simp_all
        rw [this]
        exact hms'
    have A_eq : A' = ⇑(Finsupp.equivCongrLeft σ_fin_equiv) '' A := by
      unfold A'
      simp_all
    simp_all
  · let mvp_equiv := MvPolynomial.renameEquiv K σ_fin_equiv
    ext f
    have si_mem : mvp_equiv f ∈ monomialIdeal ↑s' ↔ f ∈ monomialIdeal ↑s := by
      unfold s
      unfold monomialIdeal
      -- unfold mvp_equiv
      -- simp_all
      -- rw [Ideal.symm_apply_mem_of_equiv_iff]
      sorry
    /-
    have si_eq : monomialIdeal ↑s = Ideal.map ↑mvp_equiv.symm (monomialIdeal ↑s') := by
      unfold s
      unfold monomialIdeal
      unfold Ideal.map
      unfold Set.image
      simp_all
      -- rw [← Set.image_comp, ← Set.image_comp]
      aesop?
    have Ai_eq : monomialIdeal A = Ideal.map ↑mvp_equiv.symm (monomialIdeal A') := by
      sorry
    -/
    -- unfold Ideal.span
    simp_all
    sorry
