import Mathlib
import FaugereF4.MonomialIdeal

-- MvPolynomial σ R = AddMonoidAlgebra R (σ →₀ ℕ) = (σ →₀ ℕ) →₀ R
-- Finset.orderIsoOfFin

/-
RREF의 output에 바라는 것이 무엇인가?
- 각각의 leading monomial이 겹치지 않을 것
-- leading coeff가 1이라거나, 나머지 원소들의 해당 monomial coeff가 0인 등...
   RREF로서 만족해야 할 것들이 있으나 이는 필수적이지 X
- 모두 처음의 ideal의 원소일 것 (<== 모두 input의 linear combi-일 것)
- input의 각 원소 h는 output의 원소들의 linear combi-로 유일하게 표현되며,
  특히 그 linear combi-는 곧 std rep'n일 것
  (곧, lin combi에 관여한 output 원소들의 leading monomial이 lm(h) 이하일 것)
-- 이건 ⟨input⟩_K = ⟨output⟩_K임을 확인하면 충분. recursively...
-/

/-
output의 lead-mon'l set과 ⟨input⟩_K의 어떤 finite subset S의 lead-mon'l set이 같다면...
- ⟨input⟩_K = ⟨output⟩_K = ⟨S⟩_K
- 임의의 f ∈ ⟨input⟩_K가 S 위에서도 std rep'n을 가짐
-/

/-- Information on the choice of a polynomial, in each step of Gaussian elimination.
This includes the choice from a finite set `S`, its membership, non-zeroness (given `0 ∉ S`), and
its maximality of leading monomial within `S`. -/
structure MvPolyGEChoiceSpec {σ R : Type*} [DecidableEq σ] [CommSemiring R]
  (mo : MonomialOrder σ) (S : Finset (MvPolynomial σ R)) (hS : S.Nonempty) (hSe : 0 ∉ S) where
  choice : MvPolynomial σ R
  choice_mem : choice ∈ S
  choice_not_zero : choice ≠ 0
  choice_max_lm (f : MvPolynomial σ R) (hf : f ∈ S) :
    mo.toSyn (leading_monomial' mo f (by apply ne_of_mem_of_not_mem hf hSe)) ≤
    mo.toSyn (leading_monomial' mo choice choice_not_zero)

/-- Actual choice of a pivot for Gaussian elimination, along with all the
requirements specified in `MvPolyGEChoiceSpec`. -/
noncomputable def max_lm_poly_choice {σ R : Type*} [DecidableEq σ] [CommSemiring R] [DecidableEq R]
  (mo : MonomialOrder σ) (S : Finset (MvPolynomial σ R)) (hS : S.Nonempty) (hSe : 0 ∉ S)
  : MvPolyGEChoiceSpec mo S hS hSe :=
  let L := S.toList
  have L_nonempty : L ≠ [] := Finset.Nonempty.toList_ne_nil hS
  let L_argmax_lm := L.argmax (WithBot.map mo.toSyn ∘ leading_monomial mo)
  have L_isSome : L_argmax_lm.isSome := by
    apply by_contradiction
    simp
    push_neg
    unfold L_argmax_lm
    simp
    exact L_nonempty
  let choice := L_argmax_lm.get L_isSome
  have choice_mem_argmax : choice ∈ L_argmax_lm := by
    unfold choice L_argmax_lm
    apply Option.get_mem
  let ⟨choice_mem_list, choice_max_lm, _⟩ := List.mem_argmax_iff.mp choice_mem_argmax
  let choice_mem : choice ∈ S := by
    unfold L at choice_mem_list
    simp at choice_mem_list
    exact choice_mem_list
  {
    choice := choice
    choice_mem := choice_mem
    choice_not_zero := by apply ne_of_mem_of_not_mem choice_mem hSe
    choice_max_lm := by
      intro f hf
      have mem_S_ne_0 (f) (hf : f ∈ S) : f ≠ 0 := by apply ne_of_mem_of_not_mem hf hSe
      have (g) (hg : g ∈ S)
        : (WithBot.map ⇑mo.toSyn ∘ leading_monomial mo) g =
          ↑(mo.toSyn (leading_monomial' mo g (mem_S_ne_0 g hg))) := by
        simp_all
        let p_lmg := lm_coe_lm' mo g (mem_S_ne_0 g hg)
        simp [p_lmg]
      rw [← WithBot.coe_le_coe, ← this f hf, ← this choice choice_mem]
      exact choice_max_lm f (by unfold L; simp; exact hf)
  }


structure GEStruct (σ K : Type*) [DecidableEq σ] [Field K]
  (mo : MonomialOrder σ) (V : Submodule K (MvPolynomial σ K)) where
  SI : Finset (MvPolynomial σ K) -- input set of mvpoly's to process
  SO : Finset (MvPolynomial σ K) -- output stack of processed mvpoly's
  zero_not_mem_SI : 0 ∉ SI
  span_V : Submodule.span K (SI ∪ SO) = V
  in_lm_le_out_lm : ∀ fi ∈ SI, ∀ fo ∈ SO,
    WithBot.map mo.toSyn (leading_monomial mo fi) ≤ WithBot.map mo.toSyn (leading_monomial mo fo)
  out_lm_diff : ∀ f ∈ SO, ∀ g ∈ SO, f ≠ g → leading_monomial mo f ≠ leading_monomial mo g

noncomputable def eliminate_lead_term {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (S : Finset (MvPolynomial σ K))
  (p : MvPolynomial σ K) (hp : p ≠ 0) : Finset (MvPolynomial σ K) :=
  let lmp := leading_monomial' mo p hp
  let lcp := p.coeff lmp
  let p1 := lcp⁻¹ • p
  S.image (λ f => f - (f.coeff lmp) • p1)
  -- Finset.biUnion S (λ f => {f - (f.coeff lmp) • p1})

lemma elim_card_le {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (S : Finset (MvPolynomial σ K))
  (p : MvPolynomial σ K) (hp : p ≠ 0)
  : (eliminate_lead_term mo S p hp).card ≤ S.card := by
  let lmp := leading_monomial' mo p hp
  let lcp := p.coeff lmp
  let p1 := lcp⁻¹ • p
  let elim_fun (f : MvPolynomial σ K) : Finset _ := {f - (f.coeff lmp) • p1}
  have (f : MvPolynomial σ K) : (elim_fun f).card ≤ 1 := by unfold elim_fun; simp
  unfold eliminate_lead_term
  rw [← mul_one S.card, ← Finset.biUnion_singleton]
  exact Finset.card_biUnion_le_card_mul S (λ f => {f - (f.coeff lmp) • p1}) 1 (λ f _ => this f)

lemma elim_subset_span {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (S : Finset (MvPolynomial σ K))
  (p : MvPolynomial σ K) (hp : p ≠ 0)
  : (eliminate_lead_term mo S p hp).toSet ⊆ (Submodule.span K ({p} ∪ S) : Submodule K (MvPolynomial σ K)) := by
  intro f hf
  unfold eliminate_lead_term at hf
  simp [Finset.mem_image] at hf
  let ⟨g, hg, hgf⟩ := hf
  simp
  subst hgf
  apply sub_mem
  · apply SetLike.mem_of_subset
    · apply Submodule.subset_span
    · simp_all only [Set.mem_insert_iff, Finset.mem_coe, or_true]
  · apply SMulMemClass.smul_mem
    apply SMulMemClass.smul_mem
    apply SetLike.mem_of_subset
    · apply Submodule.subset_span
    · simp_all only [Set.mem_insert_iff, Finset.mem_coe, true_or]

lemma subset_span_elim {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (S : Finset (MvPolynomial σ K))
  (p : MvPolynomial σ K) (hp : p ≠ 0)
  : S.toSet ⊆ (Submodule.span K ({p} ∪ eliminate_lead_term mo S p hp) : Submodule K (MvPolynomial σ K)) := by
  intro g hg
  -- unfold eliminate_lead_term
  let ec := (g.coeff (leading_monomial' mo p hp)) * (p.coeff (leading_monomial' mo p hp))⁻¹
  have g_sub_add : g = g - ec • p + ec • p := by simp
  have g_sub_mem : g - ec • p ∈ eliminate_lead_term mo S p hp := by
    unfold eliminate_lead_term
    simp [Finset.mem_image]
    exists g
    constructor
    · exact hg
    · unfold ec
      rw [← smul_assoc, smul_eq_mul]
  rw [g_sub_add]
  apply add_mem
  · apply Submodule.subset_span
    apply Or.inr g_sub_mem
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    apply Or.inl
    simp

noncomputable def gaussian_elim_rec {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (V : Submodule K (MvPolynomial σ K))
  (ges : GEStruct σ K mo V) : GEStruct σ K mo V :=
  if SI_nonempty : ges.SI.Nonempty
    then
      let pivot_spec := max_lm_poly_choice mo ges.SI SI_nonempty ges.zero_not_mem_SI
      let pivot := pivot_spec.choice
      let lm_pivot := leading_monomial' mo pivot_spec.choice pivot_spec.choice_not_zero
      let pivot_1 := (pivot.coeff lm_pivot)⁻¹ • pivot
      let SO := (eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero) ∪ {pivot_1}
      let SI0 := (eliminate_lead_term mo (ges.SI.erase pivot) pivot pivot_spec.choice_not_zero)
      let SI := SI0.erase 0
      have SI_card_decr : SI.card < ges.SI.card := by -- termination proof
        have erase_pivot_decr : (ges.SI.erase pivot).card < ges.SI.card := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_exists_subset_erase]
          exists pivot
          exact ⟨pivot_spec.choice_mem, by simp⟩
        have elim_SI_nonincr : SI0.card ≤ (ges.SI.erase pivot).card := by
          unfold SI0
          apply elim_card_le
        have SI_erase_0_nonincr : SI.card ≤ SI0.card := by
          unfold SI
          apply Finset.card_erase_le
        calc
          SI.card ≤ SI0.card := SI_erase_0_nonincr
          _ ≤ (ges.SI.erase pivot).card := elim_SI_nonincr
          _ < ges.SI.card := erase_pivot_decr
      gaussian_elim_rec mo V {
        SI := SI
        SO := SO
        zero_not_mem_SI := by
          unfold SI
          simp
        span_V := by
          rw [← ges.span_V]
          apply Submodule.span_eq_span
          · apply Set.union_subset
            · unfold SI
              have cont_1 : SI0.toSet ⊆ SetLike.coe (Submodule.span K ges.SI : Submodule K (MvPolynomial σ K)) := by
                have : ges.SI = {pivot} ∪ ges.SI.erase pivot := by
                  rw [← Finset.insert_eq]
                  apply Eq.symm
                  unfold pivot
                  apply Finset.insert_erase pivot_spec.choice_mem
                rw [this]
                unfold SI0
                have : ({pivot} ∪ ges.SI.erase pivot).toSet = {pivot} ∪ (ges.SI.erase pivot).toSet := by simp
                rw [this]
                apply elim_subset_span mo (ges.SI.erase pivot) pivot pivot_spec.choice_not_zero
              have cont_2 : SetLike.coe (Submodule.span K ges.SI : Submodule K (MvPolynomial σ K))
                          ⊆ SetLike.coe (Submodule.span K (↑ges.SI ∪ ↑ges.SO)) := by
                apply Submodule.span_mono
                simp
              calc
                (SI0.erase 0).toSet ⊆ SI0.toSet := by simp
                _ ⊆ SetLike.coe (Submodule.span K ges.SI : Submodule K (MvPolynomial σ K)) := by exact cont_1
                _ ⊆ SetLike.coe (Submodule.span K (↑ges.SI ∪ ↑ges.SO)) := by exact cont_2
            · unfold SO
              rw [Finset.coe_union, Set.union_subset_iff]
              simp
              constructor
              · have cont_0 : {pivot} ∪ ges.SO.toSet ⊆ ges.SI ∪ ges.SO := by
                  apply Set.union_subset_union (by simp; exact pivot_spec.choice_mem) (by simp)
                have cont_1 : (eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero).toSet
                            ⊆ Submodule.span K ({pivot} ∪ ges.SO.toSet) := by
                  apply elim_subset_span
                have cont_2 : SetLike.coe (Submodule.span K ({pivot} ∪ ges.SO.toSet) : Submodule K (MvPolynomial σ K))
                            ⊆ SetLike.coe (Submodule.span K (↑ges.SI ∪ ↑ges.SO)) := by
                  apply Submodule.span_mono
                  exact cont_0
                calc
                  (eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero).toSet ⊆ Submodule.span K ({pivot} ∪ ges.SO.toSet) := by exact cont_1
                  _ ⊆ SetLike.coe (Submodule.span K (↑ges.SI ∪ ↑ges.SO)) := by exact cont_2
              · unfold pivot_1
                apply SMulMemClass.smul_mem
                apply Submodule.subset_span
                apply Or.inl pivot_spec.choice_mem
          · apply Set.union_subset
            ·
              sorry
            ·
              sorry
        in_lm_le_out_lm := by -- cases for fo : pivot => pivot_spec.choice_max_lm | other => ges.in_lm_le_out_lm
          sorry
        out_lm_diff := by -- ges.in_lm_le_out_lm
          sorry
      }
    else
      {
        SI := ∅
        SO := ges.SO
        zero_not_mem_SI := by simp
        span_V := by
          have prev_span_V : Submodule.span K (↑ges.SI ∪ ↑ges.SO) = V := ges.span_V
          simp at SI_nonempty
          rw [SI_nonempty] at prev_span_V
          exact prev_span_V
        in_lm_le_out_lm := by
          intro fi hfi
          trivial
        out_lm_diff := ges.out_lm_diff
      }
termination_by ges.SI.card
decreasing_by exact SI_card_decr

noncomputable def gaussian_elim {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (input : Finset (MvPolynomial σ K))
  : GEStruct σ K mo (Submodule.span K input) :=
  gaussian_elim_rec mo (Submodule.span K input) {
    SI := input.erase 0
    SO := ∅
    zero_not_mem_SI := by simp
    span_V := by simp
    in_lm_le_out_lm := by
      intro _ _ fo hfo
      trivial
    out_lm_diff := by
      intro f hf
      trivial
  }
