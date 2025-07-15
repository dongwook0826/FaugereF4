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


structure GEStruct (σ K : Type*) [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (M : Finset (σ →₀ ℕ)) (V : Submodule K (MvPolynomial σ K)) where
  SI : Finset (MvPolynomial σ K) -- input set of mvpoly's to process
  SO : Finset (MvPolynomial σ K) -- output set of processed mvpoly's
  zero_not_mem_SI : 0 ∉ SI
  zero_not_mem_SO : 0 ∉ SO
  monset_fixed : monomial_set (SI ∪ SO) = M
  span_V : Submodule.span K (SI ∪ SO) = V
  in_lm_le_out_lm (fi) (hfi : fi ∈ SI) (fo) (hfo : fo ∈ SO) :
    mo.toSyn (leading_monomial' mo fi (ne_of_mem_of_not_mem hfi zero_not_mem_SI))
    < mo.toSyn (leading_monomial' mo fo (ne_of_mem_of_not_mem hfo zero_not_mem_SO))
  out_lm_diff (f) (hfo : f ∈ SO) (g) (hgo : g ∈ SO) :
    f ≠ g →
    leading_monomial' mo f (ne_of_mem_of_not_mem hfo zero_not_mem_SO)
    ≠ leading_monomial' mo g (ne_of_mem_of_not_mem hgo zero_not_mem_SO)
  out_lc_one (fo) (hfo : fo ∈ SO) :
    leading_coeff' mo fo (ne_of_mem_of_not_mem hfo zero_not_mem_SO) = 1

noncomputable def eliminate_lead_term {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (S : Finset (MvPolynomial σ K))
  (p : MvPolynomial σ K) (hp : p ≠ 0) : Finset (MvPolynomial σ K) :=
  let lmp := leading_monomial' mo p hp
  let lcp := p.coeff lmp
  let p1 := lcp⁻¹ • p
  S.image (λ f => f - (f.coeff lmp) • p1)

lemma elim_pivot_monset_eq {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (S : Finset (MvPolynomial σ K))
  (p : MvPolynomial σ K) (hp : p ≠ 0)
  : monomial_set ((eliminate_lead_term mo S p hp) ∪ {p}) = monomial_set (S ∪ {p}) := by
  simp [eliminate_lead_term, monomial_set]
  ext μ
  simp
  constructor
  · intro ⟨f, hpf, hμf⟩
    cases hpf with
    | inl hpf =>
      let ⟨g, g_mem_S, pfg_eq⟩ := hpf
      rw [sub_eq_iff_eq_add] at pfg_eq
      cases (em (p.coeff μ = 0)) with
      | inl pμ_eq_0 =>
        have : ¬g.coeff μ = 0 := by
          rw [pfg_eq]
          simp [pμ_eq_0]
          exact hμf
        exists g
        exact ⟨Or.inl g_mem_S, this⟩
      | inr pμ_ne_0 =>
        exists p
        exact ⟨Or.inr rfl, pμ_ne_0⟩
    | inr hpf =>
      exists f
      exact ⟨Or.inr hpf, hμf⟩
  · intro ⟨g, hgSp, hμg⟩
    cases hgSp with
    | inl g_mem_S =>
      cases (em (p.coeff μ = 0)) with
      | inl pμ_eq_0 =>
        exists g - g.coeff (leading_monomial' mo p hp) • (p.coeff (leading_monomial' mo p hp))⁻¹ • p
        constructor
        · apply Or.inl
          exists g
        · simp [pμ_eq_0]
          exact hμg
      | inr pμ_ne_0 =>
        exists p
        exact ⟨Or.inr rfl, pμ_ne_0⟩
    | inr g_eq_p =>
      subst g
      exists p
      exact ⟨Or.inr rfl, hμg⟩

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

lemma smul_insert_span {K M : Type*} [Field K] [AddCommMonoid M] [Module K M]
  {p : M} {s : Set M} {c : K} {hc : c ≠ 0} :
  Submodule.span K ({p} ∪ s) = Submodule.span K ({c • p} ∪ s) := by
  rw [Submodule.span_union, Submodule.span_union]
  have : Submodule.span K {p} = Submodule.span K {c • p} := by
    ext v
    rw [Submodule.mem_span_singleton, Submodule.mem_span_singleton]
    constructor
    · intro ⟨c', hc'⟩
      exists c' • c⁻¹
      rw [← hc', smul_assoc, ← smul_assoc c⁻¹ c p]
      simp_all
    · intro ⟨c', hc'⟩
      exists c' • c
      rw [← hc', smul_assoc]
  rw [this]

noncomputable def gaussian_elim_step {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (M : Finset (σ →₀ ℕ)) (V : Submodule K (MvPolynomial σ K))
  (ges : GEStruct σ K mo M V) (SI_nonempty : ges.SI.Nonempty) : GEStruct σ K mo M V :=
  let pivot_spec := max_lm_poly_choice mo ges.SI SI_nonempty ges.zero_not_mem_SI
  let pivot := pivot_spec.choice
  let lm_pivot := leading_monomial' mo pivot pivot_spec.choice_not_zero
  have lc_pivot_ne_0 : pivot.coeff lm_pivot ≠ 0 := by
    unfold lm_pivot
    rw [← MvPolynomial.mem_support_iff]
    apply lm'_mem
  let pivot_1 := (pivot.coeff lm_pivot)⁻¹ • pivot
  have lm_piv1_eq_lm_piv : leading_monomial' mo pivot_1 (smul_ne_zero (inv_ne_zero lc_pivot_ne_0) pivot_spec.choice_not_zero)
                          = leading_monomial' mo pivot (pivot_spec.choice_not_zero) := by
    unfold pivot_1
    unfold leading_monomial'
    simp_all
  let SO := (eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero) ∪ {pivot_1}
  let SI0 := (eliminate_lead_term mo (ges.SI.erase pivot) pivot pivot_spec.choice_not_zero)
  let SI := SI0.erase 0
  have zero_not_mem_SI : 0 ∉ SI := by
    unfold SI
    simp
  have zero_not_mem_SO : 0 ∉ SO := by
    unfold SO
    simp
    constructor
    · by_contra h_cont
      simp [eliminate_lead_term] at h_cont
      let ⟨a, a_mem, ha⟩ := h_cont
      -- simp at ha
      let key := ges.in_lm_le_out_lm pivot pivot_spec.choice_mem a a_mem
      rw [sub_eq_zero, ← smul_assoc] at ha
      let C := a.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹
      have C_not_0 : C ≠ 0 := by
        unfold C lm_pivot
        by_contra HC
        rw [HC] at ha
        simp at ha
        rw [ha] at a_mem
        exact ges.zero_not_mem_SO a_mem
      let keyc := lm'_smul_eq_lm' mo pivot pivot_spec.choice_not_zero C C_not_0
      let keyc' := lm'_eq_of_eq mo a (C • pivot) ha (ne_of_mem_of_not_mem a_mem ges.zero_not_mem_SO)
      /-
      have keyc : leading_monomial' mo pivot pivot_spec.choice_not_zero
                = leading_monomial' mo a (ne_of_mem_of_not_mem a_mem ges.zero_not_mem_SO) := by
        rw [ha]
        rcases em (a.coeff lm_pivot = 0) with h0 | h0
        · unfold lm_pivot at h0
          simp [h0] at ha
          rw [ha] at a_mem
          by_contra _
          exact ges.zero_not_mem_SO a_mem
        · rw [← lm_smul_eq_lm mo _ (a.coeff lm_pivot) h0]
          rw [← lm_smul_eq_lm mo pivot _ (inv_ne_zero lc_pivot_ne_0)]
      -/
      apply ne_of_lt at key
      rw [keyc, ← keyc'] at key
      trivial
    · push_neg
      unfold pivot_1
      rw [ne_comm]
      exact smul_ne_zero (inv_ne_zero lc_pivot_ne_0) (pivot_spec.choice_not_zero)
  have lm_fi_lt_lm_piv (fi) (hfi : fi ∈ SI) :
    mo.toSyn (leading_monomial' mo fi (ne_of_mem_of_not_mem hfi zero_not_mem_SI))
    < mo.toSyn lm_pivot := by
    unfold lm_pivot pivot
    simp [SI, SI0, eliminate_lead_term] at hfi
    let ⟨fi_ne_0, fi', ⟨fi'_ne_piv, fi'_mem_ges_SI⟩, hfi'⟩ := hfi
    have lm_piv_not_in_fi : fi.coeff lm_pivot = 0 := by
      rw [← hfi']
      unfold lm_pivot
      simp
      rw [inv_mul_cancel₀ (by unfold lm_pivot at lc_pivot_ne_0; exact lc_pivot_ne_0)]
      simp
    rw [← MvPolynomial.notMem_support_iff] at lm_piv_not_in_fi
    have mo_fi : ∀ m ∈ fi.support, mo.toSyn m ≠ mo.toSyn lm_pivot := by
      intro m mem_fi
      simp
      exact ne_of_mem_of_not_mem mem_fi lm_piv_not_in_fi
    let fi_supp_sub := MvPolynomial.support_sub σ fi' (fi'.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹ • pivot)
    rw [hfi'] at fi_supp_sub
    have cont_1 : (fi'.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹ • pivot).support ⊆ pivot.support := by
      rw [← smul_assoc]
      apply MvPolynomial.support_smul
    have cont_2 : fi'.support ∪ (fi'.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹ • pivot).support ⊆ fi'.support ∪ pivot.support := by
      apply Finset.union_subset_union
      · simp
      · exact cont_1
    have mo_fi' : ∀ m ∈ fi'.support, mo.toSyn m ≤ mo.toSyn lm_pivot := by
      let lm_fi'_le_lm_piv := pivot_spec.choice_max_lm fi' fi'_mem_ges_SI
      intro m mem_fi'
      unfold lm_pivot pivot
      have : mo.toSyn m ≤ mo.toSyn (leading_monomial' mo fi' (ne_of_mem_of_not_mem fi'_mem_ges_SI ges.zero_not_mem_SI)) := by
        unfold leading_monomial' max_monomial'
        simp
        let map_mem_fi' := Finset.mem_map_of_mem (mo.toSyn.toEquiv).toEmbedding mem_fi'
        simp only [Equiv.toEmbedding_apply, AddEquiv.toEquiv_eq_coe] at map_mem_fi'
        apply Finset.le_max' _ (mo.toSyn m) map_mem_fi'
      exact le_trans this lm_fi'_le_lm_piv
    have mo_piv : ∀ m ∈ pivot.support, mo.toSyn m ≤ mo.toSyn lm_pivot := by
      intro m mem_piv
      unfold lm_pivot leading_monomial' max_monomial'
      simp
      let map_mem_piv := Finset.mem_map_of_mem (mo.toSyn.toEquiv).toEmbedding mem_piv
      simp only [Equiv.toEmbedding_apply, AddEquiv.toEquiv_eq_coe] at map_mem_piv
      apply Finset.le_max' _ (mo.toSyn m) map_mem_piv
    have mo_fi'_piv : ∀ m ∈ fi'.support ∪ pivot.support, mo.toSyn m ≤ mo.toSyn lm_pivot := by
      intro m hm
      rw [Finset.mem_union] at hm
      rcases hm with mem_fi' | mem_piv
      · exact mo_fi' m mem_fi'
      · exact mo_piv m mem_piv
    apply lt_of_le_of_ne
    · apply mo_fi'_piv
      apply cont_2
      apply fi_supp_sub
      apply lm'_mem mo fi _
    · apply mo_fi
      apply lm'_mem mo fi _
  have lm_piv_lt_lm_fo_ne_piv (fo) (hfo : fo ∈ SO) (fo_ne_piv : fo ≠ pivot_1) :
    mo.toSyn lm_pivot
    < mo.toSyn (leading_monomial' mo fo (ne_of_mem_of_not_mem hfo zero_not_mem_SO)) := by
    have hfo' : fo ∈ eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero := by
      unfold SO at hfo
      simp at hfo
      exact Or.resolve_right hfo fo_ne_piv
    unfold eliminate_lead_term at hfo'
    simp at hfo'
    let ⟨a, a_mem, ha⟩ := hfo'
    rw [← smul_assoc] at ha
    let lm_piv_lt_lm_a := ges.in_lm_le_out_lm pivot pivot_spec.choice_mem a a_mem
    let a_ss_piv_ne_0 := sub_smul_ne_0 mo pivot a
      pivot_spec.choice_not_zero
      (ne_of_mem_of_not_mem a_mem ges.zero_not_mem_SO)
      lm_piv_lt_lm_a
      (a.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹)
    let lm_ss_eq_lm_fo := lm'_eq_of_eq mo (a - (a.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹) • pivot) fo ha a_ss_piv_ne_0
    let lm_ss_eq_lm_a := lm_sub_smul_eq_lm mo pivot a
      pivot_spec.choice_not_zero
      (ne_of_mem_of_not_mem a_mem ges.zero_not_mem_SO)
      lm_piv_lt_lm_a
      (a.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹)
    rw [← lm_ss_eq_lm_fo, lm_ss_eq_lm_a]
    exact lm_piv_lt_lm_a
  {
    SI := SI
    SO := SO
    zero_not_mem_SI := zero_not_mem_SI
    zero_not_mem_SO := zero_not_mem_SO
    monset_fixed := by
      unfold SI SO SI0
      conv_lhs =>
        rw [← Finset.union_self {pivot_1}, ← Finset.union_assoc _ {pivot_1} {pivot_1},
            Finset.union_comm (eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero ∪ {pivot_1}) {pivot_1},
            ← Finset.union_assoc _ {pivot_1} _,
            monomial_set_union_distrib, monomial_set_union_distrib, monomial_set_union_distrib]
      have pivot_mem : pivot ∈ ges.SI := by
        apply pivot_spec.choice_mem
      conv_rhs =>
        rw [← ges.monset_fixed, ← Finset.insert_erase pivot_mem,
            Finset.insert_eq, Finset.union_comm {pivot} _, ← Finset.union_self {pivot},
            ← Finset.union_assoc _ {pivot} {pivot}, Finset.union_assoc _ {pivot} ges.SO,
            Finset.union_comm {pivot} ges.SO,
            monomial_set_union_distrib,
            ← elim_pivot_monset_eq mo (ges.SI.erase pivot) pivot pivot_spec.choice_not_zero,
            ← elim_pivot_monset_eq mo ges.SO pivot pivot_spec.choice_not_zero,
            monomial_set_union_distrib, monomial_set_union_distrib]
      rw [monomial_set_erase_zero]
      have piv1_piv_monset : monomial_set {pivot_1} = monomial_set {pivot} := by
        unfold pivot_1
        simp [singleton_monset_eq_support]
        exact MvPolynomial.support_smul_eq (inv_ne_zero lc_pivot_ne_0) pivot
      rw [piv1_piv_monset]
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
      · have pivot_mp : (ges.SI \ {pivot}) ∪ {pivot} = ges.SI := by
          simp
          exact pivot_spec.choice_mem
        rw [← pivot_mp, Finset.coe_union, Set.union_assoc, ← Finset.coe_union]
        apply Set.union_subset
        · rw [← Finset.erase_eq]
          let cont_0 := subset_span_elim mo (ges.SI \ {pivot}) pivot pivot_spec.choice_not_zero
          rw [← Finset.erase_eq] at cont_0
          rw [
            @smul_insert_span K _ _ _ _
              pivot
              (eliminate_lead_term mo (ges.SI.erase pivot) pivot _)
              (pivot.coeff lm_pivot)⁻¹
              (inv_ne_zero lc_pivot_ne_0)
          ] at cont_0
          have cont_1 : {pivot_1} ∪ SI0 ⊆ SI0 ∪ SO := by
            rw [Finset.union_comm]
            apply Finset.union_subset_union (by simp) (by unfold SO; simp)
          rw [← Finset.coe_subset, Finset.coe_union, Finset.coe_union, Finset.coe_singleton] at cont_1
          have cont_2 : (Submodule.span K (SI0 ∪ SO) : Submodule K (MvPolynomial σ K)) = Submodule.span K (SI ∪ SO) := by
            unfold SI
            rcases em (0 ∈ SI0) with h0 | h0
            · have : (SI0.erase 0).toSet ∪ {0} = SI0.toSet := by simp; exact h0
              rw [← this, Set.union_right_comm]
              simp
            · rw [← Finset.erase_eq_self] at h0
              rw [h0]
          rw [← cont_2]
          calc
            ↑(ges.SI.erase pivot) ⊆ SetLike.coe (Submodule.span K ({pivot_1} ∪ SI0) : Submodule K (MvPolynomial σ K)) := by
              unfold pivot_1 SI0
              exact cont_0
            _ ⊆ SetLike.coe (Submodule.span K (SI0 ∪ SO) : Submodule K (MvPolynomial σ K)) := by
              apply Submodule.span_mono
              exact cont_1
        · rw [Finset.coe_union, Set.union_subset_iff]
          constructor
          · simp
            have : pivot_1 ∈ Submodule.span K (SI ∪ SO) := by
              apply Submodule.subset_span
              unfold SO
              simp
            apply Submodule.smul_mem _ (pivot.coeff lm_pivot) at this
            unfold pivot_1 at this
            rw [smul_inv_smul₀ lc_pivot_ne_0] at this
            exact this
          · let cont_0 := subset_span_elim mo ges.SO pivot pivot_spec.choice_not_zero
            rw [
              @smul_insert_span K (MvPolynomial σ K) _ _ _
                pivot
                (eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero)
                (pivot.coeff lm_pivot)⁻¹
                (inv_ne_zero lc_pivot_ne_0)
            ] at cont_0
            have cont_1 : SetLike.coe (Submodule.span K SO : Submodule K (MvPolynomial σ K)) ⊆ SetLike.coe (Submodule.span K (SI ∪ SO)) := by
              apply Submodule.span_mono
              simp
            calc
              ges.SO.toSet ⊆
              SetLike.coe (Submodule.span K (
                {(MvPolynomial.coeff lm_pivot pivot)⁻¹ • pivot} ∪
                ↑(eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero))
                : Submodule K (MvPolynomial σ K)) := by
                exact cont_0
              _ ⊆
              SetLike.coe (Submodule.span K (SI ∪ SO)) := by
                rw [Set.union_comm]
                subst SO pivot_1
                simp_all
    in_lm_le_out_lm := by -- cases for fo : pivot => pivot_spec.choice_max_lm | other => ges.in_lm_le_out_lm
      intro fi hfi fo hfo
      cases em (fo = pivot_1) with
      | inl fo_piv =>
        subst fo_piv
        rw [lm_piv1_eq_lm_piv]
        exact lm_fi_lt_lm_piv fi hfi
      | inr fo_ne_piv =>
        exact lt_trans
          (lm_fi_lt_lm_piv fi hfi)
          (lm_piv_lt_lm_fo_ne_piv fo hfo fo_ne_piv)
    out_lm_diff := by -- ges.in_lm_le_out_lm
      intro f hfo g hgo hfg_ne
      cases em (f = pivot_1) with
      | inl f_piv =>
        simp
        subst f_piv
        rw [lm_piv1_eq_lm_piv, ← AddEquiv.apply_eq_iff_eq mo.toSyn]
        push_neg
        apply ne_of_lt
        exact lm_piv_lt_lm_fo_ne_piv g hgo (Ne.symm hfg_ne)
      | inr f_ne_piv =>
        cases em (g = pivot_1) with
        | inl g_piv =>
          rw [ne_comm]
          simp
          subst g_piv
          rw [lm_piv1_eq_lm_piv, ← AddEquiv.apply_eq_iff_eq mo.toSyn]
          push_neg
          apply ne_of_lt
          exact lm_piv_lt_lm_fo_ne_piv f hfo hfg_ne
        | inr g_ne_piv =>
          have hfo' : f ∈ eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero := by
            unfold SO at hfo
            simp at hfo
            exact Or.resolve_right hfo f_ne_piv
          have hgo' : g ∈ eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero := by
            unfold SO at hgo
            simp at hgo
            exact Or.resolve_right hgo g_ne_piv
          unfold eliminate_lead_term at hfo'
          unfold eliminate_lead_term at hgo'
          simp at hfo'
          simp at hgo'
          let ⟨af, af_mem, haf⟩ := hfo'
          let ⟨ag, ag_mem, hag⟩ := hgo'
          rw [← smul_assoc, eq_comm] at haf
          rw [← smul_assoc, eq_comm] at hag
          let lm_f_eq_lm_ss := lm'_eq_of_eq mo f _ haf (ne_of_mem_of_not_mem hfo zero_not_mem_SO)
          let lm_g_eq_lm_ss := lm'_eq_of_eq mo g _ hag (ne_of_mem_of_not_mem hgo zero_not_mem_SO)
          let lm_ss_eq_lm_af := lm_sub_smul_eq_lm mo pivot af
            pivot_spec.choice_not_zero
            (ne_of_mem_of_not_mem af_mem ges.zero_not_mem_SO)
            (ges.in_lm_le_out_lm pivot pivot_spec.choice_mem af af_mem)
            (af.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹)
          let lm_ss_eq_lm_ag := lm_sub_smul_eq_lm mo pivot ag
            pivot_spec.choice_not_zero
            (ne_of_mem_of_not_mem ag_mem ges.zero_not_mem_SO)
            (ges.in_lm_le_out_lm pivot pivot_spec.choice_mem ag ag_mem)
            (ag.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹)
          rw [lm_f_eq_lm_ss, lm_ss_eq_lm_af, lm_g_eq_lm_ss, lm_ss_eq_lm_ag]
          have af_ne_ag : af ≠ ag := by
            by_contra af_eq_ag
            subst af_eq_ag
            simp_all
          exact ges.out_lm_diff af af_mem ag ag_mem af_ne_ag
    out_lc_one := by
      intro fo hfo
      cases em (fo = pivot_1) with
      | inl fo_piv =>
        subst fo_piv
        unfold leading_coeff'
        rw [lm_piv1_eq_lm_piv]
        simp only [pivot_1, MvPolynomial.coeff_smul, lm_pivot]
        exact inv_mul_cancel₀ lc_pivot_ne_0
      | inr fo_ne_piv =>
        unfold leading_coeff'
        have hfo' : fo ∈ eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero := by
          unfold SO at hfo
          simp at hfo
          exact Or.resolve_right hfo fo_ne_piv
        unfold eliminate_lead_term at hfo'
        simp at hfo'
        let ⟨af, af_mem, haf⟩ := hfo'
        rw [← smul_assoc, eq_comm] at haf
        let lm_fo_eq_lm_ss := lm'_eq_of_eq mo fo _ haf (ne_of_mem_of_not_mem hfo zero_not_mem_SO)
        let lm_ss_eq_lm_af := lm_sub_smul_eq_lm mo pivot af
          pivot_spec.choice_not_zero
          (ne_of_mem_of_not_mem af_mem ges.zero_not_mem_SO)
          (ges.in_lm_le_out_lm pivot pivot_spec.choice_mem af af_mem)
          (af.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹)
        rw [lm_fo_eq_lm_ss, lm_ss_eq_lm_af, haf]
        have piv_coeff_af_eq_0 : pivot.coeff (leading_monomial' mo af (ne_of_mem_of_not_mem af_mem ges.zero_not_mem_SO)) = 0 := by
          rw [← MvPolynomial.notMem_support_iff]
          by_contra H
          unfold leading_monomial' max_monomial' at H
          rw [AddEquiv.invFun_eq_symm, ← Finset.mem_map' mo.toSyn.toEmbedding] at H
          rw [Equiv.toEmbedding_apply] at H
          have (x) : mo.toSyn.toEquiv (mo.toSyn.symm x) = x := by
            simp_all
          -- simp at H
          rw [this] at H
          simp only [AddEquiv.toEquiv_eq_coe, Equiv.apply_symm_apply mo.toSyn.toEquiv] at H
          have le_cont : mo.toSyn (leading_monomial' mo af (ne_of_mem_of_not_mem af_mem ges.zero_not_mem_SO)) ≤ mo.toSyn lm_pivot := by
            unfold lm_pivot leading_monomial' max_monomial'
            rw [AddEquiv.invFun_eq_symm]
            simp only [AddEquiv.apply_symm_apply mo.toSyn]
            exact Finset.le_max' _ _ H
          have gt_cont : mo.toSyn lm_pivot < mo.toSyn (leading_monomial' mo af (ne_of_mem_of_not_mem af_mem ges.zero_not_mem_SO)) := by
            exact ges.in_lm_le_out_lm pivot pivot_spec.choice_mem af af_mem
          exact not_le_of_gt gt_cont le_cont
        simp
        rw [piv_coeff_af_eq_0]
        simp
        exact ges.out_lc_one af af_mem
  }

lemma ges_SI_card_decr  {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (M : Finset (σ →₀ ℕ)) (V : Submodule K (MvPolynomial σ K))
  (ges : GEStruct σ K mo M V) (SI_nonempty : ges.SI.Nonempty)
  : (gaussian_elim_step mo M V ges SI_nonempty).SI.card < ges.SI.card := by -- termination proof
  let pivot_spec := max_lm_poly_choice mo ges.SI SI_nonempty ges.zero_not_mem_SI
  let pivot := pivot_spec.choice
  let SI0 := (eliminate_lead_term mo (ges.SI.erase pivot) pivot pivot_spec.choice_not_zero)
  let SI := SI0.erase 0
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

noncomputable def gaussian_elim_rec {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (M : Finset (σ →₀ ℕ)) (V : Submodule K (MvPolynomial σ K))
  (ges : GEStruct σ K mo M V) : GEStruct σ K mo M V :=
  if SI_nonempty : ges.SI.Nonempty
    then
      gaussian_elim_rec mo M V (gaussian_elim_step mo M V ges SI_nonempty)
    else
      {
        SI := ∅
        SO := ges.SO
        zero_not_mem_SI := by simp
        zero_not_mem_SO := ges.zero_not_mem_SO
        monset_fixed := by
          simp at SI_nonempty
          let prev_monset_fixed := ges.monset_fixed
          simp [SI_nonempty] at prev_monset_fixed
          simp [prev_monset_fixed]
        span_V := by
          have prev_span_V : Submodule.span K (↑ges.SI ∪ ↑ges.SO) = V := ges.span_V
          simp at SI_nonempty
          rw [SI_nonempty] at prev_span_V
          exact prev_span_V
        in_lm_le_out_lm := by
          intro fi hfi
          trivial
        out_lm_diff := ges.out_lm_diff
        out_lc_one := ges.out_lc_one
      }
termination_by ges.SI.card
decreasing_by apply ges_SI_card_decr

noncomputable def ges_init {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (input : Finset (MvPolynomial σ K))
  : GEStruct σ K mo (monomial_set input) (Submodule.span K input) :=
  {
    SI := input.erase 0
    SO := ∅
    zero_not_mem_SI := by simp
    zero_not_mem_SO := by simp
    monset_fixed := by
      simp
      apply monomial_set_erase_zero
    span_V := by simp
    in_lm_le_out_lm := by
      intro _ _ fo hfo
      trivial
    out_lm_diff := by
      intro f hf
      trivial
    out_lc_one := by
      intro fo hfo
      trivial
  }

noncomputable def gaussian_elim {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (input : Finset (MvPolynomial σ K))
  : GEStruct σ K mo (monomial_set input) (Submodule.span K input) :=
  gaussian_elim_rec mo (monomial_set input) (Submodule.span K input) (ges_init mo input)

lemma gaussian_elim_rec_SI_empty {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (M : Finset (σ →₀ ℕ)) (V : Submodule K (MvPolynomial σ K)) :
  ∀ n : ℕ, ∀ (ges : GEStruct σ K mo M V), ges.SI.card = n → (gaussian_elim_rec mo M V ges).SI = ∅ := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold gaussian_elim_rec
    intro ges ges_SI_card_eq_n
    split_ifs with SI_nonempty
    · -- Case: SI.Nonempty
      apply ih
      · rw [← ges_SI_card_eq_n]
        apply ges_SI_card_decr _ _ _ _ SI_nonempty
      · rfl
    · -- Case: ¬SI.Nonempty
      simp

lemma gaussian_elim_SI_empty {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (input : Finset (MvPolynomial σ K)) :
  (gaussian_elim mo input).SI = ∅ := by
  unfold gaussian_elim
  exact gaussian_elim_rec_SI_empty mo
    (monomial_set input)
    (Submodule.span K ↑input)
    ((ges_init mo input).SI.card)
    (ges_init mo input)
    (by rfl)
