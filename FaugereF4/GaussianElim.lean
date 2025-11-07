import FaugereF4.MonomialIdeal
import Mathlib.Order.CompletePartialOrder

/-!
# Gaussian elimination on `MvPolynomial` under a fixed `MonomialOrder`

This file contains the Gaussian elimination algorithm over `MvPolynomial`,
with monomials as basis set, ordered by `MonomialOrder`.
-/

/-- Information on the choice of a pivot polynomial, in each step of Gaussian elimination.
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
  (mo : MonomialOrder σ) (S : Finset (MvPolynomial σ R)) (hS : S.Nonempty) (hSe : 0 ∉ S) :
    MvPolyGEChoiceSpec mo S hS hSe :=
  let L := S.toList
  have L_nonempty : L ≠ [] := Finset.Nonempty.toList_ne_nil hS
  let L_argmax_lm := L.argmax (WithBot.map mo.toSyn ∘ leading_monomial mo)
  have L_isSome : L_argmax_lm.isSome := by
    by_contra L_none
    simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
      List.argmax_eq_none, L_argmax_lm] at L_none
    exact L_nonempty L_none
  let choice := L_argmax_lm.get L_isSome
  have choice_mem_argmax : choice ∈ L_argmax_lm := by
    unfold choice L_argmax_lm
    apply Option.get_mem
  let ⟨choice_mem_list, choice_max_lm, _⟩ := List.mem_argmax_iff.mp choice_mem_argmax
  let choice_mem : choice ∈ S := Finset.mem_toList.mp choice_mem_list
  {
    choice := choice
    choice_mem := choice_mem
    choice_not_zero := by apply ne_of_mem_of_not_mem choice_mem hSe
    choice_max_lm := by
      intro f hf
      have mem_S_ne_0 (f) (hf : f ∈ S) : f ≠ 0 := by apply ne_of_mem_of_not_mem hf hSe
      have (g) (hg : g ∈ S) :
          (WithBot.map ⇑mo.toSyn ∘ leading_monomial mo) g =
          ↑(mo.toSyn (leading_monomial' mo g (mem_S_ne_0 g hg))) := by
        simp_all only [ne_eq, Option.mem_def, Function.comp_apply]
        let p_lmg := lm_coe_lm' mo g (mem_S_ne_0 g hg)
        simp [p_lmg]
      rw [← WithBot.coe_le_coe, ← this f hf, ← this choice choice_mem]
      exact choice_max_lm f (Finset.mem_toList.mpr hf)
  }

/-- The structure of data and loop invariants to iterate through the
Gaussian elimination loop. -/
structure GEStruct (σ K : Type*) [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (M : Finset (σ →₀ ℕ)) (V : Submodule K (MvPolynomial σ K)) where
  /-- input set of polynomials to process -/
  SI : Finset (MvPolynomial σ K)
  /-- output set of processed polynomials -/
  SO : Finset (MvPolynomial σ K)
  /-- 0 is not among the input. -/
  zero_not_mem_SI : 0 ∉ SI
  /-- 0 is not among the output. -/
  zero_not_mem_SO : 0 ∉ SO
  /-- The monomial set involved in the loop doesn't change. -/
  monset_fixed : monomial_set (SI ∪ SO) = M
  /-- The linear span of polynomials in process is fixed. -/
  span_V : Submodule.span K (SI ∪ SO) = V
  /-- The leading monomials of output elements must precede those of input elements. -/
  in_lm_lt_out_lm (fi) (hfi : fi ∈ SI) (fo) (hfo : fo ∈ SO) :
    mo.toSyn (leading_monomial' mo fi (ne_of_mem_of_not_mem hfi zero_not_mem_SI))
    < mo.toSyn (leading_monomial' mo fo (ne_of_mem_of_not_mem hfo zero_not_mem_SO))
  /-- Each output element has distinct leading monomials. -/
  out_lm_diff (f) (hfo : f ∈ SO) (g) (hgo : g ∈ SO) :
    f ≠ g →
      leading_monomial' mo f (ne_of_mem_of_not_mem hfo zero_not_mem_SO) ≠
      leading_monomial' mo g (ne_of_mem_of_not_mem hgo zero_not_mem_SO)
  /-- The leading monomial of an output element `fo` is no more in the monomial set
  of input elements. -/
  out_lm_not_in_SI (fo) (hfo : fo ∈ SO) :
    leading_monomial' mo fo (ne_of_mem_of_not_mem hfo zero_not_mem_SO) ∉
    monomial_set SI
  /-- The leading monomial of an output element `fo` is no more in the monomial set
  of output elements with `fo` excluded. -/
  out_lm_not_in_other_SO (fo) (hfo : fo ∈ SO) :
    leading_monomial' mo fo (ne_of_mem_of_not_mem hfo zero_not_mem_SO) ∉
    monomial_set (SO.erase fo)
  /-- The leading coefficients of output elements are adjusted to 1. -/
  out_lc_one (fo) (hfo : fo ∈ SO) :
    leading_coeff' mo fo (ne_of_mem_of_not_mem hfo zero_not_mem_SO) = 1

/-- This eliminates the leading monomial of pivot `p` from the elements in `S`. -/
noncomputable def eliminate_lead_term {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (S : Finset (MvPolynomial σ K))
  (p : MvPolynomial σ K) (hp : p ≠ 0) :
    Finset (MvPolynomial σ K) :=
  let lmp := leading_monomial' mo p hp
  let lcp := p.coeff lmp
  let p1 := lcp⁻¹ • p
  S.image (fun f => f - (f.coeff lmp) • p1)

/-- The entire monomial set of pivot and polynomial set doesn't change after
leading monomial elimination. -/
lemma elim_pivot_monset_eq {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (S : Finset (MvPolynomial σ K))
  (p : MvPolynomial σ K) (hp : p ≠ 0) :
    monomial_set ((eliminate_lead_term mo S p hp) ∪ {p}) = monomial_set (S ∪ {p}) := by
  simp only [monomial_set, eliminate_lead_term]
  ext μ
  simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_image, Finset.mem_singleton,
    MvPolynomial.mem_support_iff]
  constructor
  · intro ⟨f, hpf, hμf⟩
    cases hpf with
    | inl hpf =>
      let ⟨g, g_mem_S, pfg_eq⟩ := hpf
      rw [sub_eq_iff_eq_add] at pfg_eq
      cases em (p.coeff μ = 0) with
      | inl pμ_eq_0 =>
        have : ¬g.coeff μ = 0 := by
          rw [pfg_eq]
          simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, pμ_eq_0,
            smul_eq_mul, mul_zero, add_zero]
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
      cases em (p.coeff μ = 0) with
      | inl pμ_eq_0 =>
        exists g - g.coeff (leading_monomial' mo p hp) • (p.coeff (leading_monomial' mo p hp))⁻¹ • p
        constructor
        · apply Or.inl
          exists g
        · simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, pμ_eq_0,
            smul_eq_mul, mul_zero, sub_zero]
          exact hμg
      | inr pμ_ne_0 =>
        exists p
        exact ⟨Or.inr rfl, pμ_ne_0⟩
    | inr g_eq_p =>
      subst g
      exists p
      exact ⟨Or.inr rfl, hμg⟩

/-- Leading monomial elimination monotonely decreases the size of set.
The set size decreases if the elimination results of two distinct elements
are equal, e.g. $x^2 + y + 1$ and $2x^2 + y + 2$ by $x^2 + 1$. -/
lemma elim_card_le {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (S : Finset (MvPolynomial σ K))
  (p : MvPolynomial σ K) (hp : p ≠ 0) :
    (eliminate_lead_term mo S p hp).card ≤ S.card := by
  let lmp := leading_monomial' mo p hp
  let lcp := p.coeff lmp
  let p1 := lcp⁻¹ • p
  let elim_fun (f : MvPolynomial σ K) : Finset _ := {f - (f.coeff lmp) • p1}
  have (f : MvPolynomial σ K) : (elim_fun f).card ≤ 1 := by simp [elim_fun]
  unfold eliminate_lead_term
  rw [← mul_one S.card, ← Finset.biUnion_singleton]
  exact Finset.card_biUnion_le_card_mul S (fun f => {f - (f.coeff lmp) • p1}) 1 (fun f _ => this f)

/-- The result of elimination is contained in the linear span of the set before elimination. -/
lemma elim_subset_span {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (S : Finset (MvPolynomial σ K))
  (p : MvPolynomial σ K) (hp : p ≠ 0) :
    SetLike.coe (eliminate_lead_term mo S p hp) ⊆
    (@Submodule.span K (MvPolynomial σ K) _ _ _ ({p} ∪ S)) := by
  intro f hf
  simp only [eliminate_lead_term, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hf
  let ⟨g, hg, hgf⟩ := hf
  simp only [Set.singleton_union, SetLike.mem_coe]
  subst hgf
  apply sub_mem
  · apply SetLike.mem_of_subset
    · apply Submodule.subset_span
    · simp_all
  · apply SMulMemClass.smul_mem
    apply SMulMemClass.smul_mem
    apply SetLike.mem_of_subset
    · apply Submodule.subset_span
    · simp_all

/-- A polynomial set is contained in the linear span of its elimination result. -/
lemma subset_span_elim {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (S : Finset (MvPolynomial σ K))
  (p : MvPolynomial σ K) (hp : p ≠ 0) :
    SetLike.coe S ⊆
    (@Submodule.span K (MvPolynomial σ K) _ _ _ ({p} ∪ eliminate_lead_term mo S p hp)) := by
  intro g hg
  let ec := (g.coeff (leading_monomial' mo p hp)) * (p.coeff (leading_monomial' mo p hp))⁻¹
  have g_sub_add : g = g - ec • p + ec • p := by simp
  have g_sub_mem : g - ec • p ∈ eliminate_lead_term mo S p hp := by
    unfold eliminate_lead_term
    simp only [Finset.mem_image]
    exists g
    constructor
    · exact hg
    · rw [← smul_assoc, smul_eq_mul]
  rw [g_sub_add]
  apply add_mem
  · apply Submodule.subset_span
    apply Or.inr g_sub_mem
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    apply Or.inl
    simp

/-- The linear span of a polynomial insertion is equal to that of insertion
of a nonzero scalar multiple. -/
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

/-- One step of Gaussian elimination. The loop continues as long as `ges.SI` is nonempty. -/
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
  have pivot_1_ne_0 : pivot_1 ≠ 0 :=
    smul_ne_zero (inv_ne_zero lc_pivot_ne_0) pivot_spec.choice_not_zero
  have lm_piv1_eq_lm_piv :
    leading_monomial' mo pivot_1 pivot_1_ne_0 =
    leading_monomial' mo pivot (pivot_spec.choice_not_zero) := by
    simp_all [pivot_1, leading_monomial']
  let SO := (eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero) ∪ {pivot_1}
  let SI0 := (eliminate_lead_term mo (ges.SI.erase pivot) pivot pivot_spec.choice_not_zero)
  let SI := SI0.erase 0
  have zero_not_mem_SI : 0 ∉ SI := by simp [SI]
  have zero_not_mem_SO : 0 ∉ SO := by
    simp only [Finset.mem_union, Finset.mem_singleton, not_or, SO]
    constructor
    · by_contra h_cont
      simp only [eliminate_lead_term, Finset.mem_image] at h_cont
      rcases h_cont with ⟨a, a_mem, ha⟩
      have key := ges.in_lm_lt_out_lm pivot pivot_spec.choice_mem a a_mem
      rw [sub_eq_zero, ← smul_assoc] at ha
      let C := a.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹
      have C_not_0 : C ≠ 0 := by
        unfold C lm_pivot
        by_contra HC
        rw [HC, zero_smul] at ha
        rw [ha] at a_mem
        exact ges.zero_not_mem_SO a_mem
      have keyc :=
        lm'_smul_eq_lm' mo pivot pivot_spec.choice_not_zero C C_not_0
      have keyc' :=
        lm'_eq_of_eq mo a (C • pivot) ha (ne_of_mem_of_not_mem a_mem ges.zero_not_mem_SO)
      apply ne_of_lt at key
      rw [keyc, ← keyc'] at key
      exact key rfl
    · push_neg
      unfold pivot_1
      symm
      exact smul_ne_zero (inv_ne_zero lc_pivot_ne_0) (pivot_spec.choice_not_zero)
  have lm_fi_lt_lm_piv (fi) (hfi : fi ∈ SI) :
    mo.toSyn (leading_monomial' mo fi (ne_of_mem_of_not_mem hfi zero_not_mem_SI)) <
    mo.toSyn lm_pivot := by
    unfold lm_pivot pivot
    simp only [eliminate_lead_term, Finset.mem_erase, ne_eq, Finset.mem_image, SI, SI0] at hfi
    let ⟨fi_ne_0, fi', ⟨fi'_ne_piv, fi'_mem_ges_SI⟩, hfi'⟩ := hfi
    have lm_piv_not_in_fi : fi.coeff lm_pivot = 0 := by
      rw [← hfi']
      simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, smul_eq_mul, lm_pivot]
      rw [inv_mul_cancel₀ lc_pivot_ne_0]
      simp
    rw [← MvPolynomial.notMem_support_iff] at lm_piv_not_in_fi
    have mo_fi : ∀ m ∈ fi.support, mo.toSyn m ≠ mo.toSyn lm_pivot := by
      intro m mem_fi
      simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]
      exact ne_of_mem_of_not_mem mem_fi lm_piv_not_in_fi
    let fi_supp_sub :=
      MvPolynomial.support_sub σ fi' (fi'.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹ • pivot)
    rw [hfi'] at fi_supp_sub
    have cont_1 :
      (fi'.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹ • pivot).support ⊆ pivot.support := by
      rw [← smul_assoc]
      apply MvPolynomial.support_smul
    have cont_2 :
      fi'.support ∪ (fi'.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹ • pivot).support ⊆
      fi'.support ∪ pivot.support := by
      apply Finset.union_subset_union
      · simp
      · exact cont_1
    have mo_fi' : ∀ m ∈ fi'.support, mo.toSyn m ≤ mo.toSyn lm_pivot := by
      let lm_fi'_le_lm_piv := pivot_spec.choice_max_lm fi' fi'_mem_ges_SI
      intro m mem_fi'
      unfold lm_pivot pivot
      have :
        mo.toSyn m ≤
        mo.toSyn
          (leading_monomial' mo fi'
            (ne_of_mem_of_not_mem fi'_mem_ges_SI ges.zero_not_mem_SI)) := by
        simp only [leading_monomial', max_monomial', AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe,
          AddEquiv.coe_toEquiv_symm, AddEquiv.apply_symm_apply]
        let map_mem_fi' := Finset.mem_map_of_mem (mo.toSyn.toEquiv).toEmbedding mem_fi'
        simp only [Equiv.toEmbedding_apply, AddEquiv.toEquiv_eq_coe] at map_mem_fi'
        apply Finset.le_max' _ (mo.toSyn m) map_mem_fi'
      exact le_trans this lm_fi'_le_lm_piv
    have mo_piv : ∀ m ∈ pivot.support, mo.toSyn m ≤ mo.toSyn lm_pivot := by
      intro m mem_piv
      simp only [leading_monomial', max_monomial', AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe,
        AddEquiv.coe_toEquiv_symm, AddEquiv.apply_symm_apply, lm_pivot]
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
    mo.toSyn lm_pivot <
    mo.toSyn (leading_monomial' mo fo (ne_of_mem_of_not_mem hfo zero_not_mem_SO)) := by
    have hfo' : fo ∈ eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero := by
      simp only [Finset.mem_union, Finset.mem_singleton, SO] at hfo
      exact Or.resolve_right hfo fo_ne_piv
    simp only [eliminate_lead_term, Finset.mem_image] at hfo'
    let ⟨a, a_mem, ha⟩ := hfo'
    rw [← smul_assoc] at ha
    let lm_piv_lt_lm_a := ges.in_lm_lt_out_lm pivot pivot_spec.choice_mem a a_mem
    let a_ss_piv_ne_0 := sub_smul_ne_0 mo pivot a
      pivot_spec.choice_not_zero
      (ne_of_mem_of_not_mem a_mem ges.zero_not_mem_SO)
      lm_piv_lt_lm_a
      (a.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹)
    let lm_ss_eq_lm_fo :=
      lm'_eq_of_eq mo
        (a - (a.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹) • pivot) fo ha a_ss_piv_ne_0
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
        rw [
          ← Finset.union_self {pivot_1},
          ← Finset.union_assoc _ {pivot_1} {pivot_1},
          Finset.union_comm
            (eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero ∪ {pivot_1}) {pivot_1},
          ← Finset.union_assoc _ {pivot_1} _,
          monomial_set_union_distrib, monomial_set_union_distrib, monomial_set_union_distrib]
      have pivot_mem : pivot ∈ ges.SI := by
        apply pivot_spec.choice_mem
      conv_rhs =>
        rw [
          ← ges.monset_fixed, ← Finset.insert_erase pivot_mem,
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
        simp only [singleton_monset_eq_support]
        exact MvPolynomial.support_smul_eq (inv_ne_zero lc_pivot_ne_0) pivot
      rw [piv1_piv_monset]
    span_V := by
      rw [← ges.span_V]
      apply Submodule.span_eq_span
      · apply Set.union_subset
        · unfold SI
          have cont_0 : SetLike.coe (SI0.erase 0) ⊆ SetLike.coe SI0 := by simp
          have cont_1 :
            SetLike.coe SI0 ⊆ @Submodule.span K (MvPolynomial σ K) _ _ _ ges.SI := by
            have : ges.SI = {pivot} ∪ ges.SI.erase pivot := by
              rw [← Finset.insert_eq]
              apply Eq.symm
              apply Finset.insert_erase pivot_spec.choice_mem
            rw [this]
            unfold SI0
            have :
              SetLike.coe ({pivot} ∪ ges.SI.erase pivot) =
              {pivot} ∪ SetLike.coe (ges.SI.erase pivot) := by simp
            rw [this]
            apply elim_subset_span mo (ges.SI.erase pivot) pivot pivot_spec.choice_not_zero
          have cont_2 :
            @Submodule.span K (MvPolynomial σ K) _ _ _ ges.SI ≤
            @Submodule.span K (MvPolynomial σ K) _ _ _ (↑ges.SI ∪ ↑ges.SO) := by
            apply Submodule.span_mono
            simp
          exact subset_trans (subset_trans cont_0 cont_1) cont_2
        · unfold SO
          rw [Finset.coe_union, Set.union_subset_iff]
          simp only [Finset.coe_singleton, Set.singleton_subset_iff, SetLike.mem_coe]
          constructor
          · have cont_0 : {pivot} ∪ SetLike.coe ges.SO ⊆ ges.SI ∪ ges.SO := by
              apply Set.union_subset_union (by simp; exact pivot_spec.choice_mem) (by simp)
            have cont_1 :
              SetLike.coe (eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero) ⊆
              Submodule.span K ({pivot} ∪ SetLike.coe ges.SO) := by
              apply elim_subset_span
            have cont_2 :
              @Submodule.span K (MvPolynomial σ K) _ _ _ ({pivot} ∪ SetLike.coe ges.SO) ≤
              Submodule.span K (↑ges.SI ∪ ↑ges.SO) := by
              apply Submodule.span_mono
              exact cont_0
            exact subset_trans cont_1 cont_2
          · unfold pivot_1
            apply SMulMemClass.smul_mem
            apply Submodule.subset_span
            apply Or.inl pivot_spec.choice_mem
      · have pivot_mp : (ges.SI \ {pivot}) ∪ {pivot} = ges.SI := by
          simp only [Finset.sdiff_union_self_eq_union, Finset.union_eq_left,
            Finset.singleton_subset_iff]
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
          rw [← Finset.coe_subset, Finset.coe_union, Finset.coe_union,
            Finset.coe_singleton] at cont_1
          have cont_2 :
            @Submodule.span K (MvPolynomial σ K) _ _ _ (SI0 ∪ SO) =
            Submodule.span K (SI ∪ SO) := by
            unfold SI
            rcases em (0 ∈ SI0) with h0 | h0
            · have : SetLike.coe (SI0.erase 0) ∪ {0} = SetLike.coe SI0 := by
                simp only [Finset.coe_erase, Set.union_singleton, Set.insert_diff_singleton,
                  Set.insert_eq_self, Finset.mem_coe]
                exact h0
              rw [← this, Set.union_right_comm]
              simp
            · rw [← Finset.erase_eq_self] at h0
              rw [h0]
          rw [← cont_2]
          calc
            SetLike.coe (ges.SI.erase pivot) ⊆
            @Submodule.span K (MvPolynomial σ K) _ _ _ ({pivot_1} ∪ SI0) := by
              unfold pivot_1 SI0
              exact cont_0
            _ ⊆ @Submodule.span K (MvPolynomial σ K) _ _ _ (SI0 ∪ SO) := by
              apply Submodule.span_mono cont_1
        · rw [Finset.coe_union, Set.union_subset_iff]
          constructor
          · simp only [Finset.coe_singleton, Set.singleton_subset_iff, SetLike.mem_coe]
            have : pivot_1 ∈ Submodule.span K (SI ∪ SO) := by
              apply Submodule.subset_span
              simp [SO]
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
            apply subset_trans cont_0
            rw [Set.union_comm]
            subst SO pivot_1
            apply Submodule.span_mono
            simp only [Set.union_singleton, Finset.coe_union, Finset.coe_singleton,
              Set.union_insert]
            apply Set.insert_subset_insert
            exact Set.subset_union_right
    in_lm_lt_out_lm := by
      intro fi hfi fo hfo
      cases em (fo = pivot_1) with
      | inl fo_eq_piv =>
        subst fo_eq_piv
        rw [lm_piv1_eq_lm_piv]
        exact lm_fi_lt_lm_piv fi hfi
      | inr fo_ne_piv =>
        exact lt_trans
          (lm_fi_lt_lm_piv fi hfi)
          (lm_piv_lt_lm_fo_ne_piv fo hfo fo_ne_piv)
    out_lm_diff := by
      intro f hfo g hgo hfg_ne
      cases em (f = pivot_1) with
      | inl f_eq_piv1 =>
        subst f_eq_piv1
        rw [lm_piv1_eq_lm_piv, ne_eq, ← AddEquiv.apply_eq_iff_eq mo.toSyn]
        push_neg
        apply ne_of_lt
        exact lm_piv_lt_lm_fo_ne_piv g hgo (Ne.symm hfg_ne)
      | inr f_ne_piv1 =>
        cases em (g = pivot_1) with
        | inl g_eq_piv1 =>
          rw [ne_comm]
          subst g_eq_piv1
          rw [lm_piv1_eq_lm_piv, ne_eq, ← AddEquiv.apply_eq_iff_eq mo.toSyn]
          push_neg
          apply ne_of_lt
          exact lm_piv_lt_lm_fo_ne_piv f hfo hfg_ne
        | inr g_ne_piv1 =>
          have hfo' : f ∈ eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero := by
            unfold SO at hfo
            simp only [Finset.mem_union, Finset.mem_singleton] at hfo
            exact Or.resolve_right hfo f_ne_piv1
          have hgo' : g ∈ eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero := by
            unfold SO at hgo
            simp only [Finset.mem_union, Finset.mem_singleton] at hgo
            exact Or.resolve_right hgo g_ne_piv1
          simp only [eliminate_lead_term, Finset.mem_image] at hfo' hgo'
          rcases hfo' with ⟨af, af_mem, haf⟩
          rcases hgo' with ⟨ag, ag_mem, hag⟩
          rw [← smul_assoc, eq_comm] at haf hag
          have lm_f_eq_lm_ss := lm'_eq_of_eq mo f _ haf (ne_of_mem_of_not_mem hfo zero_not_mem_SO)
          have lm_g_eq_lm_ss := lm'_eq_of_eq mo g _ hag (ne_of_mem_of_not_mem hgo zero_not_mem_SO)
          have lm_ss_eq_lm_af :=
            lm_sub_smul_eq_lm mo pivot af
              pivot_spec.choice_not_zero
              (ne_of_mem_of_not_mem af_mem ges.zero_not_mem_SO)
              (ges.in_lm_lt_out_lm pivot pivot_spec.choice_mem af af_mem)
              (af.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹)
          have lm_ss_eq_lm_ag :=
            lm_sub_smul_eq_lm mo pivot ag
              pivot_spec.choice_not_zero
              (ne_of_mem_of_not_mem ag_mem ges.zero_not_mem_SO)
              (ges.in_lm_lt_out_lm pivot pivot_spec.choice_mem ag ag_mem)
              (ag.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹)
          rw [lm_f_eq_lm_ss, lm_ss_eq_lm_af, lm_g_eq_lm_ss, lm_ss_eq_lm_ag]
          have af_ne_ag : af ≠ ag := by
            by_contra af_eq_ag
            subst af_eq_ag
            simp_all
          exact ges.out_lm_diff af af_mem ag ag_mem af_ne_ag
    out_lm_not_in_SI := by
      intro fo hfo
      have fo_ne_0 : fo ≠ 0 := ne_of_mem_of_not_mem hfo zero_not_mem_SO
      let lmfo := leading_monomial' mo fo fo_ne_0
      simp only [monomial_set, Finset.mem_biUnion, MvPolynomial.mem_support_iff, ne_eq, not_exists,
        not_and, Decidable.not_not]
      intro fi hfi
      let hfo_ := hfo
      simp only [Finset.mem_union, Finset.mem_singleton, SO] at hfo_
      cases em (fo = pivot_1) with
      | inl fo_eq_pivot_1 =>
        subst fo
        rw [lm_piv1_eq_lm_piv]
        apply coeff_zero_of_lt_lm mo
        simp only [lm_coe_lm' mo fi (ne_of_mem_of_not_mem hfi zero_not_mem_SI),
          WithBot.map_coe, WithBot.coe_lt_coe]
        exact lm_fi_lt_lm_piv fi hfi
      | inr fo_ne_pivot_1 =>
        have fo_mem_elim : fo ∈ eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero :=
          hfo_.resolve_right fo_ne_pivot_1
        simp only [eliminate_lead_term, Finset.mem_erase, ne_eq, Finset.mem_image, SI, SI0] at hfi
        rcases hfi with ⟨fi_ne_0, gi, ⟨gi_ne_piv, gi_mem_ges_SI⟩, hgi⟩
        have gi_ne_0 : gi ≠ 0 := ne_of_mem_of_not_mem gi_mem_ges_SI ges.zero_not_mem_SI
        rw [← hgi]
        simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, smul_eq_mul]
        have czero_1 : gi.coeff lmfo = 0 := by
          apply coeff_zero_of_lt_lm mo gi fo fo_ne_0
          simp only [lm_coe_lm' mo gi gi_ne_0, WithBot.map_coe, WithBot.coe_lt_coe]
          calc
            mo.toSyn (leading_monomial' mo gi gi_ne_0) ≤ mo.toSyn lm_pivot :=
              pivot_spec.choice_max_lm gi gi_mem_ges_SI
            _ < mo.toSyn (leading_monomial' mo fo fo_ne_0) :=
              lm_piv_lt_lm_fo_ne_piv fo hfo fo_ne_pivot_1
        have czero_2 : pivot.coeff lmfo = 0 := by
          apply coeff_zero_of_lt_lm mo pivot fo fo_ne_0
          simp only [lm_coe_lm' mo pivot pivot_spec.choice_not_zero,
            WithBot.map_coe, WithBot.coe_lt_coe]
          exact lm_piv_lt_lm_fo_ne_piv fo hfo fo_ne_pivot_1
        unfold lmfo at czero_1 czero_2
        simp [czero_1, czero_2]
    out_lm_not_in_other_SO := by
      intro fo hfo
      simp only [monomial_set, Finset.mem_biUnion, Finset.mem_erase, ne_eq,
        MvPolynomial.mem_support_iff, not_exists, not_and, Decidable.not_not, and_imp]
      intro go go_ne_fo hgo
      let hgo_ := hgo
      simp only [Finset.mem_union, Finset.mem_singleton, SO] at hgo_
      cases em (go = pivot_1) with
      | inl go_eq_pivot_1 =>
        subst go
        apply coeff_zero_of_lt_lm mo
        simp only [lm_coe_lm' mo pivot_1 pivot_1_ne_0, WithBot.map_coe, WithBot.coe_lt_coe]
        rw [lm_piv1_eq_lm_piv]
        exact lm_piv_lt_lm_fo_ne_piv fo hfo (by apply Ne.symm; exact go_ne_fo)
      | inr go_ne_pivot_1 =>
        have go_mem_elim : go ∈ eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero :=
          hgo_.resolve_right go_ne_pivot_1
        let hfo_ := hfo
        simp only [Finset.mem_union, Finset.mem_singleton, SO] at hfo_
        simp only [eliminate_lead_term, Finset.mem_image] at go_mem_elim
        rcases go_mem_elim with ⟨go', hgo', hgogo'⟩
        cases em (fo = pivot_1) with
        | inl fo_eq_pivot_1 =>
          subst fo
          rw [← hgogo', lm_piv1_eq_lm_piv]
          simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, smul_eq_mul]
          rw [inv_mul_cancel₀ lc_pivot_ne_0]
          simp
        | inr fo_ne_pivot_1 =>
          have fo_mem_elim : fo ∈ eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero :=
            hfo_.resolve_right fo_ne_pivot_1
          simp only [eliminate_lead_term, Finset.mem_image] at fo_mem_elim
          rcases fo_mem_elim with ⟨fo', hfo', hfofo'⟩
          have lm_fo_eq_lm_fo' :
            leading_monomial' mo fo (ne_of_mem_of_not_mem hfo zero_not_mem_SO) =
            leading_monomial' mo fo' (ne_of_mem_of_not_mem hfo' ges.zero_not_mem_SO) := by
            rw [lm'_eq_of_eq mo fo _ hfofo'.symm (ne_of_mem_of_not_mem hfo zero_not_mem_SO)]
            let key := lm_sub_smul_eq_lm mo pivot fo'
              pivot_spec.choice_not_zero
              (ne_of_mem_of_not_mem hfo' ges.zero_not_mem_SO)
              (ges.in_lm_lt_out_lm pivot pivot_spec.choice_mem fo' hfo')
              (fo'.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹)
            rw [← key]
            apply lm'_eq_of_eq mo
            rw [smul_assoc]
          simp only [lm_fo_eq_lm_fo', ← hgogo', MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
            smul_eq_mul]
          have :
            pivot.coeff
              (leading_monomial' mo fo'
                (ne_of_mem_of_not_mem hfo' ges.zero_not_mem_SO)) = 0 := by
            rw [← lm_fo_eq_lm_fo']
            apply coeff_zero_of_lt_lm mo pivot fo (ne_of_mem_of_not_mem hfo zero_not_mem_SO)
            simp only [lm_coe_lm' mo pivot pivot_spec.choice_not_zero, WithBot.map_coe,
              WithBot.coe_lt_coe]
            exact lm_piv_lt_lm_fo_ne_piv fo hfo fo_ne_pivot_1
          rw [this]
          simp only [mul_zero, sub_zero]
          have fo'_ne_go' : fo' ≠ go' := by
            by_contra fo_eq_go
            subst fo_eq_go
            rw [hfofo'] at hgogo'
            exact go_ne_fo hgogo'.symm
          let key := ges.out_lm_not_in_other_SO fo' hfo'
          simp only [monomial_set, Finset.mem_biUnion, Finset.mem_erase,
            MvPolynomial.mem_support_iff, not_exists, not_and, Decidable.not_not, and_imp] at key
          exact key go' fo'_ne_go'.symm hgo'
    out_lc_one := by
      intro fo hfo
      cases em (fo = pivot_1) with
      | inl fo_eq_piv1 =>
        subst fo_eq_piv1
        unfold leading_coeff'
        rw [lm_piv1_eq_lm_piv]
        simp only [pivot_1, MvPolynomial.coeff_smul, lm_pivot]
        exact inv_mul_cancel₀ lc_pivot_ne_0
      | inr fo_ne_piv1 =>
        unfold leading_coeff'
        have hfo' : fo ∈ eliminate_lead_term mo ges.SO pivot pivot_spec.choice_not_zero := by
          unfold SO at hfo
          simp only [Finset.mem_union, Finset.mem_singleton] at hfo
          exact Or.resolve_right hfo fo_ne_piv1
        simp only [eliminate_lead_term, Finset.mem_image] at hfo'
        let ⟨af, af_mem, haf⟩ := hfo'
        rw [← smul_assoc, eq_comm] at haf
        let lm_fo_eq_lm_ss := lm'_eq_of_eq mo fo _ haf (ne_of_mem_of_not_mem hfo zero_not_mem_SO)
        let lm_ss_eq_lm_af := lm_sub_smul_eq_lm mo pivot af
          pivot_spec.choice_not_zero
          (ne_of_mem_of_not_mem af_mem ges.zero_not_mem_SO)
          (ges.in_lm_lt_out_lm pivot pivot_spec.choice_mem af af_mem)
          (af.coeff lm_pivot • (pivot.coeff lm_pivot)⁻¹)
        rw [lm_fo_eq_lm_ss, lm_ss_eq_lm_af, haf]
        have piv_coeff_af_eq_0 :
          pivot.coeff
            (leading_monomial' mo af
              (ne_of_mem_of_not_mem af_mem ges.zero_not_mem_SO)) = 0 := by
          rw [← MvPolynomial.notMem_support_iff]
          by_contra H
          unfold leading_monomial' max_monomial' at H
          rw [AddEquiv.invFun_eq_symm, ← Finset.mem_map' mo.toSyn.toEmbedding] at H
          rw [Equiv.toEmbedding_apply] at H
          have key (x) : mo.toSyn.toEquiv (mo.toSyn.symm x) = x := by simp_all
          rw [key] at H
          simp only [AddEquiv.toEquiv_eq_coe] at H
          have le_cont :
            mo.toSyn
              (leading_monomial' mo af
                (ne_of_mem_of_not_mem af_mem ges.zero_not_mem_SO)) ≤
            mo.toSyn lm_pivot := by
            unfold lm_pivot leading_monomial' max_monomial'
            rw [AddEquiv.invFun_eq_symm]
            simp only [AddEquiv.apply_symm_apply mo.toSyn]
            exact Finset.le_max' _ _ H
          have gt_cont :
            mo.toSyn lm_pivot <
            mo.toSyn
              (leading_monomial' mo af
                (ne_of_mem_of_not_mem af_mem ges.zero_not_mem_SO)) := by
            exact ges.in_lm_lt_out_lm pivot pivot_spec.choice_mem af af_mem
          exact not_le_of_gt gt_cont le_cont
        simp only [smul_eq_mul, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul]
        rw [piv_coeff_af_eq_0]
        simp only [mul_zero, sub_zero]
        exact ges.out_lc_one af af_mem
  }

/-- Termination proof for Gaussian elimination. The size of `ges.SI` decreases
by 1 in each step: popping pivot from `ges.SI` and pushing its normalization
of leading coefficient into `ges.SO`. -/
lemma ges_SI_card_decr {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (M : Finset (σ →₀ ℕ)) (V : Submodule K (MvPolynomial σ K))
  (ges : GEStruct σ K mo M V) (SI_nonempty : ges.SI.Nonempty) :
    (gaussian_elim_step mo M V ges SI_nonempty).SI.card < ges.SI.card := by -- termination proof
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

/-- Recursive definition of Gaussian elimination. -/
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
          rw [Finset.not_nonempty_iff_eq_empty] at SI_nonempty
          let prev_monset_fixed := ges.monset_fixed
          simp only [SI_nonempty, Finset.empty_union] at prev_monset_fixed
          simp [prev_monset_fixed]
        span_V := by
          have prev_span_V : Submodule.span K (↑ges.SI ∪ ↑ges.SO) = V := ges.span_V
          rw [Finset.not_nonempty_iff_eq_empty] at SI_nonempty
          rw [SI_nonempty] at prev_span_V
          exact prev_span_V
        in_lm_lt_out_lm := by
          intro fi hfi
          trivial
        out_lm_not_in_SI := by
          unfold monomial_set
          simp
        out_lm_not_in_other_SO := ges.out_lm_not_in_other_SO
        out_lm_diff := ges.out_lm_diff
        out_lc_one := ges.out_lc_one
      }
termination_by ges.SI.card
decreasing_by apply ges_SI_card_decr

/-- Initial `GEStruct` object to iterate through `gaussian_elim_rec`. -/
noncomputable def ges_init {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (input : Finset (MvPolynomial σ K)) :
    GEStruct σ K mo (monomial_set input) (Submodule.span K input) :=
  {
    SI := input.erase 0
    SO := ∅
    zero_not_mem_SI := by simp
    zero_not_mem_SO := by simp
    monset_fixed := by
      rw [Finset.union_empty]
      apply monomial_set_erase_zero
    span_V := by simp
    in_lm_lt_out_lm := by
      intro _ _ fo hfo
      trivial
    out_lm_not_in_SI := by simp
    out_lm_not_in_other_SO := by simp
    out_lm_diff := by
      intro f hf
      trivial
    out_lc_one := by
      intro fo hfo
      trivial
  }

/-- Wrapper definition of Gaussian elimination. -/
noncomputable def gaussian_elim {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (input : Finset (MvPolynomial σ K)) :
    GEStruct σ K mo (monomial_set input) (Submodule.span K input) :=
  gaussian_elim_rec mo (monomial_set input) (Submodule.span K input) (ges_init mo input)

/-- Auxiliary induction argument for `gaussian_elim_SI_empty`. -/
lemma gaussian_elim_rec_SI_empty {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (M : Finset (σ →₀ ℕ)) (V : Submodule K (MvPolynomial σ K)) :
    ∀ n : ℕ, ∀ (ges : GEStruct σ K mo M V),
      ges.SI.card = n → (gaussian_elim_rec mo M V ges).SI = ∅ := by
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

/-- The termination condition of `gaussian_elim`. -/
lemma gaussian_elim_SI_empty {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (input : Finset (MvPolynomial σ K)) :
    (gaussian_elim mo input).SI = ∅ := by
  unfold gaussian_elim
  exact gaussian_elim_rec_SI_empty mo
    (monomial_set input)
    (Submodule.span K ↑input)
    ((ges_init mo input).SI.card)
    (ges_init mo input)
    rfl

/-- For any element `f ≠ 0` in the linear span `⟨H⟩_K` of finite polynomial set `H`,
there exists `n` in the Gaussian elimination of `H` which has the same leading monomial
with `f`. -/
lemma mem_span_ge_exists_same_lm_mem {σ K : Type*} [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (H : Finset (MvPolynomial σ K)) :
    let ge_H := gaussian_elim mo H
    ∀ f ∈ (Submodule.span K ↑ge_H.SO : Submodule K (MvPolynomial σ K)),
      (f_ne_0 : f ≠ 0) →
        ∃ n, ∃ (hn : n ∈ ge_H.SO),
          leading_monomial' mo f f_ne_0 =
          leading_monomial' mo n (ne_of_mem_of_not_mem hn ge_H.zero_not_mem_SO) := by
  intro ge_H f hf f_ne_0
  rw [Submodule.mem_span_finset] at hf
  rcases hf with ⟨φ, φ_in_ge, φ_sum_f⟩
  let lmf := leading_monomial' mo f f_ne_0
  have coeff_eq : ∑ a ∈ ge_H.SO, φ a • a.coeff lmf = f.coeff lmf := by
    conv_rhs => rw [← φ_sum_f]
    simp [MvPolynomial.coeff_sum]
  have φ_eq (h) :
    φ h =
      if hh : h ∈ ge_H.SO
        then f.coeff (leading_monomial' mo h (ne_of_mem_of_not_mem hh ge_H.zero_not_mem_SO))
        else 0 := by
    split_ifs with hh
    · rw [← φ_sum_f]
      simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul]
      have sum_ie :
        ∑ x ∈ ge_H.SO,
          φ x *
            x.coeff (leading_monomial' mo h (ne_of_mem_of_not_mem hh ge_H.zero_not_mem_SO)) =
        ∑ x ∈ insert h (ge_H.SO.erase h),
          φ x *
            x.coeff (leading_monomial' mo h (ne_of_mem_of_not_mem hh ge_H.zero_not_mem_SO)) := by
        unfold Finset.sum
        rw [Finset.insert_erase hh]
      simp only [sum_ie, Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true,
        Finset.sum_insert]
      let lch_eq_1 := ge_H.out_lc_one h hh
      unfold leading_coeff' at lch_eq_1
      simp only [lch_eq_1, mul_one, left_eq_add]
      apply Finset.sum_eq_zero
      intro x hx
      have key := ge_H.out_lm_not_in_other_SO h hh
      unfold monomial_set at key
      have :
        x.coeff (leading_monomial' mo h (ne_of_mem_of_not_mem hh ge_H.zero_not_mem_SO)) = 0 := by
        contrapose key
        push_neg at key
        rw [← MvPolynomial.mem_support_iff] at key
        push_neg
        have key' :=
          @Finset.subset_biUnion_of_mem (MvPolynomial σ K) (σ →₀ ℕ)
            (ge_H.SO.erase h) _
            MvPolynomial.support x hx
        exact key' key
      simp [this]
    · simp only [Function.support_subset_iff, ne_eq, Finset.mem_coe] at φ_in_ge
      let key := φ_in_ge h
      rw [← not_imp_not, Decidable.not_not] at key
      exact key hh
  have φ_eq' :
    φ =
      fun h =>
        if hh : h ∈ ge_H.SO
          then f.coeff (leading_monomial' mo h (ne_of_mem_of_not_mem hh ge_H.zero_not_mem_SO))
          else 0 := by
    ext h
    exact φ_eq h
  have lcf_ne_0 := lc_not_zero mo f f_ne_0
  unfold leading_coeff' at lcf_ne_0
  rw [← coeff_eq] at lcf_ne_0
  apply Finset.exists_ne_zero_of_sum_ne_zero at lcf_ne_0
  rcases lcf_ne_0 with ⟨n, hn, φ_lcn_ne_0⟩
  exists n, hn
  have :
    φ n = f.coeff (leading_monomial' mo n (ne_of_mem_of_not_mem hn ge_H.zero_not_mem_SO)) := by
    simp only [φ_eq']
    split_ifs with hn'
    · rfl
    · by_contra _
      exact hn' hn
  simp only [this, smul_eq_mul, ne_eq, mul_eq_zero, not_or] at φ_lcn_ne_0
  rcases φ_lcn_ne_0 with ⟨fc_lmn_ne_0, nc_lmf_ne_0⟩
  unfold lmf at nc_lmf_ne_0
  rw [← AddEquiv.apply_eq_iff_eq mo.toSyn]
  apply le_antisymm
  · conv_rhs =>
      unfold leading_monomial' max_monomial'
      simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
        AddEquiv.apply_symm_apply]
    apply Finset.le_max'
    simp [nc_lmf_ne_0]
  · conv_rhs =>
      unfold leading_monomial' max_monomial'
      simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
        AddEquiv.apply_symm_apply]
    apply Finset.le_max'
    simp [fc_lmn_ne_0]
