import FaugereF4.MonomialIdeal
import Mathlib.RingTheory.SimpleRing.Principal

/-
theorem MonomialOrder.div_set {σ : Type u_1} {m : MonomialOrder σ}
  {R : Type u_2} [CommRing R] {B : Set (MvPolynomial σ R)}
  (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b)) (f : MvPolynomial σ R) :
  ∃ (g : ↑B →₀ MvPolynomial σ R) (r : MvPolynomial σ R),
    f = (Finsupp.linearCombination (MvPolynomial σ R) fun (b : ↑B) => ↑b) g + r ∧
    (∀ (b : ↑B), m.toSyn (m.degree (↑b * g b)) ≤ m.toSyn (m.degree f)) ∧
    ∀ c ∈ r.support, ∀ b ∈ B, ¬m.degree b ≤ c
-/

/-
Division of a mvpoly by a list of mvpoly's (in an arbitrarily fixed order)
The struct must hold the dividend f and divisors F = [f0, f1, ..., f(n-1)]
==> What do we want as data and loop invariants?
(1) quotients Q = [q0, q1, ..., q(n-1)] & remainder r in that step
(2) f = ∑ fi * qi + r in each step
(3) the monomial μ ∈ r.support concerning in that step
    i.e. we search for the first qi ∈ Q whose leading monomial divides μ
(4) ∀ i, lm(fi * qi) ≤ lm(f)
-/

-- universe u v w

/-- Well-foundedness of the `WithBot`-extension of a monomial order.
This is used for the termination proof of multivariate polynomial division algorithm. -/
instance withbot_mo_syn_wf {σ : Type*} (mo : MonomialOrder σ) :
    WellFoundedRelation (WithBot mo.syn) :=
  WellFoundedLT.toWellFoundedRelation

/-- The structure to iterate through multivariate polynomial division algorithm. -/
structure MvPolyDivStruct
  (σ K : Type*) [DecidableEq σ] [Field K] [DecidableEq K] (mo : MonomialOrder σ)
  (f : MvPolynomial σ K) (F : List (MvPolynomial σ K)) (hF : 0 ∉ F) (F_Nodup : F.Nodup) where
  /-- list of quotient polynomials until then -/
  Q : List (MvPolynomial σ K)
  /-- The lengths of divisor list and quotient list are equal. -/
  FQ_len_eq : F.length = Q.length
  /-- The terms fixed as the remainder. -/
  r : MvPolynomial σ K
  /-- Remaining terms to be determined whether divisible.
  Here, LM(`p`) decreases under `mo`. -/
  p : MvPolynomial σ K
  /-- Current quotient-remainder sum representation of `f`. -/
  f_eq_FQ_r : f = ∑ i : Fin (F.length), F[i] * Q[i] + r + p
  /-- The sum representation above is standard,
  i.e. no summands have leading monomial preceding that of `f`. -/
  lm_summand_le_lmf (i : Fin (F.length)) :
    WithBot.map mo.toSyn (leading_monomial mo (F[i] * Q[i])) ≤
    WithBot.map mo.toSyn (leading_monomial mo f)
  /-- LM(`r`) doesn't exceed LM(`f`). -/
  lmr_le_lmf :
    WithBot.map mo.toSyn (leading_monomial mo r) ≤
    WithBot.map mo.toSyn (leading_monomial mo f)
  /-- LM(`p`) doesn't exceed LM(`f`). -/
  lmp_le_lmf :
    WithBot.map mo.toSyn (leading_monomial mo p) ≤
    WithBot.map mo.toSyn (leading_monomial mo f)
  /-- The terms in r are no more divisible by leading monomials in Q. -/
  r_not_divisible (fi) (hfi : fi ∈ F) :
    ∀ μ ∈ r.support, ¬leading_monomial' mo fi (ne_of_mem_of_not_mem hfi hF) ≤ μ

/-- One iteration step of multivariate polynomial division algorithm. -/
noncomputable def mvpoly_division_step {σ K : Type*}
  [DecidableEq σ] [Field K] [DecidableEq K] (mo : MonomialOrder σ)
  (f : MvPolynomial σ K) (F : List (MvPolynomial σ K)) (hF : 0 ∉ F) (F_Nodup : F.Nodup)
  (mpds : MvPolyDivStruct σ K mo f F hF F_Nodup)
  (p_ne_0 : mpds.p ≠ 0) : MvPolyDivStruct σ K mo f F hF F_Nodup :=
  have mem_F_ne_0 : ∀ fi ∈ F, fi ≠ 0 := by
    intro fi fi_mem_F
    exact ne_of_mem_of_not_mem fi_mem_F hF
  have f_ne_0 : f ≠ 0 := by
    by_contra f_eq_0
    have lmp_le_lmf := mpds.lmp_le_lmf
    subst f
    rw [lm_coe_lm' mo mpds.p p_ne_0] at lmp_le_lmf
    rw [lm_zero_eq_bot mo] at lmp_le_lmf
    simp only [WithBot.map_coe, WithBot.map_bot, le_bot_iff, WithBot.coe_ne_bot] at lmp_le_lmf
  let lmp := leading_monomial' mo mpds.p p_ne_0
  let lcp := mpds.p.coeff lmp
  have lcp_ne_0 : lcp ≠ 0 := by exact lc_not_zero mo mpds.p p_ne_0
  let ltp := MvPolynomial.monomial lmp lcp
  -- Search for the first entry in `F` whose leading monomial divides
  -- the leading monomial of `mpds.p`.
  let odi : Option (Fin F.length) :=
    Fin.find?
      (fun (i : Fin F.length) =>
        leading_monomial' mo F[i]
          (mem_F_ne_0 F[i] (by simp only [Fin.getElem_fin, List.getElem_mem])) ≤
          lmp)
  match odi_eq : odi with
  | none =>
    -- No such entry in `F`.
    -- Then simply exclude the leading term from `mpds.p`...
    -- and add it to the remainder `mpds.r`.
    have none_div := Fin.find?_eq_none_iff.mp odi_eq
    have lmltp_le_lmf :
      WithBot.map (⇑mo.toSyn) (leading_monomial mo ltp) ≤
      WithBot.map (⇑mo.toSyn) (leading_monomial mo f) := by
      conv_lhs =>
        simp only [leading_monomial, max_monomial, AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe,
          AddEquiv.coe_toEquiv_symm, MvPolynomial.support_monomial, lcp_ne_0, ↓reduceIte,
          Finset.map_singleton, Equiv.coe_toEmbedding, EquivLike.coe_coe, Finset.max_singleton,
          WithBot.map_coe, AddEquiv.symm_apply_apply, ltp]
      have prev_lmp_le_lmf := mpds.lmp_le_lmf
      simp only [lm_coe_lm' mo mpds.p p_ne_0, WithBot.map_coe] at prev_lmp_le_lmf
      exact prev_lmp_le_lmf
    {
      Q := mpds.Q
      FQ_len_eq := mpds.FQ_len_eq
      r := mpds.r + ltp
      p := mpds.p - ltp
      f_eq_FQ_r := by
        ring_nf
        exact mpds.f_eq_FQ_r
      lm_summand_le_lmf := mpds.lm_summand_le_lmf
      lmr_le_lmf := by
        apply lm_add_le_of_both_lm_le mo mpds.r ltp f
        · exact mpds.lmr_le_lmf
        · exact lmltp_le_lmf
      lmp_le_lmf := by
        rw [sub_eq_add_neg]
        apply lm_add_le_of_both_lm_le mo mpds.p (-ltp) f
        · exact mpds.lmp_le_lmf
        · conv_lhs =>
            rw [← neg_one_smul K ltp]
            rw [
              ← lm_smul_eq_lm mo ltp (-1 : K)
                (by simp only [ne_eq, neg_eq_zero, one_ne_zero, not_false_eq_true])]
          exact lmltp_le_lmf
      r_not_divisible := by
        intro fi fi_mem_F μ μ_supp_r
        apply MvPolynomial.support_add at μ_supp_r
        simp only [Finset.mem_union] at μ_supp_r
        cases μ_supp_r with
        | inl μ_supp_prevr =>
          exact mpds.r_not_divisible fi fi_mem_F μ μ_supp_prevr
        | inr μ_eq_lmp =>
          subst ltp
          rw [MvPolynomial.support_monomial] at μ_eq_lmp
          simp only [lcp_ne_0, ↓reduceIte, Finset.mem_singleton] at μ_eq_lmp
          subst μ
          rw [List.mem_iff_getElem] at fi_mem_F
          rcases fi_mem_F with ⟨i, hi, Fi_eq_fi⟩
          subst fi
          exact none_div {val := i, isLt := hi} |> of_decide_eq_false
    }
  | some di =>
    -- The entry is found in `di`'th entry.
    -- Then subtract `LT(mpds.p) / LT(F[di]) * F[di]` from `mpds.p`
    -- so that the leading term is eliminated from `mpds.p`.
    -- The multiplying term `LT(mpds.p) / LT(F[di])` is then added to `Q[di]`.
    let fdi := F[di]
    have fdi_mem_F : fdi ∈ F := by
      unfold fdi
      simp only [Fin.getElem_fin, List.getElem_mem]
    have fdi_ne_0 : fdi ≠ 0 := ne_of_mem_of_not_mem fdi_mem_F hF
    let lmfdi := leading_monomial' mo fdi fdi_ne_0
    let lcfdi := fdi.coeff lmfdi
    let ltfdi := MvPolynomial.monomial lmfdi lcfdi
    have lmfdi_div_lmp : lmfdi ≤ lmp := by
      unfold odi at odi_eq
      simp only [Fin.getElem_fin, Fin.find?_eq_some_iff] at odi_eq
      exact odi_eq.1 |> of_decide_eq_true
    let qi_term := MvPolynomial.monomial (lmp - lmfdi) (lcp / lcfdi)
    have qi_term_c_ne_0 : lcp / lcfdi ≠ 0 := by
      simp only [ne_eq, div_eq_zero_iff, not_or]
      push_neg
      constructor
      · exact lc_not_zero mo mpds.p p_ne_0
      · exact lc_not_zero mo fdi fdi_ne_0
    let Q := mpds.Q.modify di (· + qi_term)
    have FQ_len_eq : F.length = Q.length := by
      conv_lhs => rw [mpds.FQ_len_eq]
      simp only [Q, List.length_modify]
    have fdi_qiterm_mul_ne_0 : fdi * qi_term ≠ 0 := by
      apply mul_ne_zero
      · exact fdi_ne_0
      · simp only [ne_eq, MvPolynomial.monomial_eq_zero, div_eq_zero_iff, not_or, qi_term,
          lcfdi, lcp]
        constructor
        · exact lc_not_zero mo mpds.p p_ne_0
        · exact lc_not_zero mo fdi fdi_ne_0
    have lmfqi_eq_lmp :
      leading_monomial' mo (fdi * qi_term) fdi_qiterm_mul_ne_0 = lmp := by
      rw [lm'_monmul_commute mo F[di] fdi_ne_0 (lmp - lmfdi) (lcp / lcfdi) qi_term_c_ne_0]
      rw [add_comm]
      subst lmfdi
      exact tsub_add_cancel_of_le lmfdi_div_lmp
    have lmfqi_le_lmf :
      WithBot.map (⇑mo.toSyn) (leading_monomial mo (fdi * qi_term)) ≤
      WithBot.map (⇑mo.toSyn) (leading_monomial mo f) := by
      subst fdi
      conv_lhs =>
        rw [lm_coe_lm' mo (F[di] * qi_term) fdi_qiterm_mul_ne_0]
      rw [lm_coe_lm' mo f f_ne_0]
      conv_lhs => rw [lmfqi_eq_lmp]
      rw [← lm_coe_lm' mo mpds.p p_ne_0, ← lm_coe_lm' mo f f_ne_0]
      exact mpds.lmp_le_lmf
    {
      Q := Q
      FQ_len_eq := FQ_len_eq
      r := mpds.r
      p := mpds.p - fdi * qi_term
      f_eq_FQ_r := by
        conv_lhs => rw [mpds.f_eq_FQ_r]
        let prevFQ_map :=
          fun i : Fin F.length => F[i] * mpds.Q[i]'(by rw [← mpds.FQ_len_eq]; exact i.isLt)
        let FQ_map :=
          fun i : Fin F.length => F[i] * Q[i]'(by rw [← FQ_len_eq]; exact i.isLt)
        have FQ_list_eq :
          List.ofFn FQ_map = (List.ofFn prevFQ_map).modify di (· + fdi * qi_term) := by
          unfold FQ_map prevFQ_map Q
          apply List.ext_getElem
          · simp only [Fin.getElem_fin, List.length_ofFn, List.length_modify]
          · intro j hj1 hj2
            cases em (j = di) with
            | inl j_eq_di =>
              subst j fdi
              simp only [Fin.getElem_fin, List.getElem_ofFn, List.getElem_modify_eq]
              ring_nf
            | inr j_ne_di =>
              push_neg at j_ne_di
              have j_lt_F_len : j < F.length := by
                simp only [Fin.getElem_fin, List.length_ofFn] at hj1
                exact hj1
              have j_lt_Q_len : j < mpds.Q.length := by
                rw [mpds.FQ_len_eq] at j_lt_F_len
                exact j_lt_F_len
              simp only [Fin.getElem_fin, List.getElem_ofFn]
              rw [
                List.getElem_modify_ne
                  (· + qi_term) mpds.Q j_ne_di.symm
                  (by simp only [List.length_modify, j_lt_Q_len])]
              conv_rhs =>
                simp only [
                  List.getElem_modify_ne (· + fdi * qi_term) _ j_ne_di.symm,
                  List.getElem_ofFn]
        rw [← Fin.sum_ofFn prevFQ_map]
        rw [← Fin.sum_ofFn FQ_map, FQ_list_eq]
        rw [← List.sum_take_add_sum_drop (List.ofFn prevFQ_map) di]
        rw [List.modify_eq_take_drop]
        rw [
          ← List.getElem_cons_drop
            (by simp only [Fin.getElem_fin, List.length_ofFn, Fin.is_lt, prevFQ_map]),
          List.sum_cons]
        conv_rhs => rw [List.sum_append, List.modifyHead_cons, List.sum_cons]
        ring
      lmr_le_lmf := mpds.lmr_le_lmf
      lmp_le_lmf := by
        rw [sub_eq_add_neg]
        apply lm_add_le_of_both_lm_le mo mpds.p (-(fdi  * qi_term)) f
        · exact mpds.lmp_le_lmf
        · rw [← neg_one_smul K _]
          rw [
            ← lm_smul_eq_lm mo _ (-1 : K)
              (by simp only [ne_eq, neg_eq_zero, one_ne_zero, not_false_eq_true])]
          exact lmfqi_le_lmf
      lm_summand_le_lmf := by
        intro ⟨i, hi⟩
        subst Q
        cases em (i = di) with
        | inl i_eq_di =>
          simp only [i_eq_di, Fin.eta, Fin.getElem_fin, List.getElem_modify_eq, ge_iff_le]
          rw [left_distrib]
          apply lm_add_le_of_both_lm_le mo
            (F[di] * mpds.Q[di]'(by rw [← i_eq_di, ← mpds.FQ_len_eq]; exact hi))
            (F[di] * qi_term)
            f
          · exact mpds.lm_summand_le_lmf di
          · exact lmfqi_le_lmf
        | inr i_ne_di =>
          push_neg at i_ne_di
          simp only [Fin.getElem_fin, ge_iff_le]
          rw [List.getElem_modify_ne _ _ i_ne_di.symm]
          exact mpds.lm_summand_le_lmf ⟨i, hi⟩
      r_not_divisible := mpds.r_not_divisible
    }

/-- The termination proof of multivariate polynomial division algorithm.
This proves that the leading monomial of `mpds.p` strictly decreases
in each step of division, under the fixed monomial order. -/
lemma mvpoly_division_lmp_decr {σ K : Type*}
  [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (f : MvPolynomial σ K) (F : List (MvPolynomial σ K)) (hF : 0 ∉ F) (F_Nodup : F.Nodup)
  (mpds : MvPolyDivStruct σ K mo f F hF F_Nodup)
  (p_ne_0 : mpds.p ≠ 0) :
    WithBot.map mo.toSyn
      (leading_monomial mo (mvpoly_division_step mo f F hF F_Nodup mpds p_ne_0).p) <
    WithBot.map mo.toSyn
      (leading_monomial mo mpds.p) := by
  unfold mvpoly_division_step
  have mem_F_ne_0 : ∀ fi ∈ F, fi ≠ 0 := by
    intro fi fi_mem_F
    exact ne_of_mem_of_not_mem fi_mem_F hF
  have f_ne_0 : f ≠ 0 := by
    by_contra f_eq_0
    have lmp_le_lmf := mpds.lmp_le_lmf
    subst f
    rw [lm_coe_lm' mo mpds.p p_ne_0] at lmp_le_lmf
    rw [lm_zero_eq_bot mo] at lmp_le_lmf
    simp only [WithBot.map_coe, WithBot.map_bot, le_bot_iff, WithBot.coe_ne_bot] at lmp_le_lmf
  let lmp := leading_monomial' mo mpds.p p_ne_0
  let lcp := mpds.p.coeff lmp
  have lcp_ne_0 : lcp ≠ 0 := by exact lc_not_zero mo mpds.p p_ne_0
  let ltp := MvPolynomial.monomial lmp lcp
  let odi : Option (Fin F.length) :=
    Fin.find?
      (fun (i : Fin F.length) =>
        leading_monomial' mo F[i]
          (mem_F_ne_0 F[i] (by simp only [Fin.getElem_fin, List.getElem_mem])) ≤
          lmp)
  simp_all only [ne_eq, Fin.getElem_fin, gt_iff_lt]
  split
  next odi_eq =>
    have none_div := Fin.find?_eq_none_iff.mp odi_eq
    have lmltp_le_lmp :
      WithBot.map (⇑mo.toSyn) (leading_monomial mo ltp) ≤
      WithBot.map (⇑mo.toSyn) (leading_monomial mo mpds.p) := by
      conv_lhs =>
        simp only [leading_monomial, max_monomial, AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe,
          AddEquiv.coe_toEquiv_symm, MvPolynomial.support_monomial, lcp_ne_0, ↓reduceIte,
          Finset.map_singleton, Equiv.coe_toEmbedding, EquivLike.coe_coe, Finset.max_singleton,
          WithBot.map_coe, AddEquiv.symm_apply_apply, ltp]
      simp only [leading_monomial', max_monomial', AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe,
        AddEquiv.coe_toEquiv_symm, AddEquiv.apply_symm_apply, lm_coe_lm' mo mpds.p p_ne_0,
        WithBot.map_coe, le_refl, lmp]
    simp only [gt_iff_lt]
    cases em (mpds.p - ltp = 0) with
    | inl p_sub_ltp_eq_0 =>
      subst ltp lcp lmp
      simp only [p_sub_ltp_eq_0, lm_zero_eq_bot, WithBot.map_bot, lm_coe_lm' mo mpds.p p_ne_0,
        WithBot.map_coe, WithBot.bot_lt_coe]
    | inr p_sub_ltp_ne_0 =>
      apply lt_of_le_of_ne
      · rw [sub_eq_add_neg]
        apply lm_add_le_of_both_lm_le mo mpds.p (-ltp) mpds.p
        · rfl
        · rw [← neg_one_smul K _]
          rw [
            ← lm_smul_eq_lm mo _ (-1 : K)
              (by simp only [ne_eq, neg_eq_zero, one_ne_zero, not_false_eq_true])]
          exact lmltp_le_lmp
      · push_neg at p_sub_ltp_ne_0
        have key :=
          Finset.max'_mem
            (Finset.map mo.toSyn.toEmbedding (mpds.p - ltp).support)
            (by simp only [AddEquiv.toEquiv_eq_coe, Finset.map_nonempty,
              MvPolynomial.support_nonempty, ne_eq, p_sub_ltp_ne_0, not_false_eq_true])
        unfold ltp lcp lmp at p_sub_ltp_ne_0
        simp only [lm_coe_lm' mo _ p_sub_ltp_ne_0, WithBot.map_coe, lm_coe_lm' mo mpds.p p_ne_0,
          ne_eq, WithBot.coe_inj, EmbeddingLike.apply_eq_iff_eq]
        by_contra HC
        have key' : (mpds.p - ltp).coeff lmp = 0 := by
          unfold ltp lcp
          simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, ↓reduceIte, sub_self]
        rw [← MvPolynomial.notMem_support_iff] at key'
        conv_lhs at HC =>
          rw [leading_monomial', max_monomial']
          simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm]
        simp only [← AddEquiv.apply_eq_iff_eq mo.toSyn, AddEquiv.apply_symm_apply] at HC
        unfold lmp at key'
        rw [← Finset.mem_map' mo.toSyn.toEmbedding, Equiv.toEmbedding_apply,
          AddEquiv.toEquiv_eq_coe] at key'
        unfold ltp lcp lmp at key
        simp only [EquivLike.coe_coe, ltp, lcp, lmp] at key'
        rw [← HC] at key'
        exact key' key
  next di odi_eq =>
    let fdi := F[di]
    have fdi_mem_F : fdi ∈ F := by
      unfold fdi
      simp only [Fin.getElem_fin, List.getElem_mem]
    have fdi_ne_0 : fdi ≠ 0 := ne_of_mem_of_not_mem fdi_mem_F hF
    let lmfdi := leading_monomial' mo fdi fdi_ne_0
    let lcfdi := fdi.coeff lmfdi
    let ltfdi := MvPolynomial.monomial lmfdi lcfdi
    have lmfdi_div_lmp : lmfdi ≤ lmp := by
      simp only [Fin.find?_eq_some_iff] at odi_eq
      exact odi_eq.1 |> of_decide_eq_true
    let qi_term := MvPolynomial.monomial (lmp - lmfdi) (lcp / lcfdi)
    have qi_term_c_ne_0 : lcp / lcfdi ≠ 0 := by
      simp only [ne_eq, div_eq_zero_iff, not_or]
      push_neg
      constructor
      · exact lc_not_zero mo mpds.p p_ne_0
      · exact lc_not_zero mo fdi fdi_ne_0
    have fdi_qiterm_mul_ne_0 : fdi * qi_term ≠ 0 := by
      apply mul_ne_zero
      · exact fdi_ne_0
      · simp only [ne_eq, MvPolynomial.monomial_eq_zero, div_eq_zero_iff, not_or, qi_term,
          lcfdi, lcp]
        constructor
        · exact lc_not_zero mo mpds.p p_ne_0
        · exact lc_not_zero mo fdi fdi_ne_0
    have lmfqi_eq_lmp
      : leading_monomial' mo (F[↑di] * qi_term) fdi_qiterm_mul_ne_0 = lmp := by
      rw [lm'_monmul_commute mo F[di] fdi_ne_0 (lmp - lmfdi) (lcp / lcfdi) qi_term_c_ne_0]
      rw [add_comm]
      subst lmfdi
      exact tsub_add_cancel_of_le lmfdi_div_lmp
    simp only [gt_iff_lt]
    cases em (mpds.p - fdi * qi_term = 0) with
    | inl p_sub_eq_0 =>
      subst fdi qi_term lcp lcfdi lmp lmfdi
      simp only [Fin.getElem_fin] at p_sub_eq_0
      simp only [p_sub_eq_0, lm_zero_eq_bot, WithBot.map_bot, lm_coe_lm' mo mpds.p p_ne_0,
        WithBot.map_coe, WithBot.bot_lt_coe]
    | inr p_sub_ne_0 =>
      apply lt_of_le_of_ne
      · rw [sub_eq_add_neg]
        apply lm_add_le_of_both_lm_le mo mpds.p _ mpds.p
        · rfl
        · rw [← neg_one_smul K _]
          rw [
            ← lm_smul_eq_lm mo _ (-1 : K)
              (by simp only [ne_eq, neg_eq_zero, one_ne_zero, not_false_eq_true])]
          subst fdi qi_term lcp lcfdi lmp lmfdi
          rw [← WithBot.coe_eq_coe, ← lm_coe_lm' mo, ← lm_coe_lm' mo] at lmfqi_eq_lmp
          rw [← lmfqi_eq_lmp]
          rfl
      · simp only [Fin.getElem_fin, fdi, qi_term, lmp, lmfdi, lcp, lcfdi] at p_sub_ne_0
        simp only [lm_coe_lm' mo _ p_sub_ne_0, WithBot.map_coe, lm_coe_lm' mo mpds.p p_ne_0, ne_eq,
          WithBot.coe_inj, EmbeddingLike.apply_eq_iff_eq]
        by_contra HC
        have key :=
          Finset.max'_mem
            (Finset.map mo.toSyn.toEmbedding (mpds.p - fdi * qi_term).support)
            (by simp only [AddEquiv.toEquiv_eq_coe, Fin.getElem_fin, Finset.map_nonempty,
              MvPolynomial.support_nonempty, ne_eq, p_sub_ne_0, not_false_eq_true, fdi, qi_term,
              lmp, lmfdi, lcp, lcfdi])
        have key' : (mpds.p - fdi * qi_term).coeff lmp = 0 := by
          simp only [MvPolynomial.coeff_sub]
          apply sub_eq_zero_of_eq
          conv_rhs => rw [← tsub_add_cancel_of_le lmfdi_div_lmp, add_comm]
          simp only [MvPolynomial.coeff_mul_monomial, qi_term, lcp, lcfdi]
          rw [div_eq_mul_inv, ← mul_assoc, mul_comm lcfdi lcp, mul_assoc]
          simp only [@mul_inv_cancel₀ K _ lcfdi (by exact lc_not_zero mo fdi fdi_ne_0), mul_one,
            lcp, lcfdi]
        rw [← MvPolynomial.notMem_support_iff] at key'
        conv_lhs at HC =>
          rw [leading_monomial', max_monomial']
          simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm]
        simp only [← AddEquiv.apply_eq_iff_eq mo.toSyn, AddEquiv.apply_symm_apply] at HC
        unfold lmp at key'
        rw [← Finset.mem_map' mo.toSyn.toEmbedding, Equiv.toEmbedding_apply,
          AddEquiv.toEquiv_eq_coe] at key'
        simp only [EquivLike.coe_coe] at key'
        rw [← HC] at key'
        exact key' key

/-- The recursive definition of multivariate polynomial division algorithm.
This continues exactly until `mpds.p` is zero. -/
noncomputable def mvpoly_division_rec {σ K : Type*}
  [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (f : MvPolynomial σ K) (F : List (MvPolynomial σ K)) (hF : 0 ∉ F) (F_Nodup : F.Nodup)
  (mpds : MvPolyDivStruct σ K mo f F hF F_Nodup) :
    MvPolyDivStruct σ K mo f F hF F_Nodup :=
  if hp0 : mpds.p = 0
    then
      mpds
    else
      mvpoly_division_rec mo f F hF F_Nodup (mvpoly_division_step mo f F hF F_Nodup mpds hp0)
termination_by WithBot.map mo.toSyn (leading_monomial mo mpds.p)
decreasing_by
  unfold WellFoundedRelation.rel withbot_mo_syn_wf
  apply mvpoly_division_lmp_decr

/-- The starting structure of multivariate polynomial division algorithm. -/
noncomputable def mvpoly_division_init {σ K : Type*}
  [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (f : MvPolynomial σ K) (F : List (MvPolynomial σ K)) (hF : 0 ∉ F) (F_Nodup : F.Nodup) :
    MvPolyDivStruct σ K mo f F hF F_Nodup :=
  {
    Q := List.replicate F.length 0
    FQ_len_eq := by simp only [List.length_replicate]
    r := 0
    p := f
    f_eq_FQ_r := by
      simp only [Fin.getElem_fin, List.getElem_replicate, mul_zero, Finset.sum_const_zero, add_zero,
        zero_add]
    lm_summand_le_lmf := by
      simp only [Fin.getElem_fin, List.getElem_replicate, mul_zero, lm_zero_eq_bot, WithBot.map_bot,
        bot_le, implies_true]
    lmr_le_lmf := by simp only [lm_zero_eq_bot, WithBot.map_bot, bot_le]
    lmp_le_lmf := by rfl
    r_not_divisible := by
      simp only [MvPolynomial.support_zero, Finset.notMem_empty, IsEmpty.forall_iff, implies_true]
  }

/-- The full definition of multivariate polynomial division. -/
noncomputable def mvpoly_division {σ K : Type*}
  [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (f : MvPolynomial σ K) (F : List (MvPolynomial σ K)) (hF : 0 ∉ F) (F_Nodup : F.Nodup) :
    MvPolyDivStruct σ K mo f F hF F_Nodup :=
  mvpoly_division_rec mo f F hF F_Nodup (mvpoly_division_init mo f F hF F_Nodup)

/-- The multivariate polynomial division always terminates with `p = 0`
in `MvPolyDivStruct`. A prestep before `mvpoly_division_p_eq_0` to follow
the inductive definition of the algorithm. -/
lemma mvpoly_division_p_eq_0_induction {σ K : Type*}
  [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (f : MvPolynomial σ K) (F : List (MvPolynomial σ K)) (hF : 0 ∉ F) (F_Nodup : F.Nodup)
  (syn_lmp : WithBot mo.syn) :
    ∀ mpds : MvPolyDivStruct σ K mo f F hF F_Nodup,
      WithBot.map mo.toSyn (leading_monomial mo mpds.p) = syn_lmp →
        let mpds_rec := mvpoly_division_rec mo f F hF F_Nodup mpds
        mpds_rec.p = 0 := by
  induction syn_lmp using WellFounded.induction (withbot_mo_syn_wf mo).wf with
  | h syn_μ IH =>
    rw [WellFoundedRelation.rel, withbot_mo_syn_wf] at IH
    intro mpds mpds_lmp_eq_lmp
    rw [mvpoly_division_rec]
    simp only
    split
    next p_eq_0 =>
      exact p_eq_0
    next p_ne_0 =>
      let mpds' := mvpoly_division_step mo f F hF F_Nodup mpds p_ne_0
      have mpds'_lmp_lt_mpds_lmp := mvpoly_division_lmp_decr mo f F hF F_Nodup mpds p_ne_0
      subst syn_μ
      exact
        IH
          (WithBot.map mo.toSyn (leading_monomial mo mpds'.p))
          (by apply mpds'_lmp_lt_mpds_lmp)
          mpds'
          rfl

/-- The multivariate polynomial division always terminates with `p = 0`
in `MvPolyDivStruct`. -/
lemma mvpoly_division_p_eq_0 {σ K : Type*}
  [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (f : MvPolynomial σ K) (F : List (MvPolynomial σ K)) (hF : 0 ∉ F) (F_Nodup : F.Nodup) :
    (mvpoly_division mo f F hF F_Nodup).p = 0 :=
  mvpoly_division_p_eq_0_induction mo f F hF F_Nodup
    (WithBot.map mo.toSyn (leading_monomial mo f))
    (mvpoly_division_init mo f F hF F_Nodup)
    rfl

/-- Consider the multivariate polynomial division of `f` by `F = [f_1, ⋯, f_s]`,
which would return the quotients `Q = [q_1, ⋯, q_s]` and the remainder `r`.
Then `f = ∑ i : 1 ≤ i ≤ s, q_i f_i + r`. -/
lemma mvpoly_division_repn {σ K : Type*}
  [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (f : MvPolynomial σ K) (F : List (MvPolynomial σ K)) (hF : 0 ∉ F) (F_Nodup : F.Nodup) :
    let mpds := mvpoly_division mo f F hF F_Nodup
    f =
      ∑ i : Fin (F.length),
        F[i] * mpds.Q[i]'(by rw [← mpds.FQ_len_eq]; exact i.isLt) + mpds.r := by
  intro mpds
  have mpds_repn := mpds.f_eq_FQ_r
  rw [mvpoly_division_p_eq_0 mo f F hF] at mpds_repn
  simp only [mpds_repn, Fin.getElem_fin, add_zero]

/-- The multivariate polynomial division of 0 by any list of polynomials `F`
ends with quotients and remainder all 0. -/
lemma div_zero_Qr_zero {σ K : Type*}
  [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ) (F : List (MvPolynomial σ K)) (hF : 0 ∉ F) (F_Nodup : F.Nodup) :
    let mpds0 := mvpoly_division mo 0 F hF F_Nodup
    mpds0.Q = List.replicate F.length 0 ∧ mpds0.r = 0 := by
  rw [mvpoly_division, mvpoly_division_rec]
  split
  next mpds0_p_eq_0 =>
    simp only [mvpoly_division_init, and_self]
  next mpds0_p_ne_0 =>
    absurd mpds0_p_ne_0
    simp only [mvpoly_division_init]

/-- A polynomial `f` has zero remainder over a list `F` of polynomials without 0,
if the remainder of multivariate polynomial division algorithm on `f` by `F`
equals 0. -/
def remainder_zero {σ K : Type*}
  [DecidableEq σ] [Field K] [DecidableEq K]
  (mo : MonomialOrder σ)
  (f : MvPolynomial σ K) (F : Finset (MvPolynomial σ K)) (hF : 0 ∉ F) :
    Prop :=
  ∃ LF : List (MvPolynomial σ K), ∃ hFLF : F = LF.toFinset, ∃ LF_Nodup : LF.Nodup,
    (mvpoly_division mo f LF (by rw [← List.mem_toFinset, ← hFLF]; exact hF) LF_Nodup).r = 0
