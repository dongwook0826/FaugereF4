import Mathlib

-- Ideal.mem_span_singleton
-- !!! Finsupp.mem_span_iff_linearCombination !!!

lemma ideal_span_mem_iff_lin_combi' (R : Type*) [Semiring R] (s : Set R) (f : R) :
  f ∈ Ideal.span s ↔ ∃ h : ↑s →₀ R, f = ∑ g ∈ h.support, h g * g := by
  unfold Ideal.span
  rw [Finsupp.mem_span_iff_linearCombination]
  unfold Finsupp.linearCombination
  simp
  constructor
  · intro exl
    let ⟨l, hl⟩ := exl
    exists l
    rw [← hl]
    unfold Finsupp.sum
    simp
  · intro exh
    let ⟨h, hh⟩ := exh
    exists h
    rw [hh]
    unfold Finsupp.sum
    simp

lemma ideal_span_mem_iff_lin_combi (R : Type*) [Semiring R] (s : Set R) :
  Ideal.span s = {f | ∃ h : ↑s →₀ R, f = ∑ g ∈ h.support, h g * g} := by
  ext f
  exact ideal_span_mem_iff_lin_combi' R s f

/-
lemma ideal_span_mem_iff_finsum' (R : Type*) [Semiring R] (s : Set R) (f : R) :
  f ∈ Ideal.span s ↔ ∃ h : R →₀ R, ↑h.support ⊆ s ∧ f = ∑ g ∈ h.support, h g * g := by
  rw [ideal_span_mem_iff_lin_combi']
  constructor
  · intro ⟨h, hh⟩
    exists h.embDomain {
      toFun := id
      inj' := by simp
    }

  ·
-/
