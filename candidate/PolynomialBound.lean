import PolynomialQuotient
open Polynomial MeasureTheory Set
open scoped BigOperators ComplexConjugate
namespace RHTuckPolynomial

noncomputable def divided (p : Polynomial ℂ) (x y : ℝ) : ℂ :=
  ∑ n ∈ p.support, p.coeff n * (RHDividedMoments.difference n x y : ℂ)

lemma quotient_left (p : Polynomial ℂ) {x y : ℝ} (hy : y < x) :
    quotient p x y = divided p x y := by
  rw [quotient_eq_sum]
  unfold divided
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  exact_mod_cast RHDividedMoments.left_quotient n hy

lemma quotient_right (p : Polynomial ℂ) {x y : ℝ} (hy : x < y) :
    quotient p x y = -divided p x y := by
  rw [quotient_eq_sum]
  unfold divided
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have h : (((x:ℂ)^n-(y:ℂ)^n)/((|x-y|:ℝ):ℂ)) =
      -(RHDividedMoments.difference n x y : ℂ) := by
    exact_mod_cast RHDividedMoments.right_quotient n hy
  rw [h]; ring

lemma norm_quotient_le (p : Polynomial ℂ) (x y : ℝ) :
    ‖quotient p x y‖ ≤ ‖divided p x y‖ := by
  rcases lt_trichotomy y x with h | h | h
  · rw [quotient_left p h]
  · subst y
    simp [quotient]
  · rw [quotient_right p h,norm_neg]

lemma continuous_divided (p : Polynomial ℂ) :
    Continuous (fun z : ℝ × ℝ => divided p z.1 z.2) := by
  unfold divided RHDividedMoments.difference
  fun_prop

/-- Absolute integrability on the product interval, including the diagonal. -/
theorem mixed_integrable (p q : Polynomial ℂ) :
    Integrable (fun z : ℝ × ℝ => conj (p.eval (z.1:ℂ)) * quotient q z.1 z.2)
      ((volume.restrict (Icc (-1:ℝ) 1)).prod (volume.restrict (Icc (-1:ℝ) 1))) := by
  have hc : Continuous (fun z : ℝ × ℝ => ‖p.eval (z.1:ℂ)‖ * ‖divided q z.1 z.2‖) := by
    have h := continuous_divided q
    fun_prop
  have hi := hc.continuousOn.integrableOn_compact (μ := volume.prod volume)
    (isCompact_Icc.prod isCompact_Icc : IsCompact ((Icc (-1:ℝ) 1) ×ˢ (Icc (-1:ℝ) 1)))
  rw [IntegrableOn,← Measure.prod_restrict] at hi
  apply hi.mono'
  · unfold quotient
    have hp : Continuous (fun z : ℝ × ℝ => conj (p.eval (z.1:ℂ))) := by fun_prop
    have hq : Continuous (fun z : ℝ × ℝ => q.eval (z.1:ℂ)-q.eval (z.2:ℂ)) := by fun_prop
    have hd : Continuous (fun z : ℝ × ℝ => ((|z.1-z.2|:ℝ):ℂ)) := by fun_prop
    exact (hp.measurable.mul (hq.measurable.div hd.measurable)).aestronglyMeasurable
  · filter_upwards [] with z
    rw [norm_mul,Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (norm_quotient_le q z.1 z.2) (norm_nonneg _)
end RHTuckPolynomial
