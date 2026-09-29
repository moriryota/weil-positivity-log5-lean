import PolynomialBound
open Polynomial MeasureTheory Set
open scoped ComplexConjugate
namespace RHTuckMixed

theorem mixed_integrable {L : ℝ} {f : ℝ → ℂ}
    (hf : Integrable f (volume.restrict (Icc (-L) L))) (p : Polynomial ℂ) :
    Integrable (fun z : ℝ × ℝ => conj (f z.1) * RHTuckPolynomial.quotient p z.1 z.2)
      ((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L))) := by
  let μ := volume.restrict (Icc (-L) L)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc :
      IsCompact ((Icc (-L) L) ×ˢ (Icc (-L) L))).exists_bound_of_continuousOn
      (RHTuckPolynomial.continuous_divided p).continuousOn
  have hbound : Integrable (fun z : ℝ × ℝ => ‖f z.1‖ * C) (μ.prod μ) :=
    (hf.norm.comp_fst μ).mul_const C
  apply hbound.mono'
  · have hq : Measurable (fun z : ℝ × ℝ => RHTuckPolynomial.quotient p z.1 z.2) := by
      unfold RHTuckPolynomial.quotient
      have hn : Continuous (fun z : ℝ × ℝ => p.eval (z.1:ℂ)-p.eval (z.2:ℂ)) := by fun_prop
      have hd : Continuous (fun z : ℝ × ℝ => ((|z.1-z.2|:ℝ):ℂ)) := by fun_prop
      exact hn.measurable.div hd.measurable
    exact ((Complex.conjCLE.toContinuousLinearMap.integrable_comp hf).comp_fst μ).aestronglyMeasurable.mul hq.aestronglyMeasurable
  · have hm : ∀ᵐ z ∂(μ.prod μ), z ∈ ((Icc (-L) L) ×ˢ (Icc (-L) L)) := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
    filter_upwards [hm] with z hz
    rw [norm_mul,Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left
      ((RHTuckPolynomial.norm_quotient_le p z.1 z.2).trans (hC z hz)) (norm_nonneg _)
end RHTuckMixed
