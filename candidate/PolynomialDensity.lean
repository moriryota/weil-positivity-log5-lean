import ComplexApprox
import Final
import Mathlib.MeasureTheory.Function.ContinuousMapDense
open MeasureTheory Set Filter
open scoped ENNReal
namespace RHPolynomialDensity
open RHBoundedWindow

/-- Density in the actual restricted-measure Lp space used by the project. -/
theorem intervalPolynomial_denseRange {L : ℝ} (hL : 0 ≤ L) :
    DenseRange (intervalPolynomial L hL) := by
  let μ : Measure ℝ := volume.restrict (Icc (-L) L)
  letI : IsFiniteMeasure μ := Real.isFiniteMeasure_restrict_Icc _ _
  letI : μ.WeaklyRegular := Measure.WeaklyRegular.restrict_of_measure_ne_top (by simp)
  have hden := BoundedContinuousFunction.toLp_denseRange ℂ μ ℂ (p := 2) (by norm_num)
  apply Metric.denseRange_iff.mpr
  intro f ε hε
  obtain ⟨g, hg⟩ := Metric.denseRange_iff.mp hden f (ε/2) (by positivity)
  let C : ℝ := (measureUnivNNReal μ : ℝ) ^ (2:ℝ≥0∞).toReal⁻¹
  have hC : 0 ≤ C := by positivity
  let δ : ℝ := ε / (2*(C+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hCδ : C*δ ≤ ε/2 := by
    have hc : δ*(2*(C+1)) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨P, hP⟩ := RHComplexApprox.exists_complex_polynomial_near (-L) L g
    g.continuous.continuousOn hδ
  refine ⟨P, ?_⟩
  let u : Lp ℂ 2 μ := BoundedContinuousFunction.toLp 2 μ ℂ g
  let v : Lp ℂ 2 μ := intervalPolynomial L hL P
  have hu : (u : ℝ → ℂ) =ᵐ[μ] g := BoundedContinuousFunction.coeFn_toLp 2 μ ℂ g
  have hv : (v : ℝ → ℂ) =ᵐ[μ] (fun x : ℝ => P.eval (x:ℂ)) :=
    MemLp.coeFn_toLp (polynomial_memLp hL P)
  have hb : ∀ᵐ x ∂μ, ‖(u-v) x‖ ≤ δ := by
    filter_upwards [Lp.coeFn_sub u v, hu, hv, ae_restrict_mem measurableSet_Icc] with x hx hux hvx hxi
    rw [hx, Pi.sub_apply, hux, hvx]
    exact (norm_sub_rev _ _).trans_le (hP x hxi).le
  have hn : ‖u-v‖ ≤ C*δ := Lp.norm_le_of_ae_bound hδ.le hb
  have hd : dist u v ≤ ε/2 := by
    rw [dist_eq_norm]
    exact hn.trans hCδ
  exact (dist_triangle f u v).trans_lt (by change dist f u < ε/2 at hg; linarith)
end RHPolynomialDensity
