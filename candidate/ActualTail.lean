import CoefficientMass
import ResidualCoefficients
import FiniteTail
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace RHActualTail
open RHLegendreDirections

theorem finite_comparison_tail {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (w : ℕ → ℝ) (N : ℕ) (d E : ℝ)
    (hw : ∀ n, N ≤ n → d ≤ w n)
    (hfinite : ∀ M, ∑ n ∈ Finset.range M,
      w n * ‖inner ℂ (direction L hL.le n) f‖ ^ 2 ≤ E) :
    (∑ n ∈ Finset.range N, w n * ‖inner ℂ (direction L hL.le n) f‖ ^ 2) +
      d * (‖f‖ ^ 2 - ∑ n ∈ Finset.range N,
        ‖inner ℂ (direction L hL.le n) f‖ ^ 2) ≤ E :=
  RHFiniteTail.lower_bound _ w N d E (‖f‖ ^ 2)
    (fun n => sq_nonneg _) hw hfinite (coefficient_mass_tendsto hL f)

theorem zero_low_tail {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (w : ℕ → ℝ) (N : ℕ) (d E : ℝ)
    (hw : ∀ n, N ≤ n → d ≤ w n)
    (hfinite : ∀ M, ∑ n ∈ Finset.range M,
      w n * ‖inner ℂ (direction L hL.le n) f‖ ^ 2 ≤ E)
    (hzero : ∀ n, n < N → inner ℂ (direction L hL.le n) f = 0) :
    d * ‖f‖ ^ 2 ≤ E := by
  have h := finite_comparison_tail hL f w N d E hw hfinite
  have hz : ∀ n ∈ Finset.range N, ‖inner ℂ (direction L hL.le n) f‖ ^ 2 = 0 := by
    intro n hn
    simp [hzero n (Finset.mem_range.mp hn)]
  have hs : ∑ n ∈ Finset.range N, ‖inner ℂ (direction L hL.le n) f‖ ^ 2 = 0 :=
    Finset.sum_eq_zero hz
  have hsw : ∑ n ∈ Finset.range N, w n * ‖inner ℂ (direction L hL.le n) f‖ ^ 2 = 0 := by
    exact Finset.sum_eq_zero (fun n hn => by rw [hz n hn, mul_zero])
  simpa only [hs, hsw, zero_add, sub_zero] using h

/-- The negative constant is added AFTER passing to the coefficient limit. -/
theorem residual_shifted_tail {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (w : ℕ → ℝ) (N : ℕ) (d E c Q : ℝ)
    (hw : ∀ n, N ≤ n → d ≤ w n)
    (hfinite : ∀ M, ∑ n ∈ Finset.range M,
      w n * ‖inner ℂ (direction L hL.le n)
        (f - RHFiniteProjection.finiteProjection (Finset.range N)
          (direction L hL.le) f)‖ ^ 2 ≤ E)
    (hQ : E + c * ‖f - RHFiniteProjection.finiteProjection (Finset.range N)
      (direction L hL.le) f‖ ^ 2 ≤ Q) :
    (d + c) * ‖f - RHFiniteProjection.finiteProjection (Finset.range N)
      (direction L hL.le) f‖ ^ 2 ≤ Q := by
  have h := zero_low_tail hL _ w N d E hw hfinite
    (fun n hn => residual_coefficient_zero hL f N n hn)
  nlinarith
end RHActualTail
