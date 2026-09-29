import ExpectedFinite
import ExpectedTail
import ComparisonDomain
open MeasureTheory Set
namespace RHComparisonTail
open RHLegendreDirections
noncomputable def residual {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) (N : ℕ) :=
  f - RHFiniteProjection.finiteProjection (Finset.range N) (direction L hL.le) f

theorem residual_domain {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (hf : RHComparisonEnergy.InDomain L f) (N : ℕ) :
    RHComparisonEnergy.InDomain L (residual hL f N) := by
  have h := RHComparisonIntegral.actual_residual_domain hL.le f hf
    (RHProjectionPolynomial.poly hL (Finset.range N) f)
  rw [RHProjectionPolynomial.toLp_poly] at h
  exact h

theorem residual_comparison_tail {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (hf : RHComparisonEnergy.InDomain L f) (N : ℕ) :
    (harmonic N : ℝ) * ‖residual hL f N‖ ^ 2 ≤
      (RHComparisonEnergy.intervalEnergy L (residual hL f N)).toReal := by
  exact RHActualTail.zero_low_tail hL (residual hL f N)
    (fun n => (harmonic n : ℝ)) N (harmonic N : ℝ) _
    (fun n hn => RHExpected0264.harmonic_mono_real hn)
    (RHExpected0291.actual_form_finite hL _ (residual_domain hL f hf N))
    (fun n hn => RHActualTail.residual_coefficient_zero hL f N n hn)

theorem log5_comparison_tail
    (f : Lp ℂ 2 (volume.restrict (Icc (-(Real.log 5 / 2)) (Real.log 5 / 2))))
    (hf : RHComparisonEnergy.InDomain (Real.log 5 / 2) f) (N : ℕ) :
    (harmonic N : ℝ) * ‖f - RHFiniteProjection.finiteProjection (Finset.range N)
      (direction (Real.log 5 / 2) RHLog5Bridge.halfWidth_pos.le) f‖ ^ 2 ≤
    (RHComparisonEnergy.intervalEnergy (Real.log 5 / 2)
      (f - RHFiniteProjection.finiteProjection (Finset.range N)
        (direction (Real.log 5 / 2) RHLog5Bridge.halfWidth_pos.le) f)).toReal :=
  residual_comparison_tail RHLog5Bridge.halfWidth_pos f hf N

/-- The explicit Weil comparison is a hypothesis of this theorem; no finite-sum hypothesis is used. -/
theorem residual_shifted {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (hf : RHComparisonEnergy.InDomain L f) (N : ℕ) (c Q : ℝ)
    (hQ : (RHComparisonEnergy.intervalEnergy L (residual hL f N)).toReal +
      c * ‖residual hL f N‖ ^ 2 ≤ Q) :
    ((harmonic N : ℝ) + c) * ‖residual hL f N‖ ^ 2 ≤ Q := by
  have h := residual_comparison_tail hL f hf N
  nlinarith
end RHComparisonTail
