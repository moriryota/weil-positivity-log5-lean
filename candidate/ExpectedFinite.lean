import FiniteCoefficients
open MeasureTheory Set
namespace RHExpected0291
/-- Actual comparison energy controls every finite harmonic-weighted coefficient sum. -/
theorem actual_form_finite {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (hf : RHComparisonEnergy.InDomain L f) (m : ℕ) :
    (∑ n ∈ Finset.range m, (harmonic n : ℝ) *
      ‖inner ℂ (RHLegendreDirections.direction L hL.le n) f‖ ^ 2) ≤
        (RHComparisonEnergy.intervalEnergy L f).toReal :=
  RHFiniteCoefficients.finite_bound hL (Finset.range m) f hf
end RHExpected0291
