import RawCentralMass
import CentralLinear
import ProjectionNormIntegral
import ChainGeometry
import PrimeConstants
open MeasureTheory Set
open RHRawProjection RHCentralMultiplier
namespace RHCentralMass
 theorem lp_mass {L a b r : ℝ} (ha : 0<a) (h2 : 2*a≤2*L) (h3 : 2*L≤3*a)
    (hW : 2*L<a+b) (hab : b<2*a)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    ‖centralLp L b (projectLp L a r f)‖^2 =
      r^2/(2+r^2)*‖projectLp L a r f‖^2 := by
  have h := integral_mass (r := r) ((Icc (-L) L).indicator (f : ℝ → ℝ))
    (RHZeroExtension.lp_zero_extension_memLp L f) ha h2 h3 hW hab
  have hc : (Ioo (L-b) (-L+b)).indicator
      (project L a r ((Icc (-L) L).indicator (f : ℝ → ℝ))) =ᵐ[volume.restrict (Icc (-L) L)]
      (centralLp L b (projectLp L a r f) : ℝ → ℝ) := by
    filter_upwards [coeFn_centralLp L b (projectLp L a r f),
      coeFn_projectLp L a r f] with x hcx hpx
    rw [hcx]
    by_cases hx : x ∈ Ioo (L-b) (-L+b)
    · simp only [indicator_of_mem hx, hpx]
    · simp only [indicator_of_notMem hx]
  rw [RHProjectionNorm.integral_sq_norm_of_ae L _ _ hc,
    RHProjectionNorm.integral_project_sq_norm] at h
  exact h
 theorem log5_lp_mass
    (f : Lp ℝ 2 (volume.restrict (Icc (-(Real.log 5/2)) (Real.log 5/2)))) :
    ‖centralLp (Real.log 5/2) (Real.log 3)
      (projectLp (Real.log 5/2) (Real.log 2) RHPrimeConstants.ratio f)‖^2 =
    RHPrimeConstants.mass *
      ‖projectLp (Real.log 5/2) (Real.log 2) RHPrimeConstants.ratio f‖^2 := by
  have hg := RHChainGeometry.log5_geometry
  have h := lp_mass (r := RHPrimeConstants.ratio) hg.1
    (by linarith [hg.2.1]) (by linarith [hg.2.2.1])
    (by linarith [hg.2.2.2.1]) hg.2.2.2.2.1 f
  simpa only [RHPrimeConstants.mass_identity] using h
end RHCentralMass
