import RawPrimeGap
import ZeroOverlap
import ProjectionNormIntegral
import ChainGeometry
open MeasureTheory Set
open RHPrimeConstants RHRawProjection
namespace RHActualCorrelation

theorem lp_prime24_gap {L a : ℝ} (ha : 0 < a)
    (h2 : 2*a ≤ 2*L) (h3 : 2*L ≤ 3*a)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    2*alpha a*autocorr L f a + 2*beta a*autocorr L f (2*a) ≤
    lam a*‖f‖^2 - (lam a-alpha a)*‖f-projectLp L a ratio f‖^2 := by
  have h := RHRawPrimeGap.prime24_gap
    ((Icc (-L) L).indicator (f : ℝ → ℝ))
    (RHZeroExtension.lp_zero_extension_memLp L f) ha h2 h3
  have hn := RHProjectionNorm.integral_sq_norm_of_ae L f
    ((Icc (-L) L).indicator (f : ℝ → ℝ))
    (indicator_ae_eq_restrict measurableSet_Icc)
  rw [zero_extension_overlap_integral L f a ha.le,
    zero_extension_overlap_integral L f (2*a) (by positivity), hn,
    RHProjectionNorm.integral_residual_sq_norm] at h
  exact h

theorem log5_prime24_gap
    (f : Lp ℝ 2 (volume.restrict (Icc (-(Real.log 5/2)) (Real.log 5/2)))) :
    2*alpha (Real.log 2)*autocorr (Real.log 5/2) f (Real.log 2) +
    2*beta (Real.log 2)*autocorr (Real.log 5/2) f (Real.log 4) ≤
    lam (Real.log 2)*‖f‖^2 - (lam (Real.log 2)-alpha (Real.log 2))*
      ‖f-projectLp (Real.log 5/2) (Real.log 2) ratio f‖^2 := by
  have h4 : Real.log 4 = 2*Real.log 2 := by
    simpa only [show (2:ℝ)^2=4 by norm_num, Nat.cast_ofNat] using Real.log_pow 2 2
  rw [h4]
  have h := RHChainGeometry.log5_geometry
  exact lp_prime24_gap h.1 (by linarith [h.2.1]) (by linarith [h.2.2.1]) f
end RHActualCorrelation
