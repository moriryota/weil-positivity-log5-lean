import RawPrime3Bound
import ChainGeometry

open MeasureTheory Set
open RHCentralMultiplier RHActualCorrelation RHRawPrime3

namespace RHActualPrime3

noncomputable def mu3 : ℝ := Real.log 3 / Real.sqrt 3

lemma mu3_pos : 0 < mu3 := by
  unfold mu3
  exact div_pos (Real.log_pos (by norm_num : (1:ℝ) < 3)) (Real.sqrt_pos.mpr (by norm_num))

theorem lp_prime3_bound {L b : ℝ} (hb : 0 ≤ b) (hW : b ≤ 2*L) (h2b : 2*L ≤ 2*b)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    2 * mu3 * autocorr L f b ≤
      mu3 * (‖f‖^2 - ‖centralLp L b f‖^2) := by
  have h := prime3_two_point_bound L b hb hW h2b f
  have hmul := mul_le_mul_of_nonneg_left h mu3_pos.le
  calc
    2 * mu3 * autocorr L f b =
        mu3 * (2 * autocorr L f b) := by ring
    _ ≤ mu3 * (‖f‖^2 - ‖centralLp L b f‖^2) := hmul

theorem log5_prime3_bound
    (f : Lp ℝ 2 (volume.restrict (Icc (-(Real.log 5/2)) (Real.log 5/2)))) :
    2 * mu3 * autocorr (Real.log 5/2) f (Real.log 3) ≤
      mu3 * (‖f‖^2 - ‖centralLp (Real.log 5/2) (Real.log 3) f‖^2) := by
  have hg := RHChainGeometry.log5_geometry
  have hb : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num : (1:ℝ) < 3)).le
  have hW : Real.log 3 ≤ 2 * (Real.log 5/2) := by
    rw [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)]
    exact (Real.log_lt_log (by norm_num) (by norm_num)).le
  have h2b : 2 * (Real.log 5/2) ≤ 2 * Real.log 3 := by
    rw [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)]
    linarith [hg.2.2.2.2.2]
  exact lp_prime3_bound hb hW h2b f

end RHActualPrime3
