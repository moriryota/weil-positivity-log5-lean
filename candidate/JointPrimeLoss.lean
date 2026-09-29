import LpPrime3Bound
import ProjectionLoss
import CentralLinear
import LpCentralMass
import ActualPrimeGap
import LpPythagoras
import PrimeConstants

open MeasureTheory Set
open RHPrimeConstants RHRawProjection RHCentralMultiplier RHActualCorrelation
open RHProjectionLoss RHActualPrime3

namespace RHJointPrimeBound

noncomputable def log5_gamma : ℝ :=
  gamma mass (lam (Real.log 2) - alpha (Real.log 2)) mu3

lemma log5_gamma_pos : 0 < log5_gamma := by
  unfold log5_gamma
  exact gamma_pos mass_pos (delta_pos (Real.log_pos (by norm_num))) mu3_pos

theorem log5_prime_joint_bound
    (f : Lp ℝ 2 (volume.restrict (Icc (-(Real.log 5/2)) (Real.log 5/2)))) :
    2 * alpha (Real.log 2) * autocorr (Real.log 5/2) f (Real.log 2) +
    2 * beta (Real.log 2) * autocorr (Real.log 5/2) f (Real.log 4) +
    2 * mu3 * autocorr (Real.log 5/2) f (Real.log 3) ≤
    (lam (Real.log 2) + mu3 - log5_gamma) * ‖f‖^2 := by
  let L := Real.log 5 / 2
  let a := Real.log 2
  let b := Real.log 3
  let C := centralLinear L b
  let u := projectLp L a ratio f
  let v := f - u
  have hC : ∀ z, ‖C z‖ ≤ ‖z‖ := fun z => norm_centralLp_le L b z
  have hp : 0 < mass := mass_pos
  have hd : 0 < lam a - alpha a := delta_pos (Real.log_pos (by norm_num))
  have hm : 0 < mu3 := mu3_pos
  have huv : u + v = f := add_sub_cancel u f
  have horth : ‖u + v‖^2 = ‖u‖^2 + ‖v‖^2 := by
    rw [huv]
    exact RHRawProjection.log5_lp_pythagoras ratio f
  have hmass : mass * ‖u‖^2 = ‖C u‖^2 := by
    have h := RHCentralMass.log5_lp_mass f
    exact h.symm
  have h24 : 2 * alpha a * autocorr L (u+v) a + 2 * beta a * autocorr L (u+v) (Real.log 4) ≤
      lam a * ‖u + v‖^2 - (lam a - alpha a) * ‖v‖^2 := by
    rw [huv]
    exact RHActualCorrelation.log5_prime24_gap f
  have h3 : 2 * mu3 * autocorr L (u+v) b ≤ mu3 * (‖u + v‖^2 - ‖C (u + v)‖^2) := by
    rw [huv]
    exact log5_prime3_bound f
  have hj := joint_bound C hC u v hp hd hm horth hmass h24 h3
  rw [huv] at hj
  exact hj

end RHJointPrimeBound
