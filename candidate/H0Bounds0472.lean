import Quarter0472
import EulerHigh0465
import LogPiBounds0466
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace RHH0Numeric0472
noncomputable def h0Expr : ℝ := (Complex.digamma (1/4 : ℂ)).re - Real.log Real.pi
def h0Lo : ℚ := (-3357614637016040988895598435906088930634087032264721151980564144369434103571674623032611079517219409 / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def h0Hi : ℚ := (-13430458548064163955582393743624355722536348129058884607922256577477736414286698492130444318068877633 / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
theorem h0_bounds : (h0Lo : ℝ) ≤ h0Expr ∧ h0Expr ≤ (h0Hi : ℝ) := by
  have he := RHEulerNumeric0465.enclosure
  have hp := RHPi0466.pi_bounds
  have hlp := RHPi0466.log_pi_bounds
  have hl2 := Trial0455.log2_bounds
  norm_num [RHPi0466.piLo, RHPi0466.piHi] at hp
  norm_num [RHPi0466.logPiLo, RHPi0466.logPiHi] at hlp
  norm_num [Trial0455.lo, Trial0455.hi] at hl2
  unfold h0Expr
  rw [Trial0456.digamma_quarter_re]
  norm_num only [h0Lo, h0Hi, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat]
  constructor <;> linarith [he.1, he.2, hp.1, hp.2, hlp.1, hlp.2, hl2.1, hl2.2]
theorem h0_width : h0Hi-h0Lo ≤ (1:ℚ)/10^95 := by decide +kernel
end RHH0Numeric0472
