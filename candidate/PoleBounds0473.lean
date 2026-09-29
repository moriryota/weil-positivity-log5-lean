import Constants0467
import PoleIdentity0467
import Log5Bound0473
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace RHPoleNumeric0473
noncomputable def poleExpr : ℝ := 2*(Real.sinh (Real.log 5/2)-Real.log 5/2)
def poleLo : ℚ := (1794164695657313825265796017588333488268933334207028575040699048542377528025861549013976486098462091/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def poleHi : ℚ := (897082347828656912632898008794166744134466667103514287520349524271188764012930774506988243049231047/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
theorem pole_bounds : (poleLo:ℝ) ≤ poleExpr ∧ poleExpr ≤ (poleHi:ℝ) := by
  have hs := RHConstants0467.sqrt5_bounds
  have hl := Trial0456.log5_bounds
  have hpos : (0:ℝ)<(RHConstants0467.sqrt5Lo:ℝ) := by norm_num [RHConstants0467.sqrt5Lo]
  have hb := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 4) (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<5)) hs.2
  have ha := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 4) hpos hs.1
  norm_num [RHConstants0467.sqrt5Lo, RHConstants0467.sqrt5Hi] at ha hb
  norm_num [Trial0456.lo, Trial0456.hi] at hl
  unfold poleExpr
  rw [RHConstants0467.pole_penalty_identity]
  norm_num only [poleLo, poleHi, Rat.cast_div, Rat.cast_ofNat]
  constructor <;> linarith [hl.1, hl.2]
theorem pole_width : poleHi-poleLo ≤ (1:ℚ)/10^95 := by decide +kernel
end RHPoleNumeric0473
