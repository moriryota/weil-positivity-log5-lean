import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
namespace RHConstants0467
theorem pole_penalty_identity :
    2 * (Real.sinh (Real.log 5 / 2) - Real.log 5 / 2) =
      4 / Real.sqrt 5 - Real.log 5 := by
  have hp : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hs : Real.sinh (Real.log 5 / 2) = (Real.sqrt 5 - (Real.sqrt 5)⁻¹) / 2 := by
    rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    exact Real.sinh_log hp
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  rw [hs]
  field_simp
  nlinarith
end RHConstants0467
