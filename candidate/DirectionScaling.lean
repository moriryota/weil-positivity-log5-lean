import ActualDirections
import PolynomialLpFaithful
open Polynomial MeasureTheory Set
namespace RHDirectionScaling
open RHLegendreDirections RHLegendreContract

theorem rec_eval_scale {L : ℝ} (hL : 0 < L) (n : ℕ) (x : ℝ) :
    (recPoly L n).eval (x:ℂ) = (recPoly 1 n).eval ((x/L:ℝ):ℂ) := by
  rw [recPoly_eval_eq_Q_of_recurrence Q_zero_base Q_one_base Q_recurrence hL,
    recPoly_eval_eq_Q_of_recurrence Q_zero_base Q_one_base Q_recurrence (by norm_num)]
  congr 2
  field_simp

noncomputable def factor (L : ℝ) (n : ℕ) : ℂ :=
  (Real.sqrt ((2*(n:ℝ)+1)/(2*L)) : ℂ) /
    (Real.sqrt ((2*(n:ℝ)+1)/2) : ℂ)

theorem direction_eval_scale {L : ℝ} (hL : 0 < L) (n : ℕ) (x : ℝ) :
    (directionPoly L n).eval (x:ℂ) =
      factor L n * (directionPoly 1 n).eval ((x/L:ℝ):ℂ) := by
  rw [directionPoly_eval,directionPoly_eval,rec_eval_scale hL]
  have hn : (Real.sqrt ((2*(n:ℝ)+1)/2) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  simp only [factor,mul_one]
  field_simp
end RHDirectionScaling
