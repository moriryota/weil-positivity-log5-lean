import ThreePointSOS
import PrimeConstants
import RankOneCoordinates
namespace RHPrimeFiber
open RHPrimeConstants RHChainCoordinates

theorem three_point_gap {a : ℝ} (ha : 0<a) (x y z : ℝ) :
    RHThreePoint.form (alpha a) (beta a) x y z ≤
      lam a*(x^2+y^2+z^2) - (lam a-alpha a)*
        ((x-coefficient ratio x y z)^2+(y-ratio*coefficient ratio x y z)^2+
          (z-coefficient ratio x y z)^2) := by
  let t := coefficient ratio x y z
  have hh := RHThreePoint.shifted_gap (alpha a) (beta a) ratio (lam a)
    (x-t) (y-ratio*t) (z-t) t (alpha_pos ha).le (beta_pos ha).le ratio_pos
    (lam_eq_two_alpha_div_ratio a) (lam_eq_beta_add_alpha_ratio a)
    (perpendicular ratio x y z)
  simp only [sub_add_cancel] at hh
  have hα := alpha_pos ha
  have hn : 0 ≤ alpha a*((x-t)^2+(y-ratio*t)^2+(z-t)^2) := by positivity
  change RHThreePoint.form (alpha a) (beta a) x y z ≤
    lam a*(x^2+y^2+z^2)-(lam a-alpha a)*((x-t)^2+(y-ratio*t)^2+(z-t)^2)
  nlinarith

theorem central_mass_exact (t : ℝ) :
    (ratio*t)^2 = mass*((2+ratio^2)*t^2) := by
  rw [← mass_identity]
  exact central_mass ratio t

theorem log2_three_point_gap (x y z : ℝ) :
    RHThreePoint.form (alpha (Real.log 2)) (beta (Real.log 2)) x y z ≤
      lam (Real.log 2)*(x^2+y^2+z^2) - (lam (Real.log 2)-alpha (Real.log 2))*
        ((x-coefficient ratio x y z)^2+(y-ratio*coefficient ratio x y z)^2+
          (z-coefficient ratio x y z)^2) :=
  three_point_gap (Real.log_pos (by norm_num)) x y z
end RHPrimeFiber
