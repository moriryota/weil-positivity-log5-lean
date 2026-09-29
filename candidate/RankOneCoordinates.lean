import Mathlib.Tactic
namespace RHChainCoordinates
noncomputable def coefficient (r x y z : ℝ) : ℝ := (x+r*y+z)/(2+r^2)
theorem perpendicular (r x y z : ℝ) :
    (x-coefficient r x y z)+r*(y-r*coefficient r x y z)+(z-coefficient r x y z)=0 := by
  unfold coefficient
  have hd : (2+r^2) ≠ 0 := by positivity
  field_simp
  <;> ring

theorem norm_split (r x y z : ℝ) :
    x^2+y^2+z^2 = (2+r^2)*(coefficient r x y z)^2 +
      ((x-coefficient r x y z)^2+(y-r*coefficient r x y z)^2+(z-coefficient r x y z)^2) := by
  have hp := perpendicular r x y z
  nlinarith [mul_eq_zero_of_left hp (coefficient r x y z)]

theorem central_mass (r t : ℝ) :
    (r*t)^2 = (r^2/(2+r^2))*((2+r^2)*t^2) := by
  have hd : (2+r^2) ≠ 0 := by positivity
  field_simp
  <;> ring

theorem two_point_bound (a x y : ℝ) (ha : 0 ≤ a) :
    2*a*x*y ≤ a*(x^2+y^2) := by
  nlinarith [mul_nonneg ha (sq_nonneg (x-y))]
end RHChainCoordinates
