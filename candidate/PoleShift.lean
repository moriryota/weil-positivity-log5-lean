import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set

namespace RHPoleShift

variable {L : ℝ}

/-- Cauchy-Schwarz inequality for squared inner product on real L2. -/
theorem cs_sq (f g : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    (inner ℝ f g)^2 ≤ ‖g‖^2 * ‖f‖^2 := by
  have h := @norm_inner_le_norm ℝ (Lp ℝ 2 (volume.restrict (Icc (-L) L))) _ _ _ f g
  rw [Real.norm_eq_abs] at h
  have habs : 0 ≤ |inner ℝ f g| := abs_nonneg _
  have hsq : (inner ℝ f g)^2 ≤ (‖f‖ * ‖g‖)^2 := by
    rw [← sq_abs (inner ℝ f g)]
    nlinarith [habs, h]
  calc
    (inner ℝ f g)^2 ≤ (‖f‖ * ‖g‖)^2 := hsq
    _ = ‖g‖^2 * ‖f‖^2 := by ring

/-- Quadratic pole form: 2 * ⟨f, c⟩² - 2 * ⟨f, s⟩². -/
noncomputable def pole_quad (f c s : Lp ℝ 2 (volume.restrict (Icc (-L) L))) : ℝ :=
  2 * (inner ℝ f c)^2 - 2 * (inner ℝ f s)^2

/-- Even parity condition: the projection onto the odd mode sinh vanishes. -/
def is_even (f s : Lp ℝ 2 (volume.restrict (Icc (-L) L))) : Prop :=
  inner ℝ f s = 0

/-- Odd parity condition: the projection onto the even mode cosh vanishes. -/
def is_odd (f c : Lp ℝ 2 (volume.restrict (Icc (-L) L))) : Prop :=
  inner ℝ f c = 0

/-- On the even block, the pole form is non-negative. -/
theorem pole_even_lower (f c s : Lp ℝ 2 (volume.restrict (Icc (-L) L)))
    (heven : is_even f s) :
    0 ≤ pole_quad f c s := by
  unfold is_even at heven
  unfold pole_quad
  rw [heven]
  simp only [sq, mul_zero, sub_zero]
  nlinarith

/-- On the odd block, the pole form is bounded below by -2 ‖s‖² ‖f‖². -/
theorem pole_odd_lower (f c s : Lp ℝ 2 (volume.restrict (Icc (-L) L)))
    (hodd : is_odd f c) :
    -2 * ‖s‖^2 * ‖f‖^2 ≤ pole_quad f c s := by
  unfold is_odd at hodd
  unfold pole_quad
  rw [hodd]
  simp only [sq, mul_zero, zero_sub]
  have hcs := cs_sq f s
  nlinarith

/-- For any general function (without parity assumptions), the pole form
is always bounded below by -2 ‖s‖² ‖f‖². -/
theorem pole_general_lower (f c s : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    -2 * ‖s‖^2 * ‖f‖^2 ≤ pole_quad f c s := by
  unfold pole_quad
  have hcs := cs_sq f s
  have hc_sq : 0 ≤ (inner ℝ f c)^2 := sq_nonneg _
  nlinarith

/-- If ‖s‖² is bounded by S_bound, the odd lower bound specializes. -/
theorem pole_odd_bound (f c s : Lp ℝ 2 (volume.restrict (Icc (-L) L)))
    (hodd : is_odd f c) (S_bound : ℝ) (hs : ‖s‖^2 ≤ S_bound) :
    -2 * S_bound * ‖f‖^2 ≤ pole_quad f c s := by
  have h := pole_odd_lower f c s hodd
  have hf2 : 0 ≤ ‖f‖^2 := sq_nonneg _
  nlinarith

/-- If ‖s‖² is bounded by S_bound, the general lower bound specializes. -/
theorem pole_general_bound (f c s : Lp ℝ 2 (volume.restrict (Icc (-L) L)))
    (S_bound : ℝ) (hs : ‖s‖^2 ≤ S_bound) :
    -2 * S_bound * ‖f‖^2 ≤ pole_quad f c s := by
  have h := pole_general_lower f c s
  have hf2 : 0 ≤ ‖f‖^2 := sq_nonneg _
  nlinarith

end RHPoleShift

