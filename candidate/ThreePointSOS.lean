import Mathlib.Tactic

namespace RHThreePoint

/-- The quadratic form of the weighted three-point chain. -/
def form (α β x y z : ℝ) : ℝ := 2 * α * x * y + 2 * α * y * z + 2 * β * x * z

/-- A sum of three squares for the defect at the top eigenvalue. -/
theorem defect_sos (α β r lam x y z : ℝ)
    (hr : 0 < r) (hlam₁ : lam = 2 * α / r) (hlam₂ : lam = β + α * r) :
    lam * (x ^ 2 + y ^ 2 + z ^ 2) - form α β x y z =
      α / r * ((r * x - y) ^ 2 + (r * z - y) ^ 2) + β * (x - z) ^ 2 := by
  calc
    _ = (β + α * r) * (x ^ 2 + z ^ 2) + (2 * α / r) * y ^ 2 - form α β x y z := by rw [← hlam₁, ← hlam₂]; ring
    _ = _ := by unfold form; field_simp; ring

theorem top_bound (α β r lam x y z : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hr : 0 < r)
    (hlam₁ : lam = 2 * α / r) (hlam₂ : lam = β + α * r) :
    form α β x y z ≤ lam * (x ^ 2 + y ^ 2 + z ^ 2) := by
  have hs := defect_sos α β r lam x y z hr hlam₁ hlam₂
  have hp : 0 ≤ α / r * ((r * x - y) ^ 2 + (r * z - y) ^ 2) + β * (x - z) ^ 2 :=
    add_nonneg (mul_nonneg (div_nonneg hα hr.le) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (mul_nonneg hβ (sq_nonneg _))
  linarith

/-- On the orthogonal complement of `(1,r,1)`, both eigenvalues are nonpositive. -/
theorem perpendicular_nonpos (α β r lam x y z : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hr : 0 < r)
    (hlam₁ : lam = 2 * α / r) (hlam₂ : lam = β + α * r)
    (hperp : x + r * y + z = 0) :
    form α β x y z ≤ 0 := by
  have hy : y = -(x + z) / r := by apply (eq_div_iff hr.ne').2; nlinarith [hperp]
  have hs : -form α β x y z = β / 2 * (x - z) ^ 2 +
      (lam - β / 2) * (x + z) ^ 2 := by rw [hy, hlam₁]; unfold form; ring
  have hc : 0 ≤ lam - β / 2 := by rw [hlam₂]; nlinarith [mul_nonneg hα hr.le]
  have hp := add_nonneg (mul_nonneg (by positivity : 0 ≤ β / 2) (sq_nonneg (x-z)))
    (mul_nonneg hc (sq_nonneg (x+z)))
  linarith

/-- The defect has gap at least `lam` off the top direction, in orthogonal coordinates. -/
theorem shifted_gap (α β r lam x y z t : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hr : 0 < r)
    (hlam₁ : lam = 2 * α / r) (hlam₂ : lam = β + α * r)
    (hperp : x + r * y + z = 0) :
    lam * (x ^ 2 + y ^ 2 + z ^ 2) ≤
      lam * ((x+t)^2 + (y+r*t)^2 + (z+t)^2) - form α β (x+t) (y+r*t) (z+t) := by
  have hinv : lam * ((x+t)^2 + (y+r*t)^2 + (z+t)^2) - form α β (x+t) (y+r*t) (z+t) =
      lam * (x^2+y^2+z^2) - form α β x y z := by
    rw [defect_sos α β r lam (x+t) (y+r*t) (z+t) hr hlam₁ hlam₂,
      defect_sos α β r lam x y z hr hlam₁ hlam₂]
    ring
  rw [hinv]
  linarith [perpendicular_nonpos α β r lam x y z hα hβ hr hlam₁ hlam₂ hperp]

/-- Exact rank-one majorant, with its two transverse squares. -/
theorem rank_one_sos (α β r lam x y z : ℝ)
    (hr : 0 < r) (h₁ : lam = 2 * α / r) (h₂ : lam = β + α * r) :
    lam / (2+r^2) * (x+r*y+z)^2 - form α β x y z =
      β/2*(x-z)^2 + (lam-β)/(2*(2+r^2))*(r*(x+z)-2*y)^2 := by
  have ha : α = lam*r/2 := by have h := (eq_div_iff hr.ne').1 h₁; linarith
  have hb : β = lam-α*r := by linarith
  rw [hb, ha]
  unfold form
  have hd : (2+r^2) ≠ 0 := by positivity
  field_simp
  ring

/-- The other two eigenvalues are nonpositive, so the top projection alone majorizes the form. -/
theorem rank_one_bound (α β r lam x y z : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hr : 0 < r)
    (h₁ : lam = 2 * α / r) (h₂ : lam = β + α * r) :
    form α β x y z ≤ lam / (2+r^2) * (x+r*y+z)^2 := by
  have hs := rank_one_sos α β r lam x y z hr h₁ h₂
  have hc : 0 ≤ lam-β := by rw [h₂]; nlinarith [mul_nonneg hα hr.le]
  have hp : 0 ≤ β/2*(x-z)^2 + (lam-β)/(2*(2+r^2))*(r*(x+z)-2*y)^2 := by positivity
  linarith

end RHThreePoint


