import BandTail
import WeilDecomposition
import SchurStrictPositivity
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace RHWeilTailIntegration

/-- Elementary completion of squares for 2x2 quadratic form:
d * v^2 - 2 * γ * u * v + (γ^2 / d) * u^2 is non-negative when d > 0. -/
theorem completion_of_squares (d γ u v : ℝ) (hd : 0 < d) :
    0 ≤ d * v^2 - 2 * γ * u * v + (γ^2 / d) * u^2 := by
  have hd_ne : d ≠ 0 := ne_of_gt hd
  have h_sq : 0 ≤ (d * v - γ * u)^2 := sq_nonneg _
  have h_exp : (d * v - γ * u)^2 = d * (d * v^2 - 2 * γ * u * v + (γ^2 / d) * u^2) := by
    calc (d * v - γ * u)^2 = d * (d * v^2) - 2 * d * γ * u * v + γ^2 * u^2 := by ring
    _ = d * (d * v^2 - 2 * γ * u * v) + (d * (γ^2 / d)) * u^2 := by
      rw [mul_div_cancel₀ (γ^2) hd_ne]
      ring
    _ = d * (d * v^2 - 2 * γ * u * v + (γ^2 / d) * u^2) := by ring
  have h_mul : 0 ≤ d * (d * v^2 - 2 * γ * u * v + (γ^2 / d) * u^2) := by
    rwa [← h_exp]
  have hd_inv : 0 ≤ d⁻¹ := le_of_lt (inv_pos.mpr hd)
  have h_prod : 0 ≤ d⁻¹ * (d * (d * v^2 - 2 * γ * u * v + (γ^2 / d) * u^2)) :=
    mul_nonneg hd_inv h_mul
  have h_id : d⁻¹ * (d * (d * v^2 - 2 * γ * u * v + (γ^2 / d) * u^2)) =
      d * v^2 - 2 * γ * u * v + (γ^2 / d) * u^2 := by
    calc d⁻¹ * (d * (d * v^2 - 2 * γ * u * v + (γ^2 / d) * u^2))
      _ = (d⁻¹ * d) * (d * v^2 - 2 * γ * u * v + (γ^2 / d) * u^2) := by ring
      _ = 1 * (d * v^2 - 2 * γ * u * v + (γ^2 / d) * u^2) := by rw [inv_mul_cancel₀ hd_ne]
      _ = d * v^2 - 2 * γ * u * v + (γ^2 / d) * u^2 := by ring
  rwa [h_id] at h_prod

/-- Lower bound on 2x2 quadratic form by Schur complement margin:
σ * u^2 - 2 * γ * u * v + d * v^2 ≥ (σ - γ^2 / d) * u^2. -/
theorem quadratic_schur_lower (σ d γ u v : ℝ) (hd : 0 < d) :
    (σ - γ^2 / d) * u^2 ≤ σ * u^2 - 2 * γ * u * v + d * v^2 := by
  have h := completion_of_squares d γ u v hd
  linarith

/-- Schur margin positivity:
If d > 0, u > 0, and γ^2 < σ * d, then (σ - γ^2 / d) * u > 0. -/
theorem schur_factor_pos (σ d γ : ℝ) (hd : 0 < d) (h_schur : γ^2 < σ * d) :
    0 < σ - γ^2 / d := by
  have hd_ne : d ≠ 0 := ne_of_gt hd
  have h1 : γ^2 / d < σ := by
    rw [div_lt_iff₀ hd]
    linarith
  linarith

/-- Strict positivity of 2x2 quadratic form when u > 0:
If u > 0, d > 0, and γ^2 < σ * d, then σ * u^2 - 2 * γ * u * v + d * v^2 > 0. -/
theorem quadratic_schur_pos (σ d γ u v : ℝ)
    (hu : 0 < u) (hd : 0 < d) (h_schur : γ^2 < σ * d) :
    0 < σ * u^2 - 2 * γ * u * v + d * v^2 := by
  have h_factor : 0 < σ - γ^2 / d := schur_factor_pos σ d γ hd h_schur
  have hu2 : 0 < u^2 := sq_pos_of_ne_zero (ne_of_gt hu)
  have h_bound := quadratic_schur_lower σ d γ u v hd
  have h_pos : 0 < (σ - γ^2 / d) * u^2 := mul_pos h_factor hu2
  exact lt_of_lt_of_le h_pos h_bound

/-- Full quadratic form strict positivity on orthogonal sum p + r:
Given:
- Decomposition: Q(p + r) = Q(p) + 2 * B p r + Q(r)
- Cross term bound: 2 * |B p r| ≤ 2 * γ * u * ‖r‖ where u = ‖p‖
- Low-degree bound: σ * u^2 ≤ Q(p)
- Tail bound: d * ‖r‖^2 ≤ Q(r)
- Schur margin: γ^2 < σ * d
- Non-zero vector: p + r ≠ 0 (either u > 0 or ‖r‖ > 0)
Then Q(p + r) > 0. -/
theorem full_weil_schur_positive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : LinearMap.BilinForm ℝ E)
    (p r : E) (σ d γ u : ℝ)
    (hu_nonneg : 0 ≤ u)
    (hd : 0 < d)
    (h_schur : γ^2 < σ * d)
    (h_split : RHWeilDecomposition.quad_of_bilin B (p + r) =
      RHWeilDecomposition.quad_of_bilin B p + 2 * B p r + RHWeilDecomposition.quad_of_bilin B r)
    (h_low : σ * u^2 ≤ RHWeilDecomposition.quad_of_bilin B p)
    (h_tail : d * ‖r‖^2 ≤ RHWeilDecomposition.quad_of_bilin B r)
    (h_cross : 2 * |B p r| ≤ 2 * γ * u * ‖r‖)
    (h_nonzero : 0 < u ∨ 0 < ‖r‖) :
    0 < RHWeilDecomposition.quad_of_bilin B (p + r) := by
  rw [h_split]
  rcases eq_or_lt_of_le hu_nonneg with heq | hu_pos
  · -- Case 1: u = 0 (pure tail)
    have hu_zero : u = 0 := heq.symm
    have hr_pos : 0 < ‖r‖ := by
      rcases h_nonzero with hu_gt | hr_gt
      · linarith
      · exact hr_gt
    have h_cross0 : 2 * |B p r| ≤ 0 := by
      calc 2 * |B p r| ≤ 2 * γ * u * ‖r‖ := h_cross
      _ = 2 * γ * 0 * ‖r‖ := by rw [hu_zero]
      _ = 0 := by ring
    have h_abs_nonneg : 0 ≤ |B p r| := abs_nonneg _
    have h_abs_zero : |B p r| = 0 := by linarith
    have h_B_zero : B p r = 0 := abs_eq_zero.mp h_abs_zero
    have h_low0 : 0 ≤ RHWeilDecomposition.quad_of_bilin B p := by
      calc 0 = σ * 0^2 := by ring
      _ = σ * u^2 := by rw [hu_zero]
      _ ≤ RHWeilDecomposition.quad_of_bilin B p := h_low
    have hr2_pos : 0 < ‖r‖^2 := sq_pos_of_ne_zero (ne_of_gt hr_pos)
    have h_tail_pos : 0 < d * ‖r‖^2 := mul_pos hd hr2_pos
    have h_Qr_pos : 0 < RHWeilDecomposition.quad_of_bilin B r :=
      lt_of_lt_of_le h_tail_pos h_tail
    calc 0 < RHWeilDecomposition.quad_of_bilin B r := h_Qr_pos
    _ = 0 + 2 * 0 + RHWeilDecomposition.quad_of_bilin B r := by ring
    _ ≤ RHWeilDecomposition.quad_of_bilin B p + 2 * B p r + RHWeilDecomposition.quad_of_bilin B r := by
      rw [h_B_zero]
      linarith
  · -- Case 2: u > 0 (low-degree component active)
    have h_cross_le : - (2 * γ * u * ‖r‖) ≤ 2 * B p r := by
      have h_abs : 2 * |B p r| = |2 * B p r| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      rw [h_abs] at h_cross
      exact neg_le_of_abs_le h_cross
    have h_sum_le : σ * u^2 - 2 * γ * u * ‖r‖ + d * ‖r‖^2 ≤
        RHWeilDecomposition.quad_of_bilin B p + 2 * B p r + RHWeilDecomposition.quad_of_bilin B r := by
      linarith
    have h_quad_pos := quadratic_schur_pos σ d γ u ‖r‖ hu_pos hd h_schur
    exact lt_of_lt_of_le h_quad_pos h_sum_le

end RHWeilTailIntegration

