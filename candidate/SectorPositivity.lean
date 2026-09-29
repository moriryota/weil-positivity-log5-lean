import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic

/-
# SectorPositivity.lean

Strict positivity on a single sector for any non-zero element in the form domain,
including the pure-tail case where low-frequency projection coefficients are zero.
-/

namespace RHSectorPositivity

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Strict positivity in the pure tail case (s = 0, so p = 0 and r ≠ 0). -/
theorem pure_tail_positivity
    (Q : E → ℝ) (r : E) (d : ℝ)
    (h_tail : d * ‖r‖^2 ≤ Q r)
    (h_d_pos : 0 < d)
    (h_r_ne_zero : r ≠ 0) :
    0 < Q r := by
  have h_norm_pos : 0 < ‖r‖ := norm_pos_iff.mpr h_r_ne_zero
  have h_norm_sq_pos : 0 < ‖r‖^2 := sq_pos_of_pos h_norm_pos
  have h_d_norm_pos : 0 < d * ‖r‖^2 := mul_pos h_d_pos h_norm_sq_pos
  exact lt_of_lt_of_le h_d_norm_pos h_tail

/-- Strict positivity in the certified low-frequency case (s > 0). -/
theorem certified_low_positivity
    (Q : E → ℝ) (x : E) (margin s : ℝ)
    (h_lower : margin * s ≤ Q x)
    (h_margin_pos : 0 < margin)
    (h_s_pos : 0 < s) :
    0 < Q x := by
  have h_prod_pos : 0 < margin * s := mul_pos h_margin_pos h_s_pos
  exact lt_of_lt_of_le h_prod_pos h_lower

/-- Sector strict positivity covering all non-zero elements, including pure tails (s = 0). -/
theorem sector_strict_positivity
    (Q : E → ℝ) (p r : E) (s margin d : ℝ)
    (h_lower : margin * s ≤ Q (p + r))
    (h_margin_pos : 0 < margin)
    (h_tail : d * ‖r‖^2 ≤ Q r)
    (h_d_pos : 0 < d)
    (h_s_nonneg : 0 ≤ s)
    (h_p_zero_of_s_zero : s = 0 → p = 0)
    (h_nonzero : p + r ≠ 0) :
    0 < Q (p + r) := by
  rcases eq_or_lt_of_le h_s_nonneg with (hs_eq | hs_pos)
  · -- Case s = 0: pure tail
    have hp_zero : p = 0 := h_p_zero_of_s_zero (hs_eq.symm)
    rw [hp_zero, zero_add] at h_nonzero ⊢
    exact pure_tail_positivity Q r d h_tail h_d_pos h_nonzero
  · -- Case s > 0: low-frequency certificate
    exact certified_low_positivity Q (p + r) margin s h_lower h_margin_pos hs_pos

/-- Nonnegativity on the entire sector space. -/
theorem sector_nonnegative
    (Q : E → ℝ) (p r : E) (s margin d : ℝ)
    (h_lower : margin * s ≤ Q (p + r))
    (h_margin_pos : 0 < margin)
    (h_tail : d * ‖r‖^2 ≤ Q r)
    (h_d_pos : 0 < d)
    (h_s_nonneg : 0 ≤ s)
    (h_p_zero_of_s_zero : s = 0 → p = 0)
    (h_zero_eq : p + r = 0 → Q (p + r) = 0) :
    0 ≤ Q (p + r) := by
  by_cases hz : p + r = 0
  · rw [h_zero_eq hz]
  · exact le_of_lt (sector_strict_positivity Q p r s margin d h_lower h_margin_pos h_tail h_d_pos h_s_nonneg h_p_zero_of_s_zero hz)

end RHSectorPositivity

