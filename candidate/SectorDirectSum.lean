import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import SectorPositivity

/-
# SectorDirectSum.lean

Direct sum positivity across orthogonal even and odd sectors.
If either sector is non-zero, the sum of quadratic forms is strictly positive.
-/

namespace RHSectorDirectSum

set_option linter.unusedSectionVars false

variable {E_e E_o : Type*} [NormedAddCommGroup E_e] [InnerProductSpace ℝ E_e] [NormedAddCommGroup E_o] [InnerProductSpace ℝ E_o]

/-- If (x_e, x_o) ≠ (0, 0), then x_e ≠ 0 or x_o ≠ 0. -/
lemma ne_zero_or_ne_zero {x_e : E_e} {x_o : E_o} (h : (x_e, x_o) ≠ (0, 0)) :
    x_e ≠ 0 ∨ x_o ≠ 0 := by
  contrapose! h
  ext <;> simp [h.1, h.2]

/-- Strict positivity of the direct sum quadratic form. -/
theorem direct_sum_strict_positivity
    (Q_e : E_e → ℝ) (Q_o : E_o → ℝ)
    (x_e : E_e) (x_o : E_o)
    (h_pos_e : x_e ≠ 0 → 0 < Q_e x_e)
    (h_pos_o : x_o ≠ 0 → 0 < Q_o x_o)
    (h_nonneg_e : 0 ≤ Q_e x_e)
    (h_nonneg_o : 0 ≤ Q_o x_o)
    (h_nonzero : (x_e, x_o) ≠ (0, 0)) :
    0 < Q_e x_e + Q_o x_o := by
  rcases ne_zero_or_ne_zero h_nonzero with (he | ho)
  · have h_pos := h_pos_e he
    exact add_pos_of_pos_of_nonneg h_pos h_nonneg_o
  · have h_pos := h_pos_o ho
    exact add_pos_of_nonneg_of_pos h_nonneg_e h_pos

/-- Nonnegativity of the direct sum quadratic form. -/
theorem direct_sum_nonneg
    (Q_e : E_e → ℝ) (Q_o : E_o → ℝ)
    (x_e : E_e) (x_o : E_o)
    (h_nonneg_e : 0 ≤ Q_e x_e)
    (h_nonneg_o : 0 ≤ Q_o x_o) :
    0 ≤ Q_e x_e + Q_o x_o := by
  exact add_nonneg h_nonneg_e h_nonneg_o

/-- Sector decomposition strict positivity integrating certified/pure-tail bounds from each sector. -/
theorem sector_pair_strict_positivity
    (Q_e : E_e → ℝ) (p_e r_e : E_e) (s_e margin_e d_e : ℝ)
    (Q_o : E_o → ℝ) (p_o r_o : E_o) (s_o margin_o d_o : ℝ)
    (h_low_e : margin_e * s_e ≤ Q_e (p_e + r_e))
    (h_margin_e : 0 < margin_e)
    (h_tail_e : d_e * ‖r_e‖^2 ≤ Q_e r_e)
    (h_d_e : 0 < d_e)
    (h_s_e_nonneg : 0 ≤ s_e)
    (h_p_e_zero : s_e = 0 → p_e = 0)
    (h_low_o : margin_o * s_o ≤ Q_o (p_o + r_o))
    (h_margin_o : 0 < margin_o)
    (h_tail_o : d_o * ‖r_o‖^2 ≤ Q_o r_o)
    (h_d_o : 0 < d_o)
    (h_s_o_nonneg : 0 ≤ s_o)
    (h_p_o_zero : s_o = 0 → p_o = 0)
    (h_zero_e : p_e + r_e = 0 → Q_e (p_e + r_e) = 0)
    (h_zero_o : p_o + r_o = 0 → Q_o (p_o + r_o) = 0)
    (h_nonzero : (p_e + r_e, p_o + r_o) ≠ (0, 0)) :
    0 < Q_e (p_e + r_e) + Q_o (p_o + r_o) := by
  apply direct_sum_strict_positivity Q_e Q_o (p_e + r_e) (p_o + r_o)
  · intro he
    exact RHSectorPositivity.sector_strict_positivity Q_e p_e r_e s_e margin_e d_e
      h_low_e h_margin_e h_tail_e h_d_e h_s_e_nonneg h_p_e_zero he
  · intro ho
    exact RHSectorPositivity.sector_strict_positivity Q_o p_o r_o s_o margin_o d_o
      h_low_o h_margin_o h_tail_o h_d_o h_s_o_nonneg h_p_o_zero ho
  · exact RHSectorPositivity.sector_nonnegative Q_e p_e r_e s_e margin_e d_e
      h_low_e h_margin_e h_tail_e h_d_e h_s_e_nonneg h_p_e_zero h_zero_e
  · exact RHSectorPositivity.sector_nonnegative Q_o p_o r_o s_o margin_o d_o
      h_low_o h_margin_o h_tail_o h_d_o h_s_o_nonneg h_p_o_zero h_zero_o
  · exact h_nonzero

end RHSectorDirectSum

