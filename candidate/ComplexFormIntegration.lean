import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import SectorPositivity
import SectorDirectSum

/-
# ComplexFormIntegration.lean

Integration of the real and imaginary parts of a complex test function.
Given f = u + i v ≠ 0, at least one of u or v is non-zero.
Combined with the even/odd sector decomposition, this proves strict positivity
of the full Weil quadratic form on any non-zero complex test function.
-/

namespace RHComplexFormIntegration

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Non-zero complex vector means real part is non-zero or imaginary part is non-zero. -/
lemma complex_ne_zero_iff {u v : E} (h : (u, v) ≠ (0, 0)) :
    u ≠ 0 ∨ v ≠ 0 := by
  contrapose! h
  ext <;> simp [h.1, h.2]

/-- Strict positivity of the complex quadratic form Re W(f, f) = Q(u) + Q(v). -/
theorem complex_quadratic_strict_positivity
    (Q : E → ℝ) (u v : E)
    (h_pos : ∀ x, x ≠ 0 → 0 < Q x)
    (h_nonneg : ∀ x, 0 ≤ Q x)
    (h_nonzero : (u, v) ≠ (0, 0)) :
    0 < Q u + Q v := by
  rcases complex_ne_zero_iff h_nonzero with (hu | hv)
  · have h_pos_u := h_pos u hu
    have h_nn_v := h_nonneg v
    exact add_pos_of_pos_of_nonneg h_pos_u h_nn_v
  · have h_pos_v := h_pos v hv
    have h_nn_u := h_nonneg u
    exact add_pos_of_nonneg_of_pos h_nn_u h_pos_v

/-- 4-sector decomposition (real even, real odd, imag even, imag odd). -/
theorem four_sector_strict_positivity
    {E_e E_o : Type*} [NormedAddCommGroup E_e] [InnerProductSpace ℝ E_e]
    [NormedAddCommGroup E_o] [InnerProductSpace ℝ E_o]
    (Q_e : E_e → ℝ) (Q_o : E_o → ℝ)
    (ue : E_e) (uo : E_o) (ve : E_e) (vo : E_o)
    (h_pos_e : ∀ x, x ≠ 0 → 0 < Q_e x)
    (h_pos_o : ∀ x, x ≠ 0 → 0 < Q_o x)
    (h_nonneg_e : ∀ x, 0 ≤ Q_e x)
    (h_nonneg_o : ∀ x, 0 ≤ Q_o x)
    (h_nonzero : (ue, uo, ve, vo) ≠ (0, 0, 0, 0)) :
    0 < Q_e ue + Q_o uo + Q_e ve + Q_o vo := by
  have h_cases : ue ≠ 0 ∨ uo ≠ 0 ∨ ve ≠ 0 ∨ vo ≠ 0 := by
    by_contra hc
    simp only [not_or, not_not] at hc
    apply h_nonzero
    ext
    · simp [hc.1]
    · simp [hc.2.1]
    · simp [hc.2.2.1]
    · simp [hc.2.2.2]
  rcases h_cases with (h1 | h2 | h3 | h4)
  · have p1 := h_pos_e ue h1
    have n2 := h_nonneg_o uo
    have n3 := h_nonneg_e ve
    have n4 := h_nonneg_o vo
    linarith
  · have n1 := h_nonneg_e ue
    have p2 := h_pos_o uo h2
    have n3 := h_nonneg_e ve
    have n4 := h_nonneg_o vo
    linarith
  · have n1 := h_nonneg_e ue
    have n2 := h_nonneg_o uo
    have p3 := h_pos_e ve h3
    have n4 := h_nonneg_o vo
    linarith
  · have n1 := h_nonneg_e ue
    have n2 := h_nonneg_o uo
    have n3 := h_nonneg_e ve
    have p4 := h_pos_o vo h4
    linarith

end RHComplexFormIntegration

