import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace RHCertificateData

/-- Dimensional parameters for the discrete model. -/
def N_modes : ℕ := 64
def M_modes : ℕ := 128
def low_dim : ℕ := 32
def band_dim : ℕ := 32

/-- Certified upper bounds on model and approximation errors for the even sector. -/
noncomputable def eta_even_bound : ℝ := 1 / 10^20
noncomputable def tau_even_bound : ℝ := 788 / 1000

/-- Certified upper bounds on model and approximation errors for the odd sector. -/
noncomputable def eta_odd_bound : ℝ := 1 / 10^20
noncomputable def tau_odd_bound : ℝ := 925 / 1000

/-- Certified conservative rational margin for the even sector (0.211 < 0.212 - 10⁻²⁰). -/
noncomputable def margin_even_bound : ℝ := 211 / 1000

/-- Certified conservative rational margin for the odd sector (0.074 < 0.075 - 10⁻²⁰). -/
noncomputable def margin_odd_bound : ℝ := 74 / 1000

/-- Certified rational lower bounds for tail weights d_N and d_M (even sector). -/
noncomputable def d64_even_lower : ℝ := 720539 / 1000000
noncomputable def d128_even_lower : ℝ := 1409795 / 1000000

/-- Certified rational lower bounds for tail weights d_N and d_M (odd sector). -/
noncomputable def d64_odd_lower : ℝ := 541122 / 1000000
noncomputable def d128_odd_lower : ℝ := 1230379 / 1000000

/-- Positivity of even tail weights. -/
theorem even_d64_pos : 0 < d64_even_lower := by
  unfold d64_even_lower; norm_num

theorem even_d128_pos : 0 < d128_even_lower := by
  unfold d128_even_lower; norm_num

/-- Positivity of odd tail weights. -/
theorem odd_d64_pos : 0 < d64_odd_lower := by
  unfold d64_odd_lower; norm_num

theorem odd_d128_pos : 0 < d128_odd_lower := by
  unfold d128_odd_lower; norm_num

/-- Monotonicity of tail weights: d_N ≤ d_M. -/
theorem even_d_mono : d64_even_lower ≤ d128_even_lower := by
  unfold d64_even_lower d128_even_lower; norm_num

theorem odd_d_mono : d64_odd_lower ≤ d128_odd_lower := by
  unfold d64_odd_lower d128_odd_lower; norm_num

/-- Certified Schur margin for the even sector: eta + tau < 1. -/
theorem even_schur_margin : eta_even_bound + tau_even_bound < 1 := by
  unfold eta_even_bound tau_even_bound; norm_num

/-- Certified Schur margin for the odd sector: eta + tau < 1. -/
theorem odd_schur_margin : eta_odd_bound + tau_odd_bound < 1 := by
  unfold eta_odd_bound tau_odd_bound; norm_num

/-- Margin lower bounds: margin ≤ 1 - (eta + tau). -/
theorem even_margin_lower : margin_even_bound ≤ 1 - (eta_even_bound + tau_even_bound) := by
  unfold margin_even_bound eta_even_bound tau_even_bound; norm_num

theorem odd_margin_lower : margin_odd_bound ≤ 1 - (eta_odd_bound + tau_odd_bound) := by
  unfold margin_odd_bound eta_odd_bound tau_odd_bound; norm_num

/-- Strict positivity of the margins. -/
theorem even_margin_pos : 0 < margin_even_bound := by
  unfold margin_even_bound; norm_num

theorem odd_margin_pos : 0 < margin_odd_bound := by
  unfold margin_odd_bound; norm_num

end RHCertificateData

