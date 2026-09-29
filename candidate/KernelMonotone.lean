import RealAutocorr

namespace RHExternalPotential

/-- The positive Archimedean kernel decreases on the positive half-line. -/
theorem kernel_antitone : AntitoneOn RH_Rebaseline.K_kernel (Set.Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  rw [RH_Rebaseline.K_kernel_eq y hy, RH_Rebaseline.K_kernel_eq x hx]
  unfold RH_Rebaseline.K_kernel_alt
  have hnum : 2 * Real.exp (-y / 2) ≤ 2 * Real.exp (-x / 2) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Real.exp_le_exp.mpr (by linarith)
  have hdenpos : 0 < 1 - Real.exp (-2 * x) := by
    have hlt : Real.exp (-2 * x) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    linarith
  have hden : 1 - Real.exp (-2 * x) ≤ 1 - Real.exp (-2 * y) := by
    have h := Real.exp_le_exp.mpr (show -2 * y ≤ -2 * x by linarith)
    linarith
  exact div_le_div₀ (by positivity) hnum hdenpos hden

end RHExternalPotential
