import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set

namespace RHCentralMultiplier

/-- Multiplication by the indicator of the central interval, in the original interval L² space. -/
noncomputable def centralLp (L b : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    Lp ℝ 2 (volume.restrict (Icc (-L) L)) :=
  (MemLp.indicator (s := Ioo (L-b) (-L+b)) measurableSet_Ioo (Lp.memLp f)).toLp _

theorem coeFn_centralLp (L b : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    (centralLp L b f : ℝ → ℝ) =ᵐ[volume.restrict (Icc (-L) L)]
      (Ioo (L-b) (-L+b)).indicator (f : ℝ → ℝ) :=
  (MemLp.indicator (s := Ioo (L-b) (-L+b)) measurableSet_Ioo (Lp.memLp f)).coeFn_toLp

theorem norm_centralLp_le (L b : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    ‖centralLp L b f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coeFn_centralLp L b f] with x hx
  rw [hx]
  by_cases h : x ∈ Ioo (L-b) (-L+b)
  · simp only [indicator_of_mem h, le_refl]
  · simp only [indicator_of_notMem h, norm_zero, norm_nonneg]

end RHCentralMultiplier

