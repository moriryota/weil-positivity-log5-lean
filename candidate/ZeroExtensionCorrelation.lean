import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure

open MeasureTheory Set

namespace RHZeroExtension

/-- Extending a restricted L² function by zero preserves L² membership. -/
theorem indicator_memLp {S : Set ℝ} (hS : MeasurableSet S) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict S)) :
    MemLp (S.indicator f) 2 volume :=
  (memLp_indicator_iff_restrict hS).2 hf

/-- Every real translation preserves L² membership for Lebesgue measure. -/
theorem translate_memLp {u : ℝ → ℝ} (hu : MemLp u 2 volume) (d : ℝ) :
    MemLp (fun t => u (t+d)) 2 volume := by
  exact hu.comp_measurePreserving (measurePreserving_add_right volume d)

/-- A correlation of two L² functions, with any translation, is integrable. -/
theorem correlation_integrable {u v : ℝ → ℝ}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) (d : ℝ) :
    Integrable (fun t => u t * v (t+d)) volume := by
  exact hu.integrable_mul (translate_memLp hv d)

/-- The canonical representative of an interval Lp element has an L² zero extension. -/
theorem lp_zero_extension_memLp (L : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) :
    MemLp ((Icc (-L) L).indicator (f : ℝ → ℝ)) 2 volume :=
  indicator_memLp measurableSet_Icc (Lp.memLp f)

/-- The zero extension of an interval Lp element has integrable correlation at every shift. -/
theorem lp_zero_extension_correlation_integrable (L : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Icc (-L) L))) (d : ℝ) :
    Integrable (fun t =>
      (Icc (-L) L).indicator (f : ℝ → ℝ) t *
      (Icc (-L) L).indicator (f : ℝ → ℝ) (t+d)) volume :=
  correlation_integrable (lp_zero_extension_memLp L f) (lp_zero_extension_memLp L f) d

end RHZeroExtension

