import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.NormNum

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RHEnergyMass

theorem norm_mass (L : ℝ)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    ∫⁻ x in Icc (-L) L, ENNReal.ofReal (‖f x‖ ^ 2) =
      ENNReal.ofReal (‖f‖ ^ 2) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral
    (μ := volume.restrict (Icc (-L) L)) (f := (f : ℝ → ℂ)) (p := (2 : ℝ≥0)) (by norm_num : (2 : ℝ≥0) ≠ 0) (Lp.aestronglyMeasurable f)
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two,
    ← Lp.enorm_def, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h.symm

end RHEnergyMass

