import ActualComplete
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace RHActualTail
open RHLegendreDirections

theorem coefficient_mass {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    HasSum (fun n => ‖inner ℂ (direction L hL.le n) f‖ ^ 2) (‖f‖ ^ 2) := by
  have h := lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal)
    ((RHActualComplete.basis hL).repr f)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_natCast, Real.rpow_two,
    LinearIsometryEquiv.norm_map, HilbertBasis.repr_apply_apply,
    RHActualComplete.coe_basis] using h

theorem coefficient_mass_tendsto {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    Tendsto (fun M => ∑ n ∈ Finset.range M,
      ‖inner ℂ (direction L hL.le n) f‖ ^ 2) atTop (𝓝 (‖f‖ ^ 2)) :=
  (coefficient_mass hL f).tendsto_sum_nat
end RHActualTail
