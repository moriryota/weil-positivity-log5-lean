import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Function.L2Space
open MeasureTheory Set Filter
open scoped Topology
namespace RHEndpointLog
/-- The endpoint logarithm is square-integrable on every positive finite interval. -/
theorem log_sq_integrable (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => (Real.log x)^2) (Icc 0 a) := by
  have ho : (fun x : ℝ => (Real.log x)^2) =O[𝓝[>] 0]
      (fun x : ℝ => x ^ (- (1/2 : ℝ))) := by
    simpa only [Real.rpow_two, sq_abs] using
      (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (2 : ℝ)
        (by norm_num : -(1/2 : ℝ) < 0)).isBigO
  have hp : IntegrableAtFilter (fun x : ℝ => x ^ (-(1/2 : ℝ))) (𝓝[>] 0) volume :=
    ⟨Ioo 0 a, Ioo_mem_nhdsGT ha,
      (intervalIntegral.integrableOn_Ioo_rpow_iff ha).2 (by norm_num)⟩
  have hm : StronglyMeasurableAtFilter (fun x : ℝ => (Real.log x)^2) (𝓝[>] 0) volume :=
    ⟨univ, univ_mem, (Real.measurable_log.pow_const 2).aestronglyMeasurable⟩
  obtain ⟨s, hs, hi⟩ := ho.integrableAtFilter hm hp
  obtain ⟨b, hb, hbs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hs
  have hib : IntervalIntegrable (fun x : ℝ => (Real.log x)^2) volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.le).2 (hi.mono_set hbs)
  have hba : IntervalIntegrable (fun x : ℝ => (Real.log x)^2) volume b a := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.pow
    apply Real.continuousOn_log.mono
    intro x hx
    have hx' : min b a ≤ x := hx.1
    have : 0 < x := lt_of_lt_of_le (lt_min hb ha) hx'
    simpa using this.ne'
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le ha.le).1 (hib.trans hba)

theorem log_memLp_two (a : ℝ) (ha : 0 < a) :
    MemLp Real.log 2 (volume.restrict (Icc 0 a)) :=
  (memLp_two_iff_integrable_sq Real.measurable_log.aestronglyMeasurable).2
    (log_sq_integrable a ha)
end RHEndpointLog
