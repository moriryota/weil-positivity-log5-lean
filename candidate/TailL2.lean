import TailLogBound
import EndpointLogShift
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
open MeasureTheory Set
namespace RHTailL2
open RH_Rebaseline RHTailLogBound RHEndpointLog
lemma measurable_tail : Measurable T_tail := by
  unfold T_tail Real.artanh
  fun_prop

theorem right_tail_memLp_two (L : ℝ) (hL : 0 < L) :
    MemLp (fun x : ℝ => T_tail (L-x)) 2 (volume.restrict (Icc (-L) L)) := by
  let C := T_tail (2*L) + Real.exp L * Real.log (2*L)
  have hg : MemLp (fun x : ℝ => C - Real.exp L * Real.log (L-x)) 2
      (volume.restrict (Icc (-L) L)) :=
    (memLp_const C).sub ((right_log_memLp_two L hL).const_mul (Real.exp L))
  apply hg.mono' ((measurable_tail.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hh : |x| < L := abs_lt.mpr hx
  change ‖T_tail (L-x)‖ ≤ C - Real.exp L * Real.log (L-x)
  rw [Real.norm_eq_abs, abs_of_pos (T_tail_pos (sub_pos.mpr hx.2))]
  have h := right_tail_log_bound hh
  dsimp [C]
  nlinarith

theorem left_tail_memLp_two (L : ℝ) (hL : 0 < L) :
    MemLp (fun x : ℝ => T_tail (L+x)) 2 (volume.restrict (Icc (-L) L)) := by
  let C := T_tail (2*L) + Real.exp L * Real.log (2*L)
  have hg : MemLp (fun x : ℝ => C - Real.exp L * Real.log (L+x)) 2
      (volume.restrict (Icc (-L) L)) :=
    (memLp_const C).sub ((left_log_memLp_two L hL).const_mul (Real.exp L))
  apply hg.mono' ((measurable_tail.comp (measurable_const.add measurable_id)).aestronglyMeasurable)
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hh : |x| < L := abs_lt.mpr hx
  change ‖T_tail (L+x)‖ ≤ C - Real.exp L * Real.log (L+x)
  rw [Real.norm_eq_abs, abs_of_pos (T_tail_pos (by linarith [hx.1] : 0 < L+x))]
  have h := left_tail_log_bound hh
  dsimp [C]
  nlinarith
end RHTailL2
