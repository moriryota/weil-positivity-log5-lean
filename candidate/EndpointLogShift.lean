import EndpointLog
open MeasureTheory Set
namespace RHEndpointLog
 theorem right_log_memLp_two (L : ℝ) (hL : 0 < L) :
    MemLp (fun x : ℝ => Real.log (L-x)) 2 (volume.restrict (Icc (-L) L)) := by
  apply (memLp_two_iff_integrable_sq
    (Real.measurable_log.comp (measurable_const.sub measurable_id)).aestronglyMeasurable).2
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (show (0:ℝ) ≤ 2*L by linarith)).2 (log_sq_integrable (2*L) (by linarith))
  have ht := (hi.comp_sub_left L).symm
  have he : L - 2*L = -L := by ring
  simpa only [sub_zero, he, IntegrableOn, Function.comp_def, Pi.sub_apply, id_eq] using
    (intervalIntegrable_iff_integrableOn_Icc_of_le (show L-2*L ≤ L-0 by linarith)).1 ht
 theorem left_log_memLp_two (L : ℝ) (hL : 0 < L) :
    MemLp (fun x : ℝ => Real.log (L+x)) 2 (volume.restrict (Icc (-L) L)) := by
  apply (memLp_two_iff_integrable_sq
    (Real.measurable_log.comp (measurable_const.add measurable_id)).aestronglyMeasurable).2
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (show (0:ℝ) ≤ 2*L by linarith)).2 (log_sq_integrable (2*L) (by linarith))
  have ht := hi.comp_add_left L
  have he : 2*L-L=L := by ring
  simpa only [zero_sub, he, IntegrableOn, Function.comp_def, Pi.add_apply, id_eq] using
    (intervalIntegrable_iff_integrableOn_Icc_of_le (show 0-L ≤ 2*L-L by linarith)).1 ht
end RHEndpointLog
