import ConditionalLog5
import RealWeilShift
import ConcreteParameters

open RHConditionalLog5 RHTargetFormBinding RHRealWeil

lemma targetQ_real_eq_spatial_weil (u : ℝ → ℝ) :
    targetQ_real u = spatial_weil u := by
  unfold targetQ_real spatial_weil RHWeilShift.h0 RHAutocorrEnergy.spatialEnergy
  rfl

