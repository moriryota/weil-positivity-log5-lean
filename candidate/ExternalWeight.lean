import TailConvex
import OutsideIntegral
open MeasureTheory Set
namespace RHExternalPotential

theorem actual_external_weight {L x : ℝ} (hx : |x| < L) :
    IntegrableOn (fun y : ℝ => RH_Rebaseline.K_kernel |x-y|) ((Icc (-L) L)ᶜ) ∧
    RH_Rebaseline.T_tail L ≤ (1/2:ℝ) *
      (∫ y in (Icc (-L) L)ᶜ, RH_Rebaseline.K_kernel |x-y|) := by
  have h := outside_integral hx
  refine ⟨h.1, ?_⟩
  rw [h.2]
  have hs := tail_symmetric_lower hx
  linarith
end RHExternalPotential
