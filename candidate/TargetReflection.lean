import TargetFormBinding
import ParityCorrelation
open MeasureTheory
namespace RHTargetFormBinding
open RHParityCorrelation

theorem targetQ_real_reflect (u : ℝ → ℝ) :
    targetQ_real (fun x => u (-x)) = targetQ_real u := by
  have henergy : RHAutocorrEnergy.spatialEnergy (fun x => u (-x)) =
      RHAutocorrEnergy.spatialEnergy u := by
    unfold RHAutocorrEnergy.spatialEnergy
    rw [kernel_energy_reflection]
  have hc : (∫ x, u (-x) * Real.cosh (x/2)) =
      ∫ x, u x * Real.cosh (x/2) :=
    even_weight_reflection u _ (fun x => by simp only [neg_div, Real.cosh_neg])
  have hs : (∫ x, u (-x) * Real.sinh (x/2)) =
      -(∫ x, u x * Real.sinh (x/2)) :=
    odd_weight_reflection u _ (fun x => by simp only [neg_div, Real.sinh_neg])
  have ha (s : ℝ) : RH_LiteratureBridge.real_autocorr (fun x => u (-x)) s =
      RH_LiteratureBridge.real_autocorr u s := correlation_reflection u s
  unfold targetQ_real
  simp_rw [square_reflection, henergy, hc, hs, ha, neg_sq]

end RHTargetFormBinding
