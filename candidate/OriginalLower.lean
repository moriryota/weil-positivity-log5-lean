import ActualSplit
import CrossMass
import KernelConnection
open MeasureTheory Set
open scoped ENNReal
namespace RHOriginalLower

theorem comparison_internal {L : ℝ} (hL : 0 < L) (hL1 : L ≤ 1)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    RHComparisonEnergy.intervalEnergy L f ≤ (4:ℝ≥0∞)⁻¹ * RHEnergySplit.internal L f := by
  unfold RHComparisonEnergy.intervalEnergy RHComparisonEnergy.energy RHEnergySplit.internal
  apply mul_le_mul' le_rfl
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact mul_le_mul' (RHKernelConnection.kernel_le_original hL hL1 x hx y hy) le_rfl

theorem energy_lower {L : ℝ} (hL : 0 < L) (hL1 : L ≤ 1)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    RHComparisonEnergy.intervalEnergy L f +
      ENNReal.ofReal (RH_Rebaseline.T_tail L) * ENNReal.ofReal (‖f‖^2) ≤
        RHFormDomain.intervalEnergy L f := by
  have hc := RHEnergyMass.cross_mass_lower hL f
  change (2:ℝ≥0∞)*ENNReal.ofReal (RH_Rebaseline.T_tail L)*ENNReal.ofReal (‖f‖^2) ≤
    RHEnergySplit.cross L f at hc
  have hm := mul_le_mul' (show (2:ℝ≥0∞)⁻¹ ≤ (2:ℝ≥0∞)⁻¹ from le_rfl) hc
  simp only [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (by norm_num : (2:ℝ≥0∞) ≠ ⊤), one_mul] at hm
  calc
    _ ≤ (4:ℝ≥0∞)⁻¹ * RHEnergySplit.internal L f + (2:ℝ≥0∞)⁻¹ * RHEnergySplit.cross L f :=
      add_le_add (comparison_internal hL hL1 f) hm
    _ = RHFormDomain.intervalEnergy L f := by
      rw [RHEnergySplit.actual_energy_split, mul_add]
      have h42 : (4:ℝ≥0∞)⁻¹ * 2 = (2:ℝ≥0∞)⁻¹ := by
        rw [show (4:ℝ≥0∞) = 2*2 by norm_num,
          ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        exact ENNReal.inv_mul_cancel_right (by norm_num) (by norm_num)
      simp only [← mul_assoc, h42]

theorem energy_lower_real {L : ℝ} (hL : 0 < L) (hL1 : L ≤ 1)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) (hf : RHFormDomain.InDomain L f) :
    (RHComparisonEnergy.intervalEnergy L f).toReal + RH_Rebaseline.T_tail L * ‖f‖^2 ≤
      (RHFormDomain.intervalEnergy L f).toReal := by
  have h := energy_lower hL hL1 f
  have hd : RHFormDomain.intervalEnergy L f ≠ ⊤ := ne_of_lt hf
  have hc : RHComparisonEnergy.intervalEnergy L f ≠ ⊤ :=
    ne_of_lt (RHKernelConnection.domain_of_original hL hL1 f hf)
  have hm : ENNReal.ofReal (RH_Rebaseline.T_tail L) * ENNReal.ofReal (‖f‖^2) ≠ ⊤ := by finiteness
  have hr := ENNReal.toReal_mono hd h
  rw [ENNReal.toReal_add hc hm, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (RH_Rebaseline.T_tail_pos hL).le,
    ENNReal.toReal_ofReal (sq_nonneg _)] at hr
  exact hr

theorem log5_energy_lower
    (f : Lp ℂ 2 (volume.restrict (Icc (-(Real.log 5/2)) (Real.log 5/2))))
    (hf : RHFormDomain.InDomain (Real.log 5/2) f) :
    (RHComparisonEnergy.intervalEnergy (Real.log 5/2) f).toReal +
      RH_Rebaseline.T_tail (Real.log 5/2)*‖f‖^2 ≤
        (RHFormDomain.intervalEnergy (Real.log 5/2) f).toReal :=
  energy_lower_real RHLog5Bridge.halfWidth_pos RHKernelElementary.log5_half_le_one f hf
end RHOriginalLower
