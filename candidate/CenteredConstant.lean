import WindowEnergy
import ExtensionLp

open MeasureTheory Set Filter
open scoped ENNReal
namespace RHFormDomain
open RHIntervalDifference

lemma shifted_cwindow (L : ℝ) :
    (fun x => cwindow (2*L) (x+L)) = (Ioc (-L) L).indicator (fun _ : ℝ => (1:ℂ)) := by
  funext x
  have h : (0 < x+L ∧ x+L ≤ 2*L) ↔ (-L < x ∧ x ≤ L) := by constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  simp only [cwindow, window, Set.indicator, mem_Ioc, h]
  split_ifs <;> simp

lemma centered_one_ae (L : ℝ) :
    extend L (fun _ : ℝ => (1:ℂ)) =ᵐ[volume] (fun x => cwindow (2*L) (x+L)) := by
  rw [shifted_cwindow]
  exact indicator_ae_eq_of_ae_eq_set Ioc_ae_eq_Icc.symm

/-- The original centered closed interval and the exact ENNReal energy. -/
theorem centered_one_energy {L : ℝ} (hL : 0 ≤ L) :
    energy (extend L (fun _ : ℝ => (1:ℂ))) = ENNReal.ofReal
      (∫ s in Ioi (0:ℝ), min s (2*L) * RH_GammaFinalFormula.K_kernel s) := by
  rw [energy_congr_ae (centered_one_ae L), energy_translate, cwindow_energy (by linarith)]

lemma centered_one_finite {L : ℝ} (hL : 0 ≤ L) :
    energy (extend L (fun _ : ℝ => (1:ℂ))) < ⊤ := by
  rw [centered_one_energy hL]
  exact ENNReal.ofReal_lt_top

lemma interval_const_memLp (L : ℝ) (c : ℂ) :
    MemLp (fun _ : ℝ => c) 2 (volume.restrict (Icc (-L) L)) := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (-L) L)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  exact memLp_const c

noncomputable def intervalConst (L : ℝ) (c : ℂ) : Lp ℂ 2 (volume.restrict (Icc (-L) L)) :=
  (interval_const_memLp L c).toLp (fun _ => c)

lemma intervalConst_energy (L : ℝ) (c : ℂ) :
    intervalEnergy L (intervalConst L c) =
      ENNReal.ofReal (‖c‖^2) * energy (extend L (fun _ : ℝ => (1:ℂ))) := by
  unfold intervalEnergy intervalConst
  rw [energy_extend_congr_ae (MemLp.coeFn_toLp (interval_const_memLp L c))]
  have he : extend L (fun _ : ℝ => c) = c • extend L (fun _ : ℝ => (1:ℂ)) := by
    funext x
    by_cases h : x ∈ Icc (-L) L <;> simp [extend, h]
  rw [he, energy_smul]

/-- A concrete constant L² vector belongs to the finite-energy form domain. -/
theorem intervalConst_mem {L : ℝ} (hL : 0 ≤ L) (c : ℂ) : InDomain L (intervalConst L c) := by
  unfold InDomain
  rw [intervalConst_energy]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (centered_one_finite hL)

/-- For positive width the constant example is not merely the zero L² class. -/
lemma intervalConst_one_ne_zero {L : ℝ} (hL : 0 < L) : intervalConst L 1 ≠ 0 := by
  have hm : volume (Icc (-L) L) ≠ 0 := by
    rw [Real.volume_Icc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  haveI : (ae (volume.restrict (Icc (-L) L))).NeBot := ae_restrict_neBot.mpr hm
  intro hz
  have hc : (intervalConst L 1 : ℝ → ℂ) =ᵐ[volume.restrict (Icc (-L) L)] (fun _ => (1:ℂ)) :=
    MemLp.coeFn_toLp (interval_const_memLp L 1)
  rw [hz] at hc
  have hh := (Lp.coeFn_zero ℂ 2 (volume.restrict (Icc (-L) L))).symm.trans hc
  obtain ⟨x,hx⟩ := hh.exists
  norm_num at hx
end RHFormDomain
