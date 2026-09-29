import FormDomain

open MeasureTheory Set Filter
open scoped ENNReal
namespace RHFormDomain
set_option maxHeartbeats 1000000

lemma measurable_kernel : Measurable kernel := by unfold kernel; fun_prop

lemma measurable_density {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (fun p : ℝ × ℝ => kernel (p.1-p.2) * ENNReal.ofReal (‖f p.1-f p.2‖^2)) := by
  have hk := measurable_kernel
  fun_prop

lemma square_add_le (a b : ℂ) : ‖a+b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have h := norm_add_le a b
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hab := norm_nonneg (a+b)
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

lemma energy_add_le {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g) :
    energy (f+g) ≤ 2*energy f+2*energy g := by
  have hp (x y : ℝ) : kernel (x-y)*ENNReal.ofReal (‖(f+g) x-(f+g) y‖^2) ≤
      2*(kernel (x-y)*ENNReal.ofReal (‖f x-f y‖^2)) +
      2*(kernel (x-y)*ENNReal.ofReal (‖g x-g y‖^2)) := by
    have h := ENNReal.ofReal_le_ofReal (square_add_le (f x-f y) (g x-g y))
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_mul (by norm_num)] at h
    norm_num only [ENNReal.ofReal_ofNat] at h
    have he : (f+g) x-(f+g) y = (f x-f y)+(g x-g y) := by simp only [Pi.add_apply]; ring
    rw [he]
    convert mul_le_mul_left h (kernel (x-y)) using 1 <;> ring
  have hm := lintegral_mono (μ := volume) (fun x => lintegral_mono (μ := volume) (hp x))
  have hmf := measurable_density hf
  have hmg := measurable_density hg
  have inner (x : ℝ) :
      (∫⁻ y, 2*(kernel (x-y)*ENNReal.ofReal (‖f x-f y‖^2)) +
        2*(kernel (x-y)*ENNReal.ofReal (‖g x-g y‖^2))) =
      2*(∫⁻ y, kernel (x-y)*ENNReal.ofReal (‖f x-f y‖^2)) +
        2*(∫⁻ y, kernel (x-y)*ENNReal.ofReal (‖g x-g y‖^2)) := by
    have hfx : Measurable (fun y => kernel (x-y)*ENNReal.ofReal (‖f x-f y‖^2)) :=
      by
        have hk := measurable_kernel
        fun_prop
    rw [lintegral_add_left (hfx.const_mul 2)]
    simp_rw [lintegral_const_mul' _ _ (by norm_num : (2:ℝ≥0∞) ≠ ⊤)]
  simp_rw [inner] at hm
  have houter : Measurable (fun x => ∫⁻ y, kernel (x-y)*ENNReal.ofReal (‖f x-f y‖^2)) :=
    hmf.lintegral_prod_right'
  rw [lintegral_add_left (houter.const_mul 2)] at hm
  simp_rw [lintegral_const_mul' _ _ (by norm_num : (2:ℝ≥0∞) ≠ ⊤)] at hm
  unfold energy
  convert mul_le_mul_left hm (4:ℝ≥0∞)⁻¹ using 1 <;> ring

lemma energy_smul (c : ℂ) (f : ℝ → ℂ) :
    energy (c • f) = ENNReal.ofReal (‖c‖^2) * energy f := by
  have he (x y : ℝ) : kernel (x-y)*ENNReal.ofReal (‖(c • f) x-(c • f) y‖^2) =
      ENNReal.ofReal (‖c‖^2)*(kernel (x-y)*ENNReal.ofReal (‖f x-f y‖^2)) := by
    simp only [Pi.smul_apply, ← smul_sub, norm_smul, mul_pow,
      ENNReal.ofReal_mul (sq_nonneg ‖c‖)]
    ring
  unfold energy
  simp_rw [he, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  ring

lemma extend_add (L : ℝ) (f g : ℝ → ℂ) : extend L (f+g) = extend L f+extend L g := by
  exact Set.indicator_add _ _ _

lemma extend_smul (L : ℝ) (c : ℂ) (f : ℝ → ℂ) : extend L (c • f) = c • extend L f := by
  funext x
  by_cases h : x ∈ Icc (-L) L <;> simp [extend, h]

lemma intervalEnergy_smul (L : ℝ) (c : ℂ) (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    intervalEnergy L (c • f) = ENNReal.ofReal (‖c‖^2) * intervalEnergy L f := by
  unfold intervalEnergy
  rw [energy_extend_congr_ae (Lp.coeFn_smul c f), extend_smul, energy_smul]

lemma smul_mem {L : ℝ} {f : Lp ℂ 2 (volume.restrict (Icc (-L) L))}
    (hf : InDomain L f) (c : ℂ) : InDomain L (c • f) := by
  unfold InDomain at *
  rw [intervalEnergy_smul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf

lemma intervalEnergy_add_le (L : ℝ) (f g : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    intervalEnergy L (f+g) ≤ 2*intervalEnergy L f+2*intervalEnergy L g := by
  let F := (Lp.aestronglyMeasurable f).mk f
  let G := (Lp.aestronglyMeasurable g).mk g
  have hF : (f : ℝ → ℂ) =ᵐ[volume.restrict (Icc (-L) L)] F := (Lp.aestronglyMeasurable f).ae_eq_mk
  have hG : (g : ℝ → ℂ) =ᵐ[volume.restrict (Icc (-L) L)] G := (Lp.aestronglyMeasurable g).ae_eq_mk
  have hFG := (Lp.coeFn_add f g).trans (hF.add hG)
  unfold intervalEnergy
  rw [energy_extend_congr_ae hFG, energy_extend_congr_ae hF, energy_extend_congr_ae hG,
    extend_add]
  exact energy_add_le ((Lp.aestronglyMeasurable f).measurable_mk.indicator measurableSet_Icc)
    ((Lp.aestronglyMeasurable g).measurable_mk.indicator measurableSet_Icc)

lemma add_mem {L : ℝ} {f g : Lp ℂ 2 (volume.restrict (Icc (-L) L))}
    (hf : InDomain L f) (hg : InDomain L g) : InDomain L (f+g) := by
  exact lt_of_le_of_lt (intervalEnergy_add_le L f g)
    (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) hf,
      ENNReal.mul_lt_top (by norm_num) hg⟩)

/-- The finite-energy domain really is a complex linear subspace of interval L². -/
noncomputable def formSubmodule (L : ℝ) : Submodule ℂ (Lp ℂ 2 (volume.restrict (Icc (-L) L))) where
  carrier := InDomain L
  zero_mem' := zero_mem L
  add_mem' := add_mem
  smul_mem' := fun c _ hf => smul_mem hf c
end RHFormDomain
