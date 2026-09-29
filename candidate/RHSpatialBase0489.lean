import StepA2_G2
import TestG1Energy
import KernelMoment

/-! # 0489 base: finite spatial energy gives product-measure integrability

 -/

open MeasureTheory Set
open scoped ENNReal

namespace RHSpatialBase0489
open RHConditionalLog5 RHResidualMembership RHLog5Bridge

/-- The real kernel evaluated at `|s|`, as used in `spatialEnergy`. -/
local notation "Kk" => RH_GammaFinalFormula.K_kernel

noncomputable def energyDensity (h : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  Kk |z.1 - z.2| * (h z.1 - h z.2) ^ 2

lemma kernel_abs_eq_toReal (s : ℝ) : Kk |s| = (RHFormDomain.kernel s).toReal := by
  rw [RHFormDomain.kernel_eq_old, ENNReal.toReal_ofReal (RHAutocorrEnergy.kernel_abs_nonneg s)]

lemma measurable_kernel_abs : Measurable (fun s : ℝ => Kk |s|) := by
  have h : (fun s : ℝ => Kk |s|) = fun s => (RHFormDomain.kernel s).toReal := by
    funext s; exact kernel_abs_eq_toReal s
  rw [h]
  exact RHFormDomain.measurable_kernel.ennreal_toReal

lemma measurable_kernel_prod : Measurable (fun z : ℝ × ℝ => Kk |z.1 - z.2|) :=
  measurable_kernel_abs.comp (measurable_fst.sub measurable_snd)

lemma measurable_diff {h : ℝ → ℝ} (hm : Measurable h) :
    Measurable (fun z : ℝ × ℝ => h z.1 - h z.2) :=
  (hm.comp measurable_fst).sub (hm.comp measurable_snd)

lemma energyDensity_nonneg (h : ℝ → ℝ) (z : ℝ × ℝ) : 0 ≤ energyDensity h z :=
  mul_nonneg (RHAutocorrEnergy.kernel_abs_nonneg _) (sq_nonneg _)

lemma energyDensity_measurable {h : ℝ → ℝ} (hm : Measurable h) :
    Measurable (energyDensity h) :=
  measurable_kernel_prod.mul ((measurable_diff hm).pow_const 2)

lemma ofReal_energyDensity (h : ℝ → ℝ) (x y : ℝ) :
    ENNReal.ofReal (energyDensity h (x, y)) =
      RHFormDomain.kernel (x - y) * ENNReal.ofReal (‖(h x : ℂ) - (h y : ℂ)‖ ^ 2) := by
  unfold energyDensity
  rw [RHFormDomain.kernel_eq_old, ← ENNReal.ofReal_mul (RHAutocorrEnergy.kernel_abs_nonneg _)]
  congr 2
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Finite extended energy (Lebesgue double integral) gives integrability on `ℝ × ℝ`. -/
theorem energyDensity_integrable {h : ℝ → ℝ} (hm : Measurable h)
    (hE : RHFormDomain.energy (fun x => (h x : ℂ)) < ⊤) :
    Integrable (energyDensity h) (volume.prod volume) := by
  refine ⟨(energyDensity_measurable hm).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (energyDensity_nonneg h))]
  rw [lintegral_prod _ ((energyDensity_measurable hm).ennreal_ofReal.aemeasurable)]
  simp_rw [ofReal_energyDensity]
  have h4 : (4:ℝ≥0∞)⁻¹ * (∫⁻ x, ∫⁻ y, RHFormDomain.kernel (x - y) *
      ENNReal.ofReal (‖(h x : ℂ) - (h y : ℂ)‖ ^ 2)) < ⊤ := hE
  exact ENNReal.lt_top_of_mul_ne_top_right h4.ne (by norm_num)

/-- The cross density `K (Df)(Dg)` is dominated by `(E_f + E_g)/2`. -/
theorem crossDensity_integrable {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hEf : RHFormDomain.energy (fun x => (f x : ℂ)) < ⊤)
    (hEg : RHFormDomain.energy (fun x => (g x : ℂ)) < ⊤) :
    Integrable (fun z : ℝ × ℝ => Kk |z.1 - z.2| * (f z.1 - f z.2) * (g z.1 - g z.2))
      (volume.prod volume) := by
  have hsum := ((energyDensity_integrable hf hEf).add (energyDensity_integrable hg hEg)).div_const 2
  refine hsum.mono' ?_ (Filter.Eventually.of_forall (fun z => ?_))
  · exact ((measurable_kernel_prod.mul (measurable_diff hf)).mul
      (measurable_diff hg)).aestronglyMeasurable
  · have hK := RHAutocorrEnergy.kernel_abs_nonneg (z.1 - z.2)
    simp only [energyDensity, Pi.add_apply, Real.norm_eq_abs]
    set a := f z.1 - f z.2
    set b := g z.1 - g z.2
    rw [abs_mul, abs_mul, abs_of_nonneg hK]
    have hab : |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
      nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
    calc Kk |z.1 - z.2| * |a| * |b| = Kk |z.1 - z.2| * (|a| * |b|) := by ring
      _ ≤ Kk |z.1 - z.2| * ((a ^ 2 + b ^ 2) / 2) := mul_le_mul_of_nonneg_left hab hK
      _ = (Kk |z.1 - z.2| * a ^ 2 + Kk |z.1 - z.2| * b ^ 2) / 2 := by ring

/-- `E_{f+g} ≤ 2 (E_f + E_g)` pointwise, hence integrable. -/
theorem sumDensity_integrable {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hEf : RHFormDomain.energy (fun x => (f x : ℂ)) < ⊤)
    (hEg : RHFormDomain.energy (fun x => (g x : ℂ)) < ⊤) :
    Integrable (fun z : ℝ × ℝ => Kk |z.1 - z.2| * ((f z.1 + g z.1) - (f z.2 + g z.2)) ^ 2)
      (volume.prod volume) := by
  have hsum := ((energyDensity_integrable hf hEf).add (energyDensity_integrable hg hEg)).const_mul 2
  refine hsum.mono' ?_ (Filter.Eventually.of_forall (fun z => ?_))
  · exact (measurable_kernel_prod.mul
      (((hf.add hg).comp measurable_fst).sub ((hf.add hg).comp measurable_snd) |>.pow_const 2)).aestronglyMeasurable
  · have hK := RHAutocorrEnergy.kernel_abs_nonneg (z.1 - z.2)
    simp only [energyDensity, Pi.add_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg hK (sq_nonneg _))]
    have hsq : ((f z.1 + g z.1) - (f z.2 + g z.2)) ^ 2 ≤
        2 * ((f z.1 - f z.2) ^ 2 + (g z.1 - g z.2) ^ 2) := by
      nlinarith [sq_nonneg ((f z.1 - f z.2) - (g z.1 - g z.2))]
    calc Kk |z.1 - z.2| * ((f z.1 + g z.1) - (f z.2 + g z.2)) ^ 2
        ≤ Kk |z.1 - z.2| * (2 * ((f z.1 - f z.2) ^ 2 + (g z.1 - g z.2) ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq hK
      _ = 2 * (Kk |z.1 - z.2| * (f z.1 - f z.2) ^ 2 + Kk |z.1 - z.2| * (g z.1 - g z.2) ^ 2) := by ring

/-- Polarization of the spatial energy for finite-energy measurable functions. -/
theorem polarize_spatialEnergy {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hEf : RHFormDomain.energy (fun x => (f x : ℂ)) < ⊤)
    (hEg : RHFormDomain.energy (fun x => (g x : ℂ)) < ⊤) :
    RHStepA2G2.polarize RHAutocorrEnergy.spatialEnergy f g =
      (1/4:ℝ) * ∫ x, ∫ y, Kk |x - y| * (f x - f y) * (g x - g y) := by
  have hS := sumDensity_integrable hf hg hEf hEg
  have hF : Integrable (fun z : ℝ × ℝ => Kk |z.1 - z.2| * (f z.1 - f z.2) ^ 2) (volume.prod volume) :=
    energyDensity_integrable hf hEf
  have hG : Integrable (fun z : ℝ × ℝ => Kk |z.1 - z.2| * (g z.1 - g z.2) ^ 2) (volume.prod volume) :=
    energyDensity_integrable hg hEg
  have hX := crossDensity_integrable hf hg hEf hEg
  unfold RHStepA2G2.polarize RHAutocorrEnergy.spatialEnergy
  rw [integral_integral (f := fun x y => Kk |x - y| * ((f x + g x) - (f y + g y)) ^ 2) hS,
    integral_integral (f := fun x y => Kk |x - y| * (f x - f y) ^ 2) hF,
    integral_integral (f := fun x y => Kk |x - y| * (g x - g y) ^ 2) hG,
    integral_integral (f := fun x y => Kk |x - y| * (f x - f y) * (g x - g y)) hX]
  set P : Measure (ℝ × ℝ) := volume.prod volume with hP
  set A : ℝ × ℝ → ℝ := fun z => Kk |z.1 - z.2| * ((f z.1 + g z.1) - (f z.2 + g z.2)) ^ 2 with hA
  set B : ℝ × ℝ → ℝ := fun z => Kk |z.1 - z.2| * (f z.1 - f z.2) ^ 2 with hB
  set C : ℝ × ℝ → ℝ := fun z => Kk |z.1 - z.2| * (g z.1 - g z.2) ^ 2 with hC
  set X : ℝ × ℝ → ℝ := fun z => Kk |z.1 - z.2| * (f z.1 - f z.2) * (g z.1 - g z.2) with hXd
  have hAB : Integrable (fun z => A z - B z) P := hS.sub hF
  have e1 : ∫ z, (A z - B z) - C z ∂P = (∫ z, A z - B z ∂P) - ∫ z, C z ∂P := integral_sub hAB hG
  have e2 : ∫ z, A z - B z ∂P = (∫ z, A z ∂P) - ∫ z, B z ∂P := integral_sub hS hF
  have e3 : ∫ z, (A z - B z) - C z ∂P = ∫ z, 2 * X z ∂P := by
    congr 1; funext z; simp only [hA, hB, hC, hXd]; ring
  have e4 : ∫ z, 2 * X z ∂P = 2 * ∫ z, X z ∂P := integral_const_mul 2 _
  have hcomb : (∫ z, A z ∂P) - (∫ z, B z ∂P) - (∫ z, C z ∂P) = 2 * ∫ z, X z ∂P := by
    linear_combination -e1 - e2 + e3 + e4
  linear_combination (1/8:ℝ) * hcomb

/-! ### Measurability and finite energy of `low` / `tail` -/

lemma basis_measurable (n : ℕ) : Measurable (basis n) := by
  unfold basis RHWeilColumnCandidate.zeroPoly
  exact (Polynomial.continuous _).measurable.indicator measurableSet_Icc

lemma low_measurable (o : Bool) (u : ℝ → ℝ) : Measurable (low o u) := by
  have h : low o u = fun x => ∑ i : I, alpha o u i • basis (degree o i) x := by
    funext x; simp [low, Finset.sum_apply]
  rw [h]
  exact Finset.measurable_sum _ (fun i _ => by exact (basis_measurable (degree o i)).const_smul (alpha o u i))

lemma tail_measurable (o : Bool) (u : ℝ → ℝ) (hu : Test u) : Measurable (tail o u) := by
  unfold tail
  exact (RHG3RealEmbedding.component_continuous o u hu).measurable.sub (low_measurable o u)

lemma low_energy_finite (o : Bool) (u : ℝ → ℝ) :
    RHFormDomain.energy (fun x => (low o u x : ℂ)) < ⊤ := by
  have hE := RHBoundedWindow.polynomial_energy_finite halfWidth_pos.le (RHTestConjunct1.lowPoly o u)
  have heq : RHFormDomain.extend halfWidth (fun x : ℝ => (RHTestConjunct1.lowPoly o u).eval (x : ℂ)) =
      (fun x => (low o u x : ℂ)) := by
    funext x
    by_cases hx : x ∈ Icc (-halfWidth) halfWidth
    · unfold RHFormDomain.extend
      rw [indicator_of_mem hx, RHTestConjunct1.low_eq_lowPoly o u x hx]
    · unfold RHFormDomain.extend
      rw [indicator_of_notMem hx, low_zero_outside o u x hx]
      simp
  rw [heq] at hE
  exact hE

end RHSpatialBase0489

