import RealAutocorr
import FormDomain

open MeasureTheory Set
namespace RHFormDomain

/-- Match the ENNReal kernel with the previously checked real-space kernel. -/
lemma kernel_eq_old (s : ℝ) :
    kernel s = ENNReal.ofReal (RH_GammaFinalFormula.K_kernel |s|) := by rfl

/-- Truncating the first moment makes the existing square-root majorant sufficient. -/
lemma min_le_sqrt_majorant {s : ℝ} (hs : 0 ≤ s) (b : ℝ) :
    min s b ≤ max 1 b * Real.sqrt s := by
  have hr := Real.sqrt_nonneg s
  have hsquare := Real.sq_sqrt hs
  have hmax1 : 1 ≤ max 1 b := le_max_left _ _
  have hmaxb : b ≤ max 1 b := le_max_right _ _
  by_cases h : s ≤ 1
  · have hr1 : Real.sqrt s ≤ 1 := by nlinarith
    have hsr : s ≤ Real.sqrt s := by nlinarith
    exact (min_le_left s b).trans (hsr.trans (by nlinarith))
  · have hr1 : 1 ≤ Real.sqrt s := by nlinarith
    have hm : max 1 b ≤ max 1 b * Real.sqrt s := by nlinarith
    exact (min_le_right s b).trans (hmaxb.trans hm)

/-- Unconditional integrability; this is not yet the energy of the interval indicator. -/
theorem truncated_kernel_integrable {b : ℝ} (hb : 0 ≤ b) :
    IntegrableOn (fun s : ℝ => min s b * RH_GammaFinalFormula.K_kernel s) (Ioi 0) := by
  apply (RH_SqrtKernel.integrableOn_sqrt_kernel.const_mul (max 1 b)).mono'
  · unfold RH_GammaFinalFormula.K_kernel RH_GammaSqrtBound.K_kernel
    exact (by fun_prop : Measurable (fun s : ℝ =>
      min s b * (Real.exp (s/2)/Real.sinh s))).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro s hs
    have hk : 0 ≤ RH_GammaFinalFormula.K_kernel s :=
      RH_GammaSqrtBound.K_kernel_nonneg s hs
    rw [Real.norm_of_nonneg (mul_nonneg (le_min hs.le hb) hk)]
    have hm := mul_le_mul_of_nonneg_right (min_le_sqrt_majorant hs.le b) hk
    simpa only [RH_GammaFinalFormula.K_kernel, mul_assoc] using hm
end RHFormDomain
