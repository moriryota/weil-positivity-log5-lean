import TestRecPoly
import TestConjunct2
import KernelConnection
import ComparisonDomain
import TestRestriction
import ExpectedFinite

open MeasureTheory Set Filter
open scoped BigOperators Topology Matrix Polynomial
namespace RHTestConjunct1
open RHConditionalLog5 RHLog5Bridge RHResidualMembership RHRealLowZero RHTestRecPoly
open RHSpectralGapAdapter RHActualTail RHG3BandConnection RHRealCoefficientBridge
open RHComparisonEnergy RHComparisonIntegral RHKernelConnection RHTestRestriction
open RHRealBasisBridge

lemma component_contDiff (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    ContDiff ℝ 1 (component o u) := by
  have hc : ContDiff ℝ 1 u := hu.1.of_le (by norm_num)
  cases o <;> dsimp [component] <;> fun_prop

lemma intervalEnergy_intervalEmbed (u : ℝ → ℝ) (hu : MemLp u 2 volume) :
    intervalEnergy halfWidth (intervalEmbed u hu) = energy halfWidth (fun x => (u x : ℂ)) := by
  apply energy_congr_ae
  exact ((hu.restrict (Icc (-halfWidth) halfWidth)).ofReal.coeFn_toLp)

lemma compare_intervalEmbed (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (intervalEnergy halfWidth (intervalEmbed (tail o u) (tail_memLp o u hu))).toReal =
      RHConditionalLog5.compare (tail o u) := by
  unfold RHConditionalLog5.compare
  rw [intervalEnergy_intervalEmbed (tail o u) (tail_memLp o u hu)]

noncomputable def lowPoly (o : Bool) (u : ℝ → ℝ) : Polynomial ℂ :=
  ∑ i : I, (alpha o u i : ℂ) • RHLegendreDirections.directionPoly halfWidth (degree o i)

lemma low_eq_lowPoly (o : Bool) (u : ℝ → ℝ) (x : ℝ) (hx : x ∈ Icc (-halfWidth) halfWidth) :
    (low o u x : ℂ) = (lowPoly o u).eval (x : ℂ) := by
  dsimp [lowPoly]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_smul]
  unfold low
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hb : (basis (degree o i) x : ℂ) =
      (RHLegendreDirections.directionPoly halfWidth (degree o i)).eval (x : ℂ) := by
    have hbc := basis_complex (degree o i) x
    rw [hbc, Set.indicator_of_mem hx]
  rw [hb, Complex.real_smul]

lemma tail_inDomain (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    RHComparisonEnergy.InDomain halfWidth (intervalEmbed (tail o u) (tail_memLp o u hu)) := by
  have h_comp_cont : Continuous (fun x => (component o u x : ℂ)) := by
    have hc := RHG3RealEmbedding.component_continuous o u hu
    fun_prop
  let f_comp : Lp ℂ 2 μ := testLp h_comp_cont halfWidth
  have h_comp_coe : (f_comp : ℝ → ℂ) =ᵐ[μ] (fun x => (component o u x : ℂ)) :=
    MemLp.coeFn_toLp (test_memLp h_comp_cont halfWidth)
  have h_comp_c1 : ContDiff ℝ 1 (fun x => (component o u x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (component_contDiff o u hu)
  have h_form : RHFormDomain.InDomain halfWidth f_comp :=
    testLp_mem h_comp_c1 halfWidth_pos.le
  have h_comp_domain : RHComparisonEnergy.InDomain halfWidth f_comp :=
    domain_of_original halfWidth_pos RHKernelElementary.log5_half_le_one f_comp h_form
  have h_res := residual_energy_finite f_comp h_comp_domain (lowPoly o u)
  have h_ae : (fun x => f_comp x - (lowPoly o u).eval (x : ℂ)) =ᵐ[μ]
      (fun x => (tail o u x : ℂ)) := by
    filter_upwards [h_comp_coe, ae_restrict_mem measurableSet_Icc] with x h_comp h_mem
    rw [h_comp]
    have h_tail_val : (tail o u x : ℂ) = (component o u x : ℂ) - (low o u x : ℂ) := by
      simp only [tail, Pi.sub_apply, Complex.ofReal_sub]
    rw [h_tail_val, low_eq_lowPoly o u x h_mem]
  unfold RHComparisonEnergy.InDomain
  rw [intervalEnergy_intervalEmbed (tail o u) (tail_memLp o u hu)]
  rw [← energy_congr_ae h_ae]
  exact h_res

lemma harmonic_massCoeff_le_compare (o : Bool) (u : ℝ → ℝ) (hu : Test u) (M : ℕ) :
    ∑ n ∈ Finset.range M, (harmonic (degree o n) : ℝ) * massCoeff o u n ≤
      RHConditionalLog5.compare (tail o u) := by
  let f := intervalEmbed (tail o u) (tail_memLp o u hu)
  let G : ℕ → ℝ := fun k => (harmonic k : ℝ) * ‖inner ℂ (RHLegendreDirections.direction halfWidth halfWidth_pos.le k) f‖^2
  have hz : ∀ k, (k % 2 ≠ (if o then 1 else 0)) → G k = 0 := by
    intro k hk
    dsimp [G]
    have h_inner := tail_inner o u hu k
    have h_coeff := coeff_tail_opposite_parity o u hu k hk
    rw [h_inner, h_coeff]
    simp only [Complex.ofReal_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
  have h_sum : (∑ n ∈ Finset.range M, (harmonic (degree o n) : ℝ) * massCoeff o u n) =
      ∑ k ∈ Finset.range (2 * M), G k := by
    rw [sum_range_two_mul o M G hz]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [G]
    have h_inner := tail_inner o u hu (degree o n)
    unfold massCoeff
    rw [h_inner, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [h_sum]
  have h_bound := RHExpected0291.actual_form_finite halfWidth_pos f (tail_inDomain o u hu) (2 * M)
  have h_comp : (intervalEnergy halfWidth f).toReal = RHConditionalLog5.compare (tail o u) :=
    compare_intervalEmbed o u hu
  rw [h_comp] at h_bound
  exact h_bound

end RHTestConjunct1
