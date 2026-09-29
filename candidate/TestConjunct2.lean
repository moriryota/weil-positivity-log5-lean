import TestRecPoly
import G3BandConnection
import RealCoefficientBridge
import CoefficientMass
import ExpectedFinite
import ActualDirections
import SpectralGapAdapter

open MeasureTheory Set Filter
open scoped BigOperators Topology Matrix
namespace RHTestConjunct2
open RHConditionalLog5 RHLog5Bridge RHResidualMembership RHRealLowZero RHTestRecPoly
open RHSpectralGapAdapter RHActualTail RHG3BandConnection RHRealCoefficientBridge

lemma tendsto_two_mul_atTop : Tendsto (fun M : ℕ => 2 * M) atTop atTop := by
  apply tendsto_atTop_atTop_of_monotone
  · intro a b _
    change 2 * a ≤ 2 * b
    omega
  · intro b
    use b
    change b ≤ 2 * b
    omega

lemma massCoeff_tendsto (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    Tendsto (fun M => ∑ n ∈ Finset.range M, massCoeff o u n) atTop (𝓝 (‖embed (tail o u)‖^2)) := by
  let f := intervalEmbed (tail o u) (tail_memLp o u hu)
  let F : ℕ → ℝ := fun k => ‖inner ℂ (RHLegendreDirections.direction halfWidth halfWidth_pos.le k) f‖^2
  have hz : ∀ k, (k % 2 ≠ (if o then 1 else 0)) → F k = 0 := by
    intro k hk
    dsimp [F]
    have h_inner := tail_inner o u hu k
    have h_coeff := coeff_tail_opposite_parity o u hu k hk
    rw [h_inner, h_coeff]
    simp only [Complex.ofReal_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  have h_sum (M : ℕ) : (∑ n ∈ Finset.range M, massCoeff o u n) = ∑ k ∈ Finset.range (2 * M), F k := by
    rw [sum_range_two_mul o M F hz]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [F]
    have h_inner := tail_inner o u hu (degree o n)
    unfold massCoeff
    rw [h_inner, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [h_sum]
  have ht := RHActualTail.coefficient_mass_tendsto halfWidth_pos f
  have h_norm : ‖f‖^2 = ‖embed (tail o u)‖^2 := by
    rw [tail_norm o u hu]
  rw [h_norm] at ht
  exact ht.comp tendsto_two_mul_atTop

end RHTestConjunct2
