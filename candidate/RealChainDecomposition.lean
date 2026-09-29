import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open MeasureTheory Set

namespace RHRealChain

private theorem ico_integral_eq_interval (g : ℝ → ℝ) {u v : ℝ} (h : u ≤ v) :
    (∫ t in Ico u v, g t) = ∫ t in u..v, g t := by
  rw [intervalIntegral.integral_of_le h, integral_Ico_eq_integral_Ioc]

/-- Integrating over a strip of width between two and three steps gives two- and three-point chains. -/
theorem integral_chain_decomposition (g : ℝ → ℝ) (s W a : ℝ)
    (ha : 0 < a) (h₂ : 2*a ≤ W) (h₃ : W ≤ 3*a)
    (hg : IntegrableOn g (Ico s (s+W))) :
    (∫ x in Ico s (s+W), g x) =
      (∫ t in Ico s (s+W-2*a), g t + g (t+a) + g (t+2*a)) +
      (∫ t in Ico (s+W-2*a) (s+a), g t + g (t+a)) := by
  have hw : s ≤ s+W := by linarith
  have hgI : IntervalIntegrable g volume s (s+W) :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le hw).2 hg
  have hi (u v : ℝ) (hu : s ≤ u) (huv : u ≤ v) (hv : v ≤ s+W) :
      IntervalIntegrable g volume u v := by
    apply hgI.mono_set
    rw [uIcc_of_le huv, uIcc_of_le hw]
    exact Icc_subset_Icc hu hv
  have hc : s ≤ s+W-2*a := by linarith
  have hcd : s+W-2*a ≤ s+a := by linarith
  have hT := hi s (s+W-2*a) (by linarith) hc (by linarith)
  have hB := hi (s+W-2*a) (s+a) hc hcd (by linarith)
  have hT1 : IntervalIntegrable (fun t => g (t+a)) volume s (s+W-2*a) := by
    apply (IntervalIntegrable.comp_add_right_iff (by finiteness)).mpr
    exact hi _ _ (by linarith) (by linarith) (by linarith)
  have hT2 : IntervalIntegrable (fun t => g (t+2*a)) volume s (s+W-2*a) := by
    apply (IntervalIntegrable.comp_add_right_iff (by finiteness)).mpr
    exact hi _ _ (by linarith) (by linarith) (by linarith)
  have hB1 : IntervalIntegrable (fun t => g (t+a)) volume (s+W-2*a) (s+a) := by
    apply (IntervalIntegrable.comp_add_right_iff (by finiteness)).mpr
    exact hi _ _ (by linarith) (by linarith) (by linarith)
  rw [ico_integral_eq_interval _ hw, ico_integral_eq_interval _ hc,
    ico_integral_eq_interval _ hcd,
    intervalIntegral.integral_add (hT.add hT1) hT2,
    intervalIntegral.integral_add hT hT1,
    intervalIntegral.integral_add hB hB1]
  simp only [intervalIntegral.integral_comp_add_right]
  have hfirst := intervalIntegral.integral_add_adjacent_intervals hT hB
  have hsecond := intervalIntegral.integral_add_adjacent_intervals
    (hi (s+a) (s+W-2*a+a) (by linarith) (by linarith) (by linarith))
    (hi (s+W-2*a+a) (s+a+a) (by linarith) (by linarith) (by linarith))
  have hthird := intervalIntegral.integral_add_adjacent_intervals
    (hi s (s+a) (by linarith) (by linarith) (by linarith))
    (hi (s+a) (s+a+a) (by linarith) (by linarith) (by linarith))
  have hfourth := intervalIntegral.integral_add_adjacent_intervals
    (hi s (s+a+a) (by linarith) (by linarith) (by linarith))
    (hi (s+a+a) (s+W) (by linarith) (by linarith) (by linarith))
  have he₁ : s+2*a = s+a+a := by ring
  have he₂ : s+W-2*a+2*a = s+W := by ring
  rw [he₁, he₂]
  linarith

end RHRealChain

