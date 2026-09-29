import Interface0516
import PrRed0511
import ParityCorrelation

open MeasureTheory Set
open scoped BigOperators
namespace RHColParity0520

lemma mem_neg (L x : ℝ) : -x ∈ Icc (-L) L ↔ x ∈ Icc (-L) L := by
  simp only [mem_Icc]; constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

lemma integral_reflect (L : ℝ) (f : ℝ → ℝ) :
    (∫ y in Icc (-L) L, f (-y)) = ∫ y in Icc (-L) L, f y := by
  rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc]
  have h : (fun y => (Icc (-L) L).indicator (fun y => f (-y)) y) =
      fun y => (Icc (-L) L).indicator f (-y) := by
    funext y
    by_cases hy : y ∈ Icc (-L) L
    · simp [hy, (mem_neg L y).mpr hy]
    · simp [hy, mt (mem_neg L y).mp hy]
  rw [h]
  exact integral_neg_eq_self _ volume

lemma zeroPoly_parity (L s : ℝ) (p : Polynomial ℝ)
    (hp : ∀ x, p.eval (-x) = s * p.eval x) (x : ℝ) :
    RHWeilColumnCandidate.zeroPoly L p (-x) = s * RHWeilColumnCandidate.zeroPoly L p x := by
  unfold RHWeilColumnCandidate.zeroPoly
  by_cases hx : x ∈ Icc (-L) L
  · simp [hx, (mem_neg L x).mpr hx, hp]
  · simp [hx, mt (mem_neg L x).mp hx]

lemma column_parity (L s : ℝ) (p : Polynomial ℝ)
    (hp : ∀ x, p.eval (-x) = s * p.eval x) (x : ℝ) :
    RHWeilColumnCandidate.column L p (-x) = s * RHWeilColumnCandidate.column L p x := by
  have hk : (∫ y in Icc (-L) L, RH_GammaFinalFormula.K_kernel |-x-y| * (p.eval (-x)-p.eval y)) =
      s * (∫ y in Icc (-L) L, RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x-p.eval y)) := by
    rw [← integral_reflect L (fun y => RH_GammaFinalFormula.K_kernel |-x-y| * (p.eval (-x)-p.eval y))]
    simp only [hp]
    have he (y : ℝ) : RH_GammaFinalFormula.K_kernel |-x - -y| * (s*p.eval x-s*p.eval y) =
        s * (RH_GammaFinalFormula.K_kernel |x-y| * (p.eval x-p.eval y)) := by
      rw [show -x - -y = -(x-y) by ring, abs_neg]; ring
    simp_rw [he]
    exact integral_const_mul _ _
  have hc : (∫ y in Icc (-L) L, p.eval y * Real.cosh (y/2)) =
      s * (∫ y in Icc (-L) L, p.eval y * Real.cosh (y/2)) := by
    conv_lhs => rw [← integral_reflect L (fun y => p.eval y * Real.cosh (y/2))]
    simp only [hp, neg_div, Real.cosh_neg, mul_assoc]
    exact integral_const_mul _ _
  have hs : -(∫ y in Icc (-L) L, p.eval y * Real.sinh (y/2)) =
      s * (∫ y in Icc (-L) L, p.eval y * Real.sinh (y/2)) := by
    have h := integral_reflect L (fun y => p.eval y * Real.sinh (y/2))
    simp only [hp, neg_div, Real.sinh_neg, mul_neg, mul_assoc, integral_neg, integral_const_mul] at h
    linarith
  have hz (t : ℝ) :
      RHWeilColumnCandidate.zeroPoly L p (-x-t) + RHWeilColumnCandidate.zeroPoly L p (-x+t) =
      s * (RHWeilColumnCandidate.zeroPoly L p (x-t) + RHWeilColumnCandidate.zeroPoly L p (x+t)) := by
    rw [show -x-t = -(x+t) by ring, show -x+t = -(x-t) by ring,
      zeroPoly_parity L s p hp, zeroPoly_parity L s p hp]; ring
  unfold RHWeilColumnCandidate.column
  simp only [abs_neg]
  split_ifs with hx
  · rw [hk, hp]
    simp only [neg_div, Real.cosh_neg, Real.sinh_neg]
    simp_rw [hz]
    rw [show L - -x = L+x by ring, show L + -x = L-x by ring]
    have hsum : (∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        (s * (RHWeilColumnCandidate.zeroPoly L p (x-Real.log n) + RHWeilColumnCandidate.zeroPoly L p (x+Real.log n)))) =
        s * ∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
          (RHWeilColumnCandidate.zeroPoly L p (x-Real.log n) + RHWeilColumnCandidate.zeroPoly L p (x+Real.log n)) := by
      simp_rw [← mul_assoc, mul_comm _ s, mul_assoc]; rw [Finset.mul_sum]
    rw [hsum]
    linear_combination 2 * Real.cosh (x/2) * hc - 2 * Real.sinh (x/2) * hs
  · ring

/-- Pointwise parity, including the exterior and endpoints. -/
theorem colParity_pointwise (o : Bool) (i : RHConditionalLog5.I) (x : ℝ) :
    RHConditionalLog5.col o i (-x) = (-1) ^ RHConditionalLog5.degree o i * RHConditionalLog5.col o i x :=
  column_parity _ _ _ (RHPrRed0511.bparity _) x

theorem colParity : RHInterface0516.ColParity := by
  intro o i
  exact Filter.Eventually.of_forall (colParity_pointwise o i)

end RHColParity0520
