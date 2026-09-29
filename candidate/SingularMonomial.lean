import DividedMoments
open MeasureTheory Set intervalIntegral
open scoped BigOperators
namespace RHDividedMoments

lemma action_eq_split (n : ℕ) (x : ℝ) :
    action n x = (∫ y in (-1 : ℝ)..x, difference n x y) -
      (∫ y in x..(1 : ℝ), difference n x y) := by
  have hi : ∀ k ∈ Finset.range n, ∀ a b : ℝ,
      IntervalIntegrable (fun y : ℝ => x^(n-1-k)*y^k) volume a b := by
    intro k hk a b
    exact (by fun_prop : Continuous (fun y : ℝ => x^(n-1-k)*y^k)).intervalIntegrable a b
  unfold difference
  rw [integral_finsetSum (fun k hk => hi k hk _ _),
      integral_finsetSum (fun k hk => hi k hk _ _)]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [← Finset.sum_sub_distrib]
  unfold action
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Ordinary absolutely integrable singular quotient; diagonal values do not matter. -/
theorem singular_eq_action (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (∫ y in (-1 : ℝ)..1, (x^n-y^n)/|x-y|) = action n x := by
  have hd : Continuous (difference n x) := by unfold difference; fun_prop
  have hl : IntervalIntegrable (fun y : ℝ => (x^n-y^n)/|x-y|) volume (-1) x := by
    apply (hd.intervalIntegrable (-1) x).congr_uIoo
    rw [uIoo_of_le hx.1]
    intro y hy
    exact (left_quotient n hy.2).symm
  have hr : IntervalIntegrable (fun y : ℝ => (x^n-y^n)/|x-y|) volume x 1 := by
    apply (hd.neg.intervalIntegrable x 1).congr_uIoo
    rw [uIoo_of_le hx.2]
    intro y hy
    exact (right_quotient n hy.1).symm
  have el : (∫ y in (-1 : ℝ)..x, (x^n-y^n)/|x-y|) =
      (∫ y in (-1 : ℝ)..x, difference n x y) :=
    integral_congr_Ioo_of_le hx.1 (fun y hy => left_quotient n hy.2)
  have er : (∫ y in x..(1 : ℝ), (x^n-y^n)/|x-y|) =
      -(∫ y in x..(1 : ℝ), difference n x y) := by
    rw [← intervalIntegral.integral_neg]
    exact integral_congr_Ioo_of_le hx.2 (fun y hy => right_quotient n hy.1)
  rw [← integral_add_adjacent_intervals hl hr, el, er, ← sub_eq_add_neg,
    ← action_eq_split]
end RHDividedMoments
