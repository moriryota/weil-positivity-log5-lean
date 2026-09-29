import MathlibAll0483
open scoped BigOperators
namespace RHDividedMoments

noncomputable def difference (n : ℕ) (x y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, x^(n-1-k)*y^k

lemma difference_quotient (n : ℕ) {x y : ℝ} (hxy : x ≠ y) :
    (x^n-y^n)/(x-y) = difference n x y := by
  have h := geom_sum₂_mul y x n
  have hs : (∑ k ∈ Finset.range n, y^k*x^(n-1-k)) = difference n x y := by
    apply Finset.sum_congr rfl
    intro k hk
    exact mul_comm _ _
  rw [hs] at h
  apply (div_eq_iff (sub_ne_zero.mpr hxy)).mpr
  nlinarith

lemma left_quotient (n : ℕ) {x y : ℝ} (hy : y < x) :
    (x^n-y^n)/|x-y| = difference n x y := by
  rw [abs_of_pos (sub_pos.mpr hy)]
  exact difference_quotient n (ne_of_gt hy)

lemma right_quotient (n : ℕ) {x y : ℝ} (hy : x < y) :
    (x^n-y^n)/|x-y| = -difference n x y := by
  rw [abs_of_neg (sub_neg.mpr hy), div_neg]
  rw [difference_quotient n (ne_of_lt hy)]

lemma signed_moment (k : ℕ) (x : ℝ) :
    (∫ y in (-1 : ℝ)..x, y^k) - (∫ y in x..(1 : ℝ), y^k) =
      (2*x^(k+1)-((-1 : ℝ)^(k+1)+1))/(k+1) := by
  rw [integral_pow,integral_pow]
  simp only [one_pow]
  ring

noncomputable def action (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, x^(n-1-k) *
    ((∫ y in (-1 : ℝ)..x, y^k) - (∫ y in x..(1 : ℝ), y^k))

lemma action_formula (n : ℕ) (x : ℝ) :
    action n x = ∑ k ∈ Finset.range n, (1 : ℝ)/(k+1) *
      (2*x^n-(1+(-1 : ℝ)^(k+1))*x^(n-1-k)) := by
  unfold action
  apply Finset.sum_congr rfl
  intro k hk
  rw [signed_moment]
  have he : n-1-k+(k+1)=n := by have := Finset.mem_range.mp hk; omega
  have hp : x^(n-1-k)*x^(k+1)=x^n := by rw [← pow_add,he]
  calc
    x^(n-1-k)*((2*x^(k+1)-((-1:ℝ)^(k+1)+1))/(k+1))
      = (1 : ℝ)/(k+1)*(2*(x^(n-1-k)*x^(k+1))-(1+(-1:ℝ)^(k+1))*x^(n-1-k)) := by ring
    _ = _ := by rw [hp]
end RHDividedMoments
