import MathlibAll0483

open Polynomial
open scoped BigOperators

namespace RHTuckMonomial

noncomputable def image (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range n, C ((1 : ℂ) / (k+1)) *
    (C 2 * X^n - C (1 + (-1 : ℂ)^(k+1)) * X^(n-1-k))

theorem coeff_above (n m : ℕ) (hm : n < m) : (image n).coeff m = 0 := by
  rw [image, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega),
    Polynomial.coeff_X_pow, if_neg (by omega)]
  ring

theorem coeff_diag (n : ℕ) : (image n).coeff n = 2 * (harmonic n : ℂ) := by
  have key : (image n).coeff n = ∑ k ∈ Finset.range n, 2 * ((k : ℂ) + 1)⁻¹ := by
    rw [image, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl,
      Polynomial.coeff_X_pow, if_neg (by omega)]
    ring
  have hcast : (harmonic n : ℂ) = ∑ k ∈ Finset.range n, ((k : ℂ) + 1)⁻¹ := by
    have h : harmonic n = ∑ i ∈ Finset.range n, ((i + 1 : ℕ) : ℚ)⁻¹ := rfl
    rw [h, Rat.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Rat.cast_inv_nat, Nat.cast_add, Nat.cast_one]
  rw [key, hcast, Finset.mul_sum]

/-- Auxiliary consequence of `coeff_above`: the polynomial has degree at most `n`. -/
theorem natDegree_image_le (n : ℕ) : (image n).natDegree ≤ n :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun N hN => coeff_above n N hN

end RHTuckMonomial

