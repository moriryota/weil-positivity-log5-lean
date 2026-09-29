import Bernoulli0465_09
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace RHEulerNumeric0465
theorem b10 : bernoulli' 10 = (5 / 66) := by
  have c2 : Nat.choose 10 2 = 45 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 10 4 = 210 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 10 6 = 210 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 10 8 = 45 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, c2, c4, c6, c8]
theorem b11 : bernoulli' 11 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 11) (by decide) (by omega))
theorem b12 : bernoulli' 12 = (-691 / 2730) := by
  have c2 : Nat.choose 12 2 = 66 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 12 4 = 495 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 12 6 = 924 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 12 8 = 495 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 12 10 = 66 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, c2, c4, c6, c8, c10]
theorem b13 : bernoulli' 13 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 13) (by decide) (by omega))
theorem b14 : bernoulli' 14 = (7 / 6) := by
  have c2 : Nat.choose 14 2 = 91 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 14 4 = 1001 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 14 6 = 3003 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 14 8 = 3003 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 14 10 = 1001 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 14 12 = 91 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, c2, c4, c6, c8, c10, c12]
theorem b15 : bernoulli' 15 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 15) (by decide) (by omega))
theorem b16 : bernoulli' 16 = (-3617 / 510) := by
  have c2 : Nat.choose 16 2 = 120 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 16 4 = 1820 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 16 6 = 8008 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 16 8 = 12870 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 16 10 = 8008 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 16 12 = 1820 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 16 14 = 120 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, c2, c4, c6, c8, c10, c12, c14]
theorem b17 : bernoulli' 17 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 17) (by decide) (by omega))
theorem b18 : bernoulli' 18 = (43867 / 798) := by
  have c2 : Nat.choose 18 2 = 153 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 18 4 = 3060 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 18 6 = 18564 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 18 8 = 43758 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 18 10 = 43758 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 18 12 = 18564 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 18 14 = 3060 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 18 16 = 153 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, c2, c4, c6, c8, c10, c12, c14, c16]
theorem b19 : bernoulli' 19 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 19) (by decide) (by omega))
end RHEulerNumeric0465
