import EulerRemainder0463
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace RHEulerNumeric0465
theorem b0 : bernoulli' 0 = (1 / 1) := by
  norm_num
theorem b1 : bernoulli' 1 = (1 / 2) := by
  norm_num
theorem b2 : bernoulli' 2 = (1 / 6) := by
  norm_num
theorem b3 : bernoulli' 3 = (0 / 1) := by
  norm_num
theorem b4 : bernoulli' 4 = (-1 / 30) := by
  norm_num
theorem b5 : bernoulli' 5 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 5) (by decide) (by omega))
theorem b6 : bernoulli' 6 = (1 / 42) := by
  have c2 : Nat.choose 6 2 = 15 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 6 4 = 15 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, c2, c4]
theorem b7 : bernoulli' 7 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 7) (by decide) (by omega))
theorem b8 : bernoulli' 8 = (-1 / 30) := by
  have c2 : Nat.choose 8 2 = 28 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 8 4 = 70 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 8 6 = 28 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, c2, c4, c6]
theorem b9 : bernoulli' 9 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 9) (by decide) (by omega))
end RHEulerNumeric0465
