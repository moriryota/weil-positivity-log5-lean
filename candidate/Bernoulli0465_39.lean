import Bernoulli0465_29
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace RHEulerNumeric0465
theorem b30 : bernoulli' 30 = (8615841276005 / 14322) := by
  have c2 : Nat.choose 30 2 = 435 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 30 4 = 27405 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 30 6 = 593775 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 30 8 = 5852925 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 30 10 = 30045015 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 30 12 = 86493225 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 30 14 = 145422675 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 30 16 = 145422675 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 30 18 = 86493225 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 30 20 = 30045015 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 30 22 = 5852925 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 30 24 = 593775 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 30 26 = 27405 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 30 28 = 435 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28]
theorem b31 : bernoulli' 31 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 31) (by decide) (by omega))
theorem b32 : bernoulli' 32 = (-7709321041217 / 510) := by
  have c2 : Nat.choose 32 2 = 496 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 32 4 = 35960 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 32 6 = 906192 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 32 8 = 10518300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 32 10 = 64512240 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 32 12 = 225792840 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 32 14 = 471435600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 32 16 = 601080390 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 32 18 = 471435600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 32 20 = 225792840 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 32 22 = 64512240 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 32 24 = 10518300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 32 26 = 906192 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 32 28 = 35960 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 32 30 = 496 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30]
theorem b33 : bernoulli' 33 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 33) (by decide) (by omega))
theorem b34 : bernoulli' 34 = (2577687858367 / 6) := by
  have c2 : Nat.choose 34 2 = 561 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 34 4 = 46376 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 34 6 = 1344904 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 34 8 = 18156204 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 34 10 = 131128140 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 34 12 = 548354040 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 34 14 = 1391975640 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 34 16 = 2203961430 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 34 18 = 2203961430 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 34 20 = 1391975640 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 34 22 = 548354040 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 34 24 = 131128140 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 34 26 = 18156204 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 34 28 = 1344904 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 34 30 = 46376 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 34 32 = 561 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32]
theorem b35 : bernoulli' 35 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 35) (by decide) (by omega))
theorem b36 : bernoulli' 36 = (-26315271553053477373 / 1919190) := by
  have c2 : Nat.choose 36 2 = 630 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 36 4 = 58905 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 36 6 = 1947792 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 36 8 = 30260340 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 36 10 = 254186856 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 36 12 = 1251677700 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 36 14 = 3796297200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 36 16 = 7307872110 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 36 18 = 9075135300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 36 20 = 7307872110 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 36 22 = 3796297200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 36 24 = 1251677700 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 36 26 = 254186856 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 36 28 = 30260340 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 36 30 = 1947792 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 36 32 = 58905 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c34 : Nat.choose 36 34 = 630 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32, c34]
theorem b37 : bernoulli' 37 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 37) (by decide) (by omega))
theorem b38 : bernoulli' 38 = (2929993913841559 / 6) := by
  have c2 : Nat.choose 38 2 = 703 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 38 4 = 73815 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 38 6 = 2760681 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 38 8 = 48903492 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 38 10 = 472733756 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 38 12 = 2707475148 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 38 14 = 9669554100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 38 16 = 22239974430 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 38 18 = 33578000610 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 38 20 = 33578000610 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 38 22 = 22239974430 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 38 24 = 9669554100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 38 26 = 2707475148 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 38 28 = 472733756 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 38 30 = 48903492 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 38 32 = 2760681 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c34 : Nat.choose 38 34 = 73815 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c36 : Nat.choose 38 36 = 703 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32, c34, c36]
theorem b39 : bernoulli' 39 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 39) (by decide) (by omega))
end RHEulerNumeric0465
