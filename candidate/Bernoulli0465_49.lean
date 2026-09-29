import Bernoulli0465_39
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace RHEulerNumeric0465
theorem b40 : bernoulli' 40 = (-261082718496449122051 / 13530) := by
  have c2 : Nat.choose 40 2 = 780 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 40 4 = 91390 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 40 6 = 3838380 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 40 8 = 76904685 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 40 10 = 847660528 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 40 12 = 5586853480 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 40 14 = 23206929840 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 40 16 = 62852101650 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 40 18 = 113380261800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 40 20 = 137846528820 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 40 22 = 113380261800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 40 24 = 62852101650 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 40 26 = 23206929840 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 40 28 = 5586853480 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 40 30 = 847660528 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 40 32 = 76904685 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c34 : Nat.choose 40 34 = 3838380 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c36 : Nat.choose 40 36 = 91390 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c38 : Nat.choose 40 38 = 780 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32, c34, c36, c38]
theorem b41 : bernoulli' 41 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 41) (by decide) (by omega))
theorem b42 : bernoulli' 42 = (1520097643918070802691 / 1806) := by
  have c2 : Nat.choose 42 2 = 861 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 42 4 = 111930 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 42 6 = 5245786 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 42 8 = 118030185 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 42 10 = 1471442973 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 42 12 = 11058116888 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 42 14 = 52860229080 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 42 16 = 166509721602 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 42 18 = 353697121050 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 42 20 = 513791607420 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 42 22 = 513791607420 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 42 24 = 353697121050 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 42 26 = 166509721602 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 42 28 = 52860229080 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 42 30 = 11058116888 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 42 32 = 1471442973 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c34 : Nat.choose 42 34 = 118030185 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c36 : Nat.choose 42 36 = 5245786 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c38 : Nat.choose 42 38 = 111930 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c40 : Nat.choose 42 40 = 861 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32, c34, c36, c38, c40]
theorem b43 : bernoulli' 43 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 43) (by decide) (by omega))
theorem b44 : bernoulli' 44 = (-27833269579301024235023 / 690) := by
  have c2 : Nat.choose 44 2 = 946 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 44 4 = 135751 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 44 6 = 7059052 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 44 8 = 177232627 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 44 10 = 2481256778 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 44 12 = 21090682613 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 44 14 = 114955808528 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 44 16 = 416714805914 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 44 18 = 1029530696964 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 44 20 = 1761039350070 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 44 22 = 2104098963720 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 44 24 = 1761039350070 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 44 26 = 1029530696964 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 44 28 = 416714805914 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 44 30 = 114955808528 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 44 32 = 21090682613 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c34 : Nat.choose 44 34 = 2481256778 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c36 : Nat.choose 44 36 = 177232627 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c38 : Nat.choose 44 38 = 7059052 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c40 : Nat.choose 44 40 = 135751 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c42 : Nat.choose 44 42 = 946 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32, c34, c36, c38, c40, c42]
theorem b45 : bernoulli' 45 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 45) (by decide) (by omega))
theorem b46 : bernoulli' 46 = (596451111593912163277961 / 282) := by
  have c2 : Nat.choose 46 2 = 1035 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 46 4 = 163185 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 46 6 = 9366819 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 46 8 = 260932815 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 46 10 = 4076350421 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 46 12 = 38910617655 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 46 14 = 239877544005 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 46 16 = 991493848554 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 46 18 = 2818953098830 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 46 20 = 5608233007146 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 46 22 = 7890371113950 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 46 24 = 7890371113950 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 46 26 = 5608233007146 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 46 28 = 2818953098830 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 46 30 = 991493848554 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 46 32 = 239877544005 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c34 : Nat.choose 46 34 = 38910617655 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c36 : Nat.choose 46 36 = 4076350421 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c38 : Nat.choose 46 38 = 260932815 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c40 : Nat.choose 46 40 = 9366819 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c42 : Nat.choose 46 42 = 163185 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c44 : Nat.choose 46 44 = 1035 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32, c34, c36, c38, c40, c42, c44]
theorem b47 : bernoulli' 47 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 47) (by decide) (by omega))
theorem b48 : bernoulli' 48 = (-5609403368997817686249127547 / 46410) := by
  have c2 : Nat.choose 48 2 = 1128 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 48 4 = 194580 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 48 6 = 12271512 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 48 8 = 377348994 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 48 10 = 6540715896 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 48 12 = 69668534468 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 48 14 = 482320623240 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 48 16 = 2254848913647 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 48 18 = 7309837001104 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 48 20 = 16735679449896 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 48 22 = 27385657281648 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 48 24 = 32247603683100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 48 26 = 27385657281648 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 48 28 = 16735679449896 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 48 30 = 7309837001104 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 48 32 = 2254848913647 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c34 : Nat.choose 48 34 = 482320623240 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c36 : Nat.choose 48 36 = 69668534468 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c38 : Nat.choose 48 38 = 6540715896 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c40 : Nat.choose 48 40 = 377348994 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c42 : Nat.choose 48 42 = 12271512 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c44 : Nat.choose 48 44 = 194580 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c46 : Nat.choose 48 46 = 1128 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32, c34, c36, c38, c40, c42, c44, c46]
theorem b49 : bernoulli' 49 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 49) (by decide) (by omega))
end RHEulerNumeric0465
