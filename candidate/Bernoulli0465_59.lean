import Bernoulli0465_49
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace RHEulerNumeric0465
theorem b50 : bernoulli' 50 = (495057205241079648212477525 / 66) := by
  have c2 : Nat.choose 50 2 = 1225 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 50 4 = 230300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 50 6 = 15890700 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 50 8 = 536878650 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 50 10 = 10272278170 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 50 12 = 121399651100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 50 14 = 937845656300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 50 16 = 4923689695575 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 50 18 = 18053528883775 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 50 20 = 47129212243960 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 50 22 = 88749815264600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 50 24 = 121548660036300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 50 26 = 121548660036300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 50 28 = 88749815264600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 50 30 = 47129212243960 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 50 32 = 18053528883775 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c34 : Nat.choose 50 34 = 4923689695575 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c36 : Nat.choose 50 36 = 937845656300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c38 : Nat.choose 50 38 = 121399651100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c40 : Nat.choose 50 40 = 10272278170 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c42 : Nat.choose 50 42 = 536878650 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c44 : Nat.choose 50 44 = 15890700 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c46 : Nat.choose 50 46 = 230300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c48 : Nat.choose 50 48 = 1225 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32, c34, c36, c38, c40, c42, c44, c46, c48]
theorem b51 : bernoulli' 51 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 51) (by decide) (by omega))
theorem b52 : bernoulli' 52 = (-801165718135489957347924991853 / 1590) := by
  have c2 : Nat.choose 52 2 = 1326 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 52 4 = 270725 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 52 6 = 20358520 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 52 8 = 752538150 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 52 10 = 15820024220 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 52 12 = 206379406870 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 52 14 = 1768966344600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 52 16 = 10363194502115 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 52 18 = 42671977361650 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 52 20 = 125994627894135 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 52 22 = 270533919634160 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 52 24 = 426384982032100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 52 26 = 495918532948104 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 52 28 = 426384982032100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 52 30 = 270533919634160 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 52 32 = 125994627894135 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c34 : Nat.choose 52 34 = 42671977361650 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c36 : Nat.choose 52 36 = 10363194502115 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c38 : Nat.choose 52 38 = 1768966344600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c40 : Nat.choose 52 40 = 206379406870 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c42 : Nat.choose 52 42 = 15820024220 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c44 : Nat.choose 52 44 = 752538150 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c46 : Nat.choose 52 46 = 20358520 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c48 : Nat.choose 52 48 = 270725 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c50 : Nat.choose 52 50 = 1326 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32, c34, c36, c38, c40, c42, c44, c46, c48, c50]
theorem b53 : bernoulli' 53 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 53) (by decide) (by omega))
theorem b54 : bernoulli' 54 = (29149963634884862421418123812691 / 798) := by
  have c2 : Nat.choose 54 2 = 1431 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 54 4 = 316251 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 54 6 = 25827165 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 54 8 = 1040465790 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 54 10 = 23930713170 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 54 12 = 343006888770 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 54 14 = 3245372870670 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 54 16 = 21094923659355 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 54 18 = 96926348578605 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 54 20 = 321387366339585 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 54 22 = 780512175396135 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 54 24 = 1402659561581460 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 54 26 = 1877405874732108 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 54 28 = 1877405874732108 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 54 30 = 1402659561581460 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 54 32 = 780512175396135 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c34 : Nat.choose 54 34 = 321387366339585 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c36 : Nat.choose 54 36 = 96926348578605 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c38 : Nat.choose 54 38 = 21094923659355 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c40 : Nat.choose 54 40 = 3245372870670 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c42 : Nat.choose 54 42 = 343006888770 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c44 : Nat.choose 54 44 = 23930713170 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c46 : Nat.choose 54 46 = 1040465790 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c48 : Nat.choose 54 48 = 25827165 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c50 : Nat.choose 54 50 = 316251 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c52 : Nat.choose 54 52 = 1431 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32, c34, c36, c38, c40, c42, c44, c46, c48, c50, c52]
theorem b55 : bernoulli' 55 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 55) (by decide) (by omega))
theorem b56 : bernoulli' 56 = (-2479392929313226753685415739663229 / 870) := by
  have c2 : Nat.choose 56 2 = 1540 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 56 4 = 367290 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 56 6 = 32468436 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 56 8 = 1420494075 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 56 10 = 35607051480 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 56 12 = 558383307300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 56 14 = 5804731963800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 56 16 = 41648951840265 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 56 18 = 212327989773900 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 56 20 = 785613562163430 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 56 22 = 2142582442263900 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 56 24 = 4355031703297275 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 56 26 = 6646448384109072 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 56 28 = 7648690600760440 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 56 30 = 6646448384109072 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 56 32 = 4355031703297275 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c34 : Nat.choose 56 34 = 2142582442263900 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c36 : Nat.choose 56 36 = 785613562163430 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c38 : Nat.choose 56 38 = 212327989773900 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c40 : Nat.choose 56 40 = 41648951840265 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c42 : Nat.choose 56 42 = 5804731963800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c44 : Nat.choose 56 44 = 558383307300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c46 : Nat.choose 56 46 = 35607051480 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c48 : Nat.choose 56 48 = 1420494075 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c50 : Nat.choose 56 50 = 32468436 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c52 : Nat.choose 56 52 = 367290 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c54 : Nat.choose 56 54 = 1540 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32, c34, c36, c38, c40, c42, c44, c46, c48, c50, c52, c54]
theorem b57 : bernoulli' 57 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 57) (by decide) (by omega))
theorem b58 : bernoulli' 58 = (84483613348880041862046775994036021 / 354) := by
  have c2 : Nat.choose 58 2 = 1653 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 58 4 = 424270 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 58 6 = 40475358 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 58 8 = 1916797311 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 58 10 = 52179482355 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 58 12 = 891794789340 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 58 14 = 10142940735900 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 58 16 = 79960182801345 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 58 18 = 449972009097765 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 58 20 = 1847253511032930 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 58 22 = 5621728217559090 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 58 24 = 12832205713993575 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 58 26 = 22150361247847371 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 58 28 = 29065024282889672 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 58 30 = 29065024282889672 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 58 32 = 22150361247847371 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c34 : Nat.choose 58 34 = 12832205713993575 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c36 : Nat.choose 58 36 = 5621728217559090 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c38 : Nat.choose 58 38 = 1847253511032930 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c40 : Nat.choose 58 40 = 449972009097765 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c42 : Nat.choose 58 42 = 79960182801345 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c44 : Nat.choose 58 44 = 10142940735900 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c46 : Nat.choose 58 46 = 891794789340 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c48 : Nat.choose 58 48 = 52179482355 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c50 : Nat.choose 58 50 = 1916797311 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c52 : Nat.choose 58 52 = 40475358 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c54 : Nat.choose 58 54 = 424270 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c56 : Nat.choose 58 56 = 1653 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32, c34, c36, c38, c40, c42, c44, c46, c48, c50, c52, c54, c56]
theorem b59 : bernoulli' 59 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 59) (by decide) (by omega))
end RHEulerNumeric0465
