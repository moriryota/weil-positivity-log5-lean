import Bernoulli0465_79
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace RHEulerNumeric0465
theorem b80 : bernoulli' 80 = (-4603784299479457646935574969019046849794257872751288919656867 / 230010) := by
  have c2 : Nat.choose 80 2 = 3160 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 80 4 = 1581580 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 80 6 = 300500200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 80 8 = 28987537150 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 80 10 = 1646492110120 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 80 12 = 60246643120300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 80 14 = 1508152231077400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 80 16 = 26958221130508525 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 80 18 = 355214207837288800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 80 20 = 3535316142212174320 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 80 22 = 27088786024742634400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 80 24 = 162238272822099908200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 80 26 = 768759815833950334240 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 80 28 = 2910305017085669122480 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 80 30 = 8871412534840453463008 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 80 32 = 21910242651571684460050 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c34 : Nat.choose 80 34 = 44054819449149483192400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c36 : Nat.choose 80 36 = 72375774809317008101800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c38 : Nat.choose 80 38 = 97393290141698278327600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c40 : Nat.choose 80 40 = 107507208733336176461620 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c42 : Nat.choose 80 42 = 97393290141698278327600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c44 : Nat.choose 80 44 = 72375774809317008101800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c46 : Nat.choose 80 46 = 44054819449149483192400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c48 : Nat.choose 80 48 = 21910242651571684460050 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c50 : Nat.choose 80 50 = 8871412534840453463008 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c52 : Nat.choose 80 52 = 2910305017085669122480 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c54 : Nat.choose 80 54 = 768759815833950334240 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c56 : Nat.choose 80 56 = 162238272822099908200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c58 : Nat.choose 80 58 = 27088786024742634400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c60 : Nat.choose 80 60 = 3535316142212174320 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c62 : Nat.choose 80 62 = 355214207837288800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c64 : Nat.choose 80 64 = 26958221130508525 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c66 : Nat.choose 80 66 = 1508152231077400 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c68 : Nat.choose 80 68 = 60246643120300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c70 : Nat.choose 80 70 = 1646492110120 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c72 : Nat.choose 80 72 = 28987537150 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c74 : Nat.choose 80 74 = 300500200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c76 : Nat.choose 80 76 = 1581580 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c78 : Nat.choose 80 78 = 3160 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76, b77, b78, b79, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32, c34, c36, c38, c40, c42, c44, c46, c48, c50, c52, c54, c56, c58, c60, c62, c64, c66, c68, c70, c72, c74, c76, c78]
end RHEulerNumeric0465
