import Bernoulli0465_69
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace RHEulerNumeric0465
theorem b70 : bernoulli' 70 = (1505381347333367003803076567377857208511438160235 / 4686) := by
  have c2 : Nat.choose 70 2 = 2415 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 70 4 = 916895 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 70 6 = 131115985 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 70 8 = 9440350920 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 70 10 = 396704524216 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 70 12 = 10638894058520 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 70 14 = 193253756909160 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 70 16 = 2480089880334220 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 70 18 = 23196134763125940 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 70 20 = 161884603662657876 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 70 22 = 858478958817125100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 70 24 = 3508566179513467800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 70 26 = 11173433833219812840 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 70 28 = 27963143931814663880 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 70 30 = 55347740058143507128 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 70 32 = 87038784768854708790 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c34 : Nat.choose 70 34 = 109069992321755544170 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c36 : Nat.choose 70 36 = 109069992321755544170 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c38 : Nat.choose 70 38 = 87038784768854708790 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c40 : Nat.choose 70 40 = 55347740058143507128 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c42 : Nat.choose 70 42 = 27963143931814663880 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c44 : Nat.choose 70 44 = 11173433833219812840 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c46 : Nat.choose 70 46 = 3508566179513467800 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c48 : Nat.choose 70 48 = 858478958817125100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c50 : Nat.choose 70 50 = 161884603662657876 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c52 : Nat.choose 70 52 = 23196134763125940 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c54 : Nat.choose 70 54 = 2480089880334220 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c56 : Nat.choose 70 56 = 193253756909160 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c58 : Nat.choose 70 58 = 10638894058520 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c60 : Nat.choose 70 60 = 396704524216 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c62 : Nat.choose 70 62 = 9440350920 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c64 : Nat.choose 70 64 = 131115985 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c66 : Nat.choose 70 66 = 916895 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c68 : Nat.choose 70 68 = 2415 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32, c34, c36, c38, c40, c42, c44, c46, c48, c50, c52, c54, c56, c58, c60, c62, c64, c66, c68]
theorem b71 : bernoulli' 71 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 71) (by decide) (by omega))
theorem b72 : bernoulli' 72 = (-5827954961669944110438277244641067365282488301844260429 / 140100870) := by
  have c2 : Nat.choose 72 2 = 2556 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 72 4 = 1028790 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 72 6 = 156238908 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 72 8 = 11969016345 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 72 10 = 536211932256 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 72 12 = 15363284301456 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 72 14 = 298824321028320 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 72 16 = 4116305022165108 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 72 18 = 41432089765583440 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 72 20 = 312049055023946856 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 72 22 = 1791242627540058576 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 72 24 = 7950261662089028100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 72 26 = 27593523553342842144 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 72 28 = 75553695443676829680 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 72 30 = 164307576757973059488 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 72 32 = 285219402396400814958 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c34 : Nat.choose 72 34 = 396561735952215036840 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c36 : Nat.choose 72 36 = 442512540276836779204 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c38 : Nat.choose 72 38 = 396561735952215036840 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c40 : Nat.choose 72 40 = 285219402396400814958 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c42 : Nat.choose 72 42 = 164307576757973059488 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c44 : Nat.choose 72 44 = 75553695443676829680 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c46 : Nat.choose 72 46 = 27593523553342842144 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c48 : Nat.choose 72 48 = 7950261662089028100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c50 : Nat.choose 72 50 = 1791242627540058576 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c52 : Nat.choose 72 52 = 312049055023946856 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c54 : Nat.choose 72 54 = 41432089765583440 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c56 : Nat.choose 72 56 = 4116305022165108 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c58 : Nat.choose 72 58 = 298824321028320 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c60 : Nat.choose 72 60 = 15363284301456 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c62 : Nat.choose 72 62 = 536211932256 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c64 : Nat.choose 72 64 = 11969016345 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c66 : Nat.choose 72 66 = 156238908 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c68 : Nat.choose 72 68 = 1028790 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c70 : Nat.choose 72 70 = 2556 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32, c34, c36, c38, c40, c42, c44, c46, c48, c50, c52, c54, c56, c58, c60, c62, c64, c66, c68, c70]
theorem b73 : bernoulli' 73 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 73) (by decide) (by omega))
theorem b74 : bernoulli' 74 = (34152417289221168014330073731472635186688307783087 / 6) := by
  have c2 : Nat.choose 74 2 = 2701 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 74 4 = 1150626 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 74 6 = 185250786 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 74 8 = 15071474661 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 74 10 = 718406958841 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 74 12 = 21944067106416 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 74 14 = 456002537343216 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 74 16 = 6726037425812436 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 74 18 = 72667580816130436 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 74 20 = 588989865562320376 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 74 22 = 3648677478873075576 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 74 24 = 17529515713716297876 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 74 26 = 66072789997853738148 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 74 28 = 197169595549150837648 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 74 30 = 469127658375565786128 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 74 32 = 894747509724365390478 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c34 : Nat.choose 74 34 = 1373222113855042069878 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c36 : Nat.choose 74 36 = 1700179760011004467468 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c38 : Nat.choose 74 38 = 1700179760011004467468 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c40 : Nat.choose 74 40 = 1373222113855042069878 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c42 : Nat.choose 74 42 = 894747509724365390478 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c44 : Nat.choose 74 44 = 469127658375565786128 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c46 : Nat.choose 74 46 = 197169595549150837648 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c48 : Nat.choose 74 48 = 66072789997853738148 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c50 : Nat.choose 74 50 = 17529515713716297876 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c52 : Nat.choose 74 52 = 3648677478873075576 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c54 : Nat.choose 74 54 = 588989865562320376 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c56 : Nat.choose 74 56 = 72667580816130436 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c58 : Nat.choose 74 58 = 6726037425812436 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c60 : Nat.choose 74 60 = 456002537343216 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c62 : Nat.choose 74 62 = 21944067106416 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c64 : Nat.choose 74 64 = 718406958841 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c66 : Nat.choose 74 66 = 15071474661 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c68 : Nat.choose 74 68 = 185250786 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c70 : Nat.choose 74 70 = 1150626 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c72 : Nat.choose 74 72 = 2701 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32, c34, c36, c38, c40, c42, c44, c46, c48, c50, c52, c54, c56, c58, c60, c62, c64, c66, c68, c70, c72]
theorem b75 : bernoulli' 75 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 75) (by decide) (by omega))
theorem b76 : bernoulli' 76 = (-24655088825935372707687196040585199904365267828865801 / 30) := by
  have c2 : Nat.choose 76 2 = 2850 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 76 4 = 1282975 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 76 6 = 218618940 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 76 8 = 18855883575 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 76 10 = 954526728530 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 76 12 = 31022118677225 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 76 14 = 687259244541600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 76 16 = 10830060261901380 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 76 18 = 125288932441604200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 76 20 = 1090013712241956540 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 76 22 = 7266758081613043600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 76 24 = 37676560923145889100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 76 26 = 153720368566435227528 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 76 28 = 498167861094928978100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 76 30 = 1291800798425471005280 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 76 32 = 2695592391875730827550 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c34 : Nat.choose 76 34 = 4545508739241428454300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c36 : Nat.choose 76 36 = 6212195276963285554210 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c38 : Nat.choose 76 38 = 6892620648693261354600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c40 : Nat.choose 76 40 = 6212195276963285554210 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c42 : Nat.choose 76 42 = 4545508739241428454300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c44 : Nat.choose 76 44 = 2695592391875730827550 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c46 : Nat.choose 76 46 = 1291800798425471005280 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c48 : Nat.choose 76 48 = 498167861094928978100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c50 : Nat.choose 76 50 = 153720368566435227528 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c52 : Nat.choose 76 52 = 37676560923145889100 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c54 : Nat.choose 76 54 = 7266758081613043600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c56 : Nat.choose 76 56 = 1090013712241956540 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c58 : Nat.choose 76 58 = 125288932441604200 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c60 : Nat.choose 76 60 = 10830060261901380 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c62 : Nat.choose 76 62 = 687259244541600 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c64 : Nat.choose 76 64 = 31022118677225 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c66 : Nat.choose 76 66 = 954526728530 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c68 : Nat.choose 76 68 = 18855883575 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c70 : Nat.choose 76 70 = 218618940 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c72 : Nat.choose 76 72 = 1282975 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c74 : Nat.choose 76 74 = 2850 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32, c34, c36, c38, c40, c42, c44, c46, c48, c50, c52, c54, c56, c58, c60, c62, c64, c66, c68, c70, c72, c74]
theorem b77 : bernoulli' 77 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 77) (by decide) (by omega))
theorem b78 : bernoulli' 78 = (414846365575400828295179035549542073492199375372400483487 / 3318) := by
  have c2 : Nat.choose 78 2 = 3003 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c4 : Nat.choose 78 4 = 1426425 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c6 : Nat.choose 78 6 = 256851595 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c8 : Nat.choose 78 8 = 23446881315 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c10 : Nat.choose 78 10 = 1258315963905 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c12 : Nat.choose 78 12 = 43430966148115 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c14 : Nat.choose 78 14 = 1023729916348425 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c16 : Nat.choose 78 16 = 17198662594653540 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c18 : Nat.choose 78 18 = 212566476905162380 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c20 : Nat.choose 78 20 = 1980224548011249540 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c22 : Nat.choose 78 22 = 14170178259145435020 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c24 : Nat.choose 78 24 = 79065487387985398300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c26 : Nat.choose 78 26 = 348131422929868015284 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c28 : Nat.choose 78 28 = 1221222928055568752028 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c30 : Nat.choose 78 30 = 3439076061765682117780 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c32 : Nat.choose 78 32 = 7821124592080019009790 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c34 : Nat.choose 78 34 = 14429347509452441488650 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c36 : Nat.choose 78 36 = 21666924990384142298830 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c38 : Nat.choose 78 38 = 26536589497469056215210 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c40 : Nat.choose 78 40 = 26536589497469056215210 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c42 : Nat.choose 78 42 = 21666924990384142298830 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c44 : Nat.choose 78 44 = 14429347509452441488650 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c46 : Nat.choose 78 46 = 7821124592080019009790 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c48 : Nat.choose 78 48 = 3439076061765682117780 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c50 : Nat.choose 78 50 = 1221222928055568752028 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c52 : Nat.choose 78 52 = 348131422929868015284 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c54 : Nat.choose 78 54 = 79065487387985398300 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c56 : Nat.choose 78 56 = 14170178259145435020 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c58 : Nat.choose 78 58 = 1980224548011249540 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c60 : Nat.choose 78 60 = 212566476905162380 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c62 : Nat.choose 78 62 = 17198662594653540 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c64 : Nat.choose 78 64 = 1023729916348425 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c66 : Nat.choose 78 66 = 43430966148115 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c68 : Nat.choose 78 68 = 1258315963905 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c70 : Nat.choose 78 70 = 23446881315 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c72 : Nat.choose 78 72 = 256851595 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c74 : Nat.choose 78 74 = 1426425 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  have c76 : Nat.choose 78 76 = 3003 := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76, b77, c2, c4, c6, c8, c10, c12, c14, c16, c18, c20, c22, c24, c26, c28, c30, c32, c34, c36, c38, c40, c42, c44, c46, c48, c50, c52, c54, c56, c58, c60, c62, c64, c66, c68, c70, c72, c74, c76]
theorem b79 : bernoulli' 79 = (0 / 1) := by
  simpa using (bernoulli'_eq_zero_of_odd (n := 79) (by decide) (by omega))
end RHEulerNumeric0465
