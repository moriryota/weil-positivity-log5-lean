import HurwitzEM0495
import Bernoulli0465_09
import Bernoulli0465_19
import Bernoulli0465_29

/-! # 0495 step 3b: numeric enclosure of S1 = ∑ 1/(4m+1)^2 (N = 20, s = 19)

Exact values of `C 20 19` and `Rb 20 19` from the Bernoulli numbers of 0465; width ≈ 2.4e-26.
 -/

namespace RHS1Numeric0495
open RHHurwitzEM0495 RHEulerNumeric0465

def qC : ℚ := 2168670476009515411822291860056863333741062285330821065374257817695318729523149 / 2017681193655488882284156413877510280459455403594140482442468365603702360577500
def qR : ℚ := 23998353104699392 / 1975465005122733265119452104408312772437365
def S1Lo : ℚ := 107483307215669442120445743 / 100000000000000000000000000
def S1Hi : ℚ := 53741653607834721060222873 / 50000000000000000000000000

theorem C_value : C 20 19 = (qC : ℝ) := by
  simp only [C, P, bc, cj, fd, f, Iinf, Finset.sum_range_succ, Finset.sum_range_zero, saw_eval_zero,
    bernoulli]
  norm_num [qC, Nat.factorial, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20]

theorem Rb_value : Rb 20 19 = (qR : ℝ) := by
  simp only [Rb, sawBound, bernoulliBound_eq_abs_bernoulli' 20 (by decide), bernoulli, b20]
  norm_num [qR, Nat.factorial]

theorem S1_bounds : (S1Lo : ℝ) ≤ S1 ∧ S1 ≤ (S1Hi : ℝ) := by
  have h := S1_bound 20 19 (by norm_num)
  rw [C_value, Rb_value] at h
  have h1 : (S1Lo : ℝ) ≤ ((qC - qR : ℚ) : ℝ) := by exact_mod_cast (by decide +kernel : S1Lo ≤ qC - qR)
  have h2 : ((qC + qR : ℚ) : ℝ) ≤ (S1Hi : ℝ) := by exact_mod_cast (by decide +kernel : qC + qR ≤ S1Hi)
  push_cast at h1 h2
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

theorem S1_width : S1Hi - S1Lo ≤ (1 : ℚ) / 10 ^ 25 := by decide +kernel

end RHS1Numeric0495

