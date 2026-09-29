import RpErr0506
import RpCoef0506

/-! # 0506: rigorous enclosure of `Rp(n,k)` from one kernel ball computation

If `gz (run (2^512) n rq 81).2.2 k = (m, e)` then, with `F = L² c_n c_k/(2k+1)`,
`|Rp n k − F · m/2^512| ≤ F·(e/2^512 + 4(2k+1)·10⁻³²) + 10⁻²⁴·(2L + ((1+2L)/2)²)`.
 -/

open MeasureTheory Set Finset
open scoped BigOperators

namespace RHRpEncl0506
open RHConditionalLog5 RHLog5Bridge RHRpExact0506 RHAlgoBall0505 RHBall0504 RHBallVec0504 RHGForm0505

theorem Rp_encl (n k : ℕ) {m : ℤ} {e : ℕ}
    (h : gz (run (2 ^ 512) n RHEntry22_0505.rq 81).2.2 k = (m, e)) :
    |RHColDecomp0499.Rp n k - halfWidth ^ 2 * cc n * cc k / (2 * k + 1) * ((m : ℝ) / 2 ^ 512)| ≤
      halfWidth ^ 2 * cc n * cc k / (2 * k + 1) * ((e : ℝ) / 2 ^ 512 + 4 * (2 * k + 1) / 10 ^ 32) +
      2 / 10 ^ 24 / 2 * (2 * halfWidth + ((1 + 2 * halfWidth) / 2) ^ 2) := by
  have hS : 0 < 2 ^ 512 := by positivity
  have hball := (run_mem hS n RHEntry22_0505.rq RHRpCoef0506.rden_pos 81).2.2 k
  rw [h] at hball
  unfold mem at hball
  push_cast at hball
  have hc := RHRpCoef0506.coef_err n k
  rw [RHRpCoef0506.J_eq] at hc
  have hQ := RpQ_eq n k
  rw [RHRpCoef0506.J_eq] at hQ
  have hE := RHRpErr0506.Rp_err n k
  set F := halfWidth ^ 2 * cc n * cc k / (2 * k + 1) with hF
  have hF0 : 0 ≤ F := by
    have h1 : 0 ≤ cc n := Real.sqrt_nonneg _
    have h2 : 0 ≤ cc k := Real.sqrt_nonneg _
    have h3 : (0:ℝ) < 2 * k + 1 := by have := (Nat.cast_nonneg k : (0:ℝ) ≤ k); linarith
    rw [hF]; exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) h1) h2) h3.le
  have h1 : |γ n 81 rt k - (m : ℝ) / 2 ^ 512| ≤ (e : ℝ) / 2 ^ 512 + 4 * (2 * k + 1) / 10 ^ 32 := by
    have := abs_sub_le (γ n 81 rt k) (γ n 81 (rval RHEntry22_0505.rq) k) ((m : ℝ) / 2 ^ 512)
    linarith
  have h2 : |RpQ n k - F * ((m : ℝ) / 2 ^ 512)| ≤ F * ((e : ℝ) / 2 ^ 512 + 4 * (2 * k + 1) / 10 ^ 32) := by
    rw [hQ, ← mul_sub, abs_mul, abs_of_nonneg hF0]
    exact mul_le_mul_of_nonneg_left h1 hF0
  have := abs_sub_le (RHColDecomp0499.Rp n k) (RpQ n k) (F * ((m : ℝ) / 2 ^ 512))
  linarith

end RHRpEncl0506

