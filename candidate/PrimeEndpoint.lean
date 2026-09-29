import WholeZeroBridge

namespace RHPrimeEndpoint
open Real MeasureTheory Set RH_LiteratureBridge

/-- Continuity is essential at the closed support endpoint. -/
lemma continuous_zero_ge {h : ℝ → ℝ} {b : ℝ} (hc : Continuous h)
    (hs : ∀ x, h x ≠ 0 → |x| ≤ b) {x : ℝ} (hx : b ≤ x) : h x = 0 := by
  have hz : EqOn h (fun _ => (0:ℝ)) (Ioi b) := by
    intro y hy
    by_contra hh
    have hb := hs y hh
    have ha := le_abs_self y
    have hy' : b < y := hy
    linarith
  have hcl := hz.closure hc continuous_const
  apply hcl
  rwa [closure_Ioi]

theorem autocorr_zero_ge {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : ContDiff ℝ 1 f) (hs : ∀ x, f x ≠ 0 → |x| ≤ L)
    {s : ℝ} (hsl : 2*L ≤ s) : real_autocorr f s = 0 :=
  continuous_zero_ge (real_autocorr_contDiff hf hs).continuous
    (real_autocorr_supp_bound hL hs) hsl

/-- The infinite prime-power series is exactly a finite sum at the log 5 endpoint. -/
theorem prime_sum_endpoint (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) :
    S_prime (real_autocorr f) = 2*∑ n ∈ Finset.range 5,
      ((ArithmeticFunction.vonMangoldt n : ℝ)/Real.sqrt n)*real_autocorr f (Real.log n) := by
  unfold S_prime
  congr 1
  apply tsum_eq_sum
  intro n hn
  have hn5 : 5 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
  have hnreal : (5:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn5
  have hl : Real.log 5 ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) hnreal
  have hv := autocorr_zero_ge RHLog5Bridge.halfWidth_pos hf hs
    (s := Real.log n) (by rwa [RHLog5Bridge.twice_halfWidth])
  rw [hv, mul_zero]

end RHPrimeEndpoint
