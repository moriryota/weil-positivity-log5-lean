import FiniteTail

open scoped BigOperators Topology
open Filter

namespace RHBandTail

/-- Intermediate band tail lower bound:
For non-negative coefficients `a n`, weights `w n`, a cutoff `M ≥ N`,
a tail lower bound `d ≤ w n` for `n ≥ M`, and coefficients vanishing below `N` (`a n = 0` for `n < N`),
the sum of weighted coefficients on the band `[N, M)` plus `d` times the remaining mass
is bounded above by the total energy `E`. -/
theorem band_lower_bound (a w : ℕ → ℝ) (N M : ℕ) (d E mass : ℝ)
    (hNM : N ≤ M)
    (ha : ∀ n, 0 ≤ a n)
    (hzero : ∀ n, n < N → a n = 0)
    (hw : ∀ n, M ≤ n → d ≤ w n)
    (hfinite : ∀ K, ∑ n ∈ Finset.range K, w n * a n ≤ E)
    (hmass : Tendsto (fun K => ∑ n ∈ Finset.range K, a n) atTop (𝓝 mass)) :
    (∑ n ∈ Finset.Ico N M, w n * a n) +
      d * (mass - ∑ n ∈ Finset.Ico N M, a n) ≤ E := by
  have hM := RHFiniteTail.lower_bound a w M d E mass ha hw hfinite hmass
  have hz_sum : ∑ n ∈ Finset.range N, w n * a n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [hzero n (Finset.mem_range.mp hn), mul_zero]
  have hz_mass : ∑ n ∈ Finset.range N, a n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact hzero n (Finset.mem_range.mp hn)
  have hsplit_w : ∑ n ∈ Finset.range M, w n * a n
      = ∑ n ∈ Finset.Ico N M, w n * a n := by
    have h : ∑ n ∈ Finset.range M, w n * a n
        = (∑ n ∈ Finset.range N, w n * a n) + ∑ n ∈ Finset.Ico N M, w n * a n := by
      simp only [Finset.range_eq_Ico]
      rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le N) hNM]
    rw [h, hz_sum, zero_add]
  have hsplit_a : ∑ n ∈ Finset.range M, a n
      = ∑ n ∈ Finset.Ico N M, a n := by
    have h : ∑ n ∈ Finset.range M, a n
        = (∑ n ∈ Finset.range N, a n) + ∑ n ∈ Finset.Ico N M, a n := by
      simp only [Finset.range_eq_Ico]
      rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le N) hNM]
    rw [h, hz_mass, zero_add]
  rw [hsplit_w, hsplit_a] at hM
  exact hM

end RHBandTail

