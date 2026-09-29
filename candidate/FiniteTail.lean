import MathlibAll0483

open scoped BigOperators Topology
open Filter

namespace RHFiniteTail

theorem lower_bound (a w : ℕ → ℝ) (N : ℕ) (d E mass : ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hw : ∀ n, N ≤ n → d ≤ w n)
    (hfinite : ∀ M, ∑ n ∈ Finset.range M, w n * a n ≤ E)
    (hmass : Tendsto (fun M => ∑ n ∈ Finset.range M, a n) atTop (𝓝 mass)) :
    (∑ n ∈ Finset.range N, w n * a n) +
      d * (mass - ∑ n ∈ Finset.range N, a n) ≤ E := by
  -- The limit of the comparison quantity as `M → ∞`.
  have htend : Tendsto
      (fun M => (∑ n ∈ Finset.range N, w n * a n) +
        d * ((∑ n ∈ Finset.range M, a n) - ∑ n ∈ Finset.range N, a n))
      atTop (𝓝 ((∑ n ∈ Finset.range N, w n * a n) +
        d * (mass - ∑ n ∈ Finset.range N, a n))) := by
    apply Tendsto.const_add
    apply Tendsto.const_mul
    exact hmass.sub tendsto_const_nhds
  refine le_of_tendsto htend ?_
  rw [eventually_atTop]
  refine ⟨N, fun M hM => ?_⟩
  -- Split `range M` into `range N` and `Ico N M`.
  have hsplit : ∑ n ∈ Finset.range M, w n * a n
      = (∑ n ∈ Finset.range N, w n * a n) + ∑ n ∈ Finset.Ico N M, w n * a n := by
    simp only [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le N) hM]
  -- On the tail, `d * a n ≤ w n * a n`, hence the comparison of sums.
  have hsum_a : (∑ n ∈ Finset.range M, a n) - ∑ n ∈ Finset.range N, a n
      = ∑ n ∈ Finset.Ico N M, a n := by
    simp only [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le N) hM]
    ring
  have hcompare : d * ((∑ n ∈ Finset.range M, a n) - ∑ n ∈ Finset.range N, a n)
      ≤ ∑ n ∈ Finset.Ico N M, w n * a n := by
    rw [hsum_a, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Ico] at hn
    exact mul_le_mul_of_nonneg_right (hw n hn.1) (ha n)
  have key : (∑ n ∈ Finset.range N, w n * a n) +
        d * ((∑ n ∈ Finset.range M, a n) - ∑ n ∈ Finset.range N, a n)
      ≤ ∑ n ∈ Finset.range M, w n * a n := by
    rw [hsplit]; linarith [hcompare]
  linarith [key, hfinite M]

end RHFiniteTail

