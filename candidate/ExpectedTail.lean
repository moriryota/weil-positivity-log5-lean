import ActualTail
open MeasureTheory Set
open scoped BigOperators
namespace RHExpected0264
open RHLegendreDirections

theorem harmonic_mono_real {N n : ℕ} (hn : N ≤ n) :
    (harmonic N : ℝ) ≤ (harmonic n : ℝ) := by
  have hq : harmonic N ≤ harmonic n := by
    unfold harmonic
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
      (by intro i _ _; positivity)
  exact_mod_cast hq

theorem log5_residual_tail
    (f : Lp ℂ 2 (volume.restrict (Icc (-(Real.log 5 / 2)) (Real.log 5 / 2))))
    (N : ℕ) (E c Q : ℝ)
    (hfinite : ∀ M, ∑ n ∈ Finset.range M,
      (harmonic n : ℝ) * ‖inner ℂ
        (direction (Real.log 5/2) RHLog5Bridge.halfWidth_pos.le n)
        (f - RHFiniteProjection.finiteProjection (Finset.range N)
          (direction (Real.log 5/2) RHLog5Bridge.halfWidth_pos.le) f)‖ ^ 2 ≤ E)
    (hQ : E + c * ‖f - RHFiniteProjection.finiteProjection (Finset.range N)
      (direction (Real.log 5/2) RHLog5Bridge.halfWidth_pos.le) f‖ ^ 2 ≤ Q) :
    ((harmonic N : ℝ)+c) * ‖f - RHFiniteProjection.finiteProjection (Finset.range N)
      (direction (Real.log 5/2) RHLog5Bridge.halfWidth_pos.le) f‖ ^ 2 ≤ Q :=
  RHActualTail.residual_shifted_tail RHLog5Bridge.halfWidth_pos f
    (fun n => (harmonic n : ℝ)) N (harmonic N : ℝ) E c Q
    (fun n hn => harmonic_mono_real hn) hfinite hQ
end RHExpected0264
