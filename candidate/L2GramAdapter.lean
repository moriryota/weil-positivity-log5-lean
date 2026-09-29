import FiniteProjection
import LegendreContract

open MeasureTheory Set Filter
namespace RHLegendreContract

/-- Transfer an explicitly supplied real interval Gram formula to the actual
complex L² quotient. No assertion of a concrete Gram formula is made here. -/
theorem orthonormal_of_real_gram {L : ℝ} (hL : 0 ≤ L)
    (v : ℕ → Lp ℂ 2 (volume.restrict (Icc (-L) L))) (g : ℕ → ℝ → ℝ)
    (hrep : ∀ n, (v n : ℝ → ℂ) =ᵐ[volume.restrict (Icc (-L) L)]
      (fun x => (g n x : ℂ)))
    (hgram : ∀ m n : ℕ, (∫ x in -L..L, g m x*g n x) = if m=n then 1 else 0) :
    Orthonormal ℂ v := by
  classical
  apply orthonormal_iff_ite.mpr
  intro m n
  rw [L2.inner_def]
  have he : (fun x => inner ℂ (v m x) (v n x)) =ᵐ[volume.restrict (Icc (-L) L)]
      (fun x => ((g m x*g n x : ℝ):ℂ)) := by
    filter_upwards [hrep m, hrep n] with x hm hn
    rw [hm,hn]
    simp only [RCLike.inner_apply', Complex.conj_ofReal, Complex.ofReal_mul]
  rw [integral_congr_ae he, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -L ≤ L), intervalIntegral.integral_ofReal,
    hgram]
  split_ifs <;> simp

end RHLegendreContract
