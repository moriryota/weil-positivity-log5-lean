import EnergyToReal
import ComplexSpatialEndpoint
open MeasureTheory Set
open scoped ComplexConjugate
namespace RHSpatialDomain
open RHFormDomain RHTestRestriction RHComplexSpatial

lemma testLp_spatial {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) {L : ℝ} (hL : 0 ≤ L)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ L) :
    (intervalEnergy L (testLp hf.continuous L)).toReal = complexSpatialEnergy f := by
  have hE := testLp_mem hf hL
  unfold InDomain at hE
  rw [testLp_original_energy hf.continuous hs] at hE ⊢
  exact RHEnergyToReal.energy_toReal hf.continuous.measurable hE

open Zeta23
/-- The original all-zero explicit formula now uses the actual interval form-domain input. -/
theorem full_zero_domain (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) (hn : f ≠ 0) :
    ∃ g : Lp ℂ 2 (volume.restrict (Icc (-(Real.log 5 / 2)) (Real.log 5 / 2))),
      InDomain (Real.log 5 / 2) g ∧ g = testLp hf.continuous (Real.log 5 / 2) ∧ g ≠ 0 ∧
      Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f (ρ:ℂ)) ∧
      (zetaZeroConfig.W f f).re =
        ((Complex.digamma (1/4:ℂ)).re-Real.log Real.pi)*(∫ x, ‖f x‖^2) +
        (intervalEnergy (Real.log 5 / 2) g).toReal +
        2*‖∫ x, f x*(Real.cosh (x/2):ℂ)‖^2-2*‖∫ x, f x*(Real.sinh (x/2):ℂ)‖^2 -
        2*∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n:ℝ)/Real.sqrt n)*
          (∫ t, f t*conj (f (t-Real.log n))).re := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hL : 0 < Real.log 5 / 2 := RHLog5Bridge.halfWidth_pos
  have h := RHComplexSpatialEndpoint.full_zero_log5 f hf hs
  refine ⟨testLp hf.continuous _, testLp_mem hf1 hL.le, rfl,
    testLp_ne_zero hf.continuous hs hn, h.1, ?_⟩
  rw [testLp_spatial hf1 hL.le hs]
  exact h.2
end RHSpatialDomain
