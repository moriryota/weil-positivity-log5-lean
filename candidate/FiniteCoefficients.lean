import MixedLinear
import ProjectionPolynomial
import PolynomialVariation
open Polynomial MeasureTheory Set
open scoped ComplexConjugate
namespace RHFiniteCoefficients
open RHLegendreDirections RHPolynomialLpMap RHProjectionPolynomial RHFiniteMixed
noncomputable def mass {L : ℝ} (hL : 0 < L) (s : Finset ℕ)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) : ℝ :=
  ∑ n ∈ s, (harmonic n:ℝ) * ‖inner ℂ (direction L hL.le n) f‖^2

lemma value_direction {L : ℝ} (hL : 0 < L)
    (g : Lp ℂ 2 (volume.restrict (Icc (-L) L))) (n : ℕ) :
    value L g (directionPoly L n) = (harmonic n:ℂ)*inner ℂ g (direction L hL.le n) := by
  change value L g (directionPoly L n) = (harmonic n:ℂ)*inner ℂ g (toLp L hL.le (directionPoly L n))
  rw [inner_integral hL]
  exact (RHExpected0285.actual_L2_mixed hL g n).2

lemma value_poly {L : ℝ} (hL : 0 < L) (s : Finset ℕ)
    (f g : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    value L g (poly hL s f) = ∑ n ∈ s,
      (harmonic n:ℂ) * inner ℂ (direction L hL.le n) f * inner ℂ g (direction L hL.le n) := by
  change (linear L g) (poly hL s f) = _
  simp only [poly,map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n hn
  change inner ℂ (direction L hL.le n) f * value L g (directionPoly L n) = _
  rw [value_direction hL]
  ring

lemma value_poly_of_coeff {L : ℝ} (hL : 0 < L) (s : Finset ℕ)
    (f g : Lp ℂ 2 (volume.restrict (Icc (-L) L)))
    (hc : ∀ n ∈ s, inner ℂ (direction L hL.le n) g = inner ℂ (direction L hL.le n) f) :
    value L g (poly hL s f) = (mass hL s f:ℂ) := by
  rw [value_poly]
  unfold mass
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  rw [← inner_conj_symm g (direction L hL.le n),hc n hn,mul_assoc,Complex.mul_conj']

lemma polynomial_energy {L : ℝ} (hL : 0 < L) (s : Finset ℕ)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) :
    (1/4:ℝ) * (∫ z, RHComparisonIntegral.density (fun x => (poly hL s f).eval (x:ℂ)) z
      ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L)))) = mass hL s f := by
  let p := poly hL s f
  let g := toLp L hL.le p
  have hp : (fun x => g x) =ᵐ[volume.restrict (Icc (-L) L)] (fun x => p.eval (x:ℂ)) :=
    RHPolynomialLpMap.coe_poly hL.le p
  have hc : ∀ n ∈ s, inner ℂ (direction L hL.le n) g = inner ℂ (direction L hL.le n) f :=
    fun n hn => coefficient_preserved hL s f n hn
  have hv := value_poly_of_coeff hL s f g hc
  have hpc : Continuous (fun x : ℝ => p.eval (x:ℂ)) := by fun_prop
  have hpi : Integrable (fun x : ℝ => p.eval (x:ℂ)) (volume.restrict (Icc (-L) L)) :=
    hpc.continuousOn.integrableOn_compact (μ := volume) (isCompact_Icc : IsCompact (Icc (-L) L))
  have hpm := RHTuckMixed.difference_integrable (L := L) (fun x : ℝ => p.eval (x:ℂ)) p
    (RHTuckMixed.mixed_integrable hpi p)
  have he : (value L g p).re = (1/4:ℝ) *
      ∫ z, RHComparisonIntegral.density (fun x => p.eval (x:ℂ)) z
        ∂((volume.restrict (Icc (-L) L)).prod (volume.restrict (Icc (-L) L))) := by
    rw [value_congr hp p,real_value L _ p hpm,← RHComparisonIntegral.density_polynomial p]
  have hreal := congrArg Complex.re hv
  rw [Complex.ofReal_re] at hreal
  exact he.symm.trans hreal

theorem finite_bound {L : ℝ} (hL : 0 < L) (s : Finset ℕ)
    (f : Lp ℂ 2 (volume.restrict (Icc (-L) L))) (hf : RHComparisonEnergy.InDomain L f) :
    mass hL s f ≤ (RHComparisonEnergy.intervalEnergy L f).toReal := by
  have hv := RHComparisonIntegral.polynomial_variational_bound f hf (poly hL s f)
  have hm := congrArg Complex.re (value_poly_of_coeff hL s f f (fun _ _ => rfl))
  rw [Complex.ofReal_re,real_value L f _ (RHExpected0285.actual_polynomial_mixed f _).1] at hm
  have hp := polynomial_energy hL s f
  linarith
end RHFiniteCoefficients
