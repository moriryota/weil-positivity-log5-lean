import ConditionalLog5
import ConcreteParameters
import TestConjunct1
import ResidualMembership
import Final
import TestRestriction
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

open MeasureTheory Set Polynomial
open scoped ENNReal
namespace RHG1Energy

open RHConditionalLog5 RHLog5Bridge RHTestConjunct1 RHResidualMembership RHBoundedWindow RHTestRestriction

lemma contDiff_eval_poly (f : Polynomial ℂ) : ContDiff ℂ 1 (fun z : ℂ => f.eval z) := by
  simpa using contDiff_aeval (𝕜 := ℂ) f 1

lemma contDiff_eval_poly_real (f : Polynomial ℂ) : ContDiff ℝ 1 (fun x : ℝ => f.eval (x : ℂ)) := by
  have h1 := (contDiff_eval_poly f).restrict_scalars ℝ
  exact h1.comp Complex.ofRealCLM.contDiff

lemma tail_energy_finite (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    RHFormDomain.energy (fun x => (tail o u x : ℂ)) < ⊤ := by
  have hc1 : ContDiff ℝ 1 (fun x => (component o u x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (component_contDiff o u hu)
  have hp_poly : ContDiff ℝ 1 (fun x : ℝ => (lowPoly o u).eval (x : ℂ)) :=
    contDiff_eval_poly_real (lowPoly o u)
  let p : ℝ → ℂ := fun x => (component o u x : ℂ) - (lowPoly o u).eval (x : ℂ)
  have hp : ContDiff ℝ 1 p := hc1.sub hp_poly
  obtain ⟨M0, hM0, hb⟩ := continuous_bounds hp.continuous halfWidth
  obtain ⟨M1, hM1, hl⟩ := c1_lipschitz hp halfWidth
  have hE := bounded_lipschitz_energy_finite halfWidth_pos.le p hM0 hM1 hb hl
  have heq : RHFormDomain.extend halfWidth p = (fun x => (tail o u x : ℂ)) := by
    funext x
    by_cases hx : x ∈ Icc (-halfWidth) halfWidth
    · unfold RHFormDomain.extend
      rw [indicator_of_mem hx]
      dsimp [p]
      rw [← low_eq_lowPoly o u x hx]
      simp [tail]
    · unfold RHFormDomain.extend
      rw [indicator_of_notMem hx]
      have htz := tail_zero_outside o u hu x hx
      simp [htz]
  rw [heq] at hE
  exact hE

end RHG1Energy

