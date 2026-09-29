import FinalAll0524
import Uniform0579

/- Candidate proofs of the two statements of the Challenge. Does not import the Challenge. -/
open MeasureTheory
namespace RHLog5Release
theorem target_log5 (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) (hn : f ≠ 0) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      Zeta23.zetaZeroConfig.Wsummand f f (ρ : ℂ)) ∧
    0 < (Zeta23.zetaZeroConfig.W f f).re :=
  RHFinalAll0524.target_log5_concrete f hf hs hn
theorem target_log5_uniform :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f →
      (∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) →
      Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
        Zeta23.zetaZeroConfig.Wsummand f f (ρ : ℂ)) ∧
      c * (∫ x, ‖f x‖^2) ≤ (Zeta23.zetaZeroConfig.W f f).re :=
  RHUniform0579.uniform_target_log5
end RHLog5Release
