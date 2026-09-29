import Zeta23.Statement.SeamClosed

/- Trusted statements of the two theorems of the paper (release candidate 0602).
Only the trusted Zeta23 statement modules (and Mathlib through them) are imported.
The `sorry`s are the expected statement placeholders of the comparator Challenge, never proof evidence. -/
open MeasureTheory
namespace RHLog5Release
theorem target_log5 (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) (hn : f ≠ 0) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      Zeta23.zetaZeroConfig.Wsummand f f (ρ : ℂ)) ∧
    0 < (Zeta23.zetaZeroConfig.W f f).re := by
  sorry
theorem target_log5_uniform :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f →
      (∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) →
      Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
        Zeta23.zetaZeroConfig.Wsummand f f (ρ : ℂ)) ∧
      c * (∫ x, ‖f x‖^2) ≤ (Zeta23.zetaZeroConfig.W f f).re := by
  sorry
end RHLog5Release
