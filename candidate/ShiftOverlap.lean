import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
open MeasureTheory Set
namespace RHShiftOverlap

theorem product_eq_indicator (f : ℝ → ℝ) (s e d : ℝ) (hd : 0≤d) :
    (fun x => (Icc s e).indicator f x * (Icc s e).indicator f (x+d)) =
      (Icc s (e-d)).indicator (fun x => f x*f (x+d)) := by
  funext x
  by_cases hx : x ∈ Icc s (e-d)
  · have h1 : x ∈ Icc s e := by rcases hx with ⟨hl,hu⟩; constructor <;> linarith
    have h2 : x+d ∈ Icc s e := by rcases hx with ⟨hl,hu⟩; constructor <;> linarith
    simp only [indicator_of_mem hx, indicator_of_mem h1, indicator_of_mem h2]
  · rw [indicator_of_notMem hx]
    by_cases h1 : x ∈ Icc s e
    · have h2 : x+d ∉ Icc s e := by
        intro h2
        apply hx
        rcases h1 with ⟨hl,hu⟩; rcases h2 with ⟨hl2,hu2⟩
        constructor <;> linarith
      simp [indicator_of_notMem h2]
    · simp [indicator_of_notMem h1]

theorem overlap_integral (f : ℝ → ℝ) (s e d : ℝ) (hd : 0≤d) :
    (∫ x, (Icc s e).indicator f x * (Icc s e).indicator f (x+d)) =
      ∫ x in Ico s (e-d), f x*f (x+d) := by
  rw [product_eq_indicator f s e d hd, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ico]
end RHShiftOverlap
