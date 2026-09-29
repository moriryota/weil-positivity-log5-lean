import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

open Polynomial MeasureTheory Set
namespace RHLegendreContract
/-- Public Mathlib shifted Legendre convention: Q₁(t)=1-2t. -/
noncomputable def Q (n : ℕ) : Polynomial ℝ :=
  (Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)
end RHLegendreContract
