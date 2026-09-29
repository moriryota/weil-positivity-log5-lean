import ConditionalLog5
import RecurrenceBasis
open Polynomial
namespace RHRealBasisBridge
open RHConditionalLog5 RHLog5Bridge
lemma recPoly_map (n : ℕ) :
    (RHConditionalLog5.recPoly n).map Complex.ofRealHom =
      RHLegendreDirections.recPoly halfWidth n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [RHConditionalLog5.recPoly, RHLegendreDirections.recPoly]
  | one => simp [RHConditionalLog5.recPoly, RHLegendreDirections.recPoly]
  | more n ih0 ih1 =>
    simp [RHConditionalLog5.recPoly, RHLegendreDirections.recPoly, ih0, ih1]
lemma basisPoly_map (n : ℕ) :
    (basisPoly n).map Complex.ofRealHom =
      RHLegendreDirections.directionPoly halfWidth n := by
  simp [basisPoly, RHLegendreDirections.directionPoly, recPoly_map]
lemma basisPoly_eval (n : ℕ) (x : ℝ) :
    (((basisPoly n).eval x : ℝ) : ℂ) =
      (RHLegendreDirections.directionPoly halfWidth n).eval (x : ℂ) := by
  rw [← basisPoly_map, Polynomial.eval_map]
  exact (Polynomial.eval₂_at_apply (p := basisPoly n) Complex.ofRealHom x).symm
end RHRealBasisBridge
