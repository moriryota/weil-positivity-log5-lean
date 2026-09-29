import RankOneCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open Set
namespace RHRawProjection
noncomputable def seed (L a r : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  (Ico (-L) (L-2*a)).indicator (fun t => RHChainCoordinates.coefficient r (u t) (u (t+a)) (u (t+2*a)))
noncomputable def project (L a r : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun x => seed L a r u x + r*seed L a r u (x-a) + seed L a r u (x-2*a)
end RHRawProjection
