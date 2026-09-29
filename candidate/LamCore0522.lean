import LamDef0521
import LegendreBound0520
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open scoped BigOperators
namespace RHLamCore0522
noncomputable def co (κ : ℝ) (r : ℕ) : ℝ :=
  (if r % 2 = 0 then (1:ℝ) else -1) * κ^(r+1) / (r+1)
noncomputable def acc (κ : ℝ) (R l : ℕ) : ℝ :=
  ∑ r ∈ Finset.range R, co κ r * RHCcSs0510.ξ (r+1) l
noncomputable def approx (κ : ℝ) (R l : ℕ) : ℝ :=
  2 / (2*(l:ℝ)+1) * acc κ R l
end RHLamCore0522
