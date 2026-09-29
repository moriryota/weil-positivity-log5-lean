import LeanCert.Core.IntervalRat.Taylor
import PiBounds0466
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-! # 0466: rational enclosure of `Real.log Real.pi` of width ≤ 10^-100

The proven interval `[piLo, piHi] ∋ Real.pi` (PiBounds0466) is pushed through LeanCert's
`IntervalRat.logComputable` (soundness: `IntervalRat.mem_logComputable`), as in 0455 Log2_100.
The finite comparison with the explicit outward-rounded endpoints is checked by `decide +kernel`. -/

open LeanCert.Core

namespace RHPi0466

/-- The proven rational interval containing `Real.pi`. -/
def piInterval : IntervalRat := ⟨piLo, piHi, by decide +kernel⟩

/-- LeanCert's computable log enclosure of `piInterval` at series depth 220. -/
def logPiEnclosure : IntervalRat := IntervalRat.logComputable piInterval 220

def logPiLo : ℚ := 1144729885849400174143427351353058711647294812915311571513623071472137769884826079783623270275489707702/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def logPiHi : ℚ := 1144729885849400174143427351353058711647294812915311571513623071472137769884826079783623270275489707703/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

theorem log_finite_check : logPiLo ≤ logPiEnclosure.lo ∧ logPiEnclosure.hi ≤ logPiHi := by
  decide +kernel

theorem log_pi_bounds :
    (logPiLo : ℝ) ≤ Real.log Real.pi ∧ Real.log Real.pi ≤ (logPiHi : ℝ) := by
  have hmem : Real.pi ∈ piInterval := pi_bounds
  have h := IntervalRat.mem_logComputable hmem (by decide +kernel) 220
  change (logPiEnclosure.lo : ℝ) ≤ Real.log Real.pi ∧ Real.log Real.pi ≤ (logPiEnclosure.hi : ℝ) at h
  constructor
  · exact le_trans (by exact_mod_cast log_finite_check.1) h.1
  · exact le_trans h.2 (by exact_mod_cast log_finite_check.2)

theorem log_pi_width : logPiHi - logPiLo ≤ (1 : ℚ) / 10 ^ 100 := by decide +kernel

end RHPi0466

