import LeanCert.Core.IntervalRat.Taylor
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open LeanCert.Core
namespace Trial0455
private def enclosure : IntervalRat := IntervalRat.logComputable (IntervalRat.singleton 2) 220
def lo : ℚ := 6931471805599453094172321214581765680755001343602552541206800094933936219696947156058633269964186875 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def hi : ℚ := 6931471805599453094172321214581765680755001343602552541206800094933936219696947156058633269964186876 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
theorem finite_check : lo ≤ enclosure.lo ∧ enclosure.hi ≤ hi := by
  decide +kernel
theorem log2_bounds : (lo : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (hi : ℝ) := by
  have h := IntervalRat.mem_logComputable (IntervalRat.mem_singleton (2 : ℚ)) (by norm_num [IntervalRat.singleton]) 220
  change (enclosure.lo : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (enclosure.hi : ℝ) at h
  constructor
  · exact le_trans (by exact_mod_cast finite_check.1) h.1
  · exact le_trans h.2 (by exact_mod_cast finite_check.2)
end Trial0455
