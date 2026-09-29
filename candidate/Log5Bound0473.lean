import LeanCert.Core.IntervalRat.Taylor
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open LeanCert.Core
namespace Trial0456
private def enclosure : IntervalRat := IntervalRat.logComputable (IntervalRat.singleton 5) 240
def lo : ℚ := 16094379124341003746007593332261876395256013542685177219126478914741789877076577646301338780931796107 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def hi : ℚ := 16094379124341003746007593332261876395256013542685177219126478914741789877076577646301338780931796108 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
theorem finite_check : lo ≤ enclosure.lo ∧ enclosure.hi ≤ hi := by
  decide +kernel
theorem log5_bounds : (lo : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ (hi : ℝ) := by
  have h := IntervalRat.mem_logComputable (IntervalRat.mem_singleton (5 : ℚ)) (by norm_num [IntervalRat.singleton]) 240
  change (enclosure.lo : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ (enclosure.hi : ℝ) at h
  constructor
  · exact le_trans (by exact_mod_cast finite_check.1) h.1
  · exact le_trans h.2 (by exact_mod_cast finite_check.2)
end Trial0456
