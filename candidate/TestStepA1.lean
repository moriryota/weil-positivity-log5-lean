import ConditionalLog5
import ResidualMembership

open MeasureTheory Set
open RHConditionalLog5 RHResidualMembership

lemma project_memLp (o : Bool) (N : ℕ) (v : ℝ → ℝ) : MemLp (project o N v) 2 volume := by
  classical
  exact memLp_finsetSum' _ (fun j _ => (basis_memLp (degree o j)).const_smul _)

