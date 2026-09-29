import ConditionalLog5
import ConcreteParameters
import CertificateData
import MatrixCertificateEnclosure

open scoped Matrix BigOperators

namespace RHStepB1CertData

open RHConditionalLog5 RHCertificateData RHConcreteParameters

/-- Certified upper bound on the even sector low-block model error from 0417 Arb run:
    η_even ≤ 103691566 / 10^35 < 1 / 10^20. -/
noncomputable def even_eta_raw_upper : ℝ := 103691566 / 10^35

/-- Certified upper bound on the odd sector low-block model error from 0417 Arb run:
    η_odd ≤ 109642 / 10^35 < 1 / 10^20. -/
noncomputable def odd_eta_raw_upper : ℝ := 109642 / 10^35

/-- Certified upper bound on the even sector residual Gram trace from 0417 Arb run:
    τ_even ≤ 787874464226 / 10^12 < 788 / 1000. -/
noncomputable def even_tau_raw_upper : ℝ := 787874464226 / 10^12

/-- Certified upper bound on the odd sector residual Gram trace from 0417 Arb run:
    τ_odd ≤ 924616292074 / 10^12 < 925 / 1000. -/
noncomputable def odd_tau_raw_upper : ℝ := 924616292074 / 10^12

/-- Exact rational check: even sector raw Arb η bound is below the Lean target bound. -/
theorem even_eta_le_bound : even_eta_raw_upper ≤ eta_even_bound := by
  unfold even_eta_raw_upper eta_even_bound; norm_num

/-- Exact rational check: odd sector raw Arb η bound is below the Lean target bound. -/
theorem odd_eta_le_bound : odd_eta_raw_upper ≤ eta_odd_bound := by
  unfold odd_eta_raw_upper eta_odd_bound; norm_num

/-- Exact rational check: even sector raw Arb τ bound is below the Lean target bound. -/
theorem even_tau_le_bound : even_tau_raw_upper ≤ tau_even_bound := by
  unfold even_tau_raw_upper tau_even_bound; norm_num

/-- Exact rational check: odd sector raw Arb τ bound is below the Lean target bound. -/
theorem odd_tau_le_bound : odd_tau_raw_upper ≤ tau_odd_bound := by
  unfold odd_tau_raw_upper tau_odd_bound; norm_num

/-- Universal positivity of the certified τ parameter across sectors. -/
theorem tau_pos (o : Bool) : 0 < tau o := by
  cases o <;> simp only [tau, Bool.false_eq_true, ↓reduceIte]
  · unfold tau_even_bound; norm_num
  · unfold tau_odd_bound; norm_num

/-- Universal bound τ < 1 across sectors. -/
theorem tau_lt_one (o : Bool) : tau o < 1 := by
  cases o <;> simp only [tau, Bool.false_eq_true, ↓reduceIte]
  · unfold tau_even_bound; norm_num
  · unfold tau_odd_bound; norm_num

/-- Universal positivity of the certified η parameter across sectors. -/
theorem eta_pos (o : Bool) : 0 < eta o := by
  cases o <;> simp only [eta, Bool.false_eq_true, ↓reduceIte]
  · unfold eta_even_bound; norm_num
  · unfold eta_odd_bound; norm_num

/-- Universal bound η < 1 across sectors. -/
theorem eta_lt_one (o : Bool) : eta o < 1 := by
  cases o <;> simp only [eta, Bool.false_eq_true, ↓reduceIte]
  · unfold eta_even_bound; norm_num
  · unfold eta_odd_bound; norm_num

/-- The combined Schur margin 1 - η - τ is strictly positive for both sectors. -/
theorem margin_positive (o : Bool) : 0 < 1 - eta o - tau o :=
  RHConditionalLog5.margin_pos o

end RHStepB1CertData

