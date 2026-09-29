import StepB1_CertData
import StepB2_G6
import StepB3_G5
import SpectralInputs

open scoped Matrix BigOperators

namespace RHStepBAssembly

open RHConditionalLog5 RHCertificateData RHConcreteParameters RHStepB1CertData RHStepB2G6 RHStepB3G5 RHSpectralInputs

/-- System B Main Reduction Theorem:
    Given G1 and G2 from System A, and the raw Arb certificate enclosures G5RawBound and G6RawBound,
    the fixed-window Weil positivity theorem (test functions supported in |x| ≤ log 5 / 2) holds with strictly 0 sorry and standard 3 axioms. -/
theorem target_log5_of_system_a_and_raw_certificates
    (h1 : G1 concrete) (h2 : G2 concrete)
    (h5_raw : G5RawBound) (h6_raw : G6RawBound)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) (hn : f ≠ 0) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier => Zeta23.zetaZeroConfig.Wsummand f f (ρ:ℂ)) ∧
    0 < (Zeta23.zetaZeroConfig.W f f).re :=
  target_log5_unconditional_of_remaining h1 h2 (g5_of_raw_bound h5_raw) (g6_of_raw_bound h6_raw) f hf hs hn

end RHStepBAssembly

