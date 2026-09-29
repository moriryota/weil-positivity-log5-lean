import CertificateData
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace RHMatrixCertificate

open RHCertificateData

/-- Structure representing a verified numerical certificate for one parity sector. -/
structure SectorCertificate where
  parity_name : String
  eta_bound : ℝ
  tau_bound : ℝ
  d_N_lower : ℝ
  d_M_lower : ℝ
  margin_bound : ℝ
  hdN : 0 < d_N_lower
  hdM : 0 < d_M_lower
  hd_mono : d_N_lower ≤ d_M_lower
  h_schur : eta_bound + tau_bound < 1
  h_margin : margin_bound ≤ 1 - (eta_bound + tau_bound)
  hmargin_pos : 0 < margin_bound

/-- Verified certificate instance for the even parity sector. -/
noncomputable def even_sector_cert : SectorCertificate where
  parity_name := "even"
  eta_bound := eta_even_bound
  tau_bound := tau_even_bound
  d_N_lower := d64_even_lower
  d_M_lower := d128_even_lower
  margin_bound := margin_even_bound
  hdN := even_d64_pos
  hdM := even_d128_pos
  hd_mono := even_d_mono
  h_schur := even_schur_margin
  h_margin := even_margin_lower
  hmargin_pos := even_margin_pos

/-- Verified certificate instance for the odd parity sector. -/
noncomputable def odd_sector_cert : SectorCertificate where
  parity_name := "odd"
  eta_bound := eta_odd_bound
  tau_bound := tau_odd_bound
  d_N_lower := d64_odd_lower
  d_M_lower := d128_odd_lower
  margin_bound := margin_odd_bound
  hdN := odd_d64_pos
  hdM := odd_d128_pos
  hd_mono := odd_d_mono
  h_schur := odd_schur_margin
  h_margin := odd_margin_lower
  hmargin_pos := odd_margin_pos

/-- Strict positivity of the certified margin 1 - (eta + tau). -/
theorem margin_strictly_positive (cert : SectorCertificate) :
    0 < 1 - (cert.eta_bound + cert.tau_bound) := by
  linarith [cert.h_schur]

/-- Strict positivity of 1 - η - τ for any actual parameters bounded by the certificate. -/
theorem schur_multiplier_positive (cert : SectorCertificate) (η τ : ℝ)
    (hη : η ≤ cert.eta_bound) (hτ : τ ≤ cert.tau_bound) :
    0 < 1 - η - τ := by
  have h := cert.h_schur
  linarith

/-- Lower bound on 1 - η - τ by the certificate margin. -/
theorem certified_schur_margin_bound (cert : SectorCertificate) (η τ : ℝ)
    (hη : η ≤ cert.eta_bound) (hτ : τ ≤ cert.tau_bound) :
    cert.margin_bound ≤ 1 - η - τ := by
  have hm := cert.h_margin
  linarith

/-- Positivity of the margin lower bound. -/
theorem certified_schur_margin_pos (cert : SectorCertificate) (η τ : ℝ)
    (hη : η ≤ cert.eta_bound) (hτ : τ ≤ cert.tau_bound) :
    0 < cert.margin_bound :=
  cert.hmargin_pos

end RHMatrixCertificate

