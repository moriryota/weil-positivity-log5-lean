import ConditionalLog5
import ConcreteParameters
import CertificateData
import MatrixCertificateEnclosure
import StepB1_CertData
import LowCertificate
import TargetFormBinding

open scoped Matrix BigOperators

namespace RHStepB3G5

open RHConditionalLog5 RHCertificateData RHConcreteParameters RHStepB1CertData RHLowCertificate RHTargetFormBinding

/-- Intermediate band completion of squares applied to the concrete weights:
    for any low-frequency state and any test vector `y`, the Schur complement is bounded
    above by the completed quadratic form. -/
theorem concrete_schur_completion (o : Bool) (u : ℝ → ℝ) (y : I → ℝ) :
    targetQ_real (low o u) - ∑ i : I, (mixed o u i)^2 / concrete.weights o i ≤
      targetQ_real (low o u) + ∑ i : I, (2 * mixed o u i * y i + concrete.weights o i * (y i)^2) := by
  have hd : ∀ i, 0 < concrete.weights o i := fun i => (dN_pos o).trans_le ((g4 o).1 i)
  exact intermediate_band_schur_bound (concrete.weights o) (mixed o u) y hd (targetQ_real (low o u))

/-- Raw Arb low-block operator bound for the even sector:
    the Schur complement is lower bounded by the raw certified factor `1 - even_eta_raw_upper`. -/
def G5EvenRawBound : Prop := ∀ u, Test u →
  (1 - even_eta_raw_upper) * (∑ i : I, (concrete.coordinates false u i)^2) ≤
    targetQ_real (low false u) - ∑ i : I, (mixed false u i)^2 / concrete.weights false i

/-- Raw Arb low-block operator bound for the odd sector:
    the Schur complement is lower bounded by the raw certified factor `1 - odd_eta_raw_upper`. -/
def G5OddRawBound : Prop := ∀ u, Test u →
  (1 - odd_eta_raw_upper) * (∑ i : I, (concrete.coordinates true u i)^2) ≤
    targetQ_real (low true u) - ∑ i : I, (mixed true u i)^2 / concrete.weights true i

/-- Combined raw Arb low-block operator bound across sectors. -/
def G5RawBound : Prop := G5EvenRawBound ∧ G5OddRawBound

/-- G5 transfer theorem: the raw Arb operator bounds together with the certified rational bounds
    `even_eta_le_bound` and `odd_eta_le_bound` strictly imply G5 for concrete parameters. -/
theorem g5_of_sector_raw_bounds (h_even : G5EvenRawBound) (h_odd : G5OddRawBound) : G5 concrete := by
  intro o u hu
  cases o
  · dsimp [G5, eta]
    have h_raw := h_even u hu
    have h_c : 0 ≤ ∑ i : I, (concrete.coordinates false u i)^2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h_eta := even_eta_le_bound
    have h_mono : (1 - eta_even_bound) * (∑ i : I, (concrete.coordinates false u i)^2) ≤
      (1 - even_eta_raw_upper) * (∑ i : I, (concrete.coordinates false u i)^2) := by
      nlinarith
    exact h_mono.trans h_raw
  · dsimp [G5, eta]
    have h_raw := h_odd u hu
    have h_c : 0 ≤ ∑ i : I, (concrete.coordinates true u i)^2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h_eta := odd_eta_le_bound
    have h_mono : (1 - eta_odd_bound) * (∑ i : I, (concrete.coordinates true u i)^2) ≤
      (1 - odd_eta_raw_upper) * (∑ i : I, (concrete.coordinates true u i)^2) := by
      nlinarith
    exact h_mono.trans h_raw

/-- G5 transfer directly from combined raw Arb bound. -/
theorem g5_of_raw_bound (h : G5RawBound) : G5 concrete :=
  g5_of_sector_raw_bounds h.1 h.2

end RHStepB3G5

