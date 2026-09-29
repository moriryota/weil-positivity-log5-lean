import PoleParity
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory Set
open RHConditionalLog5 RHResidualMembership RHWeilColumnCandidate RHLog5Bridge
open RHConcreteParameters RHRealWeil RHWeilShift RH_LiteratureBridge RHPoleParity

namespace RHPoleParity

lemma component_eq_zero_of_not_mem (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ) (hx : |x| > halfWidth) :
    component o u x = 0 := by
  have h1 : u x = 0 := by
    by_contra h
    have h_le := hu.2 x h
    linarith
  have h2 : u (-x) = 0 := by
    by_contra h
    have h_le := hu.2 (-x) h
    rw [abs_neg] at h_le
    linarith
  unfold component
  cases o <;> dsimp <;> rw [h1, h2] <;> ring

lemma basis_eq_zero_of_not_mem (n : ℕ) (x : ℝ) (hx : |x| > halfWidth) :
    basis n x = 0 := by
  unfold basis zeroPoly indicator
  have h_not : x ∉ Icc (-halfWidth) halfWidth := by
    intro h
    have h_abs : |x| ≤ halfWidth := abs_le.mpr h
    linarith
  exact if_neg h_not

lemma low_eq_zero_of_not_mem (o : Bool) (u : ℝ → ℝ) (x : ℝ) (hx : |x| > halfWidth) :
    low o u x = 0 := by
  unfold low
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  rw [basis_eq_zero_of_not_mem (degree o i) x hx, mul_zero]

lemma tail_eq_zero_of_not_mem (o : Bool) (u : ℝ → ℝ) (hu : Test u) (x : ℝ) (hx : |x| > halfWidth) :
    tail o u x = 0 := by
  unfold tail
  simp only [Pi.sub_apply]
  rw [component_eq_zero_of_not_mem o u hu x hx, low_eq_zero_of_not_mem o u x hx, sub_zero]

end RHPoleParity
