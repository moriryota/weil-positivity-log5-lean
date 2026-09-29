import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
open MeasureTheory Set
open scoped ENNReal
namespace RHEnergySplit

theorem quadrant_split (I : Set ℝ) (hI : MeasurableSet I)
    (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F)
    (hsym : ∀ x y, F (x,y) = F (y,x))
    (hzero : ∀ x ∉ I, ∀ y ∉ I, F (x,y) = 0) :
    (∫⁻ x, ∫⁻ y, F (x,y)) =
      (∫⁻ x in I, ∫⁻ y in I, F (x,y)) +
        2 * (∫⁻ x in I, ∫⁻ y in Iᶜ, F (x,y)) := by
  have hmI : Measurable (fun x => ∫⁻ y in I, F (x,y)) := hF.lintegral_prod_right'
  have hsplit (x : ℝ) : (∫⁻ y, F (x,y)) =
      (∫⁻ y in I, F (x,y)) + (∫⁻ y in Iᶜ, F (x,y)) :=
    (lintegral_add_compl (fun y => F (x,y)) hI).symm
  have hcc : (∫⁻ x in Iᶜ, ∫⁻ y in Iᶜ, F (x,y)) = 0 := by
    have hrow : ∀ᵐ x ∂volume.restrict Iᶜ, (∫⁻ y in Iᶜ, F (x,y)) = 0 := by
      filter_upwards [ae_restrict_mem hI.compl] with x hx
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [ae_restrict_mem hI.compl] with y hy
      exact hzero x hx y hy
    exact lintegral_eq_zero_of_ae_eq_zero hrow
  have hcross : (∫⁻ x in Iᶜ, ∫⁻ y in I, F (x,y)) =
      (∫⁻ x in I, ∫⁻ y in Iᶜ, F (x,y)) := by
    rw [lintegral_lintegral_swap (f := fun x y => F (x,y)) hF.aemeasurable]
    apply lintegral_congr
    intro y
    apply lintegral_congr
    intro x
    exact hsym x y
  rw [← lintegral_add_compl (fun x => ∫⁻ y, F (x,y)) hI]
  simp_rw [hsplit]
  rw [lintegral_add_left hmI _, lintegral_add_left hmI _, hcc, add_zero, hcross,
    two_mul]
  ac_rfl

end RHEnergySplit
