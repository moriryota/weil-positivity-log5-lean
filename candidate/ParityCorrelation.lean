import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic
open MeasureTheory
namespace RHParityCorrelation
/-- The sum of the two shifted mixed products is antisymmetric under t ↦ s-t. -/
theorem shifted_mixed_zero (e o : ℝ → ℝ)
    (he : ∀ x, e (-x) = e x) (ho : ∀ x, o (-x) = -o x) (s : ℝ) :
    (∫ t, e t * o (t-s) + o t * e (t-s)) = 0 := by
  let F : ℝ → ℝ := fun t => e t * o (t-s) + o t * e (t-s)
  have hneg (t : ℝ) : F (s-t) = -F t := by
    have hst : s-t = -(t-s) := by ring
    have htt : s-t-s = -t := by ring
    dsimp only [F]
    rw [htt, hst, he, ho, he, ho]
    ring
  have hi := integral_sub_left_eq_self F volume s
  have hr : (∫ t, F (s-t)) = -(∫ t, F t) := by
    simp_rw [hneg]
    exact integral_neg F
  change (∫ t, F t) = 0
  linarith
/-- Reflection leaves the real autocorrelation integral unchanged. -/
theorem correlation_reflection (u : ℝ → ℝ) (s : ℝ) :
    (∫ t, u (-t) * u (-(t-s))) = ∫ t, u t * u (t-s) := by
  have hi := integral_sub_left_eq_self (fun t : ℝ => u (-t) * u (-(t-s))) volume s
  have he : (fun t : ℝ => u (-(s-t)) * u (-((s-t)-s))) =
      (fun t : ℝ => u t * u (t-s)) := by
    funext t
    rw [show -(s-t) = t-s by ring, show -((s-t)-s) = t by ring]
    exact mul_comm _ _
  rw [he] at hi
  exact hi.symm
/-- Reflection invariance of the full iterated square energy; no Fubini used. -/
theorem kernel_energy_reflection (K u : ℝ → ℝ) :
    (∫ x, ∫ y, K |x-y| * (u (-x)-u (-y))^2) =
    ∫ x, ∫ y, K |x-y| * (u x-u y)^2 := by
  have inner (x : ℝ) :
      (∫ y, K |x-y| * (u (-x)-u (-y))^2) =
      ∫ y, K |(-x)-y| * (u (-x)-u y)^2 := by
    have h := integral_neg_eq_self
      (fun y : ℝ => K |x-y| * (u (-x)-u (-y))^2) volume
    simp only [neg_neg] at h
    have ha (y : ℝ) : |x-(-y)| = |(-x)-y| := by
      rw [show (-x)-y = -(x-(-y)) by ring, abs_neg]
    simp_rw [ha] at h
    exact h.symm
  simp_rw [inner]
  exact integral_neg_eq_self
    (fun x : ℝ => ∫ y, K |x-y| * (u x-u y)^2) volume

theorem square_reflection (u : ℝ → ℝ) :
    (∫ x, (u (-x))^2) = ∫ x, (u x)^2 :=
  integral_neg_eq_self (fun x : ℝ => (u x)^2) volume

theorem even_weight_reflection (u w : ℝ → ℝ)
    (hw : ∀ x, w (-x) = w x) :
    (∫ x, u (-x)*w x) = ∫ x, u x*w x := by
  have h := integral_neg_eq_self (fun x : ℝ => u (-x)*w x) volume
  simp only [neg_neg, hw] at h
  exact h.symm

theorem odd_weight_reflection (u w : ℝ → ℝ)
    (hw : ∀ x, w (-x) = -w x) :
    (∫ x, u (-x)*w x) = -(∫ x, u x*w x) := by
  have h := integral_neg_eq_self (fun x : ℝ => u (-x)*w x) volume
  simp only [neg_neg, hw, mul_neg, integral_neg] at h
  exact h.symm

end RHParityCorrelation

