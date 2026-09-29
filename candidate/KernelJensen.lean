import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic
open MeasureTheory Set
namespace RHKernelJensen

lemma average_exp {s : ℝ} (hs : s ≠ 0) :
    (⨍ t in Icc (-1 : ℝ) 1, Real.exp (s*t)) = Real.sinh s / s := by
  rw [setAverage_eq, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_mul_left _ hs, integral_exp]
  simp only [Real.volume_real_Icc, sub_neg_eq_add, mul_neg, mul_one, smul_eq_mul]
  norm_num
  rw [Real.sinh_eq]
  ring

theorem sinh_ratio_bound {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) :
    Real.sinh s / s ≤ (Real.sinh 2 / 2) ^ (s/2) := by
  have hp : 0 ≤ s/2 := by positivity
  have hp1 : s/2 ≤ 1 := by linarith
  have hexp : (fun t : ℝ => (Real.exp (2*t)) ^ (s/2)) =
      (fun t : ℝ => Real.exp (s*t)) := by
    funext t
    rw [← Real.exp_mul]
    congr 1
    ring
  have hcont : Continuous (fun x : ℝ => x ^ (s/2)) :=
    Real.continuous_rpow_const hp
  have hfi : IntegrableOn (fun t : ℝ => Real.exp (2*t)) (Icc (-1) 1) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (2*t))).integrableOn_Icc
  have hgi : IntegrableOn ((fun x : ℝ => x ^ (s/2)) ∘
      (fun t : ℝ => Real.exp (2*t))) (Icc (-1) 1) := by
    exact (hcont.comp (by fun_prop)).integrableOn_Icc
  have hj := (Real.concaveOn_rpow hp hp1).le_map_set_average
    hcont.continuousOn isClosed_Ici
    (by norm_num : volume (Icc (-1 : ℝ) 1) ≠ 0)
    (by simp : volume (Icc (-1 : ℝ) 1) ≠ ⊤)
    (Filter.Eventually.of_forall (fun t : ℝ => (Real.exp_pos (2*t)).le)) hfi hgi
  change (⨍ t in Icc (-1 : ℝ) 1, (Real.exp (2*t)) ^ (s/2)) ≤
    (⨍ t in Icc (-1 : ℝ) 1, Real.exp (2*t)) ^ (s/2) at hj
  rw [hexp, average_exp hs.ne', average_exp (by norm_num : (2 : ℝ) ≠ 0)] at hj
  exact hj
end RHKernelJensen
