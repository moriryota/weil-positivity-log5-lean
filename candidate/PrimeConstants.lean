import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
namespace RHPrimeConstants

noncomputable def alpha (a : ℝ) : ℝ := a / Real.sqrt 2
noncomputable def beta (a : ℝ) : ℝ := a / 2
noncomputable def lam (a : ℝ) : ℝ := a * (1 + Real.sqrt 17) / 4
noncomputable def ratio : ℝ := Real.sqrt 2 * (Real.sqrt 17 - 1) / 4
noncomputable def mass : ℝ := (17 - Real.sqrt 17) / 34

lemma sqrt_two_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
lemma sqrt_seventeen_bounds : 4 < Real.sqrt (17 : ℝ) ∧ Real.sqrt (17 : ℝ) < 5 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17)
  have hn := Real.sqrt_nonneg (17 : ℝ)
  constructor <;> nlinarith

lemma alpha_pos {a : ℝ} (ha : 0 < a) : 0 < alpha a := div_pos ha sqrt_two_pos
lemma beta_pos {a : ℝ} (ha : 0 < a) : 0 < beta a := div_pos ha (by norm_num)
lemma ratio_pos : 0 < ratio := by
  unfold ratio
  have hs := sqrt_seventeen_bounds.1
  exact div_pos (mul_pos sqrt_two_pos (by linarith)) (by norm_num)

lemma lam_mul_ratio (a : ℝ) : lam a * ratio = 2 * alpha a := by
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs17 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17)
  unfold lam ratio alpha
  field_simp
  rw [hs2]
  have hp : (1 + Real.sqrt 17) * (Real.sqrt 17 - 1) = 16 := by nlinarith
  calc
    a * (1 + Real.sqrt 17) * 2 * (Real.sqrt 17 - 1) =
        a * ((1 + Real.sqrt 17) * (Real.sqrt 17 - 1)) * 2 := by ring
    _ = a * 4 ^ 2 * 2 := by rw [hp]; ring

lemma lam_eq_two_alpha_div_ratio (a : ℝ) : lam a = 2 * alpha a / ratio :=
  (eq_div_iff ratio_pos.ne').mpr (lam_mul_ratio a)

lemma lam_eq_beta_add_alpha_ratio (a : ℝ) : lam a = beta a + alpha a * ratio := by
  unfold lam beta alpha ratio
  field_simp
  ring

lemma delta_pos {a : ℝ} (ha : 0 < a) : 0 < lam a - alpha a := by
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs2pos := sqrt_two_pos
  have hs17 := sqrt_seventeen_bounds.1
  have h2 : 1 < Real.sqrt (2 : ℝ) := by nlinarith
  have hb : 1 / Real.sqrt (2 : ℝ) < (1 + Real.sqrt 17) / 4 := by
    apply (div_lt_iff₀ hs2pos).mpr
    nlinarith
  unfold lam alpha
  have hmul := mul_lt_mul_of_pos_left hb ha
  apply sub_pos.mpr
  calc
    a / Real.sqrt 2 = a * (1 / Real.sqrt 2) := by ring
    _ < a * ((1 + Real.sqrt 17) / 4) := hmul
    _ = a * (1 + Real.sqrt 17) / 4 := by ring

lemma ratio_sq : ratio ^ 2 = (9 - Real.sqrt 17) / 4 := by
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs17 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17)
  unfold ratio
  rw [div_pow, mul_pow]
  norm_num
  nlinarith

lemma mass_identity : ratio ^ 2 / (2 + ratio ^ 2) = mass := by
  have hs17 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17)
  have hden : 0 < 2 + ratio ^ 2 := by positivity
  apply (div_eq_iff hden.ne').mpr
  rw [ratio_sq]
  unfold mass
  nlinarith

lemma mass_pos : 0 < mass := by
  unfold mass
  have hs := sqrt_seventeen_bounds.2
  exact div_pos (by linarith) (by norm_num)

end RHPrimeConstants
