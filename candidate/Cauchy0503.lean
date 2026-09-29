import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # 0503: Cauchy repeated integration and the splitting of `|u − v|^j`

`Im f u = ∫_{−1}^u f`, `Ip f u = ∫_u^1 f`. For continuous `f`:
* `∫_{−1}^u (u−v)^j f(v) dv = j! · (Im^[j+1] f) u`,
* `∫_u^1 (v−u)^j f(v) dv = j! · (Ip^[j+1] f) u`,
* for `u ∈ [−1,1]`: `∫_{−1}^1 |u−v|^j f(v) dv = j! · ((Im^[j+1] f) u + (Ip^[j+1] f) u)`. -/

open intervalIntegral

namespace RHCauchy0503

noncomputable def Im (f : ℝ → ℝ) (u : ℝ) : ℝ := ∫ v in (-1:ℝ)..u, f v
noncomputable def Ip (f : ℝ → ℝ) (u : ℝ) : ℝ := ∫ v in u..(1:ℝ), f v

lemma hasDerivAt_Im {f : ℝ → ℝ} (hf : Continuous f) (u : ℝ) : HasDerivAt (Im f) (f u) u :=
  (hf.integral_hasStrictDerivAt (-1) u).hasDerivAt

lemma continuous_Im {f : ℝ → ℝ} (hf : Continuous f) : Continuous (Im f) :=
  continuous_iff_continuousAt.mpr (fun u => (hasDerivAt_Im hf u).continuousAt)

lemma Ip_eq (f : ℝ → ℝ) (u : ℝ) : Ip f u = -∫ v in (1:ℝ)..u, f v := by
  rw [Ip, integral_symm]

lemma hasDerivAt_Ip {f : ℝ → ℝ} (hf : Continuous f) (u : ℝ) : HasDerivAt (Ip f) (-f u) u := by
  have h := (hf.integral_hasStrictDerivAt 1 u).hasDerivAt.neg
  have e : Ip f = fun u => -∫ v in (1:ℝ)..u, f v := funext (Ip_eq f)
  rw [e]; exact h

lemma continuous_Ip {f : ℝ → ℝ} (hf : Continuous f) : Continuous (Ip f) :=
  continuous_iff_continuousAt.mpr (fun u => (hasDerivAt_Ip hf u).continuousAt)

theorem cauchy_left : ∀ (j : ℕ) {f : ℝ → ℝ}, Continuous f → ∀ u : ℝ,
    ∫ v in (-1:ℝ)..u, (u - v) ^ j * f v = (j.factorial : ℝ) * (Im^[j + 1] f) u
  | 0, f, _, u => by simp [Im]
  | j + 1, f, hf, u => by
      have hibp := integral_mul_deriv_eq_deriv_mul (a := -1) (b := u)
        (u := fun v => (u - v) ^ (j + 1)) (u' := fun v => -((j + 1 : ℝ) * (u - v) ^ j))
        (v := Im f) (v' := f)
        (fun v _ => by
          have h := ((hasDerivAt_id' v).const_sub u).pow (j + 1)
          rw [Nat.add_sub_cancel] at h
          convert h using 1; push_cast; ring)
        (fun v _ => hasDerivAt_Im hf v)
        ((by fun_prop : Continuous fun v : ℝ => -((j + 1 : ℝ) * (u - v) ^ j)).intervalIntegrable _ _)
        (hf.intervalIntegrable _ _)
      rw [hibp]
      have h0 : Im f (-1) = 0 := by simp [Im]
      have ih := cauchy_left j (continuous_Im hf) u
      simp only [sub_self, zero_pow (Nat.succ_ne_zero j), zero_mul, h0, mul_zero, sub_zero, zero_sub]
      have e : (∫ v in (-1:ℝ)..u, -((j + 1 : ℝ) * (u - v) ^ j) * Im f v) =
          -((j + 1 : ℝ) * ∫ v in (-1:ℝ)..u, (u - v) ^ j * Im f v) := by
        rw [← integral_const_mul, ← integral_neg]; congr 1; funext v; ring
      have hit : Im^[j + 1 + 1] f = Im^[j + 1] (Im f) := Function.iterate_succ_apply _ _ _
      rw [e, ih, hit, Nat.factorial_succ]
      push_cast; ring

theorem cauchy_right : ∀ (j : ℕ) {f : ℝ → ℝ}, Continuous f → ∀ u : ℝ,
    ∫ v in u..(1:ℝ), (v - u) ^ j * f v = (j.factorial : ℝ) * (Ip^[j + 1] f) u
  | 0, f, _, u => by simp [Ip]
  | j + 1, f, hf, u => by
      have hibp := integral_mul_deriv_eq_deriv_mul (a := u) (b := 1)
        (u := fun v => (v - u) ^ (j + 1)) (u' := fun v => (j + 1 : ℝ) * (v - u) ^ j)
        (v := fun v => -Ip f v) (v' := f)
        (fun v _ => by
          have h := ((hasDerivAt_id' v).sub_const u).pow (j + 1)
          rw [Nat.add_sub_cancel] at h
          convert h using 1; push_cast; ring)
        (fun v _ => by
          have h := (hasDerivAt_Ip hf v).neg
          rw [neg_neg] at h
          exact h)
        ((by fun_prop : Continuous fun v : ℝ => (j + 1 : ℝ) * (v - u) ^ j).intervalIntegrable _ _)
        (hf.intervalIntegrable _ _)
      rw [hibp]
      have h1 : Ip f 1 = 0 := by simp [Ip]
      have ih := cauchy_right j (continuous_Ip hf) u
      simp only [sub_self, zero_pow (Nat.succ_ne_zero j), zero_mul, h1, neg_zero, mul_zero, sub_zero,
        zero_sub]
      have e : (∫ v in u..(1:ℝ), (j + 1 : ℝ) * (v - u) ^ j * -Ip f v) =
          -((j + 1 : ℝ) * ∫ v in u..(1:ℝ), (v - u) ^ j * Ip f v) := by
        rw [← integral_const_mul, ← integral_neg]; congr 1; funext v; ring
      have hit : Ip^[j + 1 + 1] f = Ip^[j + 1] (Ip f) := Function.iterate_succ_apply _ _ _
      rw [e, ih, hit, Nat.factorial_succ]
      push_cast; ring

theorem abs_pow_split (j : ℕ) {f : ℝ → ℝ} (hf : Continuous f) {u : ℝ} (hu : u ∈ Set.Icc (-1:ℝ) 1) :
    ∫ v in (-1:ℝ)..1, |u - v| ^ j * f v =
      (j.factorial : ℝ) * ((Im^[j + 1] f) u + (Ip^[j + 1] f) u) := by
  have hc : Continuous fun v => |u - v| ^ j * f v := by fun_prop
  rw [← integral_add_adjacent_intervals (b := u) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have e1 : (∫ v in (-1:ℝ)..u, |u - v| ^ j * f v) = ∫ v in (-1:ℝ)..u, (u - v) ^ j * f v := by
    apply integral_congr
    intro v hv
    rw [Set.uIcc_of_le hu.1] at hv
    simp only; rw [abs_of_nonneg (by linarith [hv.2])]
  have e2 : (∫ v in u..(1:ℝ), |u - v| ^ j * f v) = ∫ v in u..(1:ℝ), (v - u) ^ j * f v := by
    apply integral_congr
    intro v hv
    rw [Set.uIcc_of_le hu.2] at hv
    simp only; rw [abs_sub_comm, abs_of_nonneg (by linarith [hv.1])]
  rw [e1, e2, cauchy_left j hf, cauchy_right j hf]; ring

end RHCauchy0503

