import SRed0516
import Interface0516

/-! # 0516: x-space integrals of `Sx` (Interface0516) reduced to `u = x/L`

* `∫ Sx_i Sx_k = L c_i c_k ∫_{−1}^1 φ_i φ_k`;
* `∫ Sx_i · basis_k = L c_i c_k ∫_{−1}^1 φ_i P_k`. -/

open Set MeasureTheory intervalIntegral

namespace RHSxScale0516
open RHLeg0503 RHSingDef0516 RHInterface0516 RHLog5Bridge

local notation "Lw" => halfWidth

lemma Sx_zero {n : ℕ} {x : ℝ} (hx : x ∉ Ioc (-Lw) Lw) : Sx n x = 0 := by
  unfold Sx
  rw [if_neg]
  intro h
  apply hx
  rw [abs_lt] at h
  exact ⟨h.1, h.2.le⟩

lemma Sx_scale (n : ℕ) {u : ℝ} (h1 : -1 < u) (h2 : u < 1) : Sx n (Lw * u) = RHRpExact0506.cc n * phi n u := by
  have hL := halfWidth_pos
  unfold Sx
  rw [if_pos, mul_div_cancel_left₀ u hL.ne']
  rw [abs_lt]; constructor <;> nlinarith

lemma to_interval (f : ℝ → ℝ) (hf : ∀ x, x ∉ Ioc (-Lw) Lw → f x = 0) :
    ∫ x, f x = Lw * ∫ u in (-1:ℝ)..1, f (Lw * u) := by
  have hL := halfWidth_pos
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hf, ← intervalIntegral.integral_of_le (by linarith)]
  have h := intervalIntegral.integral_comp_mul_left (a := -1) (b := 1) f hL.ne'
  rw [smul_eq_mul, mul_neg, mul_one] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]

theorem gam_x (i k : ℕ) : ∫ x, Sx i x * Sx k x =
    Lw * (RHRpExact0506.cc i * RHRpExact0506.cc k) * ∫ u in (-1:ℝ)..1, phi i u * phi k u := by
  rw [to_interval (fun x => Sx i x * Sx k x) (fun x hx => by rw [Sx_zero hx, zero_mul]), mul_assoc]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume 1] with u hne hu
  rw [uIoc_of_le (by norm_num)] at hu
  rw [Sx_scale i hu.1 (lt_of_le_of_ne hu.2 hne), Sx_scale k hu.1 (lt_of_le_of_ne hu.2 hne)]
  ring

theorem s_x (i k : ℕ) : ∫ x, Sx i x * RHConditionalLog5.basis k x =
    Lw * (RHRpExact0506.cc i * RHRpExact0506.cc k) * ∫ u in (-1:ℝ)..1, phi i u * p k u := by
  have hL := halfWidth_pos
  rw [to_interval (fun x => Sx i x * RHConditionalLog5.basis k x)
      (fun x hx => by rw [Sx_zero hx, zero_mul]), mul_assoc]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume 1] with u hne hu
  rw [uIoc_of_le (by norm_num)] at hu
  have h2 : u < 1 := lt_of_le_of_ne hu.2 hne
  rw [Sx_scale i hu.1 h2]
  have hb : RHConditionalLog5.basis k (Lw * u) = RHRpExact0506.cc k * p k u := by
    unfold RHConditionalLog5.basis RHWeilColumnCandidate.zeroPoly
    rw [Set.indicator_of_mem (by constructor <;> nlinarith [hu.1]), RHLink0505.basisPoly_eval,
      mul_div_cancel_left₀ u hL.ne']
    rfl
  rw [hb]; ring

end RHSxScale0516

