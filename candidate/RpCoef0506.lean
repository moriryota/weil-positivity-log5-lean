import RpExact0506
import Entry22_0505

/-! # 0506: coefficient error `rt` (exact, irrational) vs `rq` (60-digit rationals)

* `|2/(2k+1) · γ n J d k| ≤ 8 Σ_{j<J} |d_j| 2^j` (AM–GM with `orth` on [−1,1]);
* `Σ_{j<J} |rt j − rq_j| 2^j ≤ 10⁻³²` from `log 5 ∈ [l5L, l5H]` (per-coefficient rational bounds,
  `decide +kernel`);
hence `|γ n J rt k − γ n J rq k| ≤ 4(2k+1)·10⁻³²`. -/

open MeasureTheory Set Finset
open scoped BigOperators Interval

namespace RHRpCoef0506
open RHLeg0503 RHGForm0505 RHRpExact0506 RHAlgoBall0505 RHLog5Bridge

@[fun_prop] lemma cont_p (n : ℕ) : Continuous fun x => p n x := continuous_p n

lemma γ_sub (n J : ℕ) (r r' : ℕ → ℝ) (k : ℕ) :
    γ n J r k - γ n J r' k = γ n J (fun j => r j - r' j) k := by
  unfold γ; rw [← sum_sub_distrib]; exact sum_congr rfl (fun j _ => by ring)

lemma ii1 {f : ℝ → ℝ} (hf : Continuous f) : IntervalIntegrable f volume (-1) 1 := hf.intervalIntegrable _ _

lemma orth_self (n : ℕ) : ∫ u in (-1:ℝ)..1, p n u * p n u ≤ 2 := by
  rw [RHLink0505.orth, if_pos rfl]
  rw [div_le_iff₀ (by positivity)]; nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]

lemma absprod1 (n k : ℕ) : ∫ u in (-1:ℝ)..1, |p n u| * |p k u| ≤ 2 := by
  have hpt : ∀ u ∈ Icc (-1:ℝ) 1, |p n u| * |p k u| ≤ (p n u * p n u + p k u * p k u) / 2 := fun u _ => by
    nlinarith [sq_nonneg (abs (p n u) - abs (p k u)), sq_abs (p n u), sq_abs (p k u)]
  have h := intervalIntegral.integral_mono_on (a := -1) (b := 1) (by norm_num) (ii1 (by fun_prop)) (ii1 (by fun_prop)) hpt
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (ii1 (by fun_prop)) (ii1 (by fun_prop))] at h
  linarith [orth_self n, orth_self k]

lemma abs1 (n : ℕ) : ∫ u in (-1:ℝ)..1, |p n u| ≤ 2 := by
  have hpt : ∀ u ∈ Icc (-1:ℝ) 1, |p n u| ≤ (p n u * p n u + 1) / 2 := fun u _ => by
    nlinarith [sq_nonneg (abs (p n u) - 1), sq_abs (p n u)]
  have h := intervalIntegral.integral_mono_on (a := -1) (b := 1) (by norm_num) (ii1 (by fun_prop)) (ii1 (by fun_prop)) hpt
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (ii1 (by fun_prop)) (ii1 (by fun_prop)),
    intervalIntegral.integral_const, smul_eq_mul] at h
  linarith [orth_self n]

lemma Rd_bound (J : ℕ) (d : ℕ → ℝ) {w : ℝ} (hw0 : 0 ≤ w) (hw2 : w ≤ 2) :
    |∑ j ∈ range J, d j * w ^ j| ≤ ∑ j ∈ range J, |d j| * 2 ^ j := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun j _ => ?_))
  rw [abs_mul, abs_pow, abs_of_nonneg hw0]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw0 hw2 j) (abs_nonneg _)

theorem γ_bound (n J k : ℕ) (d : ℕ → ℝ) :
    |2 / (2 * k + 1) * γ n J d k| ≤ 8 * ∑ j ∈ range J, |d j| * 2 ^ j := by
  set A := ∑ j ∈ range J, |d j| * 2 ^ j with hA
  have hA0 : 0 ≤ A := sum_nonneg (fun j _ => by positivity)
  set C := ∫ v in (-1:ℝ)..1, |p n v|
  rw [← entry_eq n J k d]
  have hinner : ∀ u ∈ Icc (-1:ℝ) 1,
      |∫ v in (-1:ℝ)..1, (∑ j ∈ range J, d j * |u - v| ^ j) * (p n u - p n v)| ≤ A * (2 * |p n u| + C) := by
    intro u hu
    rw [← Real.norm_eq_abs]
    have hb : ∀ᵐ v ∂volume, v ∈ Set.Ioc (-1:ℝ) 1 →
        ‖(∑ j ∈ range J, d j * |u - v| ^ j) * (p n u - p n v)‖ ≤ A * (|p n u| + |p n v|) := by
      refine Filter.Eventually.of_forall (fun v hv => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := Rd_bound J d (abs_nonneg (u - v)) (by rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hv.1, hv.2])
      exact mul_le_mul h1 (abs_sub _ _) (abs_nonneg _) hA0
    have h := intervalIntegral.norm_integral_le_of_norm_le (a := -1) (b := 1)
      (g := fun v => A * (|p n u| + |p n v|)) (by norm_num) hb (ii1 (by fun_prop))
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (ii1 (by fun_prop)) (ii1 (by fun_prop)),
      intervalIntegral.integral_const, smul_eq_mul] at h
    have : A * ((1 - -1) * |p n u| + C) = A * (2 * |p n u| + C) := by ring
    linarith
  have hcont : Continuous fun u => A * (2 * |p n u| + C) * |p k u| := by fun_prop
  have hb2 : ∀ᵐ u ∂volume, u ∈ Set.Ioc (-1:ℝ) 1 →
      ‖p k u * ∫ v in (-1:ℝ)..1, (∑ j ∈ range J, d j * |u - v| ^ j) * (p n u - p n v)‖ ≤
        A * (2 * |p n u| + C) * |p k u| := by
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hinner u ⟨hu.1.le, hu.2⟩) (abs_nonneg _)
  have h := intervalIntegral.norm_integral_le_of_norm_le (a := -1) (b := 1)
    (g := fun u => A * (2 * |p n u| + C) * |p k u|) (by norm_num) hb2 (ii1 hcont)
  rw [Real.norm_eq_abs] at h
  refine h.trans ?_
  have e : (fun u => A * (2 * |p n u| + C) * |p k u|) = fun u => (2 * A) * (|p n u| * |p k u|) + (A * C) * |p k u| := by
    funext u; ring
  rw [e, intervalIntegral.integral_add (ii1 (by fun_prop)) (ii1 (by fun_prop)), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have h1 := absprod1 n k
  have h2 := abs1 k
  have h3 : C ≤ 2 := abs1 n
  have h4 : 0 ≤ C := intervalIntegral.integral_nonneg (by norm_num) (fun v _ => abs_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * A),
    mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ A * C), mul_le_mul_of_nonneg_left h3 hA0]

/-! ## Coefficient enclosure -/

def lo : ℚ := RHEntry00Bounds0495.l5L / 4
def hi : ℚ := RHEntry00Bounds0495.l5H / 4
def qj (j : ℕ) : ℚ := RHRkApprox0500.ql.getD j 0
def rqj (j : ℕ) : ℚ := (rnum RHEntry22_0505.rq j : ℚ) / (rden RHEntry22_0505.rq j : ℚ)
def Dq (j : ℕ) : ℚ := max |qj j * lo ^ j - rqj j| |qj j * hi ^ j - rqj j|
def Dsum : ℚ := ∑ j ∈ range 81, Dq j * 2 ^ j

lemma Dsum_le : Dsum ≤ 1 / 10 ^ 32 := by decide +kernel
lemma J_eq : J = 81 := by decide +kernel
lemma rden_pos (j : ℕ) : 0 < rden RHEntry22_0505.rq j := by
  by_cases h : j < 81
  · interval_cases j <;> decide +kernel
  · unfold rden; rw [List.getD_eq_default _ _ (by simp [RHEntry22_0505.rq]; omega)]; decide

lemma between {c a b x r : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    |c * x - r| ≤ max |c * a - r| |c * b - r| := by
  rcases le_total 0 c with hc | hc
  · have h1 : c * a ≤ c * x := mul_le_mul_of_nonneg_left hax hc
    have h2 : c * x ≤ c * b := mul_le_mul_of_nonneg_left hxb hc
    rw [abs_le]; constructor
    · have := neg_abs_le (c * a - r); have := le_max_left |c * a - r| |c * b - r|; linarith
    · have := le_abs_self (c * b - r); have := le_max_right |c * a - r| |c * b - r|; linarith
  · have h1 : c * x ≤ c * a := mul_le_mul_of_nonpos_left hax hc
    have h2 : c * b ≤ c * x := mul_le_mul_of_nonpos_left hxb hc
    rw [abs_le]; constructor
    · have := neg_abs_le (c * b - r); have := le_max_right |c * a - r| |c * b - r|; linarith
    · have := le_abs_self (c * a - r); have := le_max_left |c * a - r| |c * b - r|; linarith

lemma rt_close (j : ℕ) : |rt j - rval RHEntry22_0505.rq j| ≤ (Dq j : ℝ) := by
  have h5 := RHEntry00Bounds0495.b_l5
  have hx : (halfWidth / 2) = Real.log 5 / 4 := by unfold RHLog5Bridge.halfWidth; ring
  have hlo0 : (0:ℝ) ≤ ((lo : ℚ) : ℝ) := by
    have : (0:ℚ) ≤ lo := by unfold lo; decide +kernel
    exact_mod_cast this
  have ha : ((lo : ℚ) : ℝ) ^ j ≤ (halfWidth / 2) ^ j := by
    apply pow_le_pow_left₀ hlo0; rw [hx]; unfold lo; push_cast; linarith [h5.1]
  have hb : (halfWidth / 2) ^ j ≤ ((hi : ℚ) : ℝ) ^ j := by
    apply pow_le_pow_left₀ (by rw [hx]; have := Real.log_pos (by norm_num : (1:ℝ) < 5); positivity)
    rw [hx]; unfold hi; push_cast; linarith [h5.2]
  have h := between (c := ((qj j : ℚ) : ℝ)) (r := ((rqj j : ℚ) : ℝ)) ha hb
  have e1 : rt j = ((qj j : ℚ) : ℝ) * (halfWidth / 2) ^ j := rfl
  have e2 : rval RHEntry22_0505.rq j = ((rqj j : ℚ) : ℝ) := by unfold rval rqj; push_cast; rfl
  rw [e1, e2]
  refine h.trans (le_of_eq ?_)
  unfold Dq; push_cast; rfl

theorem coef_err (n k : ℕ) :
    |γ n J rt k - γ n J (rval RHEntry22_0505.rq) k| ≤ 4 * (2 * k + 1) / 10 ^ 32 := by
  rw [γ_sub]
  have h := γ_bound n J k (fun j => rt j - rval RHEntry22_0505.rq j)
  have hs : ∑ j ∈ range J, |rt j - rval RHEntry22_0505.rq j| * 2 ^ j ≤ 1 / 10 ^ 32 := by
    rw [J_eq]
    have : ∑ j ∈ range 81, |rt j - rval RHEntry22_0505.rq j| * 2 ^ j ≤ ∑ j ∈ range 81, (Dq j : ℝ) * 2 ^ j :=
      sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (rt_close j) (by positivity))
    have hD : (∑ j ∈ range 81, (Dq j : ℝ) * 2 ^ j) = ((Dsum : ℚ) : ℝ) := by unfold Dsum; push_cast; rfl
    have hD2 : ((Dsum : ℚ) : ℝ) ≤ 1 / 10 ^ 32 := by
      have := (Rat.cast_le (K := ℝ)).mpr Dsum_le; push_cast at this; exact this
    linarith
  have hk : (0:ℝ) < 2 / (2 * k + 1) := by positivity
  rw [abs_mul, abs_of_pos hk] at h
  have h' : 2 / (2 * k + 1) * |γ n J (fun j => rt j - rval RHEntry22_0505.rq j) k| ≤ 8 / 10 ^ 32 := by
    have : 8 * ∑ j ∈ range J, |rt j - rval RHEntry22_0505.rq j| * 2 ^ j ≤ 8 / 10 ^ 32 := by linarith
    exact h.trans this
  have hk1 : (0:ℝ) < 2 * k + 1 := by positivity
  calc |γ n J (fun j => rt j - rval RHEntry22_0505.rq j) k|
      = (2 * k + 1) / 2 * (2 / (2 * k + 1) * |γ n J (fun j => rt j - rval RHEntry22_0505.rq j) k|) := by
        field_simp
    _ ≤ (2 * k + 1) / 2 * (8 / 10 ^ 32) := mul_le_mul_of_nonneg_left h' (by positivity)
    _ = 4 * (2 * k + 1) / 10 ^ 32 := by ring

end RHRpCoef0506

