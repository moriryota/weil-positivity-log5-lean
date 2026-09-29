import RpExact0506

/-! # 0506: error of replacing `Rk` by `Qs` in `Rp`

`|Rp n k − RpQ n k| ≤ ε/2 · (2L + ((1+2L)/2)²)`, `ε = 2·10⁻²⁴` (0500 `Rk_approx`), using
`∫_I |b_n b_k| ≤ 1` and `∫_I |b_n| ≤ (1+2L)/2` (AM–GM with `gram`). -/

open MeasureTheory Set
open scoped BigOperators

namespace RHRpErr0506
open RHConditionalLog5 RHLog5Bridge RHRpExact0506 RHColDecomp0499

local notation "Lw" => halfWidth

lemma ev_cont : ∀ p : List ℚ, Continuous (RHPolyL0500.ev p)
  | [] => by
      have : RHPolyL0500.ev [] = fun _ => 0 := funext (fun t => rfl)
      rw [this]; exact continuous_const
  | c :: p => by
      have : RHPolyL0500.ev (c :: p) = fun t => (c : ℝ) + t * RHPolyL0500.ev p t := funext (fun t => rfl)
      rw [this]; exact continuous_const.add (continuous_id.mul (ev_cont p))

@[fun_prop] lemma Qs_cont : Continuous Qs := (ev_cont _).comp (continuous_id.div_const 2)

@[fun_prop] lemma bp_cont (n : ℕ) : Continuous fun x => (basisPoly n).eval x := (basisPoly n).continuous

lemma twoL : 2 * halfWidth = Real.log 5 := by unfold halfWidth; ring

lemma ii {f : ℝ → ℝ} (hf : Continuous f) : IntervalIntegrable f volume (-Lw) Lw := hf.intervalIntegrable _ _

lemma Rk_inner_ii (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-Lw) Lw) :
    IntervalIntegrable (fun y => Rk |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y)) volume (-Lw) Lw := by
  have hK := RHColL2.kernel_eval_sub_integrableOn halfWidth halfWidth_pos.le (basisPoly n) x hx
  have hQ := quot_integrableOn (basisPoly n) hx
  have hpt : (fun y => Rk |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y)) =
      fun y => RH_GammaFinalFormula.K_kernel |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y) -
        ((basisPoly n).eval x - (basisPoly n).eval y) / |x - y| := by
    funext y; unfold Rk; ring
  rw [hpt, intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [halfWidth_pos])]
  exact hK.sub hQ

lemma inner_bound (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-Lw) Lw) :
    |∫ y in (-Lw)..Lw, (Rk |x - y| - Qs |x - y|) * ((basisPoly n).eval x - (basisPoly n).eval y)| ≤
      2 / 10 ^ 24 * ∫ y in (-Lw)..Lw, |(basisPoly n).eval x - (basisPoly n).eval y| := by
  have hL := halfWidth_pos
  rw [← Real.norm_eq_abs, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_ (ii (by fun_prop))
  filter_upwards [Measure.ae_ne volume x] with y hne hy
  rw [Real.norm_eq_abs, abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have hs : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne.symm)
  have hs5 : |x - y| ≤ Real.log 5 := by
    rw [← twoL, abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  exact RHRkApprox0500.Rk_approx hs hs5

lemma inner_abs_le (n : ℕ) (x : ℝ) :
    ∫ y in (-Lw)..Lw, |(basisPoly n).eval x - (basisPoly n).eval y| ≤
      2 * Lw * |(basisPoly n).eval x| + ∫ y in (-Lw)..Lw, |(basisPoly n).eval y| := by
  have hL := halfWidth_pos
  have hpt : ∀ y ∈ Icc (-Lw) Lw, |(basisPoly n).eval x - (basisPoly n).eval y| ≤
      |(basisPoly n).eval x| + |(basisPoly n).eval y| := fun y _ => abs_sub _ _
  have h := intervalIntegral.integral_mono_on (a := -Lw) (b := Lw) (by linarith) (ii (by fun_prop)) (ii (by fun_prop)) hpt
  rw [intervalIntegral.integral_add (ii (by fun_prop)) (ii (by fun_prop)), intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

lemma gram_i (n k : ℕ) : ∫ x in (-Lw)..Lw, (basisPoly n).eval x * (basisPoly k).eval x =
    if n = k then 1 else 0 := by
  rw [← RHEntry00_0495.setI]; exact gram n k

lemma absprod_le (n k : ℕ) : ∫ x in (-Lw)..Lw, |(basisPoly n).eval x| * |(basisPoly k).eval x| ≤ 1 := by
  have hL := halfWidth_pos
  have hpt : ∀ x ∈ Icc (-Lw) Lw, |(basisPoly n).eval x| * |(basisPoly k).eval x| ≤
      ((basisPoly n).eval x * (basisPoly n).eval x + (basisPoly k).eval x * (basisPoly k).eval x) / 2 :=
    fun x _ => by
      nlinarith [sq_nonneg (abs ((basisPoly n).eval x) - abs ((basisPoly k).eval x)),
        sq_abs ((basisPoly n).eval x), sq_abs ((basisPoly k).eval x)]
  have h := intervalIntegral.integral_mono_on (a := -Lw) (b := Lw) (by linarith) (ii (by fun_prop)) (ii (by fun_prop)) hpt
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (ii (by fun_prop)) (ii (by fun_prop)), gram_i, gram_i] at h
  simpa using h

lemma abs_le_C (n : ℕ) : ∫ x in (-Lw)..Lw, |(basisPoly n).eval x| ≤ (1 + 2 * Lw) / 2 := by
  have hL := halfWidth_pos
  have hpt : ∀ x ∈ Icc (-Lw) Lw, |(basisPoly n).eval x| ≤ ((basisPoly n).eval x * (basisPoly n).eval x + 1) / 2 :=
    fun x _ => by nlinarith [sq_nonneg (abs ((basisPoly n).eval x) - 1), sq_abs ((basisPoly n).eval x)]
  have h := intervalIntegral.integral_mono_on (a := -Lw) (b := Lw) (by linarith) (ii (by fun_prop)) (ii (by fun_prop)) hpt
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (ii (by fun_prop)) (ii (by fun_prop)), gram_i, intervalIntegral.integral_const, smul_eq_mul] at h
  simp at h
  linarith

theorem Rp_err (n k : ℕ) :
    |Rp n k - RpQ n k| ≤ 2 / 10 ^ 24 / 2 * (2 * Lw + ((1 + 2 * Lw) / 2) ^ 2) := by
  have hL := halfWidth_pos
  set ε : ℝ := 2 / 10 ^ 24 with hε
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  set Cn := ∫ y in (-Lw)..Lw, |(basisPoly n).eval y|
  -- interval forms
  have eRp : Rp n k = ∫ x in (-Lw)..Lw, (1/2:ℝ) * (∫ y in (-Lw)..Lw,
      Rk |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y)) * (basisPoly k).eval x := by
    unfold Rp; simp only [RHEntry00_0495.setI]
  have eQ : RpQ n k = ∫ x in (-Lw)..Lw, (1/2:ℝ) * (∫ y in (-Lw)..Lw,
      Qs |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y)) * (basisPoly k).eval x := by
    unfold RpQ; simp only [RHEntry00_0495.setI]
  have hQc : Continuous fun x => (1/2:ℝ) * (∫ y in (-Lw)..Lw,
      Qs |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y)) * (basisPoly k).eval x := by
    have : Continuous fun x => ∫ y in (-Lw)..Lw, Qs |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _
    fun_prop
  have hRi : IntervalIntegrable (fun x => (1/2:ℝ) * (∫ y in (-Lw)..Lw,
      Rk |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y)) * (basisPoly k).eval x) volume (-Lw) Lw := by
    have h := R_intOn n k
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    refine h.congr_fun (fun x _ => ?_) measurableSet_Icc
    simp only [RHEntry00_0495.setI]
  rw [eRp, eQ, ← intervalIntegral.integral_sub hRi (ii hQc)]
  have hD : ∀ x ∈ Icc (-Lw) Lw,
      (1/2:ℝ) * (∫ y in (-Lw)..Lw, Rk |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y)) * (basisPoly k).eval x -
      (1/2:ℝ) * (∫ y in (-Lw)..Lw, Qs |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y)) * (basisPoly k).eval x =
      (1/2:ℝ) * (∫ y in (-Lw)..Lw, (Rk |x - y| - Qs |x - y|) * ((basisPoly n).eval x - (basisPoly n).eval y)) *
        (basisPoly k).eval x := by
    intro x hx
    rw [← mul_sub_right_distrib, ← mul_sub, ← intervalIntegral.integral_sub (Rk_inner_ii n hx) (ii (by fun_prop))]
    congr 3; funext y; ring
  have hbnd : Continuous fun x => (1/2:ℝ) * (ε * (2 * Lw * |(basisPoly n).eval x| + Cn)) * |(basisPoly k).eval x| := by
    fun_prop
  have hle : |∫ x in (-Lw)..Lw, ((1/2:ℝ) * (∫ y in (-Lw)..Lw, Rk |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y)) *
      (basisPoly k).eval x - (1/2:ℝ) * (∫ y in (-Lw)..Lw, Qs |x - y| * ((basisPoly n).eval x - (basisPoly n).eval y)) *
      (basisPoly k).eval x)| ≤
      ∫ x in (-Lw)..Lw, (1/2:ℝ) * (ε * (2 * Lw * |(basisPoly n).eval x| + Cn)) * |(basisPoly k).eval x| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) (Filter.Eventually.of_forall (fun x hx => ?_)) (ii hbnd)
    have hxI : x ∈ Icc (-Lw) Lw := ⟨hx.1.le, hx.2⟩
    rw [hD x hxI, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact (inner_bound n hxI).trans (mul_le_mul_of_nonneg_left (inner_abs_le n x) hε0)
  have hmid : (∫ x in (-Lw)..Lw, (1/2:ℝ) * (ε * (2 * Lw * |(basisPoly n).eval x| + Cn)) * |(basisPoly k).eval x|) =
      (1/2:ℝ) * ε * (2 * Lw) * (∫ x in (-Lw)..Lw, |(basisPoly n).eval x| * |(basisPoly k).eval x|) +
      (1/2:ℝ) * ε * Cn * ∫ x in (-Lw)..Lw, |(basisPoly k).eval x| := by
    have e : (fun x => (1/2:ℝ) * (ε * (2 * Lw * |(basisPoly n).eval x| + Cn)) * |(basisPoly k).eval x|) =
        fun x => (1/2:ℝ) * ε * (2 * Lw) * (|(basisPoly n).eval x| * |(basisPoly k).eval x|) +
          (1/2:ℝ) * ε * Cn * |(basisPoly k).eval x| := by funext x; ring
    rw [e, intervalIntegral.integral_add (ii (by fun_prop)) (ii (by fun_prop)), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hmid] at hle
  refine hle.trans ?_
  have h1 := absprod_le n k
  have h2 := abs_le_C k
  have h3 : Cn ≤ (1 + 2 * Lw) / 2 := abs_le_C n
  have h4 : 0 ≤ Cn := intervalIntegral.integral_nonneg (by linarith) (fun y _ => abs_nonneg _)
  have h5 : 0 ≤ ∫ x in (-Lw)..Lw, |(basisPoly k).eval x| :=
    intervalIntegral.integral_nonneg (by linarith) (fun y _ => abs_nonneg _)
  have h6 : Cn * ∫ x in (-Lw)..Lw, |(basisPoly k).eval x| ≤ ((1 + 2 * Lw) / 2) ^ 2 := by
    rw [sq]; exact mul_le_mul h3 h2 h5 (by positivity)
  have h7 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ (1/2:ℝ) * ε * (2 * Lw))
  have h8 := mul_le_mul_of_nonneg_left h6 (by positivity : (0:ℝ) ≤ (1/2:ℝ) * ε)
  have : (1/2:ℝ) * ε * Cn * ∫ x in (-Lw)..Lw, |(basisPoly k).eval x| =
      (1/2:ℝ) * ε * (Cn * ∫ x in (-Lw)..Lw, |(basisPoly k).eval x|) := by ring
  rw [this]
  nlinarith

end RHRpErr0506

