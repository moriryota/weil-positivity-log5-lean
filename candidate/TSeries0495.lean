import Entry00_0495

/-! # 0495 T4 pilot, step 2: exact series for `T_tail` and for `J`

* `T_tail b = ∑' m, 4 exp(-(4m+1) b/2)/(4m+1)` for `b > 0`
  (artanh and arctan series; odd indices cancel).
* `J = 16 ∑' m, (1 - exp(-(4m+1) L))/(4m+1)^2`, `L = halfWidth` (term-wise integration of a
  nonnegative series). -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RHTSeries0495
open RHLog5Bridge

/-- Odd-index-cancelling combination of the artanh and arctan series. -/
lemma hasSum_T_tail_aux {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasSum (fun k : ℕ => 2 * ((1 + (-1) ^ k) * z ^ (2 * k + 1) / (2 * k + 1)))
      (2 * (Real.artanh z + Real.arctan z)) := by
  have habs : |z| < 1 := by rw [abs_of_nonneg hz0]; exact hz1
  have hl := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have ha := Real.hasSum_arctan (x := z) (by rw [Real.norm_eq_abs]; exact habs)
  have hart : Real.artanh z = (1/2) * (Real.log (1 + z) - Real.log (1 - z)) := by
    rw [Real.artanh_eq_half_log ⟨by linarith, hz1.le⟩, Real.log_div (by linarith) (by linarith)]
  have h := ((hl.mul_left (1/2)).add ha).mul_left 2
  rw [hart]
  convert h using 1
  funext k
  push_cast
  ring

lemma T_tail_hasSum {b : ℝ} (hb : 0 < b) :
    HasSum (fun m : ℕ => 4 * Real.exp (-((4 * m + 1 : ℝ) * b / 2)) / (4 * m + 1))
      (RH_Rebaseline.T_tail b) := by
  set z := Real.exp (-b / 2) with hz
  have hz0 : 0 ≤ z := (Real.exp_pos _).le
  have hz1 : z < 1 := by
    rw [hz, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h := hasSum_T_tail_aux hz0 hz1
  unfold RH_Rebaseline.T_tail
  rw [← hz]
  have hzero : ∀ k ∉ Set.range (fun m : ℕ => 2 * m),
      (2 * ((1 + (-1 : ℝ) ^ k) * z ^ (2 * k + 1) / (2 * k + 1))) = 0 := by
    intro k hk
    have hodd : Odd k := by
      rcases Nat.even_or_odd k with he | ho
      · obtain ⟨r, hr⟩ := he
        exact absurd ⟨r, show 2 * r = k by omega⟩ hk
      · exact ho
    rw [hodd.neg_one_pow]; ring
  have h2 := (Function.Injective.hasSum_iff (f := fun k : ℕ =>
      2 * ((1 + (-1 : ℝ) ^ k) * z ^ (2 * k + 1) / (2 * k + 1)))
    (fun a b hab => by simpa using hab) hzero).mpr h
  convert h2 using 1
  funext m
  simp only [Function.comp, pow_mul, neg_one_sq, one_pow]
  rw [hz, ← Real.exp_nat_mul]
  push_cast
  ring_nf


/-- Term of the series for `T_tail(L-x) + T_tail(L+x)`. -/
noncomputable def g (m : ℕ) (x : ℝ) : ℝ :=
  4 * Real.exp (-((4 * m + 1 : ℝ) * (halfWidth - x) / 2)) / (4 * m + 1) +
  4 * Real.exp (-((4 * m + 1 : ℝ) * (halfWidth + x) / 2)) / (4 * m + 1)

lemma g_nonneg (m : ℕ) (x : ℝ) : 0 ≤ g m x := by unfold g; positivity

lemma g_continuous (m : ℕ) : Continuous (g m) := by unfold g; fun_prop

lemma pair_hasSum {x : ℝ} (hx : x ∈ Ioo (-halfWidth) halfWidth) :
    HasSum (fun m => g m x) (RH_Rebaseline.T_tail (halfWidth - x) + RH_Rebaseline.T_tail (halfWidth + x)) :=
  (T_tail_hasSum (by linarith [hx.2])).add (T_tail_hasSum (by linarith [hx.1]))

lemma exp_int (c a b : ℝ) (hc : c ≠ 0) :
    ∫ x in a..b, Real.exp (c * x) = (Real.exp (c * b) - Real.exp (c * a)) / c := by
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun x => Real.exp (c * x) / c) (Real.exp (c * x)) x := by
    intro x _
    have h := ((Real.hasDerivAt_exp (c * x)).comp x ((hasDerivAt_id x).const_mul c)).div_const c
    convert h using 1 <;> first | rfl | field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable a b)]
  ring

lemma g_integral (m : ℕ) :
    ∫ x in Icc (-halfWidth) halfWidth, g m x =
      16 * (1 - Real.exp (-((4 * m + 1 : ℝ) * halfWidth))) / (4 * m + 1) ^ 2 := by
  have hc : (4 * m + 1 : ℝ) ≠ 0 := by positivity
  have hc2 : ((4 * m + 1 : ℝ) / 2) ≠ 0 := by positivity
  set a : ℝ := (4 * m + 1 : ℝ) * halfWidth / 2 with ha
  have e1 : ∀ x : ℝ, Real.exp (-((4 * m + 1 : ℝ) * (halfWidth - x) / 2)) =
      Real.exp (-a) * Real.exp ((4 * m + 1 : ℝ) / 2 * x) := by
    intro x; rw [← Real.exp_add]; congr 1; rw [ha]; ring
  have e2 : ∀ x : ℝ, Real.exp (-((4 * m + 1 : ℝ) * (halfWidth + x) / 2)) =
      Real.exp (-a) * Real.exp (-((4 * m + 1 : ℝ) / 2) * x) := by
    intro x; rw [← Real.exp_add]; congr 1; rw [ha]; ring
  rw [RHEntry00_0495.setI]
  unfold g
  simp only [e1, e2]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    exp_int _ _ _ hc2, exp_int _ _ _ (neg_ne_zero.mpr hc2)]
  · have h1 : Real.exp ((4 * m + 1 : ℝ) / 2 * halfWidth) = Real.exp a := by congr 1; rw [ha]; ring
    have h2 : Real.exp ((4 * m + 1 : ℝ) / 2 * -halfWidth) = Real.exp (-a) := by congr 1; rw [ha]; ring
    have h3 : Real.exp (-((4 * m + 1 : ℝ) / 2) * halfWidth) = Real.exp (-a) := by congr 1; rw [ha]; ring
    have h4 : Real.exp (-((4 * m + 1 : ℝ) / 2) * -halfWidth) = Real.exp a := by congr 1; rw [ha]; ring
    have h5 : Real.exp (-((4 * m + 1 : ℝ) * halfWidth)) = Real.exp (-a) * Real.exp (-a) := by
      rw [← Real.exp_add]; congr 1; rw [ha]; ring
    have hF : Real.exp a = (Real.exp (-a))⁻¹ := by rw [Real.exp_neg, inv_inv]
    have hE : Real.exp (-a) ≠ 0 := (Real.exp_pos _).ne'
    rw [h1, h2, h3, h4, h5, hF]
    field_simp
    ring
  all_goals
    first
    | exact (by fun_prop : Continuous _).intervalIntegrable _ _

lemma v_summable :
    Summable (fun m : ℕ => 16 * (1 - Real.exp (-((4 * m + 1 : ℝ) * halfWidth))) / (4 * m + 1) ^ 2) := by
  have hbase : Summable (fun m : ℕ => 16 * (1 / ((m + 1 : ℕ) : ℝ) ^ 2)) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))).mul_left 16
  refine hbase.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
  · have : Real.exp (-((4 * m + 1 : ℝ) * halfWidth)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := halfWidth_pos; nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
    have : (0:ℝ) < (4 * m + 1) ^ 2 := by positivity
    exact div_nonneg (by nlinarith) this.le
  · have hle : 1 - Real.exp (-((4 * m + 1 : ℝ) * halfWidth)) ≤ 1 := by
      have := Real.exp_pos (-((4 * m + 1 : ℝ) * halfWidth)); linarith
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    have hpos : (0:ℝ) < ((m:ℝ) + 1) ^ 2 := by positivity
    calc 16 * (1 - Real.exp (-((4 * m + 1 : ℝ) * halfWidth))) / (4 * m + 1) ^ 2
        ≤ 16 * 1 / (4 * m + 1) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity); linarith
      _ ≤ 16 * (1 / ((m:ℝ) + 1) ^ 2) := by
          rw [mul_one_div, mul_one]; apply div_le_div_of_nonneg_left (by norm_num) hpos; nlinarith

theorem J_series :
    RHEntry00_0495.J = ∑' m : ℕ, 16 * (1 - Real.exp (-((4 * m + 1 : ℝ) * halfWidth))) / (4 * m + 1) ^ 2 := by
  have hae : ∀ᵐ x ∂volume, x ∈ Icc (-halfWidth) halfWidth →
      RH_Rebaseline.T_tail (halfWidth - x) + RH_Rebaseline.T_tail (halfWidth + x) = ∑' m, g m x := by
    filter_upwards [Measure.ae_ne volume halfWidth, Measure.ae_ne volume (-halfWidth)] with x h1 h2 hx
    exact ((pair_hasSum ⟨lt_of_le_of_ne hx.1 (Ne.symm h2), lt_of_le_of_ne hx.2 h1⟩).tsum_eq).symm
  unfold RHEntry00_0495.J
  rw [setIntegral_congr_ae measurableSet_Icc hae]
  rw [integral_tsum (fun m => (g_continuous m).aestronglyMeasurable)]
  · exact tsum_congr (fun m => g_integral m)
  · have hlin : ∀ m, ∫⁻ x in Icc (-halfWidth) halfWidth, ‖g m x‖ₑ =
        ENNReal.ofReal (16 * (1 - Real.exp (-((4 * m + 1 : ℝ) * halfWidth))) / (4 * m + 1) ^ 2) := by
      intro m
      rw [← g_integral m, ofReal_integral_eq_lintegral_ofReal
        ((g_continuous m).integrableOn_Icc) (Filter.Eventually.of_forall (g_nonneg m))]
      congr 1; funext x; exact Real.enorm_of_nonneg (g_nonneg m x)
    simp_rw [hlin]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => ?_) v_summable]
    · exact ENNReal.ofReal_ne_top
    · rw [← g_integral m]; exact setIntegral_nonneg measurableSet_Icc (fun x _ => g_nonneg m x)

end RHTSeries0495

