import LowBlockB0494

/-! # 0495 T4 pilot, step 1: closed form of the even (0,0) low-block entry

`A0true false 0 0 = h0c + J/(4L) + 16 sinh(L/2)^2 / L − (1/L) Σ_{n<5} Λ(n)/√n (2L − log n)`,
`J = ∫_{[-L,L]} (T_tail(L-x) + T_tail(L+x)) dx`, `L = halfWidth`. Derived from
`RHLowBlock0494.targetQ_zp`. -/

open MeasureTheory Set
open scoped BigOperators

namespace RHEntry00_0495
open RHConditionalLog5 RHLog5Bridge RHLowBlock0494 RHTargetFormBinding

noncomputable abbrev Lw : ℝ := halfWidth
noncomputable def c0 : ℝ := Real.sqrt (1 / (2 * halfWidth))
noncomputable def p0 : Polynomial ℝ := basisPoly 0

lemma p0_eval (x : ℝ) : p0.eval x = c0 := by
  simp [p0, basisPoly, recPoly, c0]

lemma c0_sq : c0 ^ 2 = 1 / (2 * halfWidth) :=
  Real.sq_sqrt (by have := halfWidth_pos; positivity)

lemma two_L : 2 * halfWidth = Real.log 5 := by unfold halfWidth; ring

lemma int_cosh_ab (a b : ℝ) : ∫ x in a..b, Real.cosh x = Real.sinh b - Real.sinh a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => Real.hasDerivAt_sinh x)
    (Real.continuous_cosh.intervalIntegrable a b)

lemma int_sinh_ab (a b : ℝ) : ∫ x in a..b, Real.sinh x = Real.cosh b - Real.cosh a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => Real.hasDerivAt_cosh x)
    (Real.continuous_sinh.intervalIntegrable a b)

lemma setI (f : ℝ → ℝ) : ∫ x in Icc (-halfWidth) halfWidth, f x = ∫ x in (-halfWidth)..halfWidth, f x := by
  rw [intervalIntegral.integral_of_le (by linarith [halfWidth_pos]), integral_Icc_eq_integral_Ioc]

lemma entry_eq : A0true false 0 0 = targetQ_real (zp p0) := by
  rw [targetQ_zp]
  rfl

lemma int_sq : ∫ x, (zp p0 x) ^ 2 = c0 ^ 2 * (2 * halfWidth) := by
  have h : (fun x => (zp p0 x) ^ 2) = fun x => zp p0 x * zp p0 x := by funext x; ring
  rw [h, integral_mul_zp p0 (g := zp p0)]
  rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => c0 ^ 2) (fun x hx => by
    simp only [zp_of_mem p0 hx, p0_eval]; ring)]
  rw [setI, intervalIntegral.integral_const, smul_eq_mul]
  ring

noncomputable def J : ℝ := ∫ x in Icc (-halfWidth) halfWidth,
  (RH_Rebaseline.T_tail (halfWidth - x) + RH_Rebaseline.T_tail (halfWidth + x))

lemma spatial : RHAutocorrEnergy.spatialEnergy (zp p0) = c0 ^ 2 / 2 * J := by
  rw [spatialEnergy_zp, integral_mul_zp p0 (g := colArch p0)]
  unfold J
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _
  simp only [colArch, p0_eval, sub_self, mul_zero, integral_zero]
  ring

lemma int_cosh : ∫ x, zp p0 x * Real.cosh (x / 2) = c0 * (4 * Real.sinh (halfWidth / 2)) := by
  rw [show (fun x => zp p0 x * Real.cosh (x / 2)) = fun x => Real.cosh (x / 2) * zp p0 x by
    funext x; ring, integral_mul_zp p0 (g := fun x => Real.cosh (x / 2))]
  simp only [p0_eval]
  rw [integral_mul_const, setI, intervalIntegral.integral_comp_div (fun x => Real.cosh x) (by norm_num : (2:ℝ) ≠ 0),
    int_cosh_ab, smul_eq_mul, show -halfWidth / 2 = -(halfWidth / 2) by ring, Real.sinh_neg]
  ring

lemma int_sinh : ∫ x, zp p0 x * Real.sinh (x / 2) = 0 := by
  rw [show (fun x => zp p0 x * Real.sinh (x / 2)) = fun x => Real.sinh (x / 2) * zp p0 x by
    funext x; ring, integral_mul_zp p0 (g := fun x => Real.sinh (x / 2))]
  simp only [p0_eval]
  rw [integral_mul_const, setI, intervalIntegral.integral_comp_div (fun x => Real.sinh x) (by norm_num : (2:ℝ) ≠ 0),
    int_sinh_ab, show -halfWidth / 2 = -(halfWidth / 2) by ring, Real.cosh_neg]
  simp

lemma autocorr {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 2 * halfWidth) :
    RH_LiteratureBridge.real_autocorr (zp p0) a = c0 ^ 2 * (2 * halfWidth - a) := by
  unfold RH_LiteratureBridge.real_autocorr
  have h : (fun t => zp p0 t * zp p0 (t - a)) = (Icc (a - halfWidth) halfWidth).indicator (fun _ => c0 ^ 2) := by
    funext t
    by_cases h1 : t ∈ Icc (a - halfWidth) halfWidth
    · have ht : t ∈ Icc (-halfWidth) halfWidth := ⟨by linarith [h1.1], h1.2⟩
      have ht' : t - a ∈ Icc (-halfWidth) halfWidth := ⟨by linarith [h1.1], by linarith [h1.2]⟩
      rw [indicator_of_mem h1, zp_of_mem p0 ht, zp_of_mem p0 ht', p0_eval, p0_eval]; ring
    · rw [indicator_of_notMem h1]
      by_cases ht : t ∈ Icc (-halfWidth) halfWidth
      · have ht' : t - a ∉ Icc (-halfWidth) halfWidth := by
          intro h2; exact h1 ⟨by linarith [h2.1], ht.2⟩
        rw [zp_of_not_mem p0 ht', mul_zero]
      · rw [zp_of_not_mem p0 ht, zero_mul]
  rw [h, integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, Measure.real,
    Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  ring

lemma log_range {n : ℕ} (hn : n ∈ Finset.range 5) : 0 ≤ Real.log n ∧ Real.log n ≤ 2 * halfWidth := by
  rw [two_L]
  have hn5 : n < 5 := Finset.mem_range.mp hn
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp; exact Real.log_nonneg (by norm_num)
  · refine ⟨Real.log_nonneg (by exact_mod_cast hpos), Real.log_le_log (by exact_mod_cast hpos) ?_⟩
    exact_mod_cast hn5.le

theorem entry00_closed :
    A0true false 0 0 = h0c + J / (4 * halfWidth) + 16 * Real.sinh (halfWidth / 2) ^ 2 / halfWidth -
      (1 / halfWidth) * ∑ n ∈ Finset.range 5,
        ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) * (2 * halfWidth - Real.log n) := by
  have hL := halfWidth_pos
  rw [entry_eq]
  unfold targetQ_real
  rw [int_sq, spatial, int_cosh, int_sinh]
  have hsum : ∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
      RH_LiteratureBridge.real_autocorr (zp p0) (Real.log n) =
      c0 ^ 2 * ∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        (2 * halfWidth - Real.log n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [autocorr (log_range hn).1 (log_range hn).2]
    ring
  rw [hsum, show (c0 * (4 * Real.sinh (halfWidth / 2))) ^ 2 = c0 ^ 2 * (16 * Real.sinh (halfWidth / 2) ^ 2) by ring,
    c0_sq]
  unfold h0c
  generalize (∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
    (2 * halfWidth - Real.log n)) = S
  field_simp
  ring

end RHEntry00_0495

