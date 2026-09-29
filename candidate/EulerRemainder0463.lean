import HarmonicEM0462
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecificLimits.Basic

open Set intervalIntegral Filter
open scoped Topology
open RHHarmonicEM0462
namespace RHEulerRemainder0463

theorem integrand_bound (k : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖saw k x * derivativeTerm k x‖ ≤
      (sawBound k * (k.factorial : ℝ)) * x ^ (-1 - (k : ℤ)) := by
  have hp : 0 < x ^ (-1 - (k : ℤ)) := zpow_pos hx _
  simp only [derivativeTerm, norm_mul, Real.norm_eq_abs, abs_pow, abs_neg,
    abs_one, one_pow, one_mul, abs_of_nonneg (show (0 : ℝ) ≤ (k.factorial : ℝ) from Nat.cast_nonneg _), abs_of_pos hp]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (abs_saw_le k x) (show (0 : ℝ) ≤ (k.factorial : ℝ) from Nat.cast_nonneg _)) hp.le

theorem power_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) (hk : 0 < k) :
    (∫ x in a..b, x ^ (-1 - (k : ℤ))) =
      (a ^ (-(k : ℤ)) - b ^ (-(k : ℤ))) / k := by
  rw [integral_zpow (Or.inr ⟨by omega, notMem_uIcc_of_lt ha hb⟩)]
  have he : (-1 - (k : ℤ)) + 1 = -(k : ℤ) := by omega
  rw [he]
  push_cast
  ring

theorem remainder_bound (N n k : ℕ) (hN : 0 < N) (hk : 0 < k) :
    |∫ x in (N : ℝ)..N+n, saw k x * derivativeTerm k x| ≤
      (sawBound k * (k.factorial : ℝ)) / k * (N : ℝ) ^ (-(k : ℤ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < N+n := add_pos_of_pos_of_nonneg hNr (Nat.cast_nonneg n)
  have hab : (N : ℝ) ≤ N+n := le_add_of_nonneg_right (Nat.cast_nonneg n)
  have hi : IntervalIntegrable (fun x : ℝ => x ^ (-1 - (k : ℤ))) MeasureTheory.volume N (N+n) :=
    intervalIntegrable_zpow (Or.inr (notMem_uIcc_of_lt hNr hMr))
  have hb := intervalIntegral.norm_integral_le_of_norm_le (f := fun x => saw k x * derivativeTerm k x)
    hab (Filter.Eventually.of_forall (fun x hx => integrand_bound k (lt_trans hNr hx.1)))
    (hi.const_mul (sawBound k * (k.factorial : ℝ)))
  rw [Real.norm_eq_abs, integral_const_mul, power_integral hNr hMr k hk] at hb
  apply hb.trans
  have hc : 0 ≤ (sawBound k * (k.factorial : ℝ)) / k :=
    div_nonneg (mul_nonneg sawBound_nonneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hp : 0 ≤ (N+n : ℝ) ^ (-(k : ℤ)) := (zpow_pos hMr _).le
  calc
    _ = ((sawBound k * (k.factorial : ℝ)) / k) *
        ((N : ℝ) ^ (-(k : ℤ)) - (N+n : ℝ) ^ (-(k : ℤ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sub_le_self _ hp) hc

theorem tendsto_derivativeTerm (k : ℕ) :
    Tendsto (fun n : ℕ => derivativeTerm k n) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_nhds_zero_nat
  have he : -1 - (k : ℤ) = -((k+1 : ℕ) : ℤ) := by omega
  simp only [derivativeTerm, he, zpow_neg, zpow_natCast, ← inv_pow]
  simpa only [zero_pow (Nat.succ_ne_zero k), mul_zero] using
    (hi.pow (k+1)).const_mul ((-1 : ℝ)^k * (k.factorial : ℝ))

theorem tendsto_boundaryCorrection (s : ℕ) :
    Tendsto (fun n : ℕ => boundaryCorrection s n) atTop (𝓝 0) := by
  convert tendsto_finsetSum (Finset.range s) (fun j _ =>
    (tendsto_derivativeTerm (j+1)).const_mul ((-1 : ℝ)^j * saw (j+2) 0)) using 1 <;>
    simp [boundaryCorrection]

theorem tendsto_corrected (s : ℕ) :
    Tendsto (fun n : ℕ => corrected n s) atTop (𝓝 Real.eulerMascheroniConstant) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_nhds_zero_nat
  simpa [corrected, div_eq_mul_inv] using
    (Real.tendsto_harmonic_sub_log.sub (hi.const_mul (1/2 : ℝ))).sub
      (tendsto_boundaryCorrection s)

theorem corrected_difference_bound (N n s : ℕ) (hN : 0 < N) :
    |corrected (N+n) s - corrected N s| ≤
      (sawBound (s+1) * ((s+1).factorial : ℝ)) / (s+1 : ℕ) *
      (N : ℝ) ^ (-((s+1 : ℕ) : ℤ)) := by
  rw [corrected_difference N n s hN]
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact remainder_bound N n (s+1) hN (Nat.succ_pos s)

/-- No finite error bound is assumed: it is supplied by the EM remainder estimate. -/
theorem euler_error_bound (N s : ℕ) (hN : 0 < N) :
    |Real.eulerMascheroniConstant - corrected N s| ≤
      (sawBound (s+1) * ((s+1).factorial : ℝ)) / (s+1 : ℕ) *
      (N : ℝ) ^ (-((s+1 : ℕ) : ℤ)) := by
  apply le_of_tendsto ((tendsto_corrected s).sub_const (corrected N s)).abs
  apply eventually_atTop.2
  refine ⟨N, fun n hn => ?_⟩
  simpa only [Nat.add_sub_of_le hn] using corrected_difference_bound N (n-N) s hN

theorem euler_coarse_enclosure :
    (1/2 : ℝ) ≤ Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant ≤ (2/3 : ℝ) := by
  have h := euler_error_bound 1 1 (by norm_num)
  have he : Even (2 : ℕ) := by decide
  norm_num [corrected, boundaryCorrection, derivativeTerm, Finset.sum_range_succ,
    saw_eval_zero, bernoulli_two, harmonic_succ, sawBound,
    bernoulliBound_eq_abs_bernoulli' 2 he] at h
  constructor <;> linarith [abs_le.mp h]


/-- Even-order Bernoulli remainder with no unknown saw maximum left in the bound. -/
theorem euler_error_bound_even (N s : ℕ) (hN : 0 < N) (he : Even (s+1)) :
    |Real.eulerMascheroniConstant - corrected N s| ≤
      |(bernoulli (s+1) : ℝ)| / (s+1 : ℕ) * (N : ℝ) ^ (-((s+1 : ℕ) : ℤ)) := by
  have hc : sawBound (s+1) * ((s+1).factorial : ℝ) = |(bernoulli (s+1) : ℝ)| := by
    rw [sawBound, bernoulliBound_eq_abs_bernoulli' _ he]
    have hf : ((s+1).factorial : ℝ) ≠ 0 := by positivity
    simp only [Rat.cast_abs]
    field_simp
  simpa only [hc] using euler_error_bound N s hN

end RHEulerRemainder0463


