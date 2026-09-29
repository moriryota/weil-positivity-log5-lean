import S1Numeric0495
import TSeries0495

/-! # 0495 step 3c: bounds for `J = 16 (S1 − r T)`, `r = exp(−L) = 5^(−1/2)`, `T = ∑ 25^(−m)/(4m+1)^2`
 -/

open Filter
open scoped BigOperators Topology

namespace RHJBounds0495
open RHLog5Bridge

noncomputable def r : ℝ := Real.exp (-halfWidth)

lemma r_pos : 0 < r := Real.exp_pos _

lemma r_sq : r ^ 2 = 1 / 5 := by
  unfold r
  rw [← Real.exp_nat_mul, show ((2:ℕ):ℝ) * -halfWidth = -Real.log 5 by unfold halfWidth; push_cast; ring,
    Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

def rLo : ℚ := 25840354427429161536 / 57780789062419261441
def rHi : ℚ := 109461497917277584513 / 244763350261984330562

lemma rLo_check : 0 ≤ rLo ∧ rLo ^ 2 ≤ 1 / 5 := by decide +kernel
lemma rHi_check : 0 ≤ rHi ∧ 1 / 5 ≤ rHi ^ 2 := by decide +kernel

theorem r_bounds : (rLo : ℝ) ≤ r ∧ r ≤ (rHi : ℝ) := by
  have h2 := r_sq
  have hl : (rLo : ℝ) ^ 2 ≤ 1 / 5 := by
    have := (Rat.cast_le (K := ℝ)).mpr rLo_check.2; push_cast at this; exact this
  have hh : (1 / 5 : ℝ) ≤ (rHi : ℝ) ^ 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr rHi_check.2; push_cast at this; exact this
  have hh0 : (0 : ℝ) ≤ rHi := by exact_mod_cast rHi_check.1
  constructor
  · by_contra h
    have := pow_lt_pow_left₀ (not_le.mp h) r_pos.le (by norm_num : (2 : ℕ) ≠ 0)
    linarith
  · by_contra h
    have := pow_lt_pow_left₀ (not_le.mp h) hh0 (by norm_num : (2 : ℕ) ≠ 0)
    linarith

lemma exp_term (m : ℕ) : Real.exp (-((4 * m + 1 : ℝ) * halfWidth)) = r * (1 / 25) ^ m := by
  have h4 : r ^ 4 = 1 / 25 := by rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, r_sq]; norm_num
  rw [← h4, ← pow_mul, ← pow_succ']
  unfold r
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `T = ∑ 25^(−m)/(4m+1)^2`. -/
noncomputable def tT (m : ℕ) : ℝ := (1 / 25 : ℝ) ^ m / (4 * m + 1) ^ 2

lemma tT_nonneg (m : ℕ) : 0 ≤ tT m := by unfold tT; positivity

lemma tT_le (m : ℕ) : tT m ≤ (1 / 25 : ℝ) ^ m := by
  unfold tT
  apply div_le_self (by positivity)
  have : (0:ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

lemma geo_summable : Summable (fun m : ℕ => (1 / 25 : ℝ) ^ m) :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

lemma tT_summable : Summable tT := geo_summable.of_nonneg_of_le tT_nonneg tT_le

noncomputable def T : ℝ := ∑' m, tT m

def TM : ℚ := 8621790604771625822769181768746252090974636837970577278196648244 / 8607844683695985381922654147254029303803690709173679351806640625
def Ttail : ℚ := 1 / 8731149137020111083984375000

lemma TM_eq : (∑ m ∈ Finset.range 20, tT m) = (TM : ℝ) := by
  simp only [tT, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [TM]

theorem T_bounds : (TM : ℝ) ≤ T ∧ T ≤ (TM : ℝ) + (Ttail : ℝ) := by
  have hsplit := (tT_summable.sum_add_tsum_nat_add 20).symm
  unfold T
  rw [hsplit, TM_eq]
  have hts : Summable (fun m => tT (m + 20)) := (summable_nat_add_iff 20).mpr tT_summable
  have h0 : 0 ≤ ∑' m, tT (m + 20) := tsum_nonneg (fun m => tT_nonneg _)
  have h1 : ∑' m, tT (m + 20) ≤ ∑' m, (1 / 25 : ℝ) ^ 20 * (1 / 25 : ℝ) ^ m := by
    apply hts.tsum_le_tsum _ (geo_summable.mul_left _)
    intro m
    rw [← pow_add, add_comm]
    exact tT_le _
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h1
  have h2 : (1 / 25 : ℝ) ^ 20 * (1 - 1 / 25)⁻¹ = (Ttail : ℝ) := by norm_num [Ttail]
  constructor <;> linarith

/-- `J = 16 (S1 − r T)`. -/
theorem J_eq : RHEntry00_0495.J = 16 * (RHHurwitzEM0495.S1 - r * T) := by
  rw [RHTSeries0495.J_series]
  have hf : ∀ m : ℕ, RHHurwitzEM0495.f m = 1 / (4 * m + 1) ^ 2 := by
    intro m; simp [RHHurwitzEM0495.f, zpow_neg, one_div]
  have hs1 : Summable (fun m : ℕ => (1 : ℝ) / (4 * m + 1) ^ 2) := by
    simpa [hf] using RHHurwitzEM0495.f_summable
  have hs2 : Summable (fun m : ℕ => r * tT m) := tT_summable.mul_left r
  have hterm : ∀ m : ℕ, 16 * (1 - Real.exp (-((4 * m + 1 : ℝ) * halfWidth))) / (4 * m + 1) ^ 2 =
      16 * (1 / (4 * m + 1) ^ 2 - r * tT m) := by
    intro m; rw [exp_term]; unfold tT; ring
  simp_rw [hterm]
  rw [tsum_mul_left, hs1.tsum_sub hs2, tsum_mul_left]
  unfold RHHurwitzEM0495.S1 T
  simp_rw [hf]

end RHJBounds0495

