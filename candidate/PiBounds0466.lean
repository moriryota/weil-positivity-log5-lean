import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecificLimits.Normed
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-! # 0466: rational enclosure of `Real.pi` of width ≤ 10^-100

Machin's formula (Mathlib `Real.four_mul_arctan_inv_5_sub_arctan_inv_239`) together with the
alternating-series bounds (Mathlib `Antitone.alternating_series_le_tendsto`,
`Antitone.tendsto_le_alternating_series`) applied to the arctan power series
(Mathlib `Real.hasSum_arctan`). The finite rational comparisons are checked by `decide +kernel`. -/

open Filter Topology Finset

namespace RHPi0466

/-- Rational partial sum `∑_{i<n} (-1)^i x^(2i+1)/(2i+1)` of the arctan series. -/
def atanSum (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => atanSum x n + (-1) ^ n * x ^ (2 * n + 1) / (2 * n + 1)

theorem atanSum_cast (x : ℚ) (n : ℕ) :
    (atanSum x n : ℝ) = ∑ i ∈ range n, (-1 : ℝ) ^ i * ((x : ℝ) ^ (2 * i + 1) / (2 * i + 1)) := by
  induction n with
  | zero => simp [atanSum]
  | succ n ih =>
    rw [sum_range_succ, ← ih, atanSum]
    push_cast
    ring

/-- Alternating-series enclosure of `arctan x` for rational `0 ≤ x < 1`. -/
theorem arctan_bounds (x : ℚ) (h0 : 0 ≤ x) (h1 : x < 1) (k : ℕ) :
    (atanSum x (2 * k) : ℝ) ≤ Real.arctan x ∧ Real.arctan x ≤ (atanSum x (2 * k + 1) : ℝ) := by
  have h0' : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have h1' : (x : ℝ) < 1 := by exact_mod_cast h1
  set f : ℕ → ℝ := fun i => (x : ℝ) ^ (2 * i + 1) / (2 * i + 1) with hf
  have hs := Real.hasSum_arctan (x := (x : ℝ)) (by rw [Real.norm_eq_abs, abs_of_nonneg h0']; exact h1')
  have ht : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * f i) atTop
      (𝓝 (Real.arctan x)) := by
    have := hs.tendsto_sum_nat
    refine this.congr (fun n => sum_congr rfl (fun i _ => ?_))
    simp only [hf]
    push_cast
    ring
  have hanti : Antitone f := by
    refine antitone_nat_of_succ_le (fun n => ?_)
    simp only [hf]
    apply div_le_div₀ (by positivity)
    · exact pow_le_pow_of_le_one h0' h1'.le (by omega)
    · positivity
    · push_cast; linarith
  constructor
  · rw [atanSum_cast]; exact Antitone.alternating_series_le_tendsto ht hanti k
  · rw [atanSum_cast]; exact Antitone.tendsto_le_alternating_series ht hanti k

theorem pi_eq_machin :
    Real.pi = 16 * Real.arctan ((1 / 5 : ℚ) : ℝ) - 4 * Real.arctan ((1 / 239 : ℚ) : ℝ) := by
  have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  push_cast
  rw [one_div, one_div]
  linarith

def piLo : ℚ := 3141592653589793238462643383279502884197169399375105820974944592307816406286208998628034825342117067982147/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def piHi : ℚ := 3141592653589793238462643383279502884197169399375105820974944592307816406286208998628034825342117067982149/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

theorem machin_lower_check :
    piLo ≤ 16 * atanSum (1 / 5) (2 * 37) - 4 * atanSum (1 / 239) (2 * 11 + 1) := by
  decide +kernel

theorem machin_upper_check :
    16 * atanSum (1 / 5) (2 * 37 + 1) - 4 * atanSum (1 / 239) (2 * 11) ≤ piHi := by
  decide +kernel

theorem pi_bounds : (piLo : ℝ) ≤ Real.pi ∧ Real.pi ≤ (piHi : ℝ) := by
  obtain ⟨a1, a2⟩ := arctan_bounds (1 / 5) (by norm_num) (by norm_num) 37
  obtain ⟨b1, b2⟩ := arctan_bounds (1 / 239) (by norm_num) (by norm_num) 11
  have hl : ((piLo : ℚ) : ℝ) ≤ ((16 * atanSum (1 / 5) (2 * 37) -
      4 * atanSum (1 / 239) (2 * 11 + 1) : ℚ) : ℝ) := by exact_mod_cast machin_lower_check
  have hu : ((16 * atanSum (1 / 5) (2 * 37 + 1) - 4 * atanSum (1 / 239) (2 * 11) : ℚ) : ℝ)
      ≤ ((piHi : ℚ) : ℝ) := by exact_mod_cast machin_upper_check
  push_cast at hl hu
  rw [pi_eq_machin]
  constructor <;> linarith

theorem pi_lo_pos : 0 < piLo := by decide +kernel

theorem pi_width : piHi - piLo ≤ (1 : ℚ) / 10 ^ 100 := by decide +kernel

end RHPi0466

