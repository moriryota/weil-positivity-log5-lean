import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Set
namespace RHChainGeometry

theorem log5_geometry :
    0 < Real.log 2 ∧ 2*Real.log 2 < Real.log 5 ∧ Real.log 5 < 3*Real.log 2 ∧
    Real.log 5 < Real.log 2+Real.log 3 ∧ Real.log 3 < 2*Real.log 2 ∧
    Real.log 5 < 2*Real.log 3 := by
  have h4 : Real.log 4 = 2*Real.log 2 := by simpa only [show (2:ℝ)^2=4 by norm_num, Nat.cast_ofNat] using Real.log_pow 2 2
  have h8 : Real.log 8 = 3*Real.log 2 := by simpa only [show (2:ℝ)^3=8 by norm_num, Nat.cast_ofNat] using Real.log_pow 2 3
  have h9 : Real.log 9 = 2*Real.log 3 := by simpa only [show (3:ℝ)^2=9 by norm_num, Nat.cast_ofNat] using Real.log_pow 3 2
  have h6 : Real.log 6 = Real.log 2+Real.log 3 := by
    simpa only [show (2:ℝ)*3=6 by norm_num] using Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)
  refine ⟨Real.log_pos (by norm_num), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h4]; exact Real.log_lt_log (by norm_num) (by norm_num)
  · rw [← h8]; exact Real.log_lt_log (by norm_num) (by norm_num)
  · rw [← h6]; exact Real.log_lt_log (by norm_num) (by norm_num)
  · rw [← h4]; exact Real.log_lt_log (by norm_num) (by norm_num)
  · rw [← h9]; exact Real.log_lt_log (by norm_num) (by norm_num)

theorem middle_in_gap {L a b t : ℝ} (hW : 2*L<a+b)
    (ht : t ∈ Ico (-L) (L-2*a)) : t+a ∈ Ioo (L-b) (-L+b) := by
  rcases ht with ⟨hl,hu⟩
  constructor <;> linarith

theorem outside_gap {L a b t : ℝ} (hab : b<2*a)
    (ht : t ∈ Ico (-L) (L-2*a)) :
    t ∉ Ioo (L-b) (-L+b) ∧ t+2*a ∉ Ioo (L-b) (-L+b) := by
  rcases ht with ⟨hl,hu⟩
  constructor
  · intro h; rcases h with ⟨h1,h2⟩; linarith
  · intro h; rcases h with ⟨h1,h2⟩; linarith
end RHChainGeometry
