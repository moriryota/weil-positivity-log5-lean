import Interface0516

open MeasureTheory Set
open scoped BigOperators
namespace RHSmoothIdentity0520
open RHConditionalLog5 RHLog5Bridge RHLowBlock0494 RHColDecomp0499

lemma basis_eval (n : ℕ) (x : ℝ) :
    (basisPoly n).eval x = RHRpExact0506.cc n * RHLeg0503.p n (x / halfWidth) :=
  RHLink0505.basisPoly_eval n x

lemma shift_minus (n : ℕ) {s x : ℝ} (hs : 0 ≤ s) (hx : |x| < halfWidth)
    (hne : x ≠ s - halfWidth) :
    zp (basisPoly n) (x-s) = RHRpExact0506.cc n *
      RHSingDef0516.pm n (s/halfWidth) (x/halfWidth) := by
  have hL := halfWidth_pos
  obtain ⟨hx1,hx2⟩ := abs_lt.mp hx
  have he : s/halfWidth - 1 < x/halfWidth ↔ s-halfWidth < x := by
    rw [div_sub_one hL.ne', div_lt_div_iff_of_pos_right hL]
  unfold RHSingDef0516.pm
  by_cases hh : s-halfWidth < x
  · rw [if_pos (he.mpr hh), zp_of_mem _ ⟨by linarith, by linarith⟩, basis_eval]
    rw [sub_div]
  · rw [if_neg (fun h => hh (he.mp h)), zp_of_not_mem, mul_zero]
    intro h
    apply hne
    have := h.1
    linarith

lemma shift_plus (n : ℕ) {s x : ℝ} (hs : 0 ≤ s) (hx : |x| < halfWidth) :
    zp (basisPoly n) (x+s) = RHRpExact0506.cc n *
      RHSingDef0516.pp n (s/halfWidth) (x/halfWidth) := by
  have hL := halfWidth_pos
  obtain ⟨hx1,hx2⟩ := abs_lt.mp hx
  have he : x/halfWidth ≤ 1-s/halfWidth ↔ x ≤ halfWidth-s := by
    rw [one_sub_div hL.ne', div_le_div_iff_of_pos_right hL]
  unfold RHSingDef0516.pp
  by_cases hh : x ≤ halfWidth-s
  · rw [if_pos (he.mpr hh), zp_of_mem _ ⟨by linarith, by linarith⟩, basis_eval]
    rw [add_div]
  · rw [if_neg (fun h => hh (he.mp h)), zp_of_not_mem, mul_zero]
    intro h
    exact hh (by linarith [h.2])

lemma prime_eq (n : ℕ) {x : ℝ} (hx : |x| < halfWidth)
    (h2 : x ≠ Real.log 2-halfWidth) (h3 : x ≠ Real.log 3-halfWidth)
    (h4 : x ≠ Real.log 4-halfWidth) :
    primeTerm (basisPoly n) x = RHRpExact0506.cc n * RHSingDef0516.pr n (x/halfWidth) := by
  unfold primeTerm
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  rw [RHStepA1G1.vm_zero, RHStepA1G1.vm_one, RHStepA1G1.vm_two,
    RHStepA1G1.vm_three, RHStepA1G1.vm_four]
  simp only [zero_div, zero_mul, zero_add]
  rw [shift_minus n (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)) hx h2,
    shift_minus n (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)) hx h3,
    shift_minus n (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)) hx h4,
    shift_plus n (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)) hx,
    shift_plus n (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)) hx,
    shift_plus n (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)) hx]
  have hsqrt : Real.sqrt (4:ℝ) = 2 := by norm_num
  rw [hsqrt]
  unfold RHSingDef0516.pr RHSingDef0516.σ RHPrSum0511.w2 RHPrSum0511.w3 RHPrSum0511.w4
  norm_num only [Nat.cast_ofNat]
  ring

lemma log_identity {x : ℝ} (hx : |x| < halfWidth) :
    RHSingDef0516.lg (x/halfWidth) =
      Real.log (halfWidth-x) + Real.log (halfWidth+x) - 2*Real.log halfWidth := by
  have hL := halfWidth_pos
  obtain ⟨hx1,hx2⟩ := abs_lt.mp hx
  have hu1 : -1 < x/halfWidth := (lt_div_iff₀ hL).mpr (by linarith)
  have hu2 : x/halfWidth < 1 := (div_lt_iff₀ hL).mpr (by linarith)
  rw [RHSingDef0516.lg_eq hu1 hu2]
  have hp : 1+x/halfWidth = (halfWidth+x)/halfWidth := by field_simp [hL.ne']
  have hm : 1-x/halfWidth = (halfWidth-x)/halfWidth := by field_simp [hL.ne']
  rw [hp, hm, Real.log_div (by linarith) hL.ne', Real.log_div (by linarith) hL.ne']
  ring

noncomputable def smooth (n : ℕ) (x : ℝ) : ℝ :=
  (h0c + (harmonic n : ℝ) - Real.log halfWidth) * (basisPoly n).eval x +
  (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth,
    Rk |x-y| * ((basisPoly n).eval x - (basisPoly n).eval y)) +
  (1/2:ℝ) * ((RH_Rebaseline.T_tail (halfWidth-x) + Real.log (halfWidth-x)) +
    (RH_Rebaseline.T_tail (halfWidth+x) + Real.log (halfWidth+x))) * (basisPoly n).eval x +
  2 * Cc n * Real.cosh (x/2) - 2 * Ss n * Real.sinh (x/2)

lemma column_add_Sx_eq (n : ℕ) {x : ℝ} (hx : |x| < halfWidth)
    (h2 : x ≠ Real.log 2-halfWidth) (h3 : x ≠ Real.log 3-halfWidth)
    (h4 : x ≠ Real.log 4-halfWidth) :
    RHWeilColumnCandidate.column halfWidth (basisPoly n) x + RHInterface0516.Sx n x = smooth n x := by
  rw [column_eq_colFull _ hx]
  simp only [colFull, colArch]
  rw [kernel_split n (abs_le.mp hx.le), prime_eq n hx h2 h3 h4]
  simp only [RHInterface0516.Sx, if_pos hx, RHSingDef0516.phi]
  rw [log_identity hx]
  unfold smooth Cc Ss
  rw [basis_eval n x]
  ring

/-- Exact smooth part of the actual column, away from three null boundary points. -/
theorem column_add_Sx_ae (n : ℕ) :
    ∀ᵐ x ∂(volume : Measure ℝ), |x| < halfWidth →
      RHWeilColumnCandidate.column halfWidth (basisPoly n) x + RHInterface0516.Sx n x = smooth n x := by
  filter_upwards [Measure.ae_ne volume (Real.log 2-halfWidth),
    Measure.ae_ne volume (Real.log 3-halfWidth), Measure.ae_ne volume (Real.log 4-halfWidth)] with x h2 h3 h4 hx
  exact column_add_Sx_eq n hx h2 h3 h4

end RHSmoothIdentity0520
