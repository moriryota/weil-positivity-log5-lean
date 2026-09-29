import G2Final0489
import ColL2Components
import OutsideIntegral

/-! # 0494 T1 step A: Riesz representation of `targetQ_real` on one zero-extended polynomial

For a real polynomial `p` and `zp = zeroPoly halfWidth p`:
`targetQ_real zp = ∫ x, column halfWidth p x * zp x`.
The spatial-energy part reuses the 0489/0490 route (`Φ = Ψ + Ψ ∘ swap`) with `f = g = zp`.
 -/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace RHLowBlock0494
open RHConditionalLog5 RHLog5Bridge RHSpatialBase0489 RHWeilColumnCandidate RHTargetFormBinding

local notation "Kk" => RH_GammaFinalFormula.K_kernel

variable (p : Polynomial ℝ)

noncomputable def zp : ℝ → ℝ := fun x => zeroPoly halfWidth p x

lemma zp_of_mem {x : ℝ} (hx : x ∈ Icc (-halfWidth) halfWidth) : zp p x = p.eval x := by
  simp [zp, zeroPoly, hx]

lemma zp_of_not_mem {x : ℝ} (hx : x ∉ Icc (-halfWidth) halfWidth) : zp p x = 0 := by
  simp [zp, zeroPoly, hx]

lemma zp_eq_indicator : zp p = (Icc (-halfWidth) halfWidth).indicator (fun y => p.eval y) := by
  funext x; rfl

lemma zp_measurable : Measurable (zp p) := by
  rw [zp_eq_indicator]
  exact p.continuous.measurable.indicator measurableSet_Icc

lemma zp_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |zp p x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (p.continuous.continuousOn (s := Icc (-halfWidth) halfWidth))
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (-halfWidth) halfWidth
  · rw [zp_of_mem p hx, ← Real.norm_eq_abs]; exact (hC x hx).trans (le_max_left _ _)
  · rw [zp_of_not_mem p hx, abs_zero]; exact le_max_right _ _

/-- `zp · g` for continuous `g` is integrable (compact support). -/
lemma mul_zp_integrable {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun x => g x * zp p x) := by
  have h : (fun x => g x * zp p x) =
      (Icc (-halfWidth) halfWidth).indicator (fun x => g x * p.eval x) := by
    funext x
    by_cases hx : x ∈ Icc (-halfWidth) halfWidth
    · rw [indicator_of_mem hx, zp_of_mem p hx]
    · rw [indicator_of_notMem hx, zp_of_not_mem p hx, mul_zero]
  rw [h]
  exact (hg.mul p.continuous).integrableOn_Icc.integrable_indicator measurableSet_Icc

lemma integral_mul_zp {g : ℝ → ℝ} :
    ∫ x, g x * zp p x = ∫ x in Icc (-halfWidth) halfWidth, g x * p.eval x := by
  have h : (fun x => g x * zp p x) =
      (Icc (-halfWidth) halfWidth).indicator (fun x => g x * p.eval x) := by
    funext x
    by_cases hx : x ∈ Icc (-halfWidth) halfWidth
    · rw [indicator_of_mem hx, zp_of_mem p hx]
    · rw [indicator_of_notMem hx, zp_of_not_mem p hx, mul_zero]
  rw [h, integral_indicator measurableSet_Icc]

lemma zp_integrable : Integrable (zp p) := by
  simpa using mul_zp_integrable p (g := fun _ => (1:ℝ)) continuous_const

lemma map_eval_ofReal (x : ℝ) : (p.map Complex.ofRealHom).eval (x : ℂ) = ((p.eval x : ℝ) : ℂ) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply Complex.ofRealHom x

lemma zp_energy_finite : RHFormDomain.energy (fun x => (zp p x : ℂ)) < ⊤ := by
  have hE := RHBoundedWindow.polynomial_energy_finite halfWidth_pos.le (p.map Complex.ofRealHom)
  have heq : RHFormDomain.extend halfWidth (fun x : ℝ => (p.map Complex.ofRealHom).eval (x : ℂ)) =
      (fun x => (zp p x : ℂ)) := by
    funext x
    by_cases hx : x ∈ Icc (-halfWidth) halfWidth
    · unfold RHFormDomain.extend
      rw [indicator_of_mem hx, zp_of_mem p hx, map_eval_ofReal]
    · unfold RHFormDomain.extend
      rw [indicator_of_notMem hx, zp_of_not_mem p hx]
      simp
  rw [heq] at hE
  exact hE

/-! ### Spatial energy -/

noncomputable def colArch (x : ℝ) : ℝ :=
  (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth, Kk |x - y| * (p.eval x - p.eval y)) +
  (1/2:ℝ) * (RH_Rebaseline.T_tail (halfWidth - x) + RH_Rebaseline.T_tail (halfWidth + x)) * p.eval x

noncomputable def PsiP (z : ℝ × ℝ) : ℝ := Kk |z.1 - z.2| * (zp p z.1 - zp p z.2) * zp p z.1

noncomputable def PhiP (z : ℝ × ℝ) : ℝ :=
  Kk |z.1 - z.2| * (zp p z.1 - zp p z.2) * (zp p z.1 - zp p z.2)

lemma phiP_integrable : Integrable (PhiP p) (volume.prod volume) :=
  crossDensity_integrable (zp_measurable p) (zp_measurable p) (zp_energy_finite p) (zp_energy_finite p)

lemma psiP_measurable : Measurable (PsiP p) :=
  (measurable_kernel_prod.mul (measurable_diff (zp_measurable p))).mul
    ((zp_measurable p).comp measurable_fst)

lemma psiP_bound_inside :
    ∃ C : ℝ, ∀ x ∈ Icc (-halfWidth) halfWidth, ∀ y ∈ Icc (-halfWidth) halfWidth, |PsiP p (x, y)| ≤ C := by
  obtain ⟨_M0, M1, _hM0, hM1, _hb, hl⟩ :=
    RHBoundedWindow.polynomial_bounds (p.map Complex.ofRealHom) halfWidth_pos.le
  obtain ⟨Mp, hMp0, hMp⟩ := zp_bounded p
  refine ⟨M1 * Real.exp halfWidth * Mp, fun x hx y hy => ?_⟩
  have hk := RHColL2.kernel_eval_sub_le halfWidth halfWidth_pos.le p M1 hl x y hx hy
  have hxy : |x - y| ≤ 2 * halfWidth := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hK := RHAutocorrEnergy.kernel_abs_nonneg (x - y)
  have hmK : min |x - y| (2 * halfWidth) * Kk |x - y| ≤ Real.exp halfWidth := by
    calc min |x - y| (2 * halfWidth) * Kk |x - y| ≤ |x - y| * Kk |x - y| :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hK
      _ = Kk |x - y| * |x - y| := by ring
      _ ≤ Real.exp (|x - y| / 2) := RHSpatialDensity0490.kernel_mul_self_le (abs_nonneg _)
      _ ≤ Real.exp halfWidth := Real.exp_le_exp.mpr (by linarith)
  have h1 : |Kk |x - y| * (p.eval x - p.eval y)| ≤ M1 * Real.exp halfWidth := by
    rw [← Real.norm_eq_abs]; exact hk.trans (mul_le_mul_of_nonneg_left hmK hM1)
  have hpx : |zp p x| ≤ Mp := hMp x
  simp only [PsiP]
  rw [zp_of_mem p hx, zp_of_mem p hy, abs_mul]
  rw [zp_of_mem p hx] at hpx
  exact mul_le_mul h1 hpx (abs_nonneg _) (mul_nonneg hM1 (Real.exp_pos _).le)

lemma psiP_decomp (z : ℝ × ℝ) :
    PsiP p z = (Icc (-halfWidth) halfWidth ×ˢ Icc (-halfWidth) halfWidth).indicator (PsiP p) z +
      (Icc (-halfWidth) halfWidth ×ˢ (Icc (-halfWidth) halfWidth)ᶜ).indicator (PhiP p) z := by
  obtain ⟨x, y⟩ := z
  by_cases hx : x ∈ Icc (-halfWidth) halfWidth <;> by_cases hy : y ∈ Icc (-halfWidth) halfWidth
  · rw [indicator_of_mem (mk_mem_prod hx hy), indicator_of_notMem (fun h => h.2 hy), add_zero]
  · rw [indicator_of_notMem (fun h => hy h.2), indicator_of_mem (mk_mem_prod hx hy), zero_add]
    simp only [PsiP, PhiP]
    rw [zp_of_not_mem p hy]
    simp only [sub_zero]
  · rw [indicator_of_notMem (fun h => hx h.1), indicator_of_notMem (fun h => hx h.1), add_zero]
    simp only [PsiP]
    rw [zp_of_not_mem p hx, mul_zero]
  · rw [indicator_of_notMem (fun h => hx h.1), indicator_of_notMem (fun h => hx h.1), add_zero]
    simp only [PsiP]
    rw [zp_of_not_mem p hx, mul_zero]

lemma psiP_integrable : Integrable (PsiP p) (volume.prod volume) := by
  have hII : MeasurableSet (Icc (-halfWidth) halfWidth ×ˢ Icc (-halfWidth) halfWidth) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hIc : MeasurableSet (Icc (-halfWidth) halfWidth ×ˢ (Icc (-halfWidth) halfWidth)ᶜ) :=
    measurableSet_Icc.prod measurableSet_Icc.compl
  have hfin : (volume.prod volume) (Icc (-halfWidth) halfWidth ×ˢ Icc (-halfWidth) halfWidth) ≠ ⊤ := by
    rw [Measure.prod_prod, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  obtain ⟨C, hC⟩ := psiP_bound_inside p
  have h1 : IntegrableOn (PsiP p) (Icc (-halfWidth) halfWidth ×ˢ Icc (-halfWidth) halfWidth)
      (volume.prod volume) :=
    Measure.integrableOn_of_bounded hfin (psiP_measurable p).aestronglyMeasurable (M := C)
      ((ae_restrict_iff' hII).mpr (Filter.Eventually.of_forall (fun z hz => by
        rw [Real.norm_eq_abs]; exact hC z.1 hz.1 z.2 hz.2)))
  have h2 := (phiP_integrable p).indicator hIc
  have h3 := h1.integrable_indicator hII
  exact (h3.add h2).congr (Filter.Eventually.of_forall (fun z => (psiP_decomp p z).symm))

lemma half_inner_psi_ae :
    (fun x => (1/2:ℝ) * ∫ y, PsiP p (x, y)) =ᵐ[volume] fun x => colArch p x * zp p x := by
  filter_upwards [(psiP_integrable p).prod_right_ae, Measure.ae_ne volume halfWidth,
    Measure.ae_ne volume (-halfWidth)] with x hx h1 h2
  by_cases hxI : x ∈ Icc (-halfWidth) halfWidth
  · have hlt : |x| < halfWidth :=
      abs_lt.mpr ⟨lt_of_le_of_ne hxI.1 (Ne.symm h2), lt_of_le_of_ne hxI.2 h1⟩
    rw [← integral_add_compl measurableSet_Icc hx]
    have e1 : ∫ y in Icc (-halfWidth) halfWidth, PsiP p (x, y) =
        (∫ y in Icc (-halfWidth) halfWidth, Kk |x - y| * (p.eval x - p.eval y)) * p.eval x := by
      rw [← integral_mul_const]
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      simp only [PsiP]
      rw [zp_of_mem p hxI, zp_of_mem p hy]
    have e2 : ∫ y in (Icc (-halfWidth) halfWidth)ᶜ, PsiP p (x, y) =
        (RH_Rebaseline.T_tail (halfWidth - x) + RH_Rebaseline.T_tail (halfWidth + x)) *
          (p.eval x * p.eval x) := by
      have hc : EqOn (fun y => PsiP p (x, y))
          (fun y => RH_Rebaseline.K_kernel |x - y| * (p.eval x * p.eval x))
          (Icc (-halfWidth) halfWidth)ᶜ := by
        intro y hy
        simp only [PsiP]
        rw [zp_of_mem p hxI, zp_of_not_mem p hy, sub_zero]
        rw [← RH_GammaFinalFormula.K_kernel_eq_Rebaseline]
        ring
      rw [setIntegral_congr_fun measurableSet_Icc.compl hc, integral_mul_const,
        (RHExternalPotential.outside_integral hlt).2]
    rw [e1, e2]
    unfold colArch
    rw [zp_of_mem p hxI]
    ring
  · have h0 : (fun y => PsiP p (x, y)) = fun _ => 0 := by
      funext y; simp only [PsiP]; rw [zp_of_not_mem p hxI, mul_zero]
    rw [h0, zp_of_not_mem p hxI]
    simp

theorem spatialEnergy_zp :
    RHAutocorrEnergy.spatialEnergy (zp p) = ∫ x, colArch p x * zp p x := by
  have hE : Integrable (fun z : ℝ × ℝ => Kk |z.1 - z.2| * (zp p z.1 - zp p z.2) ^ 2)
      (volume.prod volume) := energyDensity_integrable (zp_measurable p) (zp_energy_finite p)
  have hΨ := psiP_integrable p
  have ha : (∫ x, ∫ y, Kk |x - y| * (zp p x - zp p y) ^ 2) =
      ∫ z, Kk |z.1 - z.2| * (zp p z.1 - zp p z.2) ^ 2 ∂(volume.prod volume) :=
    integral_integral (f := fun x y => Kk |x - y| * (zp p x - zp p y) ^ 2) hE
  have hb : ∫ z, Kk |z.1 - z.2| * (zp p z.1 - zp p z.2) ^ 2 ∂(volume.prod volume) =
      2 * ∫ z, PsiP p z ∂(volume.prod volume) := by
    have hsw : Integrable (fun z : ℝ × ℝ => PsiP p z.swap) (volume.prod volume) := hΨ.swap
    have e : (fun z : ℝ × ℝ => Kk |z.1 - z.2| * (zp p z.1 - zp p z.2) ^ 2) =
        fun z => PsiP p z + PsiP p z.swap := by
      funext z
      obtain ⟨x, y⟩ := z
      simp only [PsiP, Prod.swap_prod_mk]
      rw [abs_sub_comm y x]
      ring
    rw [e, integral_add hΨ hsw, integral_prod_swap (PsiP p)]
    ring
  have hc : ∫ z, PsiP p z ∂(volume.prod volume) = ∫ x, ∫ y, PsiP p (x, y) :=
    (integral_integral (f := fun x y => PsiP p (x, y)) hΨ).symm
  unfold RHAutocorrEnergy.spatialEnergy
  rw [ha, hb, hc, ← integral_congr_ae (half_inner_psi_ae p), integral_const_mul]
  ring

lemma colArch_mul_zp_integrable : Integrable (fun x => colArch p x * zp p x) := by
  have h := ((psiP_integrable p).integral_prod_left).const_mul (1/2:ℝ)
  exact h.congr (half_inner_psi_ae p)

/-! ### The full column -/

noncomputable def h0c : ℝ := (Complex.digamma (1/4:ℂ)).re - Real.log Real.pi

noncomputable def primeTerm (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
    (zp p (x - Real.log n) + zp p (x + Real.log n))

noncomputable def colFull (x : ℝ) : ℝ :=
  h0c * p.eval x + colArch p x +
  2 * (∫ y in Icc (-halfWidth) halfWidth, p.eval y * Real.cosh (y/2)) * Real.cosh (x/2) -
  2 * (∫ y in Icc (-halfWidth) halfWidth, p.eval y * Real.sinh (y/2)) * Real.sinh (x/2) -
  primeTerm p x

lemma column_eq_colFull {x : ℝ} (hx : |x| < halfWidth) :
    column halfWidth p x = colFull p x := by
  unfold column colFull colArch primeTerm h0c
  rw [if_pos hx]
  simp only [zp]
  ring

lemma column_mul_zp_ae :
    (fun x => column halfWidth p x * zp p x) =ᵐ[volume] fun x => colFull p x * zp p x := by
  filter_upwards [Measure.ae_ne volume halfWidth, Measure.ae_ne volume (-halfWidth)] with x h1 h2
  by_cases hxI : x ∈ Icc (-halfWidth) halfWidth
  · have hlt : |x| < halfWidth :=
      abs_lt.mpr ⟨lt_of_le_of_ne hxI.1 (Ne.symm h2), lt_of_le_of_ne hxI.2 h1⟩
    rw [column_eq_colFull p hlt]
  · rw [zp_of_not_mem p hxI, mul_zero, mul_zero]

lemma shift_mul_zp_integrable (a : ℝ) : Integrable (fun x => zp p (x + a) * zp p x) := by
  obtain ⟨C, _, hC⟩ := zp_bounded p
  exact (zp_integrable p).bdd_mul ((zp_measurable p).comp (measurable_id.add_const a)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hC _))

lemma integral_shift_plus (a : ℝ) :
    ∫ x, zp p (x + a) * zp p x = RH_LiteratureBridge.real_autocorr (zp p) a := by
  unfold RH_LiteratureBridge.real_autocorr
  have h := integral_sub_right_eq_self (μ := volume) (fun x => zp p (x + a) * zp p x) a
  simp only [sub_add_cancel] at h
  rw [← h]

lemma integral_shift_minus (a : ℝ) :
    ∫ x, zp p (x - a) * zp p x = RH_LiteratureBridge.real_autocorr (zp p) a := by
  unfold RH_LiteratureBridge.real_autocorr
  congr 1; funext x; ring

/-- Riesz representation of the target quadratic form on a zero-extended polynomial. -/
theorem targetQ_zp :
    targetQ_real (zp p) = ∫ x, column halfWidth p x * zp p x := by
  rw [integral_congr_ae (column_mul_zp_ae p)]
  set Cc := ∫ y in Icc (-halfWidth) halfWidth, p.eval y * Real.cosh (y/2)
  set Ss := ∫ y in Icc (-halfWidth) halfWidth, p.eval y * Real.sinh (y/2)
  have hsq : (fun x => h0c * p.eval x * zp p x) = fun x => h0c * (zp p x)^2 := by
    funext x
    by_cases hx : x ∈ Icc (-halfWidth) halfWidth
    · rw [zp_of_mem p hx]; ring
    · rw [zp_of_not_mem p hx]; ring
  have iA : Integrable (fun x => h0c * p.eval x * zp p x) := by
    have := mul_zp_integrable p (g := fun x => h0c * p.eval x) (continuous_const.mul p.continuous)
    exact this
  have iB := colArch_mul_zp_integrable p
  have iC : Integrable (fun x => 2 * Cc * Real.cosh (x/2) * zp p x) :=
    mul_zp_integrable p (continuous_const.mul (Real.continuous_cosh.comp (continuous_id.div_const 2)))
  have iD : Integrable (fun x => 2 * Ss * Real.sinh (x/2) * zp p x) :=
    mul_zp_integrable p (continuous_const.mul (Real.continuous_sinh.comp (continuous_id.div_const 2)))
  have iE : ∀ n ∈ Finset.range 5, Integrable (fun x =>
      ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        (zp p (x - Real.log n) * zp p x + zp p (x + Real.log n) * zp p x)) := by
    intro n _
    refine Integrable.const_mul ?_ _
    refine Integrable.add ?_ (shift_mul_zp_integrable p _)
    simpa [sub_eq_add_neg] using shift_mul_zp_integrable p (-Real.log n)
  have iP : Integrable (fun x => primeTerm p x * zp p x) := by
    have h := integral_finsetSum (μ := volume) (Finset.range 5) iE
    have hi := integrable_finsetSum (Finset.range 5) iE
    refine hi.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [primeTerm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hsplit : (fun x => colFull p x * zp p x) = fun x =>
      h0c * p.eval x * zp p x + colArch p x * zp p x + 2 * Cc * Real.cosh (x/2) * zp p x -
      2 * Ss * Real.sinh (x/2) * zp p x - primeTerm p x * zp p x := by
    funext x; unfold colFull; ring
  rw [hsplit]
  have jAB : Integrable (fun x => h0c * p.eval x * zp p x + colArch p x * zp p x) := iA.add iB
  have jABC : Integrable (fun x => h0c * p.eval x * zp p x + colArch p x * zp p x +
      2 * Cc * Real.cosh (x/2) * zp p x) := jAB.add iC
  have jABCD : Integrable (fun x => h0c * p.eval x * zp p x + colArch p x * zp p x +
      2 * Cc * Real.cosh (x/2) * zp p x - 2 * Ss * Real.sinh (x/2) * zp p x) := jABC.sub iD
  rw [integral_sub jABCD iP, integral_sub jABC iD, integral_add jAB iC, integral_add iA iB,
    ← spatialEnergy_zp p, hsq, integral_const_mul]
  have hCc : ∫ x, 2 * Cc * Real.cosh (x/2) * zp p x = 2 * Cc * Cc := by
    rw [integral_mul_zp p (g := fun x => 2 * Cc * Real.cosh (x/2))]
    rw [show (fun x => 2 * Cc * Real.cosh (x/2) * p.eval x) = fun x => (2 * Cc) * (p.eval x * Real.cosh (x/2)) by
      funext x; ring, integral_const_mul]
  have hSs : ∫ x, 2 * Ss * Real.sinh (x/2) * zp p x = 2 * Ss * Ss := by
    rw [integral_mul_zp p (g := fun x => 2 * Ss * Real.sinh (x/2))]
    rw [show (fun x => 2 * Ss * Real.sinh (x/2) * p.eval x) = fun x => (2 * Ss) * (p.eval x * Real.sinh (x/2)) by
      funext x; ring, integral_const_mul]
  have hCz : ∫ x, zp p x * Real.cosh (x / 2) = Cc := by
    rw [show (fun x => zp p x * Real.cosh (x / 2)) = fun x => Real.cosh (x/2) * zp p x by funext x; ring,
      integral_mul_zp p (g := fun x => Real.cosh (x/2))]
    congr 1; funext x; ring
  have hSz : ∫ x, zp p x * Real.sinh (x / 2) = Ss := by
    rw [show (fun x => zp p x * Real.sinh (x / 2)) = fun x => Real.sinh (x/2) * zp p x by funext x; ring,
      integral_mul_zp p (g := fun x => Real.sinh (x/2))]
    congr 1; funext x; ring
  have hP : ∫ x, primeTerm p x * zp p x =
      2 * ∑ n ∈ Finset.range 5, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        RH_LiteratureBridge.real_autocorr (zp p) (Real.log n) := by
    have e : (fun x => primeTerm p x * zp p x) = fun x => ∑ n ∈ Finset.range 5,
        ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
          (zp p (x - Real.log n) * zp p x + zp p (x + Real.log n) * zp p x) := by
      funext x; simp only [primeTerm, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro n _; ring
    rw [e, integral_finsetSum _ iE, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [integral_const_mul, integral_add ?_ (shift_mul_zp_integrable p _),
      integral_shift_minus, integral_shift_plus]
    · ring
    · simpa [sub_eq_add_neg] using shift_mul_zp_integrable p (-Real.log n)
  rw [hCc, hSs, hP]
  unfold targetQ_real
  rw [hCz, hSz]
  unfold h0c
  ring

end RHLowBlock0494

