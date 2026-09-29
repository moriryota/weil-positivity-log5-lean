import RHSpatialBase0489
import ColL2Components

/-! # 0489/0490 h2: `RHStepA2G2.SpatialEnergyDensityIntegral` without research hypotheses

Route (contract §2 h2): `Φ = Ψ + Ψ ∘ swap` with the asymmetric density
`Ψ(x,y) = K(|x-y|) (low x - low y) tail x`. `Ψ` is integrable on `ℝ × ℝ`:
bounded on `I × I` (polynomial Lipschitz bound and `K(s) s ≤ exp(s/2)`), equal to the
integrable `Φ` on `I × Iᶜ`, and zero for `x ∉ I`. Then Fubini and the existing
`RHStepA2G2.arch_density_integral_eq`. -/

open MeasureTheory Set
open scoped ENNReal

namespace RHSpatialDensity0490
open RHConditionalLog5 RHResidualMembership RHLog5Bridge RHSpatialBase0489

local notation "Kk" => RH_GammaFinalFormula.K_kernel

/-- `K(s) s ≤ exp(s/2)` for `s ≥ 0` (uses `s ≤ sinh s`; `K 0 = 0` by the division convention). -/
lemma kernel_mul_self_le {s : ℝ} (hs : 0 ≤ s) : Kk s * s ≤ Real.exp (s / 2) := by
  rcases hs.eq_or_lt with h | h
  · rw [← h, mul_zero]; positivity
  · have hsh : 0 < Real.sinh s := Real.sinh_pos_iff.mpr h
    have hle : s ≤ Real.sinh s := Real.self_le_sinh_iff.mpr hs
    unfold RH_GammaFinalFormula.K_kernel RH_GammaSqrtBound.K_kernel
    rw [div_mul_eq_mul_div, div_le_iff₀ hsh]
    exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le

/-- Real polynomial representing `low o u` on the window. -/
noncomputable def lowPR (o : Bool) (u : ℝ → ℝ) : Polynomial ℝ :=
  ∑ j : I, Polynomial.C (alpha o u j) * basisPoly (degree o j)

lemma low_eq_lowPR (o : Bool) (u : ℝ → ℝ) (x : ℝ) (hx : x ∈ Icc (-halfWidth) halfWidth) :
    low o u x = (lowPR o u).eval x := by
  rw [RHStepA2G2.low_eval_eq_sum o u x hx, lowPR, Polynomial.eval_finsetSum]
  simp [Polynomial.eval_mul, Polynomial.eval_C]

/-- Uniform bound of the asymmetric density on `I × I`. -/
lemma psi_bound_inside (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    ∃ C : ℝ, ∀ x ∈ Icc (-halfWidth) halfWidth, ∀ y ∈ Icc (-halfWidth) halfWidth,
      |Kk |x - y| * (low o u x - low o u y) * tail o u x| ≤ C := by
  obtain ⟨_M0, M1, _hM0, hM1, _hb, hl⟩ :=
    RHBoundedWindow.polynomial_bounds ((lowPR o u).map Complex.ofRealHom) halfWidth_pos.le
  have hcont : ContinuousOn (fun x => component o u x - (lowPR o u).eval x)
      (Icc (-halfWidth) halfWidth) :=
    ((RHG3RealEmbedding.component_continuous o u hu).sub (Polynomial.continuous _)).continuousOn
  obtain ⟨Mg, hMg⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨M1 * Real.exp halfWidth * Mg, fun x hx y hy => ?_⟩
  have hk := RHColL2.kernel_eval_sub_le halfWidth halfWidth_pos.le (lowPR o u) M1 hl x y hx hy
  have hg : |tail o u x| ≤ Mg := by
    have h := hMg x hx
    rw [Real.norm_eq_abs] at h
    have ht : tail o u x = component o u x - (lowPR o u).eval x := by
      rw [← low_eq_lowPR o u x hx]; rfl
    rw [ht]; exact h
  have hxy : |x - y| ≤ 2 * halfWidth := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hK := RHAutocorrEnergy.kernel_abs_nonneg (x - y)
  have hmK : min |x - y| (2 * halfWidth) * Kk |x - y| ≤ Real.exp halfWidth := by
    calc min |x - y| (2 * halfWidth) * Kk |x - y| ≤ |x - y| * Kk |x - y| :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hK
      _ = Kk |x - y| * |x - y| := by ring
      _ ≤ Real.exp (|x - y| / 2) := kernel_mul_self_le (abs_nonneg _)
      _ ≤ Real.exp halfWidth := Real.exp_le_exp.mpr (by linarith)
  have h1 : |Kk |x - y| * ((lowPR o u).eval x - (lowPR o u).eval y)| ≤ M1 * Real.exp halfWidth := by
    rw [← Real.norm_eq_abs]; exact hk.trans (mul_le_mul_of_nonneg_left hmK hM1)
  rw [low_eq_lowPR o u x hx, low_eq_lowPR o u y hy, abs_mul]
  exact mul_le_mul h1 hg (abs_nonneg _) (mul_nonneg hM1 (Real.exp_pos _).le)

noncomputable def Psi (o : Bool) (u : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  Kk |z.1 - z.2| * (low o u z.1 - low o u z.2) * tail o u z.1

noncomputable def Phi (o : Bool) (u : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  Kk |z.1 - z.2| * (low o u z.1 - low o u z.2) * (tail o u z.1 - tail o u z.2)

lemma phi_integrable (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    Integrable (Phi o u) (volume.prod volume) :=
  crossDensity_integrable (low_measurable o u) (tail_measurable o u hu)
    (low_energy_finite o u) (RHG1Energy.tail_energy_finite o u hu)

lemma psi_measurable (o : Bool) (u : ℝ → ℝ) (hu : Test u) : Measurable (Psi o u) :=
  (measurable_kernel_prod.mul (measurable_diff (low_measurable o u))).mul
    ((tail_measurable o u hu).comp measurable_fst)

lemma psi_decomp (o : Bool) (u : ℝ → ℝ) (hu : Test u) (z : ℝ × ℝ) :
    Psi o u z = (Icc (-halfWidth) halfWidth ×ˢ Icc (-halfWidth) halfWidth).indicator (Psi o u) z +
      (Icc (-halfWidth) halfWidth ×ˢ (Icc (-halfWidth) halfWidth)ᶜ).indicator (Phi o u) z := by
  obtain ⟨x, y⟩ := z
  by_cases hx : x ∈ Icc (-halfWidth) halfWidth <;> by_cases hy : y ∈ Icc (-halfWidth) halfWidth
  · rw [indicator_of_mem (mk_mem_prod hx hy),
      indicator_of_notMem (fun h => h.2 hy), add_zero]
  · rw [indicator_of_notMem (fun h => hy h.2), indicator_of_mem (mk_mem_prod hx hy), zero_add]
    simp only [Psi, Phi]
    rw [low_zero_outside o u y hy, tail_zero_outside o u hu y hy]
    simp only [sub_zero]
  · rw [indicator_of_notMem (fun h => hx h.1), indicator_of_notMem (fun h => hx h.1), add_zero]
    simp only [Psi]
    rw [tail_zero_outside o u hu x hx, mul_zero]
  · rw [indicator_of_notMem (fun h => hx h.1), indicator_of_notMem (fun h => hx h.1), add_zero]
    simp only [Psi]
    rw [tail_zero_outside o u hu x hx, mul_zero]

lemma psi_integrable (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    Integrable (Psi o u) (volume.prod volume) := by
  have hII : MeasurableSet (Icc (-halfWidth) halfWidth ×ˢ Icc (-halfWidth) halfWidth) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hIc : MeasurableSet (Icc (-halfWidth) halfWidth ×ˢ (Icc (-halfWidth) halfWidth)ᶜ) :=
    measurableSet_Icc.prod measurableSet_Icc.compl
  have hfin : (volume.prod volume) (Icc (-halfWidth) halfWidth ×ˢ Icc (-halfWidth) halfWidth) ≠ ⊤ := by
    rw [Measure.prod_prod, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  obtain ⟨C, hC⟩ := psi_bound_inside o u hu
  have h1 : IntegrableOn (Psi o u) (Icc (-halfWidth) halfWidth ×ˢ Icc (-halfWidth) halfWidth)
      (volume.prod volume) :=
    Measure.integrableOn_of_bounded hfin (psi_measurable o u hu).aestronglyMeasurable (M := C)
      ((ae_restrict_iff' hII).mpr (Filter.Eventually.of_forall (fun z hz => by
        rw [Real.norm_eq_abs]; exact hC z.1 hz.1 z.2 hz.2)))
  have h2 := (phi_integrable o u hu).indicator hIc
  have h3 := h1.integrable_indicator hII
  exact (h3.add h2).congr (Filter.Eventually.of_forall (fun z => (psi_decomp o u hu z).symm))

theorem spatialEnergyDensityIntegral : RHStepA2G2.SpatialEnergyDensityIntegral := by
  intro o u hu
  have hX := phi_integrable o u hu
  have hΨ := psi_integrable o u hu
  have ha : (∫ x, ∫ y, Kk |x - y| * (low o u x - low o u y) * (tail o u x - tail o u y)) =
      ∫ z, Phi o u z ∂(volume.prod volume) :=
    integral_integral (f := fun x y => Kk |x - y| * (low o u x - low o u y) * (tail o u x - tail o u y)) hX
  have hb : ∫ z, Phi o u z ∂(volume.prod volume) = 2 * ∫ z, Psi o u z ∂(volume.prod volume) := by
    have hsw : Integrable (fun z : ℝ × ℝ => Psi o u z.swap) (volume.prod volume) := hΨ.swap
    have e : (fun z => Phi o u z) = fun z => Psi o u z + Psi o u z.swap := by
      funext z
      obtain ⟨x, y⟩ := z
      simp only [Phi, Psi, Prod.swap_prod_mk]
      exact RHStepA2G2.spatial_diff_kernel_eq_add_swap o u x y
    rw [e, integral_add hΨ hsw, integral_prod_swap (Psi o u)]
    ring
  have hc : ∫ z, Psi o u z ∂(volume.prod volume) = ∫ x, ∫ y, Psi o u (x, y) :=
    (integral_integral (f := fun x y => Psi o u (x, y)) hΨ).symm
  have hd : (fun x => (1/2:ℝ) * ∫ y, Psi o u (x, y)) =ᵐ[volume] fun x =>
      (1/2:ℝ) * (∫ y in Icc (-halfWidth) halfWidth, Kk |x - y| * (low o u x - low o u y)) * tail o u x +
      (1/2:ℝ) * (∫ y in (Icc (-halfWidth) halfWidth)ᶜ,
        Kk |x - y| * ((low o u x - low o u y) * (tail o u x - tail o u y))) := by
    filter_upwards [hΨ.prod_right_ae] with x hx
    rw [← integral_add_compl measurableSet_Icc hx]
    have e1 : ∫ y in Icc (-halfWidth) halfWidth, Psi o u (x, y) =
        (∫ y in Icc (-halfWidth) halfWidth, Kk |x - y| * (low o u x - low o u y)) * tail o u x := by
      simp only [Psi]
      exact integral_mul_const _ _
    have e2 : ∫ y in (Icc (-halfWidth) halfWidth)ᶜ, Psi o u (x, y) =
        ∫ y in (Icc (-halfWidth) halfWidth)ᶜ,
          Kk |x - y| * ((low o u x - low o u y) * (tail o u x - tail o u y)) := by
      apply setIntegral_congr_fun measurableSet_Icc.compl
      intro y hy
      simp only [Psi]
      rw [tail_zero_outside o u hu y hy]
      ring
    rw [e1, e2]
    ring
  rw [ha, hb, hc, RHStepA2G2.arch_density_integral_eq o u hu, ← integral_congr_ae hd,
    integral_const_mul]
  ring

end RHSpatialDensity0490

