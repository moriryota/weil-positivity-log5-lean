import Contract
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Complex.RealDeriv

-- Source: EnergyMajorant.lean

open MeasureTheory Set Filter
open scoped ENNReal
namespace RHBoundedWindow
open RHFormDomain
set_option maxHeartbeats 1000000

lemma moment_lintegral_finite {b : ℝ} (hb : 0 ≤ b) :
    (∫⁻ s : ℝ, kernel s * ENNReal.ofReal (min |s| b)) < ⊤ := by
  have he (s : ℝ) : kernel s * ENNReal.ofReal (min |s| b) =
      ENNReal.ofReal (min |s| b * RH_GammaFinalFormula.K_kernel |s|) := by
    rw [kernel_eq_old, ← ENNReal.ofReal_mul (RHAutocorrEnergy.kernel_abs_nonneg s)]
    congr 1
    ring
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal (full_moment_integrable hb)
    (Eventually.of_forall (full_moment_nonneg hb))]
  exact ENNReal.ofReal_lt_top

noncomputable def firstMajorant (L M : ℝ) (x y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (M^2*(2*L)) * (Icc (-L) L).indicator (fun _ : ℝ => (1:ℝ≥0∞)) x *
    (kernel (x-y) * ENNReal.ofReal (min |x-y| (2*L)))

lemma firstMajorant_measurable (L M : ℝ) :
    Measurable (fun z : ℝ × ℝ => firstMajorant L M z.1 z.2) := by
  have hk := measurable_kernel
  have hi : Measurable ((Icc (-L) L).indicator (fun _ : ℝ => (1:ℝ≥0∞))) :=
    measurable_const.indicator measurableSet_Icc
  unfold firstMajorant
  fun_prop

lemma firstMajorant_integral_finite {L : ℝ} (hL : 0 ≤ L) (M : ℝ) :
    (∫⁻ x : ℝ, ∫⁻ y : ℝ, firstMajorant L M x y) < ⊤ := by
  let a : ℝ≥0∞ := ENNReal.ofReal (M^2*(2*L))
  let u : ℝ → ℝ≥0∞ := (Icc (-L) L).indicator (fun _ : ℝ => (1:ℝ≥0∞))
  let q : ℝ → ℝ≥0∞ := fun s => kernel s * ENNReal.ofReal (min |s| (2*L))
  have ha : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hu (x : ℝ) : u x ≠ ⊤ := by
    dsimp [u]
    by_cases h : x ∈ Icc (-L) L <;> simp [h]
  have hi (x : ℝ) : (∫⁻ y : ℝ, firstMajorant L M x y) = a * u x * ∫⁻ s : ℝ, q s := by
    change (∫⁻ y : ℝ, a*u x*q (x-y)) = _
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ha (hu x))]
    rw [lintegral_sub_left_eq_self (μ := volume)]
  simp_rw [hi]
  have hq : (∫⁻ s : ℝ, q s) ≠ ⊤ := ne_of_lt (moment_lintegral_finite (by linarith : 0 ≤ 2*L))
  rw [lintegral_mul_const' _ _ hq, lintegral_const_mul' _ _ ha]
  have hui : (∫⁻ x : ℝ, u x) = volume (Icc (-L) L) := by
    exact lintegral_indicator_one measurableSet_Icc
  rw [hui]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)) (lt_of_le_of_ne le_top hq)

lemma energy_finite_of_majorant {f g : ℝ → ℂ} {F : ℝ × ℝ → ℝ≥0∞}
    (hF : Measurable F) (hFin : (∫⁻ x : ℝ, ∫⁻ y : ℝ, F (x,y)) < ⊤)
    (hg : energy g < ⊤) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ x y : ℝ, kernel (x-y) * ENNReal.ofReal (‖f x-f y‖^2) ≤
      F (x,y) + c * (kernel (x-y)*ENNReal.ofReal (‖g x-g y‖^2))) :
    energy f < ⊤ := by
  have hm := lintegral_mono (μ := volume) (fun x => lintegral_mono (μ := volume) (h x))
  have hi (x : ℝ) : (∫⁻ y : ℝ, F (x,y) + c*(kernel (x-y)*ENNReal.ofReal (‖g x-g y‖^2))) =
      (∫⁻ y : ℝ, F (x,y)) + c*(∫⁻ y : ℝ, kernel (x-y)*ENNReal.ofReal (‖g x-g y‖^2)) := by
    have hFx : Measurable (fun y : ℝ => F (x,y)) := hF.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_add_left hFx, lintegral_const_mul' _ _ hc]
  simp_rw [hi] at hm
  rw [lintegral_add_left hF.lintegral_prod_right', lintegral_const_mul' _ _ hc] at hm
  have he : energy f ≤ (4:ℝ≥0∞)⁻¹ * (∫⁻ x : ℝ, ∫⁻ y : ℝ, F (x,y)) + c*energy g := by
    unfold energy
    convert mul_le_mul_left hm (4:ℝ≥0∞)⁻¹ using 1 <;> ring
  apply he.trans_lt
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) hFin,
    ENNReal.mul_lt_top (lt_of_le_of_ne le_top hc) hg⟩

end RHBoundedWindow

-- Source: BoundedEnergy.lean

open MeasureTheory Set Filter
open scoped ENNReal
namespace RHBoundedWindow
open RHFormDomain
set_option maxHeartbeats 1000000

/-- A pointwise upper bound implies finiteness of the original extended energy.
No integrability hypothesis on that energy is smuggled into this interface. -/
theorem energy_finite_of_pointwise {L : ℝ} (hL : 0 ≤ L) (p : ℝ → ℂ)
    (M0 M1 : ℝ) (hp : PointwiseBound L p M0 M1) :
    energy (extend L p) < ⊤ := by
  apply energy_finite_of_majorant (firstMajorant_measurable L M1)
    (firstMajorant_integral_finite hL M1) (centered_one_finite hL)
    (ENNReal.ofReal (M0^2)) ENNReal.ofReal_ne_top
  intro x y
  have hn : 0 ≤ M1^2*(2*L)*min |x-y| (2*L)*(Icc (-L) L).indicator (fun _ : ℝ => (1:ℝ)) x := by
    have hu : 0 ≤ (Icc (-L) L).indicator (fun _ : ℝ => (1:ℝ)) x := by
      by_cases hx : x ∈ Icc (-L) L <;> simp [hx]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg M1) (by linarith))
      (le_min (abs_nonneg _) (by linarith))) hu
  have he : kernel (x-y)*ENNReal.ofReal
      (M1^2*(2*L)*min |x-y| (2*L)*(Icc (-L) L).indicator (fun _ : ℝ => (1:ℝ)) x) =
      firstMajorant L M1 x y := by
    by_cases hx : x ∈ Icc (-L) L
    · simp only [firstMajorant, indicator_of_mem hx, mul_one]
      rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg M1) (by linarith))]
      ring
    · simp [firstMajorant, hx]
  have h := ENNReal.ofReal_le_ofReal (hp x y)
  rw [ENNReal.ofReal_add hn (by positivity), ENNReal.ofReal_mul (sq_nonneg M0)] at h
  have hh := mul_le_mul_right h (kernel (x-y))
  rw [mul_add, he] at hh
  convert hh using 1 <;> ring

end RHBoundedWindow

-- Source: BoundedLp.lean

open MeasureTheory Set Filter
open scoped ENNReal
namespace RHBoundedWindow
open RHFormDomain

lemma bounded_memLp (L : ℝ) (p : ℝ → ℂ) (hp : Measurable p) (M : ℝ)
    (hb : BoundedOn L p M) : MemLp p 2 (volume.restrict (Icc (-L) L)) := by
  letI : IsFiniteMeasure (volume.restrict (Icc (-L) L)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  exact MemLp.of_bound hp.aestronglyMeasurable M
    (ae_restrict_of_forall_mem measurableSet_Icc hb)

noncomputable def boundedIntervalLp (L : ℝ) (p : ℝ → ℂ) (hp : Measurable p) (M : ℝ)
    (hb : BoundedOn L p M) : Lp ℂ 2 (volume.restrict (Icc (-L) L)) :=
  (bounded_memLp L p hp M hb).toLp p

lemma boundedIntervalLp_energy (L : ℝ) (p : ℝ → ℂ) (hp : Measurable p) (M : ℝ)
    (hb : BoundedOn L p M) :
    intervalEnergy L (boundedIntervalLp L p hp M hb) = energy (extend L p) := by
  exact energy_extend_congr_ae (MemLp.coeFn_toLp (bounded_memLp L p hp M hb))

lemma boundedIntervalLp_mem (L : ℝ) (p : ℝ → ℂ) (hp : Measurable p) (M : ℝ)
    (hb : BoundedOn L p M) (hE : energy (extend L p) < ⊤) :
    InDomain L (boundedIntervalLp L p hp M hb) := by
  unfold InDomain
  rw [boundedIntervalLp_energy]
  exact hE

end RHBoundedWindow

-- Source: A/Pointwise.lean

open MeasureTheory Set

namespace RHBoundedWindow

/-- Pointwise square bound for the zero-extension of a window function `p`.
The right-hand side splits the contribution into a Lipschitz part (active only on the
window through the real indicator at `x`) and a boundedness part carried by the
constant-window difference. -/
theorem pointwise_bound {L : ℝ} (hL : 0 ≤ L) (p : ℝ → ℂ)
    {M0 M1 : ℝ} (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hb : BoundedOn L p M0) (hl : LipschitzBoundOn L p M1) :
    PointwiseBound L p M0 M1 := by
  intro x y
  have h2L : (0:ℝ) ≤ 2 * L := by linarith
  have habs : (0:ℝ) ≤ |x - y| := abs_nonneg _
  have hmin_nonneg : (0:ℝ) ≤ min |x - y| (2 * L) := le_min habs h2L
  have hterm1_nonneg : (0:ℝ) ≤ M1 ^ 2 * (2 * L) * min |x - y| (2 * L) :=
    mul_nonneg (mul_nonneg (sq_nonneg M1) h2L) hmin_nonneg
  by_cases hx : x ∈ Icc (-L) L <;> by_cases hy : y ∈ Icc (-L) L
  · -- both endpoints inside the window
    simp only [RHFormDomain.extend, Set.indicator_of_mem hx, Set.indicator_of_mem hy,
      sub_self, norm_zero, mul_one]
    have hxy2L : |x - y| ≤ 2 * L := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have h1 := hx.1; have h2 := hy.2; linarith
      · have h1 := hx.2; have h2 := hy.1; linarith
    rw [min_eq_left hxy2L]
    have hlip := hl x hx y hy
    have hnn := norm_nonneg (p x - p y)
    have hsq : ‖p x - p y‖ * ‖p x - p y‖ ≤ (M1 * |x - y|) * (M1 * |x - y|) :=
      mul_le_mul hlip hlip hnn (mul_nonneg hM1 habs)
    nlinarith [hsq, mul_nonneg (mul_nonneg (mul_nonneg hM1 hM1) habs) (sub_nonneg.mpr hxy2L)]
  · -- `x` inside, `y` outside
    simp only [RHFormDomain.extend, Set.indicator_of_mem hx, Set.indicator_of_notMem hy,
      sub_zero, mul_one, norm_one, one_pow]
    have hbx := hb x hx
    have hnn := norm_nonneg (p x)
    have hsq : ‖p x‖ * ‖p x‖ ≤ M0 * M0 := mul_le_mul hbx hbx hnn hM0
    nlinarith [hsq, hterm1_nonneg]
  · -- `x` outside, `y` inside
    simp only [RHFormDomain.extend, Set.indicator_of_notMem hx, Set.indicator_of_mem hy,
      zero_sub, norm_neg, mul_zero, zero_add, norm_one, one_pow, mul_one]
    have hby := hb y hy
    have hnn := norm_nonneg (p y)
    have hsq : ‖p y‖ * ‖p y‖ ≤ M0 * M0 := mul_le_mul hby hby hnn hM0
    nlinarith [hsq]
  · -- both endpoints outside the window
    simp only [RHFormDomain.extend, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy,
      sub_self, norm_zero, mul_zero, zero_add]
    norm_num

end RHBoundedWindow


-- Source: B/PolynomialBounds.lean

open MeasureTheory Set

namespace RHBoundedWindow

/-- The real restriction `x ↦ P.eval x` of a complex polynomial is continuous:
it is the composition of the continuous coercion `ℝ → ℂ` with polynomial evaluation. -/
lemma continuous_polyOfReal (P : Polynomial ℂ) :
    Continuous (fun x : ℝ => P.eval (x : ℂ)) :=
  P.continuous.comp Complex.continuous_ofReal

theorem polynomial_measurable (P : Polynomial ℂ) :
    Measurable (fun x : ℝ => P.eval (x : ℂ)) :=
  (continuous_polyOfReal P).measurable

/-- On the compact interval `Icc (-L) L` the real restriction of a complex polynomial is
norm-bounded by a nonnegative constant (local, not global, boundedness). -/
lemma exists_norm_bound_on_Icc (P : Polynomial ℂ) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (-L) L, ‖P.eval (x : ℂ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_polyOfReal P).continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩

theorem polynomial_bounds (P : Polynomial ℂ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ M0 M1 : ℝ, 0 ≤ M0 ∧ 0 ≤ M1 ∧
      BoundedOn L (fun x : ℝ => P.eval (x : ℂ)) M0 ∧
      LipschitzBoundOn L (fun x : ℝ => P.eval (x : ℂ)) M1 := by
  -- `M0` bounds the polynomial, `M1` bounds its derivative, both on `Icc (-L) L`.
  obtain ⟨M0, hM0, hM0b⟩ := exists_norm_bound_on_Icc P L
  obtain ⟨M1, hM1, hM1b⟩ := exists_norm_bound_on_Icc P.derivative L
  refine ⟨M0, M1, hM0, hM1, hM0b, ?_⟩
  intro x hx y hy
  -- On the convex set `Icc (-L) L` the function has derivative `P.derivative.eval` (chain rule
  -- through the coercion `ℝ → ℂ`), so the mean value inequality applies.
  have hderiv : ∀ z ∈ Icc (-L) L,
      HasDerivWithinAt (fun t : ℝ => P.eval (t : ℂ)) (P.derivative.eval (z : ℂ))
        (Icc (-L) L) z := by
    intro z _
    exact ((P.hasDerivAt (z : ℂ)).comp_ofReal).hasDerivWithinAt
  have hmvt := (convex_Icc (-L) L).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hM1b hy hx
  calc ‖P.eval (x : ℂ) - P.eval (y : ℂ)‖
      ≤ M1 * ‖(x : ℝ) - y‖ := hmvt
    _ = M1 * |x - y| := by rw [Real.norm_eq_abs]

end RHBoundedWindow


-- Source: integration/PolynomialDomain.lean

open MeasureTheory Set
open scoped ENNReal
namespace RHBoundedWindow
open RHFormDomain

/-- Interval hypotheses only; the conclusion concerns the original double integral. -/
theorem bounded_lipschitz_energy_finite {L : ℝ} (hL : 0 ≤ L) (p : ℝ → ℂ)
    {M0 M1 : ℝ} (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hb : BoundedOn L p M0) (hl : LipschitzBoundOn L p M1) :
    energy (extend L p) < ⊤ :=
  energy_finite_of_pointwise hL p M0 M1 (pointwise_bound hL p hM0 hM1 hb hl)

theorem polynomial_energy_finite {L : ℝ} (hL : 0 ≤ L) (P : Polynomial ℂ) :
    energy (extend L (fun x : ℝ => P.eval (x : ℂ))) < ⊤ := by
  obtain ⟨M0,M1,hM0,hM1,hb,hl⟩ := polynomial_bounds P hL
  exact bounded_lipschitz_energy_finite hL _ hM0 hM1 hb hl

lemma polynomial_memLp {L : ℝ} (hL : 0 ≤ L) (P : Polynomial ℂ) :
    MemLp (fun x : ℝ => P.eval (x : ℂ)) 2 (volume.restrict (Icc (-L) L)) := by
  obtain ⟨M0,M1,hM0,hM1,hb,hl⟩ := polynomial_bounds P hL
  exact bounded_memLp L _ (polynomial_measurable P) M0 hb

noncomputable def intervalPolynomial (L : ℝ) (hL : 0 ≤ L) (P : Polynomial ℂ) :
    Lp ℂ 2 (volume.restrict (Icc (-L) L)) :=
  (polynomial_memLp hL P).toLp (fun x : ℝ => P.eval (x : ℂ))

lemma intervalPolynomial_energy {L : ℝ} (hL : 0 ≤ L) (P : Polynomial ℂ) :
    intervalEnergy L (intervalPolynomial L hL P) =
      energy (extend L (fun x : ℝ => P.eval (x : ℂ))) :=
  energy_extend_congr_ae (MemLp.coeFn_toLp (polynomial_memLp hL P))

/-- Membership in the already defined L² form domain, including the a.e. quotient. -/
theorem intervalPolynomial_mem {L : ℝ} (hL : 0 ≤ L) (P : Polynomial ℂ) :
    InDomain L (intervalPolynomial L hL P) := by
  unfold InDomain
  rw [intervalPolynomial_energy]
  exact polynomial_energy_finite hL P

end RHBoundedWindow

