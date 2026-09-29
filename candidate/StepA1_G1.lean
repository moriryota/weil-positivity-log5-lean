import TargetFormBinding
import ConditionalLog5
import ConcreteParameters
import ResidualMembership
import TestDefEq
import TestG1Energy
import RealWeilShift
import WeilShiftBound
import OriginalLower
import PrimeShift
import PoleShift
import BandNorm
import WeilShiftIntegration
import G1MembershipAdapter
import PoleOddDischarge
import TailSupport
import EnergyToReal
import TestConjunct1
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.MeasureTheory.Measure.Restrict

open MeasureTheory Set Filter
open RHConditionalLog5 RHResidualMembership RHConcreteParameters RHRealWeil RHWeilShift RHBandNorm RHWeilIntegration RHTargetFormBinding RH_LiteratureBridge RHPoleParity RHLog5Bridge RHActualCorrelation RHPrimeShift RHEnergyToReal RHTestConjunct1 RHG1Energy

namespace RHStepA1G1

/-- Transfer from Lp norm-squared to Lebesgue integral of square. -/
lemma embed_norm_sq (v : ℝ → ℝ) (hv : MemLp v 2 volume) :
    ‖embed v‖^2 = ∫ x, (v x)^2 := by
  rw [← real_inner_self_eq_norm_sq, inner_embed v v hv hv]
  simp [sq]

/-- Shift bound transfer: from spatial_weil_shift to G1 comparison inequality. -/
lemma tail_shift_bound (o : Bool) (u : ℝ → ℝ) (hu : Test u)
    (h_shift : compare (tail o u) + concrete.shift o * (∫ x, (tail o u x)^2) ≤ spatial_weil (tail o u)) :
    compare (tail o u) + concrete.shift o * ‖embed (tail o u)‖^2 ≤ targetQ_real (tail o u) := by
  rw [targetQ_real_eq_spatial_weil, embed_norm_sq (tail o u) (tail_memLp o u hu)]
  exact h_shift

/-- The exact spatial shift bound hypothesis for tail functions. -/
def G1ShiftBound (P : Parameters) : Prop := ∀ o u, Test u →
  compare (tail o u) + P.shift o * (∫ x, (tail o u x)^2) ≤ spatial_weil (tail o u)

/-- Sector-wise shift bounds. -/
def G1EvenShiftBound : Prop := ∀ u, Test u →
  compare (tail false u) + concrete.shift false * (∫ x, (tail false u x)^2) ≤ spatial_weil (tail false u)

def G1OddShiftBound : Prop := ∀ u, Test u →
  compare (tail true u) + concrete.shift true * (∫ x, (tail true u x)^2) ≤ spatial_weil (tail true u)

/-- Equivalence of combined shift bound and sector-wise shift bounds. -/
theorem g1_shift_bound_iff :
    G1ShiftBound concrete ↔ (G1EvenShiftBound ∧ G1OddShiftBound) := by
  constructor
  · intro h
    exact ⟨fun u hu => h false u hu, fun u hu => h true u hu⟩
  · rintro ⟨h_even, h_odd⟩ o u hu
    cases o
    · exact h_even u hu
    · exact h_odd u hu

/-- G1 transfer theorem: G1ShiftBound strictly implies G1 for concrete parameters. -/
theorem g1_of_shift_bound (h : G1ShiftBound concrete) : G1 concrete := by
  intro o u hu
  refine ⟨tail_memLp o u hu, RHG1Energy.tail_energy_finite o u hu, ?_⟩
  exact tail_shift_bound o u hu (h o u hu)

/-- Sector-wise G1 transfer theorem. -/
theorem g1_of_sector_shift_bounds (h_even : G1EvenShiftBound) (h_odd : G1OddShiftBound) : G1 concrete :=
  g1_of_shift_bound (g1_shift_bound_iff.mpr ⟨h_even, h_odd⟩)

/-- Connection to Weil shift bound via Archimedean energy, prime, and pole forms. -/
theorem even_shift_of_analytic
    (h_shift_le : concrete.shift false ≤ c_even)
    (u : ℝ → ℝ) (_hu : Test u)
    (hE : compare (tail false u) + T_tail * (∫ x, (tail false u x)^2) ≤
      (1/4:ℝ)*(∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| *(tail false u x - tail false u y)^2))
    (hprime : 2*∑ n ∈ Finset.range 5,
      ((ArithmeticFunction.vonMangoldt n : ℝ)/Real.sqrt n)*real_autocorr (tail false u) (Real.log n) ≤
      RHPrimeShift.B_prime * (∫ x, (tail false u x)^2))
    (hpole : 0 ≤ 2*(∫ x, tail false u x * Real.cosh (x/2))^2 - 2*(∫ x, tail false u x * Real.sinh (x/2))^2) :
    compare (tail false u) + concrete.shift false * (∫ x, (tail false u x)^2) ≤ spatial_weil (tail false u) := by
  have h_weil := spatial_weil_shift_even (tail false u) (compare (tail false u)) hE hprime hpole
  have h_sq : 0 ≤ ∫ x, (tail false u x)^2 := integral_nonneg (fun x => sq_nonneg _)
  have h_order : concrete.shift false * (∫ x, (tail false u x)^2) ≤ c_even * (∫ x, (tail false u x)^2) :=
    mul_le_mul_of_nonneg_right h_shift_le h_sq
  linarith

theorem odd_shift_of_analytic
    (h_shift_le : concrete.shift true ≤ c_odd)
    (u : ℝ → ℝ) (_hu : Test u)
    (hE : compare (tail true u) + T_tail * (∫ x, (tail true u x)^2) ≤
      (1/4:ℝ)*(∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| *(tail true u x - tail true u y)^2))
    (hprime : 2*∑ n ∈ Finset.range 5,
      ((ArithmeticFunction.vonMangoldt n : ℝ)/Real.sqrt n)*real_autocorr (tail true u) (Real.log n) ≤
      RHPrimeShift.B_prime * (∫ x, (tail true u x)^2))
    (hpole : - P_penalty * (∫ x, (tail true u x)^2) ≤
      2*(∫ x, tail true u x * Real.cosh (x/2))^2 - 2*(∫ x, tail true u x * Real.sinh (x/2))^2) :
    compare (tail true u) + concrete.shift true * (∫ x, (tail true u x)^2) ≤ spatial_weil (tail true u) := by
  have h_weil := spatial_weil_shift_odd (tail true u) (compare (tail true u)) hE hprime hpole
  have h_sq : 0 ≤ ∫ x, (tail true u x)^2 := integral_nonneg (fun x => sq_nonneg _)
  have h_order : concrete.shift true * (∫ x, (tail true u x)^2) ≤ c_odd * (∫ x, (tail true u x)^2) :=
    mul_le_mul_of_nonneg_right h_shift_le h_sq
  linarith

/-- Archimedean energy lower bound for tail functions in sector o. -/
def TailArchimedeanBound (o : Bool) : Prop := ∀ u, Test u →
  compare (tail o u) + T_tail * (∫ x, (tail o u x)^2) ≤
    (1/4:ℝ)*(∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| *(tail o u x - tail o u y)^2)

/-- Prime correlation quadratic upper bound for tail functions in sector o. -/
def TailPrimeBound (o : Bool) : Prop := ∀ u, Test u →
  2*∑ n ∈ Finset.range 5,
    ((ArithmeticFunction.vonMangoldt n : ℝ)/Real.sqrt n)*real_autocorr (tail o u) (Real.log n) ≤
    RHPrimeShift.B_prime * (∫ x, (tail o u x)^2)

/-- Even sector G1 shift bound derived from discharged pole bound. -/
theorem g1_even_shift_bound_of_discharged
    (h_shift : concrete.shift false ≤ c_even)
    (hE : TailArchimedeanBound false)
    (hprime : TailPrimeBound false) :
    G1EvenShiftBound := by
  intro u hu
  exact even_shift_of_analytic_discharged h_shift u hu (hE u hu) (hprime u hu)

/-- Odd sector G1 shift bound derived from discharged pole bound. -/
theorem g1_odd_shift_bound_of_discharged
    (h_shift : concrete.shift true ≤ c_odd)
    (hE : TailArchimedeanBound true)
    (hprime : TailPrimeBound true) :
    G1OddShiftBound := by
  intro u hu
  exact odd_shift_of_analytic_discharged h_shift u hu (hE u hu) (hprime u hu)

/-- Combined G1ShiftBound derived from sector-wise discharged analytic bounds. -/
theorem g1_shift_bound_of_discharged
    (h_shift_even : concrete.shift false ≤ c_even)
    (h_shift_odd : concrete.shift true ≤ c_odd)
    (hE_even : TailArchimedeanBound false)
    (hE_odd : TailArchimedeanBound true)
    (hprime_even : TailPrimeBound false)
    (hprime_odd : TailPrimeBound true) :
    G1ShiftBound concrete :=
  g1_shift_bound_iff.mpr ⟨
    g1_even_shift_bound_of_discharged h_shift_even hE_even hprime_even,
    g1_odd_shift_bound_of_discharged h_shift_odd hE_odd hprime_odd
  ⟩

/-- G1 concrete derived from sector-wise discharged analytic bounds. -/
theorem g1_of_discharged
    (h_shift_even : concrete.shift false ≤ c_even)
    (h_shift_odd : concrete.shift true ≤ c_odd)
    (hE_even : TailArchimedeanBound false)
    (hE_odd : TailArchimedeanBound true)
    (hprime_even : TailPrimeBound false)
    (hprime_odd : TailPrimeBound true) :
    G1 concrete :=
  g1_of_shift_bound (g1_shift_bound_of_discharged h_shift_even h_shift_odd hE_even hE_odd hprime_even hprime_odd)

/-- Structured bundle of analytic prerequisites for G1 tail shift bounds. -/
structure G1AnalyticPrerequisites : Prop where
  shift_even : concrete.shift false ≤ c_even
  shift_odd : concrete.shift true ≤ c_odd
  archimedean : ∀ o, TailArchimedeanBound o
  prime : ∀ o, TailPrimeBound o

theorem g1_shift_bound_of_prerequisites (h : G1AnalyticPrerequisites) :
    G1ShiftBound concrete :=
  g1_shift_bound_of_discharged h.shift_even h.shift_odd (h.archimedean false) (h.archimedean true)
    (h.prime false) (h.prime true)

theorem g1_of_prerequisites (h : G1AnalyticPrerequisites) :
    G1 concrete :=
  g1_of_discharged h.shift_even h.shift_odd (h.archimedean false) (h.archimedean true)
    (h.prime false) (h.prime true)

/-! ### Track 1: Shift Order Reduction & Certified Enclosures -/

/-- The canonical observed 80-digit lower enclosure for c_even from constants.json. -/
noncomputable def c_even_observed_lower : ℝ :=
  (-402335143495720182899444246584910110815483700126924367402028 : ℝ) / 100000000000000000000000000000000000000000000000000000000000

/-- The canonical observed 80-digit lower enclosure for c_odd from constants.json. -/
noncomputable def c_odd_observed_lower : ℝ :=
  (-420276790452293321152102206760793445698173033468994653152435 : ℝ) / 100000000000000000000000000000000000000000000000000000000000

/-- Unconditional rational inequality: concrete even shift is bounded by the observed enclosure. -/
theorem shift_even_le_observed : concrete.shift false ≤ c_even_observed_lower := by
  change RHFixedWeights.shift false ≤ c_even_observed_lower
  unfold RHFixedWeights.shift c_even_observed_lower
  dsimp
  norm_num

/-- Unconditional rational inequality: concrete odd shift is bounded by the observed enclosure. -/
theorem shift_odd_le_observed : concrete.shift true ≤ c_odd_observed_lower := by
  change RHFixedWeights.shift true ≤ c_odd_observed_lower
  unfold RHFixedWeights.shift c_odd_observed_lower
  dsimp
  norm_num

/-- Certified lower enclosure condition for c_even and c_odd. -/
structure ShiftLowerEnclosure : Prop where
  c_even_ge : c_even_observed_lower ≤ c_even
  c_odd_ge : c_odd_observed_lower ≤ c_odd

/-- Shift order reduction: ShiftLowerEnclosure implies shift_even and shift_odd. -/
theorem shift_orders_of_enclosure (h : ShiftLowerEnclosure) :
    concrete.shift false ≤ c_even ∧ concrete.shift true ≤ c_odd :=
  ⟨le_trans shift_even_le_observed h.c_even_ge, le_trans shift_odd_le_observed h.c_odd_ge⟩

/-! ### Track 2: Archimedean Energy Reduction -/

lemma tail_indicator_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (Icc (-(Real.log 5/2)) (Real.log 5/2)).indicator (tail o u) = tail o u := by
  funext x
  by_cases hx : x ∈ Icc (-(Real.log 5/2)) (Real.log 5/2)
  · simp [hx]
  · simp [hx, tail_zero_outside o u hu x hx]

/-- The Archimedean mass-gain lower bound for tail functions derived from OriginalLower. -/
def TailOriginalLowerBound (o : Bool) : Prop := ∀ u, Test u →
  compare (tail o u) + T_tail * (∫ x, (tail o u x)^2) ≤
    (RHFormDomain.energy (fun x => (tail o u x : ℂ))).toReal

/-- The canonical complex restricted Lp representative of tail o u on [-log 5/2, log 5/2]. -/
noncomputable def tail_lp_complex (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    Lp ℂ 2 (volume.restrict (Icc (-(Real.log 5/2)) (Real.log 5/2))) :=
  (((tail_memLp o u hu).restrict (Icc (-(Real.log 5/2)) (Real.log 5/2))).ofReal).toLp (fun x => (tail o u x : ℂ))

lemma tail_lp_complex_coeFn (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (tail_lp_complex o u hu : ℝ → ℂ) =ᵐ[volume.restrict (Icc (-(Real.log 5/2)) (Real.log 5/2))]
    (fun x => (tail o u x : ℂ)) :=
  MemLp.coeFn_toLp (((tail_memLp o u hu).restrict (Icc (-(Real.log 5/2)) (Real.log 5/2))).ofReal)

lemma tail_complex_indicator_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (Icc (-(Real.log 5/2)) (Real.log 5/2)).indicator (fun x => (tail o u x : ℂ)) =
    (fun x => (tail o u x : ℂ)) := by
  funext x
  by_cases hx : x ∈ Icc (-(Real.log 5/2)) (Real.log 5/2)
  · simp [hx]
  · simp [hx, tail_zero_outside o u hu x hx]

lemma tail_lp_complex_norm_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    ‖tail_lp_complex o u hu‖ = ‖embed (tail o u)‖ := by
  let s := Icc (-(Real.log 5/2)) (Real.log 5/2)
  have hs : MeasurableSet s := measurableSet_Icc
  have h_mem := (tail_memLp o u hu).restrict s
  have h_tail_lp : ‖tail_lp_complex o u hu‖ = ENNReal.toReal (eLpNorm (fun x => (tail o u x : ℂ)) 2 (volume.restrict s)) :=
    Lp.norm_toLp (fun x => (tail o u x : ℂ)) h_mem.ofReal
  have hn : eLpNorm (fun x => (tail o u x : ℂ)) 2 (volume.restrict s) = eLpNorm (tail o u) 2 (volume.restrict s) := by
    apply eLpNorm_congr_norm_ae h_mem.ofReal.aestronglyMeasurable h_mem.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by simp)
  have h_ind : eLpNorm (tail o u) 2 (volume.restrict s) = eLpNorm (s.indicator (tail o u)) 2 volume :=
    (eLpNorm_indicator_eq_eLpNorm_restrict hs).symm
  rw [tail_indicator_eq o u hu] at h_ind
  have h_embed : ‖embed (tail o u)‖ = ENNReal.toReal (eLpNorm (tail o u) 2 volume) := by
    simp only [embed, dif_pos (tail_memLp o u hu)]
    exact Lp.norm_toLp (tail o u) (tail_memLp o u hu)
  rw [h_tail_lp, hn, h_ind, h_embed]

lemma tail_lp_complex_norm_sq (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    ‖tail_lp_complex o u hu‖^2 = ∫ x, (tail o u x)^2 := by
  rw [tail_lp_complex_norm_eq o u hu, embed_norm_sq (tail o u) (tail_memLp o u hu)]

lemma tail_lp_complex_compare_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (RHComparisonEnergy.intervalEnergy (Real.log 5/2) (tail_lp_complex o u hu)).toReal =
    compare (tail o u) := by
  unfold RHComparisonEnergy.intervalEnergy
  have h_ae := tail_lp_complex_coeFn o u hu
  have h_energy := RHComparisonEnergy.energy_congr_ae h_ae
  change (RHComparisonEnergy.energy (Real.log 5/2) (tail_lp_complex o u hu)).toReal = compare (tail o u)
  rw [h_energy]
  unfold RHConditionalLog5.compare
  rfl

lemma tail_lp_complex_form_energy_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    RHFormDomain.intervalEnergy (Real.log 5/2) (tail_lp_complex o u hu) =
    RHFormDomain.energy (fun x => (tail o u x : ℂ)) := by
  unfold RHFormDomain.intervalEnergy
  have h_ae := tail_lp_complex_coeFn o u hu
  rw [RHFormDomain.energy_extend_congr_ae h_ae]
  unfold RHFormDomain.extend
  rw [tail_complex_indicator_eq o u hu]

lemma tail_lp_complex_inDomain (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    RHFormDomain.InDomain (Real.log 5/2) (tail_lp_complex o u hu) := by
  unfold RHFormDomain.InDomain
  rw [tail_lp_complex_form_energy_eq o u hu]
  exact RHG1Energy.tail_energy_finite o u hu

/-- Unconditional proof of TailOriginalLowerBound for tail functions:
    discharges Track 2 original lower bound from milestone 0306. -/
theorem tail_original_lower_bound (o : Bool) : TailOriginalLowerBound o := by
  intro u hu
  have h_lower := RHOriginalLower.log5_energy_lower (tail_lp_complex o u hu) (tail_lp_complex_inDomain o u hu)
  have h_comp := tail_lp_complex_compare_eq o u hu
  have h_norm := tail_lp_complex_norm_sq o u hu
  have h_form := tail_lp_complex_form_energy_eq o u hu
  have h_T : RH_Rebaseline.T_tail (Real.log 5 / 2) = T_tail := rfl
  rw [h_comp, h_norm, h_form, h_T] at h_lower
  exact h_lower

/-- Identification / upper bound of the extended form domain energy with the spatial double integral. -/
def FormDomainEnergyLebesgueLe (o : Bool) : Prop := ∀ u, Test u →
  (RHFormDomain.energy (fun x => (tail o u x : ℂ))).toReal ≤
    (1/4:ℝ)*(∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| *(tail o u x - tail o u y)^2)

lemma complex_sub_norm_sq (a b : ℝ) :
    ‖(a : ℂ) - (b : ℂ)‖^2 = (a - b)^2 := by
  have h_sub : (a : ℂ) - (b : ℂ) = ((a - b : ℝ) : ℂ) := by push_cast; rfl
  rw [h_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]

lemma tail_complex_eq_extend (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (fun x => (tail o u x : ℂ)) =
      RHFormDomain.extend halfWidth (fun x => (component o u x : ℂ) - (lowPoly o u).eval (x : ℂ)) := by
  funext x
  by_cases hx : x ∈ Icc (-halfWidth) halfWidth
  · unfold RHFormDomain.extend
    rw [indicator_of_mem hx]
    rw [← low_eq_lowPoly o u x hx]
    simp [tail]
  · unfold RHFormDomain.extend
    rw [indicator_of_notMem hx]
    have htz := tail_zero_outside o u hu x hx
    simp [htz]

lemma tail_complex_measurable (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    Measurable (fun x => (tail o u x : ℂ)) := by
  rw [tail_complex_eq_extend o u hu]
  have hc1 : ContDiff ℝ 1 (fun x => (component o u x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (component_contDiff o u hu)
  have hp_poly : ContDiff ℝ 1 (fun x : ℝ => (lowPoly o u).eval (x : ℂ)) :=
    contDiff_eval_poly_real (lowPoly o u)
  have hp : ContDiff ℝ 1 (fun x => (component o u x : ℂ) - (lowPoly o u).eval (x : ℂ)) :=
    hc1.sub hp_poly
  exact hp.continuous.measurable.indicator measurableSet_Icc

theorem form_domain_energy_lebesgue_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (RHFormDomain.energy (fun x => (tail o u x : ℂ))).toReal =
      (1/4:ℝ) * ∫ x, ∫ y, RH_GammaFinalFormula.K_kernel |x-y| * (tail o u x - tail o u y)^2 := by
  have h_meas := tail_complex_measurable o u hu
  have h_fin := tail_energy_finite o u hu
  have h_toReal := RHEnergyToReal.energy_toReal h_meas h_fin
  rw [h_toReal]
  simp_rw [complex_sub_norm_sq]

/-- Unconditional proof of FormDomainEnergyLebesgueLe:
    identifies the extended form domain energy with the spatial double integral. -/
theorem form_domain_energy_lebesgue_le (o : Bool) : FormDomainEnergyLebesgueLe o := by
  intro u hu
  rw [form_domain_energy_lebesgue_eq o u hu]

/-- Archimedean energy bound reduction connecting OriginalLower to TailArchimedeanBound. -/
theorem tail_archimedean_bound_of_components (o : Bool)
    (h_orig : TailOriginalLowerBound o)
    (h_lebesgue : FormDomainEnergyLebesgueLe o) :
    TailArchimedeanBound o := by
  intro u hu
  exact le_trans (h_orig u hu) (h_lebesgue u hu)

/-- TailArchimedeanBound proved from FormDomainEnergyLebesgueLe:
    eliminates TailOriginalLowerBound as a prerequisite. -/
theorem tail_archimedean_bound_of_lebesgue (o : Bool)
    (h_lebesgue : FormDomainEnergyLebesgueLe o) :
    TailArchimedeanBound o :=
  tail_archimedean_bound_of_components o (tail_original_lower_bound o) h_lebesgue

/-- Unconditional proof of TailArchimedeanBound:
    completely discharges Track 2 Archimedean energy lower bound. -/
theorem tail_archimedean_bound (o : Bool) : TailArchimedeanBound o :=
  tail_archimedean_bound_of_lebesgue o (form_domain_energy_lebesgue_le o)


/-! ### Track 3: Prime Form Bound Reduction -/

/-- Canonical 3-point prime autocorrelation form from milestone 0329. -/
noncomputable def prime_autocorr_form (f : ℝ → ℝ) : ℝ :=
  2 * RHPrimeConstants.alpha (Real.log 2) * real_autocorr f (Real.log 2) +
  2 * RHPrimeConstants.beta (Real.log 2) * real_autocorr f (Real.log 4) +
  2 * RHActualPrime3.mu3 * real_autocorr f (Real.log 3)

/-- Range-5 von Mangoldt prime sum identification with prime_autocorr_form. -/
def Range5PrimeIdent (o : Bool) : Prop := ∀ u, Test u →
  2 * ∑ n ∈ Finset.range 5,
    ((ArithmeticFunction.vonMangoldt n : ℝ)/Real.sqrt n)*real_autocorr (tail o u) (Real.log n) =
  prime_autocorr_form (tail o u)

lemma vm_zero : ArithmeticFunction.vonMangoldt 0 = 0 := ArithmeticFunction.map_zero
lemma vm_one : ArithmeticFunction.vonMangoldt 1 = 0 := ArithmeticFunction.vonMangoldt_apply_one
lemma vm_two : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
lemma vm_three : ArithmeticFunction.vonMangoldt 3 = Real.log 3 := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three
lemma vm_four : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
  have h4 : 4 = 2^2 := rfl
  rw [h4, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  rfl

/-- Completely unconditional proof of the Range-5 prime sum identification. -/
theorem range5_prime_ident (o : Bool) : Range5PrimeIdent o := by
  intro u hu
  unfold prime_autocorr_form RHPrimeConstants.alpha RHPrimeConstants.beta RHActualPrime3.mu3
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [vm_zero, vm_one, vm_two, vm_three, vm_four]
  push_cast
  have hsqrt4 : Real.sqrt 4 = 2 := by
    have h : (4 : ℝ) = 2^2 := by norm_num
    rw [h, Real.sqrt_sq (by norm_num)]
  rw [hsqrt4]
  ring

/-- Upper bound on the 3-point prime autocorrelation form from milestone 0329. -/
def PrimeAutocorrBound (o : Bool) : Prop := ∀ u, Test u →
  prime_autocorr_form (tail o u) ≤ RHPrimeShift.B_prime * (∫ x, (tail o u x)^2)

/-- The canonical restricted Lp representative of tail o u on [-log 5/2, log 5/2]. -/
noncomputable def tail_lp (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    Lp ℝ 2 (volume.restrict (Icc (-(Real.log 5/2)) (Real.log 5/2))) :=
  ((tail_memLp o u hu).restrict (Icc (-(Real.log 5/2)) (Real.log 5/2))).toLp (tail o u)

lemma tail_lp_indicator_ae_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    (Icc (-(Real.log 5/2)) (Real.log 5/2)).indicator (tail_lp o u hu : ℝ → ℝ) =ᵐ[volume] tail o u := by
  let s := Icc (-(Real.log 5/2)) (Real.log 5/2)
  have hs : MeasurableSet s := measurableSet_Icc
  have h_coe := MemLp.coeFn_toLp ((tail_memLp o u hu).restrict s)
  have h_ind : s.indicator (tail_lp o u hu : ℝ → ℝ) =ᵐ[volume] s.indicator (tail o u) :=
    (ae_eq_restrict_iff_indicator_ae_eq hs).mp h_coe
  have h_eq : s.indicator (tail o u) = tail o u := tail_indicator_eq o u hu
  exact h_ind.trans (EventuallyEq.of_eq h_eq)

lemma tail_lp_indicator_shift_ae_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) (d : ℝ) :
    (fun t => (Icc (-(Real.log 5/2)) (Real.log 5/2)).indicator (tail_lp o u hu : ℝ → ℝ) (t - d)) =ᵐ[volume]
    (fun t => tail o u (t - d)) := by
  have h := tail_lp_indicator_ae_eq o u hu
  have ht := (measurePreserving_add_right volume (-d)).quasiMeasurePreserving.tendsto_ae
  have hc := h.comp_tendsto ht
  simpa only [Function.comp_def, sub_eq_add_neg] using hc

lemma tail_lp_autocorr_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) (d : ℝ) :
    autocorr (Real.log 5/2) (tail_lp o u hu) d = real_autocorr (tail o u) d := by
  have h_neg := negative_shift (Real.log 5/2) (tail_lp o u hu) d
  rw [← h_neg]
  unfold real_autocorr
  apply integral_congr_ae
  have h1 := tail_lp_indicator_ae_eq o u hu
  have h2 := tail_lp_indicator_shift_ae_eq o u hu d
  exact h1.mul h2

lemma tail_lp_norm_eq (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    ‖tail_lp o u hu‖ = ‖embed (tail o u)‖ := by
  let s := Icc (-(Real.log 5/2)) (Real.log 5/2)
  have hs : MeasurableSet s := measurableSet_Icc
  have h_mem := tail_memLp o u hu
  have h_tail_lp : ‖tail_lp o u hu‖ = ENNReal.toReal (eLpNorm (tail o u) 2 (volume.restrict s)) :=
    Lp.norm_toLp (tail o u) (h_mem.restrict s)
  have h_ind : eLpNorm (tail o u) 2 (volume.restrict s) = eLpNorm (s.indicator (tail o u)) 2 volume :=
    (eLpNorm_indicator_eq_eLpNorm_restrict hs).symm
  rw [tail_indicator_eq o u hu] at h_ind
  have h_embed : ‖embed (tail o u)‖ = ENNReal.toReal (eLpNorm (tail o u) 2 volume) := by
    simp only [embed, dif_pos h_mem]
    exact Lp.norm_toLp (tail o u) h_mem
  rw [h_tail_lp, h_ind, h_embed]

lemma tail_lp_norm_sq (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    ‖tail_lp o u hu‖^2 = ∫ x, (tail o u x)^2 := by
  rw [tail_lp_norm_eq o u hu, embed_norm_sq (tail o u) (tail_memLp o u hu)]

/-- Exact bridge between the milestone 0329 Lp prime form and the spatial prime autocorrelation form. -/
theorem prime_form_eq_prime_autocorr_form (o : Bool) (u : ℝ → ℝ) (hu : Test u) :
    prime_form (tail_lp o u hu) = prime_autocorr_form (tail o u) := by
  unfold prime_form prime_autocorr_form
  rw [tail_lp_autocorr_eq o u hu (Real.log 2),
      tail_lp_autocorr_eq o u hu (Real.log 4),
      tail_lp_autocorr_eq o u hu (Real.log 3)]

/-- Unconditional discharge of PrimeAutocorrBound for tail functions:
    derived from milestone 0329 (RHPrimeShift.prime_form_le). -/
theorem prime_autocorr_bound (o : Bool) : PrimeAutocorrBound o := by
  intro u hu
  rw [← prime_form_eq_prime_autocorr_form o u hu, ← tail_lp_norm_sq o u hu]
  exact prime_form_le (tail_lp o u hu)

/-- Prime bound reduction connecting the range-5 sum and milestone 0329 to TailPrimeBound. -/
theorem tail_prime_bound_of_components (o : Bool)
    (h_ident : Range5PrimeIdent o)
    (h_bound : PrimeAutocorrBound o) :
    TailPrimeBound o := by
  intro u hu
  rw [h_ident u hu]
  exact h_bound u hu

/-- Reduction from PrimeAutocorrBound to TailPrimeBound:
    eliminates Range5PrimeIdent as a prerequisite. -/
theorem tail_prime_bound_of_prime_bound (o : Bool)
    (h_bound : PrimeAutocorrBound o) :
    TailPrimeBound o :=
  tail_prime_bound_of_components o (range5_prime_ident o) h_bound

/-- Completely unconditional proof of TailPrimeBound for tail functions:
    discharges Track 3 prime bound unconditionally. -/
theorem tail_prime_bound_unconditional (o : Bool) : TailPrimeBound o :=
  tail_prime_bound_of_prime_bound o (prime_autocorr_bound o)

/-! ### Master Assembly for G1AnalyticPrerequisites -/

/-- Master reduction theorem: discharges G1AnalyticPrerequisites from the decomposed
    numerical enclosures, Archimedean bridges, and prime autocorrelation representations. -/
theorem g1_prerequisites_of_components
    (h_shift : ShiftLowerEnclosure)
    (h_orig : ∀ o, TailOriginalLowerBound o)
    (h_lebesgue : ∀ o, FormDomainEnergyLebesgueLe o)
    (h_prime_ident : ∀ o, Range5PrimeIdent o)
    (h_prime_bound : ∀ o, PrimeAutocorrBound o) :
    G1AnalyticPrerequisites := by
  obtain ⟨h_se, h_so⟩ := shift_orders_of_enclosure h_shift
  refine ⟨h_se, h_so, ?_, ?_⟩
  · intro o
    exact tail_archimedean_bound_of_components o (h_orig o) (h_lebesgue o)
  · intro o
    exact tail_prime_bound_of_components o (h_prime_ident o) (h_prime_bound o)

/-- Master G1 shift bound derived from the decomposed analytic and numerical components. -/
theorem g1_shift_bound_of_components
    (h_shift : ShiftLowerEnclosure)
    (h_orig : ∀ o, TailOriginalLowerBound o)
    (h_lebesgue : ∀ o, FormDomainEnergyLebesgueLe o)
    (h_prime_ident : ∀ o, Range5PrimeIdent o)
    (h_prime_bound : ∀ o, PrimeAutocorrBound o) :
    G1ShiftBound concrete :=
  g1_shift_bound_of_prerequisites (g1_prerequisites_of_components h_shift h_orig h_lebesgue h_prime_ident h_prime_bound)

/-- Master G1 concrete derived from the decomposed analytic and numerical components. -/
theorem g1_of_components
    (h_shift : ShiftLowerEnclosure)
    (h_orig : ∀ o, TailOriginalLowerBound o)
    (h_lebesgue : ∀ o, FormDomainEnergyLebesgueLe o)
    (h_prime_ident : ∀ o, Range5PrimeIdent o)
    (h_prime_bound : ∀ o, PrimeAutocorrBound o) :
    G1 concrete :=
  g1_of_prerequisites (g1_prerequisites_of_components h_shift h_orig h_lebesgue h_prime_ident h_prime_bound)

/-- Master G1 prerequisites derived without assuming Range5PrimeIdent (discharged by range5_prime_ident). -/
theorem g1_prerequisites_of_prime_bound
    (h_shift : ShiftLowerEnclosure)
    (h_orig : ∀ o, TailOriginalLowerBound o)
    (h_lebesgue : ∀ o, FormDomainEnergyLebesgueLe o)
    (h_prime_bound : ∀ o, PrimeAutocorrBound o) :
    G1AnalyticPrerequisites :=
  g1_prerequisites_of_components h_shift h_orig h_lebesgue (fun o => range5_prime_ident o) h_prime_bound

theorem g1_shift_bound_of_prime_bound
    (h_shift : ShiftLowerEnclosure)
    (h_orig : ∀ o, TailOriginalLowerBound o)
    (h_lebesgue : ∀ o, FormDomainEnergyLebesgueLe o)
    (h_prime_bound : ∀ o, PrimeAutocorrBound o) :
    G1ShiftBound concrete :=
  g1_shift_bound_of_prerequisites (g1_prerequisites_of_prime_bound h_shift h_orig h_lebesgue h_prime_bound)

theorem g1_of_prime_bound
    (h_shift : ShiftLowerEnclosure)
    (h_orig : ∀ o, TailOriginalLowerBound o)
    (h_lebesgue : ∀ o, FormDomainEnergyLebesgueLe o)
    (h_prime_bound : ∀ o, PrimeAutocorrBound o) :
    G1 concrete :=
  g1_of_prerequisites (g1_prerequisites_of_prime_bound h_shift h_orig h_lebesgue h_prime_bound)

/-- Master G1 prerequisites derived with prime bounds unconditionally discharged,
    parameterized by TailOriginalLowerBound. -/
theorem g1_prerequisites_of_orig_bound
    (h_shift : ShiftLowerEnclosure)
    (h_orig : ∀ o, TailOriginalLowerBound o)
    (h_lebesgue : ∀ o, FormDomainEnergyLebesgueLe o) :
    G1AnalyticPrerequisites :=
  g1_prerequisites_of_components h_shift h_orig h_lebesgue (fun o => range5_prime_ident o) (fun o => prime_autocorr_bound o)

theorem g1_shift_bound_of_orig_bound
    (h_shift : ShiftLowerEnclosure)
    (h_orig : ∀ o, TailOriginalLowerBound o)
    (h_lebesgue : ∀ o, FormDomainEnergyLebesgueLe o) :
    G1ShiftBound concrete :=
  g1_shift_bound_of_prerequisites (g1_prerequisites_of_orig_bound h_shift h_orig h_lebesgue)

theorem g1_of_orig_bound
    (h_shift : ShiftLowerEnclosure)
    (h_orig : ∀ o, TailOriginalLowerBound o)
    (h_lebesgue : ∀ o, FormDomainEnergyLebesgueLe o) :
    G1 concrete :=
  g1_of_prerequisites (g1_prerequisites_of_orig_bound h_shift h_orig h_lebesgue)

/-- Master G1 prerequisites derived with Lebesgue double-integral bound parameterized. -/
theorem g1_prerequisites_of_lebesgue
    (h_shift : ShiftLowerEnclosure)
    (h_lebesgue : ∀ o, FormDomainEnergyLebesgueLe o) :
    G1AnalyticPrerequisites :=
  g1_prerequisites_of_orig_bound h_shift (fun o => tail_original_lower_bound o) h_lebesgue

theorem g1_shift_bound_of_lebesgue
    (h_shift : ShiftLowerEnclosure)
    (h_lebesgue : ∀ o, FormDomainEnergyLebesgueLe o) :
    G1ShiftBound concrete :=
  g1_shift_bound_of_prerequisites (g1_prerequisites_of_lebesgue h_shift h_lebesgue)

theorem g1_of_lebesgue
    (h_shift : ShiftLowerEnclosure)
    (h_lebesgue : ∀ o, FormDomainEnergyLebesgueLe o) :
    G1 concrete :=
  g1_of_prerequisites (g1_prerequisites_of_lebesgue h_shift h_lebesgue)

/-- Master G1 prerequisites derived with ALL analytic tracks unconditionally discharged:
    Track 1 (Poles), Track 2 (OriginalLower + EnergyToReal), Track 3 (PrimeShift).
    Requires only the 80-digit numerical enclosure of the shift parameter. -/
theorem g1_prerequisites_unconditional
    (h_shift : ShiftLowerEnclosure) :
    G1AnalyticPrerequisites :=
  g1_prerequisites_of_lebesgue h_shift (fun o => form_domain_energy_lebesgue_le o)

/-- Master G1 shift bound with all analytic tracks unconditionally discharged. -/
theorem g1_shift_bound_unconditional
    (h_shift : ShiftLowerEnclosure) :
    G1ShiftBound concrete :=
  g1_shift_bound_of_prerequisites (g1_prerequisites_unconditional h_shift)

/-- Master G1 concrete with all analytic tracks unconditionally discharged. -/
theorem g1_unconditional
    (h_shift : ShiftLowerEnclosure) :
    G1 concrete :=
  g1_of_prerequisites (g1_prerequisites_unconditional h_shift)

end RHStepA1G1

