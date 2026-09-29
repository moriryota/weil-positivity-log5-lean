import RawPythagoras
import ShiftChain
import PrimeFiber
import Mathlib.MeasureTheory.Group.Integral
open MeasureTheory Set
namespace RHRawPrimeGap
open RHPrimeConstants RHRawProjection

theorem prime24_gap {L a : ℝ} (u : ℝ → ℝ) (hu : MemLp u 2 volume)
    (ha : 0<a) (h2 : 2*a ≤ 2*L) (h3 : 2*L ≤ 3*a) :
    2*alpha a*(∫ t in Ico (-L) (L-a), u t*u (t+a)) +
      2*beta a*(∫ t in Ico (-L) (L-2*a), u t*u (t+2*a)) ≤
    lam a*(∫ t in Ico (-L) L, (u t)^2) -
      (lam a-alpha a)*(∫ t in Ico (-L) L, (u t-project L a ratio u t)^2) := by
  let g : ℝ → ℝ := fun t => lam a*(u t)^2 - (lam a-alpha a)*(u t-project L a ratio u t)^2
  let q : ℝ → ℝ := fun t => 2*alpha a*(u t*u (t+a)+u (t+a)*u (t+2*a)) +
    2*beta a*(u t*u (t+2*a))
  let b : ℝ → ℝ := fun t => 2*alpha a*(u t*u (t+a))
  have hiu := square_integrable hu
  have hip := project_memLp L a ratio hu
  have hir := square_integrable (show MemLp (fun t => u t-project L a ratio u t) 2 volume from hu.sub hip)
  have hig : Integrable g volume := (hiu.const_mul (lam a)).sub (hir.const_mul (lam a-alpha a))
  have hc1 := RHZeroExtension.correlation_integrable hu hu a
  have hc2 := RHZeroExtension.correlation_integrable hu hu (2*a)
  have hc3 := RHZeroExtension.correlation_integrable (RHZeroExtension.translate_memLp hu a) hu (2*a)
  have hiq : Integrable q volume := ((hc1.add hc3).const_mul (2*alpha a)).add (hc2.const_mul (2*beta a))
  have hib : Integrable b volume := hc1.const_mul (2*alpha a)
  have hig1 : Integrable (fun t => g (t+a)) volume := hig.comp_add_right a
  have hig2 : Integrable (fun t => g (t+2*a)) volume := hig.comp_add_right (2*a)
  have hit : Integrable (fun t => g t+g (t+a)+g (t+2*a)) volume := (hig.add hig1).add hig2
  have hid : Integrable (fun t => g t+g (t+a)) volume := hig.add hig1
  have htpoint (t : ℝ) (ht : t ∈ Ico (-L) (L-2*a)) : q t ≤ g t+g (t+a)+g (t+2*a) := by
    dsimp only [q,g]
    rw [project_triple_left u ha h2 h3 ht, project_triple_middle u ha h2 h3 ht,
      project_triple_right u ha h2 h3 ht]
    have hh := RHPrimeFiber.three_point_gap ha (u t) (u (t+a)) (u (t+2*a))
    unfold RHThreePoint.form at hh
    nlinarith
  have hbpoint (t : ℝ) (ht : t ∈ Ico (L-2*a) (-L+a)) : b t ≤ g t+g (t+a) := by
    obtain ⟨hz1,hz2⟩ := project_double_zero (r := ratio) u ha h2 h3 ht
    dsimp only [b,g]
    rw [hz1,hz2]
    have hh := RHChainCoordinates.two_point_bound (alpha a) (u t) (u (t+a)) (alpha_pos ha).le
    nlinarith
  have hti : (∫ t in Ico (-L) (L-2*a), q t) ≤
      ∫ t in Ico (-L) (L-2*a), g t+g (t+a)+g (t+2*a) := by
    apply integral_mono_ae hiq.integrableOn hit.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    exact htpoint t ht
  have hbi : (∫ t in Ico (L-2*a) (-L+a), b t) ≤
      ∫ t in Ico (L-2*a) (-L+a), g t+g (t+a) := by
    apply integral_mono_ae hib.integrableOn hid.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    exact hbpoint t ht
  have hweight := RHShiftChain.weighted_product_chain u (alpha a) (beta a)
    (s := -L) (W := 2*L) ha h2 h3 hc1.integrableOn hc2.integrableOn
  have hchain := RHRealChain.integral_chain_decomposition g (-L) (2*L) a ha h2 h3 hig.integrableOn
  simp only [show -L+2*L = L by ring] at hweight hchain
  change _ = (∫ t in Ico (-L) (L-2*a), q t) + (∫ t in Ico (L-2*a) (-L+a), b t) at hweight
  rw [hweight]
  have hsum := add_le_add hti hbi
  rw [← hchain] at hsum
  dsimp only [g] at hsum
  rw [integral_sub (hiu.const_mul (lam a)).integrableOn (hir.const_mul (lam a-alpha a)).integrableOn] at hsum
  dsimp only [b] at hsum ⊢
  simp only [integral_const_mul] at hsum ⊢
  exact hsum

end RHRawPrimeGap
