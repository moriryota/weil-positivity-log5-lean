import ComplexEnergy
namespace RHComplexSpatial
open MeasureTheory RHAutocorrEnergy

set_option maxHeartbeats 800000 in
theorem spatialEnergy_parallelogram {L : ℝ} (hL : 0 < L)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hsu : ∀ x, u x ≠ 0 → |x| ≤ L)
    (hsv : ∀ x, v x ≠ 0 → |x| ≤ L) :
    spatialEnergy (fun x => u x + v x) + spatialEnergy (fun x => u x - v x) =
      2 * spatialEnergy u + 2 * spatialEnergy v := by
  have hp : ∀ x, u x + v x ≠ 0 → |x| ≤ L := by
    intro x hn
    by_contra h
    have hz : u x = 0 := by by_contra hz; exact h (hsu x hz)
    have hw : v x = 0 := by by_contra hw; exact h (hsv x hw)
    exact hn (by simp [hz, hw])
  have hm : ∀ x, u x - v x ≠ 0 → |x| ≤ L := by
    intro x hn
    by_contra h
    have hz : u x = 0 := by by_contra hz; exact h (hsu x hz)
    have hw : v x = 0 := by by_contra hw; exact h (hsv x hw)
    exact hn (by simp [hz, hw])
  let F (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
    RH_GammaFinalFormula.K_kernel |p.1| * (f p.2 - f (p.2-p.1))^2
  have iu : Integrable (F u) (volume.prod volume) :=
    displacement_product_integrable hL hu hsu
  have iv : Integrable (F v) (volume.prod volume) :=
    displacement_product_integrable hL hv hsv
  have ip : Integrable (F (fun x => u x+v x)) (volume.prod volume) :=
    displacement_product_integrable hL (hu.add hv) hp
  have im : Integrable (F (fun x => u x-v x)) (volume.prod volume) :=
    displacement_product_integrable hL (hu.sub hv) hm
  have he : (fun p => F (fun x => u x+v x) p + F (fun x => u x-v x) p) =
      (fun p => 2*F u p+2*F v p) := by
    funext p
    dsimp [F]
    ring
  have hi := congrArg (fun f : ℝ × ℝ → ℝ => ∫ p, f p ∂(volume.prod volume)) he
  rw [integral_add ip im, integral_add (iu.const_mul 2) (iv.const_mul 2),
    integral_const_mul, integral_const_mul] at hi
  rw [real_spatial_product hL (hu.add hv) hp, real_spatial_product hL (hu.sub hv) hm,
    real_spatial_product hL hu hsu, real_spatial_product hL hv hsv]
  change (1/4:ℝ)*(∫ p, F (fun x => u x+v x) p ∂(volume.prod volume)) +
    (1/4:ℝ)*(∫ p, F (fun x => u x-v x) p ∂(volume.prod volume)) =
    2*((1/4:ℝ)*(∫ p, F u p ∂(volume.prod volume))) +
    2*((1/4:ℝ)*(∫ p, F v p ∂(volume.prod volume)))
  linarith
end RHComplexSpatial
