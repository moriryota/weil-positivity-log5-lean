import TargetReflection
import SpatialParallelogram
open MeasureTheory
namespace RHTargetFormBinding
open RHAutocorrEnergy RH_LiteratureBridge
set_option maxHeartbeats 1000000

lemma product_integrable (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hc : HasCompactSupport u) : Integrable (fun x => u x*v x) :=
  (hu.mul hv).integrable_of_hasCompactSupport hc.mul_right

lemma integral_product_parallelogram (a b c d : ℝ → ℝ)
    (hp : Integrable (fun x => (a x+b x)*(c x+d x)))
    (hm : Integrable (fun x => (a x-b x)*(c x-d x)))
    (ha : Integrable (fun x => a x*c x))
    (hb : Integrable (fun x => b x*d x)) :
    (∫ x, (a x+b x)*(c x+d x)) + (∫ x, (a x-b x)*(c x-d x)) =
      2*(∫ x, a x*c x)+2*(∫ x, b x*d x) := by
  have hf : (fun x => (a x+b x)*(c x+d x)+(a x-b x)*(c x-d x)) =
      (fun x => 2*(a x*c x)+2*(b x*d x)) := by funext x; ring
  have h := congrArg (fun f : ℝ → ℝ => ∫ x, f x) hf
  rw [integral_add hp hm, integral_add (ha.const_mul 2) (hb.const_mul 2),
    integral_const_mul, integral_const_mul] at h
  exact h

lemma autocorr_parallelogram (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hcu : HasCompactSupport u) (hcv : HasCompactSupport v) (s : ℝ) :
    real_autocorr (fun x => u x+v x) s + real_autocorr (fun x => u x-v x) s =
      2*real_autocorr u s+2*real_autocorr v s := by
  have hus : Continuous (fun x => u (x-s)) := hu.comp (continuous_id.sub continuous_const)
  have hvs : Continuous (fun x => v (x-s)) := hv.comp (continuous_id.sub continuous_const)
  exact integral_product_parallelogram u v (fun x => u (x-s)) (fun x => v (x-s))
    (product_integrable _ _ (hu.add hv) (hus.add hvs) (hcu.add hcv))
    (product_integrable _ _ (hu.sub hv) (hus.sub hvs) (hcu.sub hcv))
    (product_integrable _ _ hu hus hcu) (product_integrable _ _ hv hvs hcv)

lemma norm_integral_parallelogram (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hcu : HasCompactSupport u) (hcv : HasCompactSupport v) :
    (∫ x, (u x+v x)^2)+(∫ x, (u x-v x)^2) =
      2*(∫ x, (u x)^2)+2*(∫ x, (v x)^2) := by
  simpa only [pow_two] using integral_product_parallelogram u v u v
    (product_integrable _ _ (hu.add hv) (hu.add hv) (hcu.add hcv))
    (product_integrable _ _ (hu.sub hv) (hu.sub hv) (hcu.sub hcv))
    (product_integrable _ _ hu hu hcu) (product_integrable _ _ hv hv hcv)

lemma moment_parallelogram (u v w : ℝ → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (hcu : HasCompactSupport u) (hcv : HasCompactSupport v) :
    (∫ x, (u x+v x)*w x)^2+(∫ x, (u x-v x)*w x)^2 =
      2*(∫ x, u x*w x)^2+2*(∫ x, v x*w x)^2 := by
  have iu := product_integrable u w hu hw hcu
  have iv := product_integrable v w hv hw hcv
  simp_rw [add_mul, sub_mul]
  rw [integral_add iu iv, integral_sub iu iv]
  ring

theorem targetQ_real_parallelogram {L : ℝ} (hL : 0 < L)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hsu : ∀ x, u x ≠ 0 → |x| ≤ L)
    (hsv : ∀ x, v x ≠ 0 → |x| ≤ L) :
    targetQ_real (fun x => u x+v x)+targetQ_real (fun x => u x-v x) =
      2*targetQ_real u+2*targetQ_real v := by
  have hcu := compact_real hsu
  have hcv := compact_real hsv
  have hn := norm_integral_parallelogram u v hu.continuous hv.continuous hcu hcv
  have he := RHComplexSpatial.spatialEnergy_parallelogram hL u v hu hv hsu hsv
  have hc := moment_parallelogram u v (fun x => Real.cosh (x/2))
    hu.continuous hv.continuous (by fun_prop) hcu hcv
  have hs := moment_parallelogram u v (fun x => Real.sinh (x/2))
    hu.continuous hv.continuous (by fun_prop) hcu hcv
  let c : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ)/Real.sqrt n
  have hp : (∑ n ∈ Finset.range 5, c n * real_autocorr (fun x => u x+v x) (Real.log n)) +
      (∑ n ∈ Finset.range 5, c n * real_autocorr (fun x => u x-v x) (Real.log n)) =
      2*(∑ n ∈ Finset.range 5, c n * real_autocorr u (Real.log n)) +
      2*(∑ n ∈ Finset.range 5, c n * real_autocorr v (Real.log n)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have h := autocorr_parallelogram u v hu.continuous hv.continuous hcu hcv (Real.log n)
    linear_combination c n * h
  unfold targetQ_real
  change _ = _ at hp
  dsimp only [c] at hp
  linear_combination ((Complex.digamma (1/4:ℂ)).re - Real.log Real.pi) * hn + he + 2*hc - 2*hs - 2*hp
end RHTargetFormBinding
