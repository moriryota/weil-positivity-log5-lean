import GammaThm0516
import PrAff0511

/-! # 0516: affine reduction of `OO`, `X`, `F` to Legendre-coefficient sums

For an interval `[lo, hi]` put `b = (hi−lo)/2`, `a = (lo+hi)/2`, `u = a + b t`:
* `OO i k s t = b Σ_j Af b (a−s) i j · Af b (a−t) k j · 2/(2j+1)`   (`lo = max s t − 1`, `hi = 1`);
* `X i k s t  = b Σ_j Af b (a−s) i j · Af b (a+t) k j · 2/(2j+1)`   (`lo = s−1`, `hi = 1−t`);
* `F i k s = b[(log b + log(1+a)) Σ_j A_j B_j 2/(2j+1)
             + Σ_j Σ_j' A_j B_j' ((−1)^{j+j'} M⁺_{jj'} + Mκ_{jj'})]`, `a = s/2`, `b = 1 − s/2`,
  `κ = b/(1+a)`, `A = Af b a i`, `B = Af b (a−s) k`, `Mκ = Mw (log(1+κ·))`.
 -/

open Set MeasureTheory intervalIntegral Finset

namespace RHAffRed0516
open RHLeg0503 RHLegVec0503 RHSingDef0516 RHPairInt0516 RHPrAff0511 RHRec2D0515

lemma aff_sub {lo hi : ℝ} (h : lo < hi) (f : ℝ → ℝ) :
    ∫ u in lo..hi, f u = ((hi - lo) / 2) * ∫ t in (-1:ℝ)..1, f ((hi - lo) / 2 * t + (lo + hi) / 2) := by
  have hb : (hi - lo) / 2 ≠ 0 := by intro h'; linarith
  have e := intervalIntegral.integral_comp_mul_add (a := -1) (b := 1) f hb ((lo + hi) / 2)
  rw [smul_eq_mul] at e
  rw [e, ← mul_assoc, mul_inv_cancel₀ hb, one_mul]
  congr 1 <;> ring

/-- weighted bilinear expansion -/
theorem wbil (w : ℝ → ℝ) (hw : IntervalIntegrable w volume (-1) 1) (i k : ℕ) (α γ₁ γ₂ : ℝ) :
    ∫ t in (-1:ℝ)..1, w t * (p i (α * t + γ₁) * p k (α * t + γ₂)) =
      ∑ j ∈ range (i + 1), ∑ j' ∈ range (k + 1), Af α γ₁ i j * Af α γ₂ k j' * Mw w j j' := by
  have hI : ∀ j j' : ℕ, IntervalIntegrable (fun t => w t * (p j t * p j' t)) volume (-1) 1 :=
    fun j j' => hw.mul_continuousOn ((continuous_p j).mul (continuous_p j')).continuousOn
  have e : (fun t => w t * (p i (α * t + γ₁) * p k (α * t + γ₂))) =
      fun t => ∑ j ∈ range (i + 1), ∑ j' ∈ range (k + 1), Af α γ₁ i j * Af α γ₂ k j' * (w t * (p j t * p j' t)) := by
    funext t; rw [aff_eq, aff_eq]; unfold evV; rw [sum_mul_sum, mul_sum]
    exact sum_congr rfl (fun j _ => by rw [mul_sum]; exact sum_congr rfl (fun j' _ => by ring))
  rw [e, intervalIntegral.integral_finsetSum (fun j _ =>
    (IntervalIntegrable.sum (range (k + 1))
      (f := fun j' t => Af α γ₁ i j * Af α γ₂ k j' * (w t * (p j t * p j' t)))
      (fun j' _ => (hI j j').const_mul _)).congr (fun t _ => by simp [Finset.sum_apply]))]
  refine sum_congr rfl (fun j _ => ?_)
  rw [intervalIntegral.integral_finsetSum (fun j' _ => (hI j j').const_mul _)]
  refine sum_congr rfl (fun j' _ => ?_)
  rw [intervalIntegral.integral_const_mul]; rfl

theorem OO_eq (i k : ℕ) {s t : ℝ} (hs : s < 2) (ht : t < 2) :
    OO i k s t = ((1 - (max s t - 1)) / 2) *
      ∑ j ∈ range (i + 1), Af ((1 - (max s t - 1)) / 2) ((max s t - 1 + 1) / 2 - s) i j *
        Af ((1 - (max s t - 1)) / 2) ((max s t - 1 + 1) / 2 - t) k j * (2 / (2 * j + 1)) := by
  unfold OO
  rw [aff_sub (by have := max_lt hs ht; linarith), ← aff_int]
  congr 1; congr 1; funext x; ring_nf

theorem X_eq (i k : ℕ) {s t : ℝ} (hst : s + t < 2) :
    X i k s t = ((1 - t - (s - 1)) / 2) *
      ∑ j ∈ range (i + 1), Af ((1 - t - (s - 1)) / 2) ((s - 1 + (1 - t)) / 2 - s) i j *
        Af ((1 - t - (s - 1)) / 2) ((s - 1 + (1 - t)) / 2 + t) k j * (2 / (2 * j + 1)) := by
  unfold X
  rw [aff_sub (by linarith), ← aff_int]
  congr 1; congr 1; funext x; ring_nf

end RHAffRed0516

