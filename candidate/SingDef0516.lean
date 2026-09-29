import Kappa0514
import PrSum0511

/-! # 0516: the singular part `φ_n` of the column functions (u = x/L) and basic integrals

`φ_n(u) = ½ log(1−u²) P_n(u) + Σ_{m=2,3,4} w_m (pm_n(σ_m,u) + pp_n(σ_m,u))`, with
`pm_n(s,u) = [s−1 < u] P_n(u−s)`, `pp_n(s,u) = [u ≤ 1−s] P_n(u+s)`, `σ_m = log m / L`.
Indicator integrals over `[−1,1]` reduce to sub-intervals exactly (no a.e. argument).
 -/

open Set MeasureTheory intervalIntegral

namespace RHSingDef0516
open RHLeg0503 RHConditionalLog5 RHLog5Bridge

noncomputable def σ (m : ℕ) : ℝ := Real.log m / halfWidth

noncomputable def pm (n : ℕ) (s u : ℝ) : ℝ := if s - 1 < u then p n (u - s) else 0
noncomputable def pp (n : ℕ) (s u : ℝ) : ℝ := if u ≤ 1 - s then p n (u + s) else 0

noncomputable def lg (u : ℝ) : ℝ := Real.log (1 - u ^ 2)

noncomputable def pr (n : ℕ) (u : ℝ) : ℝ :=
  RHPrSum0511.w2 * (pm n (σ 2) u + pp n (σ 2) u) + RHPrSum0511.w3 * (pm n (σ 3) u + pp n (σ 3) u) +
    RHPrSum0511.w4 * (pm n (σ 4) u + pp n (σ 4) u)

noncomputable def phi (n : ℕ) (u : ℝ) : ℝ := (1 / 2) * lg u * p n u + pr n u

/-! ### Indicator integrals -/

lemma int_gt {c : ℝ} (hc : -1 ≤ c) (hc1 : c ≤ 1) (f : ℝ → ℝ) :
    ∫ u in (-1:ℝ)..1, (if c < u then f u else 0) = ∫ u in c..1, f u := by
  have e : (fun u => if c < u then f u else 0) = (Ioi c).indicator f := by
    funext u; simp [Set.indicator_apply]
  rw [e, intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le hc1,
    setIntegral_indicator measurableSet_Ioi]
  have hs : Ioc (-1:ℝ) 1 ∩ Ioi c = Ioc c 1 := by
    ext u; simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
  rw [hs]

lemma int_le {c : ℝ} (hc : -1 ≤ c) (hc1 : c ≤ 1) (f : ℝ → ℝ) :
    ∫ u in (-1:ℝ)..1, (if u ≤ c then f u else 0) = ∫ u in (-1:ℝ)..c, f u := by
  have e : (fun u => if u ≤ c then f u else 0) = (Iic c).indicator f := by
    funext u; simp [Set.indicator_apply]
  rw [e, intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le hc,
    setIntegral_indicator measurableSet_Iic]
  have hs : Ioc (-1:ℝ) 1 ∩ Iic c = Ioc (-1) c := by
    ext u; simp only [mem_inter_iff, mem_Ioc, mem_Iic]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, h2⟩
  rw [hs]

/-! ### Integrability -/

lemma ii_gt {f : ℝ → ℝ} (hf : IntervalIntegrable f volume (-1) 1) (c : ℝ) :
    IntervalIntegrable (fun u => if c < u then f u else 0) volume (-1) 1 := by
  have e : (fun u => if c < u then f u else 0) = (Ioi c).indicator f := by
    funext u; simp [Set.indicator_apply]
  rw [e]
  exact ⟨hf.1.indicator measurableSet_Ioi, hf.2.indicator measurableSet_Ioi⟩

lemma ii_le {f : ℝ → ℝ} (hf : IntervalIntegrable f volume (-1) 1) (c : ℝ) :
    IntervalIntegrable (fun u => if u ≤ c then f u else 0) volume (-1) 1 := by
  have e : (fun u => if u ≤ c then f u else 0) = (Iic c).indicator f := by
    funext u; simp [Set.indicator_apply]
  rw [e]
  exact ⟨hf.1.indicator measurableSet_Iic, hf.2.indicator measurableSet_Iic⟩

lemma lg_eq {u : ℝ} (h1 : -1 < u) (h2 : u < 1) : lg u = Real.log (1 + u) + Real.log (1 - u) := by
  unfold lg
  rw [← Real.log_mul (by linarith) (by linarith)]
  congr 1; ring

/-- `lg` agrees with `log(1+u) + log(1−u)` on `Ι(−1,1)` except at `u = 1`. -/
lemma lg_ae : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.uIoc (-1:ℝ) 1 → lg u = Real.log (1 + u) + Real.log (1 - u) := by
  filter_upwards [Measure.ae_ne volume 1] with u hne hu
  rw [uIoc_of_le (by norm_num)] at hu
  exact lg_eq hu.1 (lt_of_le_of_ne hu.2 hne)

lemma lg_ii : IntervalIntegrable lg volume (-1) 1 := by
  have h := RHLogMoment0508.log1p_ii.add RHKappa0514.log1m_ii
  refine h.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr ?_)
  filter_upwards [lg_ae] with u hu hu'
  exact (hu hu').symm

end RHSingDef0516

