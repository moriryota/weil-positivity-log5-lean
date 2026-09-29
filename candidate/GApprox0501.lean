import RkApprox0500

/-! # 0501: certified approximation of the analytic part `g` of the Archimedean tail `T`

With `Gq b = ∫₀^b Q(s/2) ds = 2·ev (integL ql) (b/2)` (`Q = ql` from 0500):
for `0 < b ≤ log 5`,
`|T(b) + log b + Gq b − (2 log 2 + π/2)| ≤ 2·10⁻²⁴ · b`.

Proof: `F = T + log + Gq` has `F' = −(Rk − Q(·/2))` (`T' = −K`, 0459 `hasDerivAt_T_tail`), so the
mean value theorem and `Rk_approx` give `|F b − F δ| ≤ ε (b − δ)`; and `F δ → 2 log 2 + π/2` as
`δ → 0⁺` (artanh = half-log, slope of `1 − e^{−δ/2}` → 1/2, `arctan 1 = π/4`). -/

open Filter Topology Set
open scoped BigOperators

namespace RHGApprox0501
open RHPolyL0500 RHRkApprox0500

def integAux : ℕ → List ℚ → List ℚ
  | _, [] => []
  | k, c :: p => c / (k + 1) :: integAux (k + 1) p

/-- Antiderivative (vanishing at 0) of a list polynomial. -/
def integL (p : List ℚ) : List ℚ := 0 :: integAux 0 p

lemma hasDerivAt_integAux : ∀ (p : List ℚ) (k : ℕ) (t : ℝ),
    HasDerivAt (fun t => t ^ (k + 1) * ev (integAux k p) t) (t ^ k * ev p t) t
  | [], k, t => by
      simp only [integAux, ev, mul_zero]; exact hasDerivAt_const t 0
  | c :: p, k, t => by
      have ih := hasDerivAt_integAux p (k + 1) t
      have h1 := (hasDerivAt_pow (k + 1) t).const_mul (((c / (k + 1) : ℚ) : ℝ))
      have h := h1.add ih
      have hf : (fun t => t ^ (k + 1) * ev (integAux k (c :: p)) t) =
          fun t => ((c / (k + 1) : ℚ) : ℝ) * t ^ (k + 1) +
            t ^ (k + 1 + 1) * ev (integAux (k + 1) p) t := by
        funext t; simp only [integAux, ev]; ring
      rw [hf]
      convert h using 1
      simp only [ev, Nat.add_sub_cancel]
      push_cast
      have hk : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring

lemma hasDerivAt_integL (p : List ℚ) (t : ℝ) :
    HasDerivAt (fun t => ev (integL p) t) (ev p t) t := by
  have h := hasDerivAt_integAux p 0 t
  simp only [zero_add, pow_one, pow_zero, one_mul] at h
  convert h using 1
  funext t; simp [integL, ev]

/-- `Gq b = ∫₀^b Q(s/2) ds`. -/
noncomputable def Gq (b : ℝ) : ℝ := 2 * ev (integL ql) (b / 2)

lemma hasDerivAt_Gq (b : ℝ) : HasDerivAt Gq (ev ql (b / 2)) b := by
  have h := ((hasDerivAt_integL ql (b / 2)).comp b ((hasDerivAt_id b).div_const 2)).const_mul 2
  have hf : Gq = fun y => 2 * ((fun t => ev (integL ql) t) ∘ fun x => id x / 2) y := by
    funext y; simp [Gq]
  rw [hf]
  convert h using 1
  ring

lemma Gq_zero : Gq 0 = 0 := by simp [Gq, integL, ev]

lemma continuous_Gq : Continuous Gq :=
  continuous_iff_continuousAt.mpr (fun b => (hasDerivAt_Gq b).continuousAt)

noncomputable def F (b : ℝ) : ℝ := RH_Rebaseline.T_tail b + Real.log b + Gq b

lemma hasDerivAt_F {b : ℝ} (hb : 0 < b) :
    HasDerivAt F (-(RHColDecomp0499.Rk b - ev ql (b / 2))) b := by
  have h := ((RH_Rebaseline.hasDerivAt_T_tail hb).add (Real.hasDerivAt_log hb.ne')).add
    (hasDerivAt_Gq b)
  convert h using 1
  · funext x; rfl
  · unfold RHColDecomp0499.Rk
    have : RH_GammaFinalFormula.K_kernel b = RH_Rebaseline.K_kernel b := rfl
    rw [this]; ring

lemma F_diff {δ b : ℝ} (hδ : 0 < δ) (hδb : δ ≤ b) (hb : b ≤ Real.log 5) :
    |F b - F δ| ≤ 2 / 10 ^ 24 * (b - δ) := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := F)
    (f' := fun x => -(RHColDecomp0499.Rk x - ev ql (x / 2))) (s := Icc δ b) (C := 2 / 10 ^ 24)
    (fun x hx => (hasDerivAt_F (hδ.trans_le hx.1)).hasDerivWithinAt)
    (fun x hx => by
      rw [Real.norm_eq_abs, abs_neg]
      exact Rk_approx (hδ.trans_le hx.1) (hx.2.trans hb))
    (convex_Icc δ b) ⟨le_rfl, hδb⟩ ⟨hδb, le_rfl⟩
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ b - δ)] at h

/-- `F δ = log(1+z) − log((1−z)/δ) + 2 arctan z + Gq δ`, `z = e^{−δ/2}`. -/
lemma F_eq {δ : ℝ} (hδ : 0 < δ) :
    F δ = Real.log (1 + Real.exp (-δ / 2)) - Real.log ((1 - Real.exp (-δ / 2)) / δ) +
      2 * Real.arctan (Real.exp (-δ / 2)) + Gq δ := by
  set z := Real.exp (-δ / 2) with hz
  have hz0 : 0 < z := Real.exp_pos _
  have hz1 : z < 1 := by rw [hz, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  unfold F RH_Rebaseline.T_tail
  rw [← hz, Real.artanh_eq_half_log ⟨by linarith, hz1.le⟩,
    Real.log_div (by linarith) (by linarith), Real.log_div (by linarith) hδ.ne']
  ring

lemma slope_lim :
    Tendsto (fun δ : ℝ => (1 - Real.exp (-δ / 2)) / δ) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have hd : HasDerivAt (fun δ : ℝ => 1 - Real.exp (-δ / 2)) (1 / 2) 0 := by
    have h := ((Real.hasDerivAt_exp (-(0:ℝ) / 2)).comp 0
      (((hasDerivAt_id (0:ℝ)).neg).div_const 2)).const_sub 1
    convert h using 1
    all_goals norm_num
  have h := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono _ (fun x (hx : x ∈ Ioi (0:ℝ)) => (ne_of_gt hx : x ≠ 0)))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ _
  simp [slope_def_field, div_eq_inv_mul]

lemma F_lim : Tendsto F (𝓝[>] 0) (𝓝 (2 * Real.log 2 + Real.pi / 2)) := by
  have hz : Tendsto (fun δ : ℝ => Real.exp (-δ / 2)) (𝓝[>] 0) (𝓝 1) := by
    have : Continuous (fun δ : ℝ => Real.exp (-δ / 2)) := by fun_prop
    have h := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using h
  have h1 : Tendsto (fun δ : ℝ => Real.log (1 + Real.exp (-δ / 2))) (𝓝[>] 0) (𝓝 (Real.log 2)) := by
    have h := ((Real.continuousAt_log (by norm_num : (1 + 1 : ℝ) ≠ 0)).tendsto).comp
      (tendsto_const_nhds.add hz)
    rw [show (1 + 1 : ℝ) = 2 by norm_num] at h
    exact h
  have h2 : Tendsto (fun δ : ℝ => Real.log ((1 - Real.exp (-δ / 2)) / δ)) (𝓝[>] 0)
      (𝓝 (Real.log (1 / 2))) :=
    ((Real.continuousAt_log (by norm_num : (1 / 2 : ℝ) ≠ 0)).tendsto).comp slope_lim
  have h3 : Tendsto (fun δ : ℝ => 2 * Real.arctan (Real.exp (-δ / 2))) (𝓝[>] 0)
      (𝓝 (2 * Real.arctan 1)) :=
    tendsto_const_nhds.mul ((Real.continuous_arctan.tendsto 1).comp hz)
  have h4 : Tendsto Gq (𝓝[>] 0) (𝓝 0) := by
    have h := (continuous_Gq.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rwa [Gq_zero] at h
  have h := ((h1.sub h2).add h3).add h4
  rw [Real.arctan_one, one_div, Real.log_inv] at h
  have e : Real.log 2 - -Real.log 2 + 2 * (Real.pi / 4) + 0 = 2 * Real.log 2 + Real.pi / 2 := by ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [F_eq hδ]

/-- Main result: `|T(b) + log b + Gq b − (2 log 2 + π/2)| ≤ 2·10⁻²⁴·b` on `(0, log 5]`. -/
theorem g_approx {b : ℝ} (hb : 0 < b) (hb5 : b ≤ Real.log 5) :
    |RH_Rebaseline.T_tail b + Real.log b + Gq b - (2 * Real.log 2 + Real.pi / 2)| ≤
      2 / 10 ^ 24 * b := by
  have hlim : Tendsto (fun δ => |F b - F δ|) (𝓝[>] 0)
      (𝓝 |F b - (2 * Real.log 2 + Real.pi / 2)|) :=
    (tendsto_const_nhds.sub F_lim).abs
  have hev : ∀ᶠ δ in 𝓝[>] (0:ℝ), |F b - F δ| ≤ 2 / 10 ^ 24 * b := by
    filter_upwards [Ioo_mem_nhdsGT hb] with δ hδ
    have h1 := F_diff hδ.1 hδ.2.le hb5
    have h2 : (0:ℝ) ≤ 2 / 10 ^ 24 * δ := by have := hδ.1; positivity
    linarith
  have hle := le_of_tendsto hlim hev
  simpa only [F] using hle

end RHGApprox0501

