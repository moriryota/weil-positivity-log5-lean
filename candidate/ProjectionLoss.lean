import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
open scoped RealInnerProductSpace
namespace RHProjectionLoss
noncomputable def gamma (p δ μ : ℝ) : ℝ := p*δ*μ/(δ+μ+p*μ)

theorem gamma_pos {p δ μ : ℝ} (hp : 0<p) (hd : 0<δ) (hm : 0<μ) :
    0 < gamma p δ μ := by
  unfold gamma
  positivity

theorem scalar_loss {p δ μ U v x : ℝ}
    (hp : 0<p) (hd : 0<δ) (hm : 0<μ)
    (hU : p*U ≤ (x+v)^2) :
    gamma p δ μ * (U+v^2) ≤ δ*v^2+μ*x^2 := by
  have hden : 0 < δ+μ+p*μ := by positivity
  have hw : δ*μ*(x+v)^2 ≤ (δ+μ)*(δ*v^2+μ*x^2) := by
    nlinarith [sq_nonneg (δ*v-μ*x)]
  have h1 := mul_le_mul_of_nonneg_left hU (show 0 ≤ δ*μ by positivity)
  have h2 : 0 ≤ p*μ*μ*x^2 := by positivity
  unfold gamma
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith [h1, hw, h2]

theorem norm_loss {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : E →ₗ[ℝ] E) (hC : ∀ z, ‖C z‖ ≤ ‖z‖)
    (u v : E) {p δ μ : ℝ} (hp : 0<p) (hd : 0<δ) (hm : 0<μ)
    (horth : ‖u+v‖^2 = ‖u‖^2+‖v‖^2)
    (hmass : p*‖u‖^2 = ‖C u‖^2) :
    gamma p δ μ * ‖u+v‖^2 ≤ δ*‖v‖^2+μ*‖C (u+v)‖^2 := by
  have he : C u = C (u+v)-C v := by simp
  have ht : ‖C u‖ ≤ ‖C (u+v)‖+‖v‖ := by
    calc
      _ = ‖C (u+v)-C v‖ := congrArg norm he
      _ ≤ ‖C (u+v)‖+‖C v‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl (hC v)
  have hs : p*‖u‖^2 ≤ (‖C (u+v)‖+‖v‖)^2 := by
    rw [hmass]
    nlinarith [mul_self_le_mul_self (norm_nonneg (C u)) ht]
  rw [horth]
  exact scalar_loss hp hd hm hs
theorem joint_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : E →ₗ[ℝ] E) (hC : ∀ z, ‖C z‖ ≤ ‖z‖)
    (u v : E) {p δ μ lam m24 m3 : ℝ} (hp : 0<p) (hd : 0<δ) (hm : 0<μ)
    (horth : ‖u+v‖^2 = ‖u‖^2+‖v‖^2)
    (hmass : p*‖u‖^2 = ‖C u‖^2)
    (h24 : m24 ≤ lam*‖u+v‖^2-δ*‖v‖^2)
    (h3 : m3 ≤ μ*(‖u+v‖^2-‖C (u+v)‖^2)) :
    m24+m3 ≤ (lam+μ-gamma p δ μ)*‖u+v‖^2 := by
  have h := norm_loss C hC u v hp hd hm horth hmass
  nlinarith
end RHProjectionLoss
