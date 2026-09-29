import SingDef0516
import RpExact0506

/-! # 0516: pinned interface between the singular-part computation and Claim A

Canonical sign convention:
* `Sx n x = c_n · φ_n(x/L)` on `|x| < L` (0 outside), with `φ_n = ½ log(1−u²) P_n + prime pieces`
  (`RHSingDef0516.phi`, POSITIVE sign; the polynomial term `log L · b_n` belongs to `Q`).
* `col = Q − Sx` on `(−L, L)`, i.e. `Q := col + Sx`.
* `s_im := ∫ Sx_i · e_m`, `Γ_ik := ∫ Sx_i · Sx_k`, and `W :=` coefficients of `P^o − Π Sx`.

Deliverables of the Claim A side are exactly `ClaimA δ` (for an explicit rational `δ`, target `δ ≤ 1/10^14`)
and `ColParity`. This file contains definitions only. -/

open MeasureTheory

namespace RHInterface0516
open RHLog5Bridge

noncomputable def Sx (n : ℕ) (x : ℝ) : ℝ :=
  if |x| < halfWidth then RHRpExact0506.cc n * RHSingDef0516.phi n (x / halfWidth) else 0

/-- Claim A: the smooth part `col + Sx` is uniformly `δ`-close (a.e. on `(−L,L)`) to a polynomial of degree ≤ 127. -/
def ClaimA (δ : ℝ) : Prop :=
  ∀ (o : Bool) (i : RHConditionalLog5.I), ∃ P : Polynomial ℝ, P.natDegree ≤ 127 ∧
    ∀ᵐ x ∂(volume : Measure ℝ), |x| < halfWidth →
      |RHConditionalLog5.col o i x + Sx (RHConditionalLog5.degree o i) x - P.eval x| ≤ δ

/-- Parity of the column functions. -/
def ColParity : Prop :=
  ∀ (o : Bool) (i : RHConditionalLog5.I), ∀ᵐ x ∂(volume : Measure ℝ),
    RHConditionalLog5.col o i (-x) = (-1) ^ (RHConditionalLog5.degree o i) * RHConditionalLog5.col o i x

end RHInterface0516
