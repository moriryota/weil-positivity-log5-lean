import TabCore0515
import CcBall0510
import BallDot0509

/-! # 0521: pinned definition of the ball base row `λ_l(κ) = ∫_{−1}^1 log(1+κt) P_l(t) dt`

Taylor: `log(1+κt) = Σ_{r=1}^R (−1)^{r+1} κ^r t^r / r + E_R(t)`, `|E_R| ≤ κ^{R+1}/(1−κ)`.
`t^r` has Legendre vector `XS^r δ_0` (ball iterate `vX`), so
`λ_l ≈ (2/(2l+1)) · [Σ_r c_r XS^r δ_0]_l`, and the remainder adds `2 κ^{R+1}/(1−κ)` (using `|P_l| ≤ 1`).
Definitions only (the enclosure theorem `lamBase_mem` is a separate deliverable). -/

namespace RHLamDef0521
open RHBall0504 RHBallVec0504 RHBallDot0509 RHCcBall0510

/-- `(u_r, κ^r ball, accumulated Σ_{r'≤r} c_{r'} u_{r'})` after `r` steps, starting from `(δ_0, 1, [])`. -/
def lamIter (S : ℕ) (kB : Ball) : ℕ → List Ball × Ball × List Ball
  | 0 => (vunit S 0, ((S : ℤ), 0), [])
  | r + 1 =>
    let st := lamIter S kB r
    let u := vX st.1
    let pw := mulB S st.2.1 kB
    let c := smul (if r % 2 = 0 then 1 else -1) (r + 1) pw
    (u, pw, vadd st.2.2 (vscaleB S c u))

/-- Remainder radius `⌈2 K^{R+1} S / (S^R (S − K))⌉ + 1`, `K = kB.1 + kB.2` (as a natural number). -/
def lamErr (S : ℕ) (kB : Ball) (R : ℕ) : ℕ :=
  let K := (kB.1 + kB.2).toNat
  let D := S ^ R * (S - K)
  (2 * K ^ (R + 1) * S + D - 1) / D + 1

def lamBase (S : ℕ) (kB : Ball) (R NL : ℕ) : List Ball :=
  mapI (fun l b => ((smul 2 (2 * l + 1) b).1, (smul 2 (2 * l + 1) b).2 + lamErr S kB R)) 0
    (((lamIter S kB R).2.2).take NL)

end RHLamDef0521
