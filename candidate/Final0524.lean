import RhoSound0524
import ClaimA0520
import ColParity0520
import T5Final0512
import Caps0494

/-! # 0524: G6c for the concrete parameters and the fixed-width log 5 target, **conditional only on**
`RHInterface0524.AssemblyGoal` (the analytic assembly, delegated). All other inputs are proved:
ClaimA (0520), ColParity (0520), `numBound` (0515–0524 kernel tables), G5c (0512).
RH itself is not claimed. -/

namespace RHFinal0524
open RHConditionalLog5

theorem G6c_of_assembly (hAsm : RHInterface0524.AssemblyGoal) :
    RHCaps0494.G6c RHConcreteParameters.concrete RHT5Final0512.capsNew := by
  have h := hAsm (1 / 10 ^ 14) (1 / 10 ^ 4) (99 / 100) (by norm_num) (by norm_num)
    RHClaimA0520.claimA RHColParity0520.colParity RHRhoSound0524.numBound
  choose W hW using h
  exact RHResidualApprox0494.G6c_of_approx RHT5Final0512.capsNew W (fun o => by
    simpa [RHT5Final0512.capsNew] using hW o)

theorem target_log5_of_assembly (hAsm : RHInterface0524.AssemblyGoal)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hs : ∀ x, f x ≠ 0 → |x| ≤ Real.log 5 / 2) (hn : f ≠ 0) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier => Zeta23.zetaZeroConfig.Wsummand f f (ρ:ℂ)) ∧
    0 < (Zeta23.zetaZeroConfig.W f f).re :=
  RHCaps0494.target_log5_of_G5c_G6c RHT5Final0512.capsNew RHT5Final0512.G5c_concrete
    (G6c_of_assembly hAsm) f hf hs hn

end RHFinal0524

