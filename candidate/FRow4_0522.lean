import FY4_0522
import FamDataA_0522

/-! # 0522: the F-stage row function for m = 4. -/

namespace RHFRow4_0522
open RHBall0504 RHBallVec0504 RHBallDot0509 RHPrBall0511 RHG6Core0522 RHFamDefs0522

def fRow (A : List Ball) : List Ball :=
  (List.zip RHFamB_0522.famB4 RHFY4_0522.Y).map (fun p =>
    mulB (2 ^ 256) (alphaB 4) (add (mulB (2 ^ 256) RHConst0521.ell4 (dB (2 ^ 256) A p.1)) (dotB (2 ^ 256) A p.2)))

end RHFRow4_0522
