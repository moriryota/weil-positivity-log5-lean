import FY2_0522
import FamDataA_0522

/-! # 0522: the F-stage row function for m = 2. -/

namespace RHFRow2_0522
open RHBall0504 RHBallVec0504 RHBallDot0509 RHPrBall0511 RHG6Core0522 RHFamDefs0522

def fRow (A : List Ball) : List Ball :=
  (List.zip RHFamB_0522.famB2 RHFY2_0522.Y).map (fun p =>
    mulB (2 ^ 256) (alphaB 2) (add (mulB (2 ^ 256) RHConst0521.ell2 (dB (2 ^ 256) A p.1)) (dotB (2 ^ 256) A p.2)))

end RHFRow2_0522
