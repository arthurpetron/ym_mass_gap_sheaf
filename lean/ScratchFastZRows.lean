import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate

namespace ScratchFastZRows

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

open YMGap.Continuum
open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate

abbrev PE := RingNormaliser.PolyExpr
abbrev RP := RingNormaliser.RawPoly

private def rConst (c : Int) : RP :=
  RingNormaliser.canon [([], c)]

private def rVar (i : Nat) : RP :=
  [(RingNormaliser.varMono i, 1)]

private def rAdd (a b : RP) : RP :=
  RingNormaliser.canon (a ++ b)

private def rMul (a b : RP) : RP :=
  RingNormaliser.canon (RingNormaliser.rawMul a b)

private def rNeg (a : RP) : RP :=
  RingNormaliser.canon (RingNormaliser.rawNeg a)

private def zAdd : List RP → List RP → List RP
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => rAdd a b :: zAdd p q

private def zScale (a : RP) : List RP → List RP
  | [] => []
  | b :: q => rMul a b :: zScale a q

private def zShift : List RP → List RP
  | [] => []
  | q => rConst 0 :: q

private def zMul : List RP → List RP → List RP
  | [], _ => []
  | a :: p, q => zAdd (zScale a q) (zShift (zMul p q))

private def zNeg : List RP → List RP
  | [] => []
  | a :: p => rNeg a :: zNeg p

private def zPow (p : List RP) : Nat → List RP
  | 0 => [rConst 1]
  | n + 1 => zMul (zPow p n) p

def zFastRows : PE → List RP
  | .const c => [rConst c]
  | .var i => if i = 1 then [rConst 0, rConst 1] else [rVar i]
  | .add a b => zAdd (zFastRows a) (zFastRows b)
  | .mul a b => zMul (zFastRows a) (zFastRows b)
  | .neg a => zNeg (zFastRows a)
  | .pow a n => zPow (zFastRows a) n

theorem zFastRows_length :
    (zFastRows pExactLowerHigh).length = 37 := by decide

theorem zFastRows_coefficients_nonnegative :
    (zFastRows pExactLowerHigh).all RawCoefficientsNonnegative = true := by
  decide

#print axioms zFastRows_length
#print axioms zFastRows_coefficients_nonnegative

end ScratchFastZRows
