import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate

open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate
open YMGap.Continuum

private abbrev PE := RingNormaliser.PolyExpr

private def zAdd : List PE → List PE → List PE
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => .add a b :: zAdd p q

private def zScale (a : PE) : List PE → List PE
  | [] => []
  | b :: q => .mul a b :: zScale a q

private def zShift : List PE → List PE
  | [] => []
  | q => .const 0 :: q

private def zMul : List PE → List PE → List PE
  | [], _ => []
  | a :: p, q => zAdd (zScale a q) (zShift (zMul p q))

private def zNeg : List PE → List PE
  | [] => []
  | a :: p => .neg a :: zNeg p

private def zPow (p : List PE) : Nat → List PE
  | 0 => [.const 1]
  | n + 1 => zMul (zPow p n) p

private def zRows : PE → List PE
  | .const c => [.const c]
  | .var i => if i = 1 then [.const 0, .const 1] else [.var i]
  | .add a b => zAdd (zRows a) (zRows b)
  | .mul a b => zMul (zRows a) (zRows b)
  | .neg a => zNeg (zRows a)
  | .pow a n => zPow (zRows a) n

#eval (zRows pExactLowerHigh).length
