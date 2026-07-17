import YMGap.Continuum.HarmonicLowerSixSecondFluxSign
import YMGap.Continuum.HarmonicLowerSixFirstBlockGeometric

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow

def probeDebtCell (k n : Nat) : Q' :=
  -(Q'.ofNat 4 * lowerSixDiscreteHermiteRemainder k n)

def probeDebtPrefix (k : Nat) : Q' :=
  finSum (fun j => probeDebtCell k (j + 1)) (thetaWindowLeft k)

#eval (probeDebtPrefix 247).num
#eval (probeDebtPrefix 390).num
#eval (probeDebtPrefix 8189).num
