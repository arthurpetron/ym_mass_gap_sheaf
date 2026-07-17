import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticRecovery

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticRecovery
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftScaleStep
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow

def linearSigns (k count : Nat) : List Bool :=
  (List.range count).map (fun j =>
    decide ((0 : Q') ≤ lowerSixScaledLinearDriftCarrier k
      (thetaWindowRight k + 1 + j)))

def suffixPaysPrefix (k : Nat) : Bool :=
  decide (-lowerSixScaledCrossWindowPrefix k ≤
    lowerSixScaledCrossWindowSuffix k)

def prefixSign (k : Nat) : Bool :=
  decide ((0 : Q') ≤ lowerSixScaledCrossWindowPrefix k)

def quadraticPaymentSign (k : Nat) : Bool :=
  decide (-lowerSixScaledLinearCrossPaymentResidual k ≤
    lowerSixScaledQuadraticCrossWindowSuffix k)

def recoveryPaymentSign (k : Nat) : Bool :=
  decide (-lowerSixScaledLinearCrossPaymentResidual k ≤
    lowerSixScaledQuadraticRecoverySuffix k)

#eval linearSigns 48 50
#eval linearSigns 247 50
#eval linearSigns 248 50
#eval linearSigns 646 50
#eval (List.range 24).map (fun i => prefixSign (i + 247))
#eval (List.range 24).map (fun i => suffixPaysPrefix (i + 247))
#eval (List.range 16).map (fun i => quadraticPaymentSign (i + 240))
#eval (List.range 16).map (fun i => recoveryPaymentSign (i + 240))
