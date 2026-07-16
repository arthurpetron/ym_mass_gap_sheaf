/-
# Aggregated separable coefficient rows for the high-branch Base certificate
-/

import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateSeparableRows0
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateSeparableRows1
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateSeparableRows2
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateSeparableRows3
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateSeparableRows4
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateSeparableRows5

namespace YMGap.Continuum.HarmonicLowerSixTailBaseCertificateSeparableRows

def tailBaseScaledPowerRows : List (List Int) :=
  tailBaseScaledPowerRows0 ++ tailBaseScaledPowerRows1 ++
    tailBaseScaledPowerRows2 ++ tailBaseScaledPowerRows3 ++
      tailBaseScaledPowerRows4 ++ tailBaseScaledPowerRows5

def tailBaseXPascalRows : List (List Int) :=
  tailBaseXPascalRows0 ++ tailBaseXPascalRows1 ++
    tailBaseXPascalRows2 ++ tailBaseXPascalRows3 ++
      tailBaseXPascalRows4 ++ tailBaseXPascalRows5

end YMGap.Continuum.HarmonicLowerSixTailBaseCertificateSeparableRows
