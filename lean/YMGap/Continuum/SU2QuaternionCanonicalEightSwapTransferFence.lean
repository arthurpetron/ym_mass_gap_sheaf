/-
# The strict boundary swap is not the positive Wilson transfer

The canonical interacting GNS state is now fully constructed, so the generic
isometric-time warning can be tested on an actual observable.  The coordinate
difference `g_0-h_0` has exact interacting squared norm `7/16`, while one raw
boundary swap changes the reflected pairing to `-7/16`.  Hence the full-state
period-two automorphism cannot satisfy the halfspace positivity law.  A
physical transfer must be a compression/conditional expectation, not this raw
swap.
-/

import YMGap.Continuum.SU2QuaternionCanonicalEightWilsonGNS
import YMGap.Continuum.ReferenceWeightTransferConstruction

namespace YMGap.Continuum.SU2QuaternionCanonicalEightSwapTransferFence

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ReferenceWeightTransferConstruction
open YMGap.Continuum.SU2QuaternionCanonicalEightCarrier
open YMGap.Continuum.SU2QuaternionCanonicalEightHaarPairModule
open YMGap.Continuum.SU2QuaternionCanonicalEightWilsonGNS
open YMGap.Continuum.SU2QuaternionCanonicalEightWilsonWeight

def g0Observable8 : Poly8 := [(basisMono8 (gIndex8 0), 1)]
def h0Observable8 : Poly8 := [(basisMono8 (hIndex8 0), 1)]

def antisymmetricCoordinate8 : Poly8 :=
  polyAdd8 g0Observable8 (polySmul8 (-(1 : Q')) h0Observable8)

def sevenSixteenths : Q' := Q'.mkPos 7 16 (by decide)

set_option maxRecDepth 100000 in
theorem antisymmetricCoordinate8_norm_exact :
    (canonicalRetainedWilsonGNSData.B
      antisymmetricCoordinate8 antisymmetricCoordinate8).eqv
        sevenSixteenths := by
  decide

set_option maxRecDepth 100000 in
theorem antisymmetricCoordinate8_reflected_exact :
    (canonicalRetainedWilsonGNSData.B
      (swapPoly8 antisymmetricCoordinate8)
      antisymmetricCoordinate8).eqv (-sevenSixteenths) := by
  decide

/-- Exact witness that the selected full boundary automorphism is not a
positive halfspace transfer on the constructed interacting Wilson GNS state. -/
theorem no_canonicalBoundarySwap_TimeHalfspaceLaw :
    TimeHalfspaceLaw canonicalRetainedBoundarySwapHaarPairGeometry
      canonicalRetained_E_congr canonicalRetained_E_add
      canonicalRetained_E_smul canonicalRetained_E_hconj → False := by
  intro L
  have hpos := L.reflected_positive antisymmetricCoordinate8
  have hneg : (0 : Q') ≤ -sevenSixteenths :=
    Q'.le_trans' _ _ _ hpos
      (Q'.le_of_eqv antisymmetricCoordinate8_reflected_exact)
  exact (by decide : ¬ ((0 : Q') ≤ -sevenSixteenths)) hneg

end YMGap.Continuum.SU2QuaternionCanonicalEightSwapTransferFence

#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightSwapTransferFence.antisymmetricCoordinate8_norm_exact
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightSwapTransferFence.antisymmetricCoordinate8_reflected_exact
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightSwapTransferFence.no_canonicalBoundarySwap_TimeHalfspaceLaw
