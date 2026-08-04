/-
# Chunk 10 of the BF4 surface-forest ledger word certificate

This kernel certificate checks four surface masks using only oriented words.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateBridge

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate

def surfaceForestGaugeLedgerWordMaskChunk10 :
    List {candidate // candidate ∈ binarySurfaceMasks} :=
  (binarySurfaceMasks.attach.drop 40).take 4

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 200000 in
theorem surfaceForestGaugeLedgerWordMaskChunk10_all_true :
    surfaceForestGaugeLedgerWordMaskChunk10.all
      surfaceForestGaugeLedgerWordRowCheck = true := by
  decide

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceForestGaugeLedgerWordMaskChunk10_all_true
