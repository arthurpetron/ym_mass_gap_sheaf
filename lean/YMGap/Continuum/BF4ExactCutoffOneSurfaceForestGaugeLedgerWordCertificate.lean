/-
# Aggregate BF4 surface-forest ledger word certificate

The 128 masks are split into 32 four-mask kernel certificates.  This file
assembles them and exposes the full coordinate semantic theorem.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck00
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck01
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck02
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck03
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck04
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck05
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck06
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck07
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck08
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck09
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck10
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck11
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck12
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck13
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck14
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck15
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck16
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck17
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck18
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck19
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck20
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck21
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck22
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck23
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck24
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck25
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck26
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck27
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck28
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck29
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck30
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCheck31

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

set_option maxRecDepth 1000000
set_option maxHeartbeats 12000000

open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar

private theorem binarySurfaceMasks_attach_eq_word_chunks :
    binarySurfaceMasks.attach =
  surfaceForestGaugeLedgerWordMaskChunk00
    ++ surfaceForestGaugeLedgerWordMaskChunk01
    ++ surfaceForestGaugeLedgerWordMaskChunk02
    ++ surfaceForestGaugeLedgerWordMaskChunk03
    ++ surfaceForestGaugeLedgerWordMaskChunk04
    ++ surfaceForestGaugeLedgerWordMaskChunk05
    ++ surfaceForestGaugeLedgerWordMaskChunk06
    ++ surfaceForestGaugeLedgerWordMaskChunk07
    ++ surfaceForestGaugeLedgerWordMaskChunk08
    ++ surfaceForestGaugeLedgerWordMaskChunk09
    ++ surfaceForestGaugeLedgerWordMaskChunk10
    ++ surfaceForestGaugeLedgerWordMaskChunk11
    ++ surfaceForestGaugeLedgerWordMaskChunk12
    ++ surfaceForestGaugeLedgerWordMaskChunk13
    ++ surfaceForestGaugeLedgerWordMaskChunk14
    ++ surfaceForestGaugeLedgerWordMaskChunk15
    ++ surfaceForestGaugeLedgerWordMaskChunk16
    ++ surfaceForestGaugeLedgerWordMaskChunk17
    ++ surfaceForestGaugeLedgerWordMaskChunk18
    ++ surfaceForestGaugeLedgerWordMaskChunk19
    ++ surfaceForestGaugeLedgerWordMaskChunk20
    ++ surfaceForestGaugeLedgerWordMaskChunk21
    ++ surfaceForestGaugeLedgerWordMaskChunk22
    ++ surfaceForestGaugeLedgerWordMaskChunk23
    ++ surfaceForestGaugeLedgerWordMaskChunk24
    ++ surfaceForestGaugeLedgerWordMaskChunk25
    ++ surfaceForestGaugeLedgerWordMaskChunk26
    ++ surfaceForestGaugeLedgerWordMaskChunk27
    ++ surfaceForestGaugeLedgerWordMaskChunk28
    ++ surfaceForestGaugeLedgerWordMaskChunk29
    ++ surfaceForestGaugeLedgerWordMaskChunk30
    ++ surfaceForestGaugeLedgerWordMaskChunk31 := by
  decide

theorem binarySurfaceForestGaugeLedgerWordCheck_true :
    binarySurfaceForestGaugeLedgerWordCheck = true := by
  unfold binarySurfaceForestGaugeLedgerWordCheck
  rw [binarySurfaceMasks_attach_eq_word_chunks]
  simp only [List.all_append,
    surfaceForestGaugeLedgerWordMaskChunk00_all_true,
    surfaceForestGaugeLedgerWordMaskChunk01_all_true,
    surfaceForestGaugeLedgerWordMaskChunk02_all_true,
    surfaceForestGaugeLedgerWordMaskChunk03_all_true,
    surfaceForestGaugeLedgerWordMaskChunk04_all_true,
    surfaceForestGaugeLedgerWordMaskChunk05_all_true,
    surfaceForestGaugeLedgerWordMaskChunk06_all_true,
    surfaceForestGaugeLedgerWordMaskChunk07_all_true,
    surfaceForestGaugeLedgerWordMaskChunk08_all_true,
    surfaceForestGaugeLedgerWordMaskChunk09_all_true,
    surfaceForestGaugeLedgerWordMaskChunk10_all_true,
    surfaceForestGaugeLedgerWordMaskChunk11_all_true,
    surfaceForestGaugeLedgerWordMaskChunk12_all_true,
    surfaceForestGaugeLedgerWordMaskChunk13_all_true,
    surfaceForestGaugeLedgerWordMaskChunk14_all_true,
    surfaceForestGaugeLedgerWordMaskChunk15_all_true,
    surfaceForestGaugeLedgerWordMaskChunk16_all_true,
    surfaceForestGaugeLedgerWordMaskChunk17_all_true,
    surfaceForestGaugeLedgerWordMaskChunk18_all_true,
    surfaceForestGaugeLedgerWordMaskChunk19_all_true,
    surfaceForestGaugeLedgerWordMaskChunk20_all_true,
    surfaceForestGaugeLedgerWordMaskChunk21_all_true,
    surfaceForestGaugeLedgerWordMaskChunk22_all_true,
    surfaceForestGaugeLedgerWordMaskChunk23_all_true,
    surfaceForestGaugeLedgerWordMaskChunk24_all_true,
    surfaceForestGaugeLedgerWordMaskChunk25_all_true,
    surfaceForestGaugeLedgerWordMaskChunk26_all_true,
    surfaceForestGaugeLedgerWordMaskChunk27_all_true,
    surfaceForestGaugeLedgerWordMaskChunk28_all_true,
    surfaceForestGaugeLedgerWordMaskChunk29_all_true,
    surfaceForestGaugeLedgerWordMaskChunk30_all_true,
    surfaceForestGaugeLedgerWordMaskChunk31_all_true]
  decide

/-- All selected plaquette words agree with the letterwise compiler after
the complete dependent ledger.  This certificate manipulates finite edge
lists only; it never expands a polynomial. -/
theorem binarySurfaceForestGaugeLedgerFaceWordCheck_true :
    binarySurfaceForestGaugeLedgerFaceWordCheck = true := by
  unfold binarySurfaceForestGaugeLedgerFaceWordCheck
  rw [binarySurfaceMasks_attach_eq_word_chunks]
  simp only [List.all_append,
    surfaceForestGaugeLedgerWordMaskChunk00_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk01_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk02_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk03_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk04_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk05_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk06_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk07_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk08_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk09_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk10_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk11_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk12_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk13_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk14_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk15_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk16_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk17_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk18_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk19_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk20_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk21_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk22_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk23_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk24_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk25_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk26_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk27_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk28_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk29_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk30_face_all_true,
    surfaceForestGaugeLedgerWordMaskChunk31_face_all_true]
  decide

theorem surfaceForestGaugeLedgerCoordinateSemantic_coeffEqv
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (hnonzero : mask ≠ 0) (edgeId : Nat) (hedgeId : edgeId < 32)
    (reverse : Bool) :
    PolyQuaternionCoeffEqv
      (applySelectedTranslationStepsQuaternion (by decide : 0 < 31)
        (surfaceForestGaugeTranslationSteps mask hmask)
        (orientedCoordinateQuaternion
          (surfaceActiveBlock edgeId) reverse))
      (paddedSubstitutedSurfaceGaugeEntryQuaternion
        mask (edgeId, reverse)) :=
  surfaceForestGaugeLedgerCoordinateSemantic_coeffEqv_of_wordCheck
    binarySurfaceForestGaugeLedgerWordCheck_true
    mask hmask hnonzero edgeId hedgeId reverse

/-- Public face-level specialization of the complete ledger certificate. -/
theorem surfaceForestGaugeLedgerFaceWordSemantic_coeffEqv
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (hnonzero : mask ≠ 0) (faceId : Nat)
    (hface : faceId ∈ surfaceSelectedCompactFaceIds mask) :
    PolyQuaternionCoeffEqv
      (applySelectedTranslationStepsQuaternion (by decide : 0 < 31)
        (surfaceForestGaugeTranslationSteps mask hmask)
        (compactOrientedQuaternionWord
          (surfaceActiveFaceWord faceId)))
      (reindexPolyQuaternion (identityQuaternionBlockInvolution 32)
        (compactOrientedQuaternionWord
          ((substituteSurfaceGaugeWord mask
            (hypercubeFaceWords.getD faceId [])).map fun substituted =>
              (surfaceActiveBlock substituted.1, substituted.2)))) :=
  surfaceForestGaugeLedgerFaceWordSemantic_coeffEqv_of_checks
    binarySurfaceForestGaugeLedgerWordCheck_true
    binarySurfaceForestGaugeLedgerFaceWordCheck_true
    mask hmask hnonzero faceId hface

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.binarySurfaceForestGaugeLedgerWordCheck_true
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.binarySurfaceForestGaugeLedgerFaceWordCheck_true
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceForestGaugeLedgerCoordinateSemantic_coeffEqv
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck.surfaceForestGaugeLedgerFaceWordSemantic_coeffEqv
