/-
# BF4 forest-gauge face and factor-product bridge

This module lifts the checked action of the complete surface translation
ledger from oriented quaternion words to fundamental face characters and to
the product of every selected face.  It remains non-expanding: the only
finite computation is the chunked word certificate imported below.

## Axiom gate

Finite list induction and the constructive coefficient quotient only.  No
`Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeLedgerWordCertificate

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeFaceProductBridge

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveFactorizedHaar
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordSemantics
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar

/-- The fundamental character of the padded, active-block form of one
rooted-path-substituted selected face word. -/
def paddedActiveSubstitutedSurfaceGaugeFaceFactor
    (mask faceId : Nat) : RatPoly :=
  characterPolynomial
    (reindexPolyQuaternion (identityQuaternionBlockInvolution 32)
      (compactOrientedQuaternionWord
        ((substituteSurfaceGaugeWord mask
          (hypercubeFaceWords.getD faceId [])).map fun substituted =>
            (surfaceActiveBlock substituted.1, substituted.2)))).scalar 1

/-- Padded translated factors in exactly the selected physical-face order. -/
def paddedActiveSubstitutedSurfaceGaugeFactors
    (mask : Nat) : List RatPoly :=
  (surfaceSelectedCompactFaceIds mask).map
    (paddedActiveSubstitutedSurfaceGaugeFaceFactor mask)

/-- Translation of one active selected face factor is coefficientwise equal
to the padded character of its checked rooted-path substitution. -/
theorem applySurfaceForestGaugeLedger_faceFactor_coeffEqv
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (hnonzero : mask ≠ 0) (faceId : Nat)
    (hface : faceId ∈ surfaceSelectedCompactFaceIds mask) :
    RatPolyCoeffEqv
      (applySelectedTranslationSteps (by decide : 0 < 31)
        (surfaceForestGaugeTranslationSteps mask hmask)
        (compactFundamentalWordFactor (surfaceActiveFaceWord faceId)))
      (paddedActiveSubstitutedSurfaceGaugeFaceFactor mask faceId) := by
  have hword := surfaceForestGaugeLedgerFaceWordSemantic_coeffEqv
    mask hmask hnonzero faceId hface
  unfold compactFundamentalWordFactor
    paddedActiveSubstitutedSurfaceGaugeFaceFactor
  change RatPolyCoeffEqv
    (applySelectedTranslationSteps (by decide : 0 < 31)
      (surfaceForestGaugeTranslationSteps mask hmask)
      (polySmul 2
        (compactOrientedQuaternionWord
          (surfaceActiveFaceWord faceId)).scalar))
    (polySmul 2
      (reindexPolyQuaternion (identityQuaternionBlockInvolution 32)
        (compactOrientedQuaternionWord
          ((substituteSurfaceGaugeWord mask
            (hypercubeFaceWords.getD faceId [])).map fun substituted =>
              (surfaceActiveBlock substituted.1, substituted.2)))).scalar)
  exact RatPolyCoeffEqv.trans
    (applySelectedTranslationSteps_smul (by decide : 0 < 31)
      (surfaceForestGaugeTranslationSteps mask hmask) 2
      (compactOrientedQuaternionWord
        (surfaceActiveFaceWord faceId)).scalar)
    (hword.scalar.smul 2)

private theorem selectedCompactFaceIds_nonempty
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (hnonzero : mask ≠ 0) :
    surfaceSelectedCompactFaceIds mask ≠ [] := by
  have hselected := embeddedSurfaceSelectedFaces_nonempty
    mask hmask hnonzero
  have hgeometry := selectedSurfaceLiteralFaceGeometry mask hmask
  intro hnil
  apply hselected
  rw [hgeometry.1, hnil]
  rfl

private theorem translatedFaceFactorProducts_coeffEqv
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (hnonzero : mask ≠ 0) :
    ∀ ids : List Nat,
      (∀ faceId, faceId ∈ ids →
        faceId ∈ surfaceSelectedCompactFaceIds mask) →
      RatPolyCoeffEqv
        (factorProduct (ids.map fun faceId =>
          applySelectedTranslationSteps (by decide : 0 < 31)
            (surfaceForestGaugeTranslationSteps mask hmask)
            (compactFundamentalWordFactor
              (surfaceActiveFaceWord faceId))))
        (factorProduct (ids.map
          (paddedActiveSubstitutedSurfaceGaugeFaceFactor mask))) := by
  intro ids
  induction ids with
  | nil =>
      intro _
      exact RatPolyCoeffEqv.refl polyOne
  | cons faceId rest induction =>
      intro hids
      simp only [List.map_cons, factorProduct]
      exact RatPolyCoeffEqv.mul
        (applySurfaceForestGaugeLedger_faceFactor_coeffEqv
          mask hmask hnonzero faceId
          (hids faceId List.mem_cons_self))
        (induction fun other hother =>
          hids other (List.mem_cons_of_mem faceId hother))

/-- The complete translated selected-face product is coefficientwise equal
to the product of the padded rooted-path-substituted face characters. -/
theorem applySurfaceForestGaugeLedger_activeWordFactorProduct_coeffEqv
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (hnonzero : mask ≠ 0) :
    RatPolyCoeffEqv
      (applySurfaceForestGaugeTranslationLedger mask hmask
        (factorProduct (activeSurfaceSelectedWordFactors mask)))
      (factorProduct
        (paddedActiveSubstitutedSurfaceGaugeFactors mask)) := by
  have hnonemptyIds := selectedCompactFaceIds_nonempty
    mask hmask hnonzero
  have hnonemptyFactors : activeSurfaceSelectedWordFactors mask ≠ [] := by
    unfold activeSurfaceSelectedWordFactors
    simpa using hnonemptyIds
  have hproduct := applySelectedTranslationSteps_factorProduct
    (by decide : 0 < 31)
    (surfaceForestGaugeTranslationSteps mask hmask)
    (activeSurfaceSelectedWordFactors mask) hnonemptyFactors
  have hfactors := translatedFaceFactorProducts_coeffEqv
    mask hmask hnonzero (surfaceSelectedCompactFaceIds mask)
    (fun _ hface => hface)
  exact RatPolyCoeffEqv.trans
    (by simpa [applySurfaceForestGaugeTranslationLedger] using hproduct)
    (by simpa [activeSurfaceSelectedWordFactors,
        paddedActiveSubstitutedSurfaceGaugeFactors] using hfactors)

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeFaceProductBridge

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeFaceProductBridge.applySurfaceForestGaugeLedger_faceFactor_coeffEqv
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeFaceProductBridge.applySurfaceForestGaugeLedger_activeWordFactorProduct_coeffEqv
