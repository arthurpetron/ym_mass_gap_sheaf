/-
# The actual blocked endpoint marginal is not a free heat marginal

The exact gluedMiddle endpoint identity transports the checked width-two,
cutoff-one face witness to the ORIGINAL ambient middle integral and its
already-computed compressed boundary kernel. Changing the nome or cutoff
of a FREE kinetic vacuum marginal cannot match these endpoint tests.

The witness concerns an unnormalized finite numerator. It assumes neither
positivity of the complete cutoff-one action nor a normalized blocking law.
It does not rule out an interacting coarse action or supply a useful
changing-action relative error, AF survival, or a physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialGluedEndpointMarginal
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeHeatOnlyObstruction

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeGluedHeatOnlyObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticContraction (kineticMap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing (gluedMiddle)
open YMGap.Continuum.BF4ExactSlabFixedSpatialGluedEndpointMarginal
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeHeatOnlyObstruction
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion (firstFaceTrace)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar (plaquette_supported)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.RingNormaliser (qpow)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks

private theorem firstFace_supported : SupportedQuaternionBlocks (N 2) firstFaceTrace :=
  plaquette_supported 2 ((0,0,0,0),.p01)

/-- The original blocked middle retains a nonzero face channel at its
lower endpoint, with its full middle spatial interaction. -/
theorem glued_firstFace_exact {start extent : Nat}
    (hw : 2 ≤ extent) (ht : start+2 ≤ extent) (w : Q') :
    quaternionHaar (B extent)
      (polyMul
        ((BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
          (show start ≤ extent by omega)).polynomial firstFaceTrace)
        (gluedMiddle w 1 extent 2 start)) ≈
      qpow w 12 * (coeffW w 1 + qpow (coeffW w 1) 5 * Q'.mkPos 1 16 (by decide)) :=
  Q'.eqv_trans _ _ _ (glued_lower_endpoint_pairing hw ht w 1 firstFace_supported)
    (tested_original_one_exact w)

/-- Strictness of this exact finite numerator, not cutoff-action positivity. -/
theorem glued_firstFace_positive {start extent : Nat}
    (hw : 2 ≤ extent) (ht : start+2 ≤ extent) {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') < quaternionHaar (B extent)
      (polyMul
        ((BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
          (show start ≤ extent by omega)).polynomial firstFaceTrace)
        (gluedMiddle w 1 extent 2 start)) :=
  Q'.pos_of_lt_of_le (tested_original_one_positive hw0)
    (Q'.ge_of_eqv (glued_lower_endpoint_pairing hw ht w 1 firstFace_supported))

/-- No free heat nome or cutoff matches the ACTUAL blocked endpoint tests. -/
theorem glued_endpoint_not_free {start extent : Nat}
    (hw : 2 ≤ extent) (ht : start+2 ≤ extent) {w : Q'} (hw0 : (0 : Q') < w)
    (wC : Q') (KC : Nat) :
    ¬ (∀ p : RatPoly, SupportedQuaternionBlocks (N 2) p →
      quaternionHaar (B extent)
        (polyMul
          ((BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
            (show start ≤ extent by omega)).polynomial p)
          (gluedMiddle w 1 extent 2 start)) ≈
        quaternionHaar (N 2) (polyMul p (kineticMap wC KC 2 polyOne))) := by
  intro h
  apply original_one_not_free hw0 wC KC
  intro p hp
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (glued_lower_endpoint_pairing hw ht w 1 hp)) (h p hp)

/-- The identical obstruction on the preexisting compressed boundary
carrier, with its original ordering and explicitly compressed endpoint test. -/
theorem compressed_endpoint_not_free {start extent : Nat}
    (hw : 2 ≤ extent) (ht : start+2 ≤ extent) {w : Q'} (hw0 : (0 : Q') < w)
    (wC : Q') (KC : Nat) :
    ¬ (∀ p : RatPoly, SupportedQuaternionBlocks (N 2) p →
      quaternionHaar (BF4ExactSlabFixedSpatialBoundaryCarrier.baseLinks 2).length
        (polyMul
          ((BF4ExactSlabFixedSpatialBoundaryCarrier.embedding hw ht).compress
            ((BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
              (show start ≤ extent by omega)).polynomial p))
          (BF4ExactSlabFixedSpatialBoundaryCarrier.kernel hw ht w 1)) ≈
        quaternionHaar (N 2) (polyMul p (kineticMap wC KC 2 polyOne))) := by
  intro h
  apply original_one_not_free hw0 wC KC
  intro p hp
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (compressed_lower_endpoint_pairing hw ht w 1 hp)) (h p hp)

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeGluedHeatOnlyObstruction

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeGluedHeatOnlyObstruction.glued_firstFace_exact
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeGluedHeatOnlyObstruction.glued_firstFace_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeGluedHeatOnlyObstruction.glued_endpoint_not_free
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeGluedHeatOnlyObstruction.compressed_endpoint_not_free
