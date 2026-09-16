/-
# Finite powers of the actual completed Haar transfer retain original moments

Iterate the already constructed completedTransfer on its existing
ordinary-Haar completion. On dense polynomials these are exactly the
pre-existing iterateStep powers of the actual kinetic and spatial weights.
Pair the output with the terminal V*g, retaining that spatial factor once,
to recover compactNumerator and the original selected-chain numerator.

At zero steps this is the single-slice pairing integral f*V*g. These are
finite-cutoff, finite-time identities, not a stationary limit, operator
cutoff limit, reflected OS identification, contraction or physical gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedHaarTransfer

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedIteration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedHaarTransfer
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBoundedCompletion
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- Finite iteration of the ACTUAL completed map, with the same ordering as iterateStep. -/
def completedIterate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) :
    Nat → GNSCompletionSpace (sliceData width).toGNSData →
      GNSCompletionSpace (sliceData width).toGNSData
  | 0, x => x
  | steps+1, x => completedIterate hw0 hw1 K width hK steps
      (completedTransfer hw0 hw1 K width hK x)

/-- Every finite power has an exact dense pin to the existing actual K/V iterate. -/
theorem completedIterate_embed {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (steps : Nat)
    (f : (sliceData width).toGNSData.V) :
    completedIterate hw0 hw1 K width hK steps (embedV (sliceData width).toGNSData f) =
      embedV (sliceData width).toGNSData
        ⟨iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) steps f.val,
          iterateStep_supported (kineticWeight_supported w K width)
            (spatialWeight_supported w K width) steps f.property⟩ := by
  induction steps generalizing f with
  | zero => rfl
  | succ steps ih =>
      rw [completedIterate, completedTransfer_embed, ih]
      rfl

private theorem haar_inner_embed (blocks : Nat) (f g : (haarData blocks).V) :
    (haarData blocks).cinnerCompl (embedV (haarData blocks) f) (embedV (haarData blocks) g) =
      Quotient.mk CReal.crealSetoid
        (CReal.ofQ' (quaternionHaar blocks (polyMul f.val g.val))) :=
  ((haarData blocks).cinnerCompl_embed f g).trans
    (Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => haarData_pair blocks f g)))

/-- The terminal spatial weight remains explicit and occurs exactly once, even at zero steps. -/
theorem completedIterate_pair_dense {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (steps : Nat)
    (f g : (sliceData width).toGNSData.V) :
    (sliceData width).toGNSData.cinnerCompl
        (completedIterate hw0 hw1 K width hK steps (embedV (sliceData width).toGNSData f))
        (embedV (sliceData width).toGNSData
          ⟨polyMul (spatialWeight w K width) g.val,
            supported_polyMul (spatialWeight_supported w K width) g.property⟩) =
      Quotient.mk CReal.crealSetoid
        (CReal.ofQ' (quaternionHaar (N width)
          (polyMul (iterateStep (N width) (kineticWeight w K width)
            (spatialWeight w K width) steps f.val) (polyMul (spatialWeight w K width) g.val)))) := by
  rw [completedIterate_embed]
  exact haar_inner_embed (N width) _ _

/-- Signed source probes recover the existing compact scalar numerator without rescaling. -/
theorem completedIterate_compactNumerator {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (steps : Nat) (low high : List FaceFactor) :
    (sliceData width).toGNSData.cinnerCompl
        (completedIterate hw0 hw1 K width hK steps
          (embedV (sliceData width).toGNSData ⟨sourceProbe width low, sourceProbe_supported width low⟩))
        (embedV (sliceData width).toGNSData
          ⟨polyMul (spatialWeight w K width) (sourceProbe width high),
            supported_polyMul (spatialWeight_supported w K width) (sourceProbe_supported width high)⟩) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' (compactNumerator w K width steps low high)) :=
  completedIterate_pair_dense hw0 hw1 K width hK steps
    ⟨sourceProbe width low, sourceProbe_supported width low⟩
    ⟨sourceProbe width high, sourceProbe_supported width high⟩

/-- Same original selected action, same endpoint probes, and the same completed power.
The physical/spatial guards justify the previously proved common-sweep moment identity. -/
theorem completedIterate_originalNumerator {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width start steps extent : Nat} (hw : width ≤ extent) (ht : start+steps ≤ extent)
    (K : Nat) (hK : headCutoff w ≤ K) (low high : List FaceFactor)
    (hlow : ∀ f, f ∈ low → f.1 ∈ spatialFaces width)
    (hhigh : ∀ f, f ∈ high → f.1 ∈ spatialFaces width) :
    (sliceData width).toGNSData.cinnerCompl
        (completedIterate hw0 hw1 K width hK steps
          (embedV (sliceData width).toGNSData ⟨sourceProbe width low, sourceProbe_supported width low⟩))
        (embedV (sliceData width).toGNSData
          ⟨polyMul (spatialWeight w K width) (sourceProbe width high),
            supported_polyMul (spatialWeight_supported w K width) (sourceProbe_supported width high)⟩) =
      Quotient.mk CReal.crealSetoid
        (CReal.ofQ' (numerator w (B extent) extent (chainIds extent width start steps)
          (endpointInsertion extent start steps low high) K)) :=
  (completedIterate_compactNumerator hw0 hw1 K width hK steps low high).trans
    (Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun _ => compactNumerator_pin hw ht w K low high hlow hhigh)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedIteration

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedIteration.completedIterate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedIteration.completedIterate_embed
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedIteration.completedIterate_pair_dense
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedIteration.completedIterate_compactNumerator
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedIteration.completedIterate_originalNumerator
