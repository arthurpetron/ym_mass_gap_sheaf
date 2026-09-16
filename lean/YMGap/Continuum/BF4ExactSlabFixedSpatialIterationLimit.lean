/-
# The original selected-action cutoff limit of compact scalar iterates

The compact endpoint pairing and its empty-endpoint partition are pinned
to the SAME original finite-chain numerator and partition. The existing
positive-tail reciprocal therefore normalizes this compact partition,
without normalizing individual layers or asserting T(1)=1.

For fixed geometry and fixed signed endpoint face factors, the normalized
scalar iterate inherits the existing selected-face Cauchy modulus and
converges to that original expectation. Its intermediate polynomial messages
may depend on the cutoff; no convergence of messages or operators is used
or proved. There is no uniformity in width, chain length, nome or spacing,
and no stationary-vacuum, OS-completion or mass-gap assertion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalIteration
import YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalIteration
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

/-- The original endpoint polynomial is fixed while the heat cutoff varies. -/
def endpointInsertion (extent start steps : Nat) (low high : List FaceFactor) : RatPoly :=
  sweptProduct extent 0 (placeProbes start low ++ placeProbes (start+steps) high)

/-- The actual compact scalar iterate, including the terminal spatial weight. -/
def compactNumerator (w : Q') (K width steps : Nat) (low high : List FaceFactor) : Q' :=
  quaternionHaar (N width)
    (polyMul (iterateStep (N width) (kineticWeight w K width)
      (spatialWeight w K width) steps (sourceProbe width low))
      (polyMul (spatialWeight w K width) (sourceProbe width high)))

/-- Empty probes give the compact partition; both source probes are polyOne. -/
def compactPartition (w : Q') (K width steps : Nat) : Q' :=
  compactNumerator w K width steps [] []

private theorem selected_physical (extent width start steps : Nat) :
    ∀ id, id ∈ chainIds extent width start steps → id ∈ slabPhysicalFaceEdges extent :=
  fun _ hi => chainIds_physical hi

/-- Exact identification with the original numerator, not a surrogate action. -/
theorem compactNumerator_pin {width start steps extent : Nat}
    (hw : width ≤ extent) (ht : start+steps ≤ extent) (w : Q') (K : Nat)
    (low high : List FaceFactor)
    (hlow : ∀ f, f ∈ low → f.1 ∈ spatialFaces width)
    (hhigh : ∀ f, f ∈ high → f.1 ∈ spatialFaces width) :
    compactNumerator w K width steps low high ≈
      numerator w (B extent) extent (chainIds extent width start steps)
        (endpointInsertion extent start steps low high) K :=
  Q'.eqv_symm (original_chain_iteration hw ht w K low high hlow hhigh)

/-- The empty/empty compact iterate is exactly the selected original partition. -/
theorem compactPartition_pin {width start steps extent : Nat}
    (hw : width ≤ extent) (ht : start+steps ≤ extent) (w : Q') (K : Nat) :
    compactPartition w K width steps ≈
      heatProductHaar w (B extent) extent (chainIds extent width start steps) K := by
  have h := original_chain_iteration hw ht w K [] []
    (fun _ hm => False.elim (List.not_mem_nil hm))
    (fun _ hm => False.elim (List.not_mem_nil hm))
  change quaternionHaar (B extent)
    (polyMul polyOne (originalChainAction w K extent width start steps)) ≈
      compactPartition w K width steps at h
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm h)
    (haar_of_coeff (RatPolyCoeffEqv.one_mul _))

/-- The existing positive floor applies to this very compact partition. -/
theorem compactPartition_floor (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width start steps extent : Nat} (hw : width ≤ extent) (ht : start+steps ≤ extent)
    (K : Nat) (hK : headCutoff w ≤ K) :
    partitionFloor w (chainIds extent width start steps) ≤ compactPartition w K width steps :=
  Q'.le_trans' _ _ _
    (partition_floor hw0 hw1 extent (chainIds extent width start steps)
      (selected_physical extent width start steps) K hK)
    (Q'.ge_of_eqv (compactPartition_pin hw ht w K))

/-- The ORIGINAL reciprocal cancels the SAME compact partition at each late cutoff. -/
theorem compactPartition_reciprocal (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width start steps extent : Nat} (hw : width ≤ extent) (ht : start+steps ≤ extent)
    (stage : Nat) :
    compactPartition w (headCutoff w+stage) width steps *
        reciprocalTerm w hw0 hw1 extent (chainIds extent width start steps)
          (selected_physical extent width start steps) stage ≈ 1 := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (compactPartition_pin hw ht w (headCutoff w+stage))) ?_
  unfold reciprocalTerm PositiveRationalCauchyReciprocal.term
  exact Q'.mul_recipPos_eqv _ _

/-- The compact scalar iterate normalized by its identified original partition.
Only the explicit initial cutoff segment is discarded. -/
def normalizedScalar (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent width start steps : Nat) (low high : List FaceFactor) (stage : Nat) : Q' :=
  compactNumerator w (headCutoff w+stage) width steps low high *
    reciprocalTerm w hw0 hw1 extent (chainIds extent width start steps)
      (selected_physical extent width start steps) stage

/-- Termwise equality with the pre-existing normalized original scalar stream. -/
theorem normalizedScalar_pin (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width start steps extent : Nat} (hw : width ≤ extent) (ht : start+steps ≤ extent)
    (low high : List FaceFactor)
    (hlow : ∀ f, f ∈ low → f.1 ∈ spatialFaces width)
    (hhigh : ∀ f, f ∈ high → f.1 ∈ spatialFaces width) (stage : Nat) :
    normalizedScalar w hw0 hw1 extent width start steps low high stage ≈
      finiteValue w hw0 hw1 extent (chainIds extent width start steps)
        (selected_physical extent width start steps)
        (endpointInsertion extent start steps low high) stage :=
  Q'.mul_eqv_congr_right _ _ _
    (compactNumerator_pin hw ht w (headCutoff w+stage) low high hlow hhigh)

/-- An explicit Cauchy modulus for the ACTUAL normalized compact scalar iterates.
The modulus is precisely the existing selected-face finiteCauchy modulus. -/
def normalizedCauchy (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width start steps extent : Nat} (hw : width ≤ extent) (ht : start+steps ≤ extent)
    (low high : List FaceFactor)
    (hlow : ∀ f, f ∈ low → f.1 ∈ spatialFaces width)
    (hhigh : ∀ f, f ∈ high → f.1 ∈ spatialFaces width) :
    QCauchy (normalizedScalar w hw0 hw1 extent width start steps low high) where
  M := (finiteCauchy w hw0 hw1 extent (chainIds extent width start steps)
    (selected_physical extent width start steps)
    (endpointInsertion extent start steps low high)).M
  bound := by
    intro epsilon he i j hi hj
    have h := (finiteCauchy w hw0 hw1 extent (chainIds extent width start steps)
      (selected_physical extent width start steps)
      (endpointInsertion extent start steps low high)).bound epsilon he i j hi hj
    have hip := normalizedScalar_pin w hw0 hw1 hw ht low high hlow hhigh i
    have hjp := normalizedScalar_pin w hw0 hw1 hw ht low high hlow hhigh j
    exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hip)
        (Q'.le_trans' _ _ _ h.1
          (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hjp))),
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hjp)
        (Q'.le_trans' _ _ _ h.2
          (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hip)))⟩

theorem normalizedCauchy_modulus (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width start steps extent : Nat} (hw : width ≤ extent) (ht : start+steps ≤ extent)
    (low high : List FaceFactor)
    (hlow : ∀ f, f ∈ low → f.1 ∈ spatialFaces width)
    (hhigh : ∀ f, f ∈ high → f.1 ∈ spatialFaces width) (epsilon : Q') :
    (normalizedCauchy w hw0 hw1 hw ht low high hlow hhigh).M epsilon =
      (finiteCauchy w hw0 hw1 extent (chainIds extent width start steps)
        (selected_physical extent width start steps)
        (endpointInsertion extent start steps low high)).M epsilon := rfl

/-- The compact scalar stream converges to the EXISTING original expectation. -/
theorem normalized_converges (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width start steps extent : Nat} (hw : width ≤ extent) (ht : start+steps ≤ extent)
    (low high : List FaceFactor)
    (hlow : ∀ f, f ∈ low → f.1 ∈ spatialFaces width)
    (hhigh : ∀ f, f ∈ high → f.1 ∈ spatialFaces width) :
    ConvergesTo
      (fun stage => ofQ' (normalizedScalar w hw0 hw1 extent width start steps low high stage))
      (expectation w hw0 hw1 extent (chainIds extent width start steps)
        (selected_physical extent width start steps)
        (endpointInsertion extent start steps low high)) :=
  TrigAddCReal.convergesTo_congr_seq
    (s := fun stage => ofQ' (finiteValue w hw0 hw1 extent (chainIds extent width start steps)
      (selected_physical extent width start steps)
      (endpointInsertion extent start steps low high) stage))
    (fun stage => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => Q'.eqv_symm (normalizedScalar_pin w hw0 hw1 hw ht low high hlow hhigh stage)))
    (finite_converges w hw0 hw1 extent (chainIds extent width start steps)
      (selected_physical extent width start steps)
      (endpointInsertion extent start steps low high))

/-- Completing the compact scalar stream gives the same selected-action CReal,
not a separately assumed limiting state. -/
theorem normalizedLimit_pin (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width start steps extent : Nat} (hw : width ≤ extent) (ht : start+steps ≤ extent)
    (low high : List FaceFactor)
    (hlow : ∀ f, f ∈ low → f.1 ∈ spatialFaces width)
    (hhigh : ∀ f, f ∈ high → f.1 ∈ spatialFaces width) :
    CReal.Equiv
      (ofQ'CauchySeq (normalizedScalar w hw0 hw1 extent width start steps low high)
        (normalizedCauchy w hw0 hw1 hw ht low high hlow hhigh))
      (expectation w hw0 hw1 extent (chainIds extent width start steps)
        (selected_physical extent width start steps)
        (endpointInsertion extent start steps low high)) :=
  Equiv_of_limit_of_equal
    (fun stage => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => normalizedScalar_pin w hw0 hw1 hw ht low high hlow hhigh stage))
    (convergesTo_ofQ'CauchySeq _ (normalizedCauchy w hw0 hw1 hw ht low high hlow hhigh))
    (finite_converges w hw0 hw1 extent (chainIds extent width start steps)
      (selected_physical extent width start steps)
      (endpointInsertion extent start steps low high))

end YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit.endpointInsertion
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit.compactNumerator
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit.compactPartition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit.compactNumerator_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit.compactPartition_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit.compactPartition_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit.compactPartition_reciprocal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit.normalizedScalar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit.normalizedScalar_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit.normalizedCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit.normalizedCauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit.normalized_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit.normalizedLimit_pin
