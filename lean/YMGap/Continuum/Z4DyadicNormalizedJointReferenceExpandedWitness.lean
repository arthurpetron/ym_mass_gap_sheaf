/-
# Literal witness expansion of the normalized joint reference

The preceding carrier exposes every accepted fine fusion assignment, both
accepted coarse fusion assignments, and the four lowering words whose exact
sum is the coupling-one joint reference numerator.  Here the remaining two
scalar operations are restored without losing that witness structure:

* multiply by the explicit coarse parity-ground heat power;
* divide by the exact product of the two tilted-row normalization masses.

Consequently the existing ground-normalized unit congestion is not an opaque
constant: it is exactly the sum of a duplicate-free finite carrier of literal
SU(2) witnesses, each carrying the same beta-dependent normalization scale.

Constructive contract: exact finite rational algebra only; no classical
choice, proof hole, trusted external computation, computability escape,
heartbeat increase, or new axiom.
-/

import YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
import YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedGroundFractionSum

namespace YMGap.Continuum.Z4DyadicNormalizedJointReferenceExpandedWitness

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinaryJointParityGroundNormalization
open YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedGroundFractionSum
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinaryTargetExcitationCasimirExcess
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_mul_left_local {A : Type}
    (factor : Q') (weight : A -> Q') :
    forall items : List A,
      listQSum (fun item => factor * weight item) items ≈
        factor * listQSum weight items
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv factor)
  | item :: items => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_mul_left_local factor weight items))
        (Q'.eqv_symm
          (Q'.mul_add_eqv factor (weight item) (listQSum weight items)))

/-- Multiplication after positive division can be moved into the numerator.
This small lemma keeps the large dependent witness expressions folded. -/
private theorem divPos_mul_right_eqv_local
    (left right denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos left denominator hdenominator * right ≈
      Q'.divPos (left * right) denominator hdenominator := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv left (Q'.recipPos denominator hdenominator) right) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left left _ _
      (Q'.mul_comm_eqv (Q'.recipPos denominator hdenominator) right)) ?_
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv left right (Q'.recipPos denominator hdenominator))

/-! ## 1. Restore the beta-dependent normalization scale witnesswise -/

/-- The common beta-dependent scale carried by every literal joint witness:
the oriented coarse parity-ground heat power divided by the exact two-row
normalization mass. -/
def finePacketOrientedNormalizedJointExpandedWitnessScale
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S) : Q' :=
  Q'.divPos
    (qpow S.coarse.coupling
      (finePacketOrientedTotalTargetParityGroundCasimir
        S orientation first.1 second.1))
    (finePacketOrientedEnvelopeNormalizationMass S first second)
    (finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling first second)

/-- A literal joint SU(2) witness weighted by its common parity-ground heat
power and exact row normalization. -/
def finePacketOrientedNormalizedJointExpandedWitnessWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (witness : FinePacketOrientedJointUnitExpandedWitness S) : Q' :=
  finePacketOrientedNormalizedJointExpandedWitnessScale
      S hfineCutoff hcoarseCoupling orientation first second *
    finePacketOrientedJointUnitExpandedWitnessWeight S witness

/-- The normalized literal witness carrier remains duplicate-free. -/
theorem finePacketOrientedNormalizedJointExpandedWitnessCarrier_nodup
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hleft : pair.1 ∈ S.coarse.physicalLabellings)
    (hright : pair.2 ∈ S.coarse.physicalLabellings) :
    (finePacketOrientedJointUnitExpandedWitnessCarrier
      S orientation first second pair hleft hright).Nodup :=
  finePacketOrientedJointUnitExpandedWitnessCarrier_nodup
    S orientation first second pair hleft hright

/-! ## 2. Exact contraction to the normalized connected tail -/

/-- The normalized literal witness carrier sums exactly to the parity-ground
reference divided by the complete two-row normalization. -/
theorem finePacketOrientedNormalizedJointExpandedWitnessWeight_total_reference
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hleft : pair.1 ∈ S.coarse.physicalLabellings)
    (hright : pair.2 ∈ S.coarse.physicalLabellings) :
    listQSum
        (finePacketOrientedNormalizedJointExpandedWitnessWeight
          S hfineCutoff hcoarseCoupling orientation first second)
        (finePacketOrientedJointUnitExpandedWitnessCarrier
          S orientation first second pair hleft hright) ≈
      finePacketOrientedNormalizedParityGroundReferenceWeight
        S hfineCutoff hcoarseCoupling orientation first second pair := by
  let scale := finePacketOrientedNormalizedJointExpandedWitnessScale
    S hfineCutoff hcoarseCoupling orientation first second
  let rawWeight := finePacketOrientedJointUnitExpandedWitnessWeight S
  let carrier := finePacketOrientedJointUnitExpandedWitnessCarrier
    S orientation first second pair hleft hright
  have hsum :
      listQSum (fun witness => scale * rawWeight witness) carrier ≈
        scale * listQSum rawWeight carrier :=
    listQSum_mul_left_local scale rawWeight carrier
  have hraw :=
    finePacketOrientedJointUnitExpandedWitnessWeight_total
      S orientation first second pair hleft hright
  refine Q'.eqv_trans _
    (scale * listQSum rawWeight carrier) _ ?_ ?_
  · simpa only [finePacketOrientedNormalizedJointExpandedWitnessWeight,
      scale, rawWeight, carrier] using hsum
  refine Q'.eqv_trans _
    (scale * finePacketOrientedJointUnitReferenceNumerator
      S orientation first.1 second.1 pair) _
    (Q'.mul_eqv_congr_left scale _ _ hraw) ?_
  unfold scale finePacketOrientedNormalizedJointExpandedWitnessScale
  unfold finePacketOrientedNormalizedParityGroundReferenceWeight
    finePacketOrientedJointParityGroundReferenceWeight
    finePacketOrientedJointUnitReferenceNumerator
  exact divPos_mul_right_eqv_local _ _ _ _

/-- Hence the same literal witness sum is exactly the already-established
ground-normalized unit congestion.  This is the normalized carrier required
by the connected component tail, with every dependence on the fine and
coarse couplings still explicit in the statement. -/
theorem finePacketOrientedNormalizedJointExpandedWitnessWeight_total
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hleft : pair.1 ∈ S.coarse.physicalLabellings)
    (hright : pair.2 ∈ S.coarse.physicalLabellings) :
    listQSum
        (finePacketOrientedNormalizedJointExpandedWitnessWeight
          S hfineCutoff hcoarseCoupling orientation first second)
        (finePacketOrientedJointUnitExpandedWitnessCarrier
          S orientation first second pair hleft hright) ≈
      finePacketOrientedGroundNormalizedUnitCongestion
        S hfineCutoff hcoarseCoupling orientation first second pair := by
  exact Q'.eqv_trans _ _ _
    (finePacketOrientedNormalizedJointExpandedWitnessWeight_total_reference
      S hfineCutoff hcoarseCoupling orientation first second pair
        hleft hright)
    (finePacketOrientedReferenceDivRow_eqv_unitCongestion_mul_groundFraction
      S hfineCutoff hcoarseCoupling orientation first second pair)

#print axioms finePacketOrientedNormalizedJointExpandedWitnessScale
#print axioms finePacketOrientedNormalizedJointExpandedWitnessWeight
#print axioms finePacketOrientedNormalizedJointExpandedWitnessCarrier_nodup
#print axioms finePacketOrientedNormalizedJointExpandedWitnessWeight_total_reference
#print axioms finePacketOrientedNormalizedJointExpandedWitnessWeight_total

end YMGap.Continuum.Z4DyadicNormalizedJointReferenceExpandedWitness
