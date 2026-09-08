/-
# Normalize the full-carrier posterior mismatch by its literal target mass

The split connected and disconnected posterior columns have already been
reassembled as one absolute coefficient-defect sum over the original opposite
four-cell target carrier.  This module divides that full-carrier `l1` cost by
the literal physical mass of the same carrier.

The definition is total.  If the target carrier has positive mass, it uses
constructive positive-denominator division.  Otherwise strict positivity of
every two-replica Gibbs weight at positive coupling forces the finite carrier
to be empty, hence its full posterior `l1` cost is exactly zero.  Therefore

```text
fullCarrierPosteriorRelativeCost * fullCarrierTargetMass
  ~= fullCarrierPosteriorL1
```

without a distinct-root/target assumption.  A ceiling on this one scalar is
thus exactly the weakest aggregate full-carrier relative estimate used by the
posterior compiler; it introduces neither a pointwise column bound nor a
carrier-cardinality factor.

This is an exact finite normalization only.  It proves no smallness estimate,
lower spacing law, continuum limit, OS/GNS reconstruction, Hamiltonian gap,
or Clay conclusion.

Constructive contract: finite rational sums, decidable positive-denominator
division, and strict physical weight positivity only; no choice, `Classical`,
`native_decide`, proof hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnCombinedCarrier
import YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
import YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnCombinedCarrierRelativeCost

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnCombinedCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-- The literal physical mass of the full opposite four-cell target carrier. -/
def actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass
    (S : SlabScalePair) (root target : Nat) : Q' :=
  listQSum (slabObservableTwoReplicaPairWeight S.coarse)
    (slabObservableFourCellTargetPairs S.coarse root target)

/-- The full target-carrier mass is nonnegative. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass_nonnegative
    (S : SlabScalePair) (root target : Nat) :
    (0 : Q') ≤
      actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass
        S root target := by
  unfold actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass
  apply listQSum_nonnegative_on
  intro receiver _
  exact slabObservableTwoReplicaPairWeight_nonnegative
    S.coarse root receiver

/-- At positive coupling, nonpositive full-carrier mass can occur only when
the carrier is empty.  This closes the zero-denominator branch constructively. -/
theorem slabObservableFourCellTargetPairs_eq_nil_of_targetMass_not_pos
    (S : SlabScalePair) (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (hmass : ¬ (0 : Q') <
      actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass
        S root target) :
    slabObservableFourCellTargetPairs S.coarse root target = [] := by
  cases hcarrier :
      slabObservableFourCellTargetPairs S.coarse root target with
  | nil => rfl
  | cons receiver tail =>
      exfalso
      apply hmass
      unfold actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass
      rw [hcarrier]
      exact Q'.pos_add_nonneg
        (slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
          S.coarse hcoarseCoupling receiver)
        (listQSum_nonnegative_on
          (slabObservableTwoReplicaPairWeight S.coarse) tail
          (fun item _ =>
            slabObservableTwoReplicaPairWeight_nonnegative
              S.coarse root item))

/-- The one total scalar left by exact full-carrier posterior normalization. -/
def actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  let mass :=
    actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass
      S root target
  let l1 :=
    actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1
      S hfineCutoff hcoarseCoupling root target htarget
  if hmass : (0 : Q') < mass then Q'.divPos l1 mass hmass else 0

/-- Total normalization is exact, including the empty-carrier branch. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost_mul_targetMass_eqv_densityL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost
          S hfineCutoff hcoarseCoupling root target htarget *
        actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass
          S root target ≈
      actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1
        S hfineCutoff hcoarseCoupling root target htarget := by
  let mass :=
    actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass
      S root target
  let l1 :=
    actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1
      S hfineCutoff hcoarseCoupling root target htarget
  by_cases hmass : (0 : Q') < mass
  · unfold actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost
    change (if h : (0 : Q') < mass then
      Q'.divPos l1 mass h else 0) * mass ≈ l1
    rw [dif_pos hmass]
    exact Q'.divPos_mul_eqv l1 mass hmass
  · have hcarrier :
        slabObservableFourCellTargetPairs S.coarse root target = [] := by
      apply slabObservableFourCellTargetPairs_eq_nil_of_targetMass_not_pos
        S hcoarseCoupling root target
      simpa only [mass] using hmass
    have hl1 : l1 ≈ (0 : Q') := by
      unfold l1
        actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1
      rw [hcarrier]
      exact Q'.eqv_refl 0
    unfold actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost
    change (if h : (0 : Q') < mass then
      Q'.divPos l1 mass h else 0) * mass ≈ l1
    rw [dif_neg hmass]
    exact Q'.eqv_trans _ 0 _
      (Q'.zero_mul_eqv mass) (Q'.eqv_symm hl1)

/-- A ceiling on the normalized scalar implies the literal full-carrier
posterior estimate, with no pointwise hypothesis or carrier-size loss. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1_le_of_relativeCost_le
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent)
    (ceiling : Q')
    (hcost :
      actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost
          S hfineCutoff hcoarseCoupling root target htarget ≤ ceiling) :
    actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1
        S hfineCutoff hcoarseCoupling root target htarget ≤
      ceiling *
        actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass
          S root target := by
  let cost :=
    actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost
      S hfineCutoff hcoarseCoupling root target htarget
  let mass :=
    actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass
      S root target
  let l1 :=
    actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1
      S hfineCutoff hcoarseCoupling root target htarget
  have hidentity : cost * mass ≈ l1 := by
    simpa only [cost, mass, l1] using
      actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost_mul_targetMass_eqv_densityL1
        S hfineCutoff hcoarseCoupling root target htarget
  have hscaled : cost * mass ≤ ceiling * mass :=
    Q'.mul_le_mul_of_nonneg_right cost ceiling mass
      (by simpa only [cost] using hcost)
      (by simpa only [mass] using
        (actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass_nonnegative
          S root target))
  simpa only [l1, mass] using
    Q'.le_trans' l1 (cost * mass) (ceiling * mass)
      (Q'.ge_of_eqv hidentity) hscaled

/-- Conversely, any nonnegative aggregate full-carrier ceiling bounds the
total normalized scalar.  Together with the preceding theorem, this makes
the scalar and literal aggregate formulations constructively equivalent. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost_le_of_densityL1_le
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent)
    (ceiling : Q') (hceiling : (0 : Q') ≤ ceiling)
    (hl1 :
      actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1
          S hfineCutoff hcoarseCoupling root target htarget ≤
        ceiling *
          actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass
            S root target) :
    actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost
        S hfineCutoff hcoarseCoupling root target htarget ≤ ceiling := by
  let mass :=
    actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass
      S root target
  let l1 :=
    actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1
      S hfineCutoff hcoarseCoupling root target htarget
  by_cases hmass : (0 : Q') < mass
  · unfold actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost
    change (if h : (0 : Q') < mass then
      Q'.divPos l1 mass h else 0) ≤ ceiling
    rw [dif_pos hmass]
    apply Q'.divPos_le_of_le_mul l1 mass hmass
    simpa only [l1, mass] using hl1
  · unfold actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost
    change (if h : (0 : Q') < mass then
      Q'.divPos l1 mass h else 0) ≤ ceiling
    rw [dif_neg hmass]
    exact hceiling

#print axioms actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass
#print axioms actualPositiveExpandedReceiverFiberScaleDefectFullCarrierTargetMass_nonnegative
#print axioms slabObservableFourCellTargetPairs_eq_nil_of_targetMass_not_pos
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost_mul_targetMass_eqv_densityL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnDensityL1_le_of_relativeCost_le
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCombinedPosteriorColumnRelativeCost_le_of_densityL1_le

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnCombinedCarrierRelativeCost
