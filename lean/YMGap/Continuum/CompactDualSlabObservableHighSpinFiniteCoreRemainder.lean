/-
# All positive-mass estimates contract to one finite-core remainder

The positive observable-rooted carrier has already been split exactly into an
exterior branch and a core branch.  The core has in turn been split into near
and far anchors, and the far branch into entropy-paid and residual-dominant
certificates.  This module reassociates those exact finite decompositions.

The exterior branch costs at most `8/17` of the physical partition, while the
entropy-paid far branch at radius `32 * floor` costs at most
`50 * (4/5)^(floor+1)`.  What remains is one literal finite-core mass: near
anchors together with the far low-spin residual branch.  No decay or
coercivity is attributed to that remainder.

Constructive contract: exact finite Boolean partitions and rational order
algebra only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableHighSpinCoreResidualSupport

namespace YMGap.Continuum.CompactDualSlabObservableHighSpinFiniteCoreRemainder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyRate
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropySplit
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyTargetTail
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreGeometry
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorContraction
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorPartition
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal branch weights -/

/-- Weight of core certificates whose anchors lie within `radius`. -/
def slabObservableHighSpinNearCoreWeight
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) : Q' :=
  listQSum slabObservableHighSpinCoreCertificateWeight
    (slabObservableHighSpinNearCoreCertificates
      D faceId hface threshold radius)

/-- Weight of entropy-paid certificates in the far core. -/
def slabObservableHighSpinFarCoreEntropyPaidWeight
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) : Q' :=
  listQSum slabObservableHighSpinCoreCertificateWeight
    (slabObservableHighSpinFarCoreEntropyPaidCertificates
      D faceId hface threshold radius)

/-- Weight of residual-dominant certificates in the far core. -/
def slabObservableHighSpinFarCoreEntropyResidualWeight
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) : Q' :=
  listQSum slabObservableHighSpinCoreCertificateWeight
    (slabObservableHighSpinFarCoreEntropyResidualCertificates
      D faceId hface threshold radius)

/-- The sole positive-mass remainder after the exterior and entropy-paid
branches have been estimated: near anchors plus far low-spin residual paths. -/
def slabObservableHighSpinFiniteCoreRemainderWeight
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) : Q' :=
  slabObservableHighSpinNearCoreWeight
      D faceId hface threshold radius +
    slabObservableHighSpinFarCoreEntropyResidualWeight
      D faceId hface threshold radius

/-! ## 2. Exact contraction to the remainder -/

/-- The complete core mass is exactly the entropy-paid far mass plus the
literal finite-core remainder. -/
theorem slabObservableHighSpinCoreSourceWeight_split_entropyPaid_remainder
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) :
    slabObservableHighSpinCoreSourceWeight D faceId hface threshold ≈
      slabObservableHighSpinFarCoreEntropyPaidWeight
          D faceId hface threshold radius +
        slabObservableHighSpinFiniteCoreRemainderWeight
          D faceId hface threshold radius := by
  let near := slabObservableHighSpinNearCoreWeight
    D faceId hface threshold radius
  let far := listQSum slabObservableHighSpinCoreCertificateWeight
    (slabObservableHighSpinFarCoreCertificates
      D faceId hface threshold radius)
  let paid := slabObservableHighSpinFarCoreEntropyPaidWeight
    D faceId hface threshold radius
  let residual := slabObservableHighSpinFarCoreEntropyResidualWeight
    D faceId hface threshold radius
  have hnearFar :
      slabObservableHighSpinCoreSourceWeight D faceId hface threshold ≈
        near + far := by
    exact slabObservableHighSpinCoreSourceWeight_split_near_far
      D faceId hface threshold radius
  have hpaidResidual : far ≈ paid + residual := by
    exact slabObservableHighSpinFarCoreCertificates_entropy_weight_split
      D faceId hface threshold radius
  have hnested :
      slabObservableHighSpinCoreSourceWeight D faceId hface threshold ≈
        near + (paid + residual) :=
    Q'.eqv_trans _ _ _ hnearFar
      (Q'.add_eqv_congr_left near far (paid + residual) hpaidResidual)
  have hreorder : near + (paid + residual) ≈
      paid + (near + residual) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv near paid residual))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right
          (near + paid) (paid + near) residual
          (Q'.add_comm_eqv near paid))
        (Q'.add_assoc_eqv paid near residual))
  exact Q'.eqv_trans _ _ _ hnested hreorder

/-! ## 3. Established branches bounded, one branch exposed -/

/-- **Resolved positive-mass bound.**  At arbitrary `0 < w < 1`, every
group-agnostic positive-mass estimate is discharged.  The only remaining term
is the named finite-core remainder; obtaining correlation decay from it
requires an additional cancellation/coercivity statement and is not asserted
here. -/
theorem slabObservablePositiveSourceWeight_le_resolved_add_finiteCoreRemainder
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) (D : SlabPhysicalData)
    (hD : D = observableCouplingSlabPhysicalData
      w (Q'.le_of_lt hw0) cutoff half)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (floor : Nat) :
    slabObservablePositiveSourceWeight D faceId <=
      Q'.mkPos 8 17 (by decide) * D.physicalPartition +
        ((50 * componentCoreCompletionEntropyCeiling ^ (floor + 1)) *
            D.physicalPartition +
          slabObservableHighSpinFiniteCoreRemainderWeight
            D faceId hface (anchorPaidExteriorThreshold w) (32 * floor)) := by
  let threshold := anchorPaidExteriorThreshold w
  let radius := 32 * floor
  let exteriorBudget := Q'.mkPos 8 17 (by decide) * D.physicalPartition
  let paidBudget :=
    (50 * componentCoreCompletionEntropyCeiling ^ (floor + 1)) *
      D.physicalPartition
  let remainder := slabObservableHighSpinFiniteCoreRemainderWeight
    D faceId hface threshold radius
  have hsource : slabObservablePositiveSourceWeight D faceId <=
      exteriorBudget +
        slabObservableHighSpinCoreSourceWeight D faceId hface threshold := by
    exact slabObservablePositiveSourceWeight_le_eightSeventeenths_add_core
      hw0 hw1 cutoff half D hD faceId hface
  have hcoreSplit :
      slabObservableHighSpinCoreSourceWeight D faceId hface threshold ≈
        slabObservableHighSpinFarCoreEntropyPaidWeight
            D faceId hface threshold radius + remainder := by
    exact slabObservableHighSpinCoreSourceWeight_split_entropyPaid_remainder
      D faceId hface threshold radius
  have hpaid :
      slabObservableHighSpinFarCoreEntropyPaidWeight
          D faceId hface threshold radius <= paidBudget := by
    exact slabObservableHighSpinFarCoreEntropyPaidCertificates_weight_le_partition
      hw0 hw1 cutoff half D hD faceId hface floor
  have hcore :
      slabObservableHighSpinCoreSourceWeight D faceId hface threshold <=
        paidBudget + remainder :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hcoreSplit)
      (Q'.add_le_add hpaid (Q'.le_refl' remainder))
  exact Q'.le_trans' _ _ _ hsource
    (Q'.add_le_add (Q'.le_refl' exteriorBudget) hcore)

#print axioms slabObservableHighSpinNearCoreWeight
#print axioms slabObservableHighSpinFarCoreEntropyPaidWeight
#print axioms slabObservableHighSpinFarCoreEntropyResidualWeight
#print axioms slabObservableHighSpinFiniteCoreRemainderWeight
#print axioms slabObservableHighSpinCoreSourceWeight_split_entropyPaid_remainder
#print axioms slabObservablePositiveSourceWeight_le_resolved_add_finiteCoreRemainder

end YMGap.Continuum.CompactDualSlabObservableHighSpinFiniteCoreRemainder
