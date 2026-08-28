/-
# The positive native outward Y/Z target row

Instantiate the complete target compiler on the full linked-list product at
the literal connected outward Y/Z source.  The selected target belongs to
the enumerated heterogeneous target carrier, every selected local SU(2)
coordinate is strictly positive, and therefore the exact whole-product
weight is positive.  The separately compiled native target graph is already
marked-face disconnected.

The product is deliberately kept in its linked-list presentation.  Its
package list is propositionally equal to the older observable product, but
transporting the 1,554-coordinate dependent tuple across that equality is
not used as a proof surrogate for the still-open semantic question: the old
observable success predicate decodes an equal-rank left representative,
whereas this target's strand graph uses its native right-tree basis tag.

Constructive contract: structural finite products and previously proved
local positivity only; no choice, `Classical`, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNativeTargetDisconnection
import YMGap.Continuum.Z4OutwardYZEdgeTouchSlabWholeProductPositivity

namespace YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNativeTargetPositiveRow

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.FiniteBistochasticQKernelProductPositivity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNativeTargetDisconnection
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNativeTargetEdges
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabTargetAssignment
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabWholeProductPositivity

/-! ## 1. The literal linked-list source and target -/

abbrev OutwardYZSwitchLinkedPackagesFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  linkedList.map fun linked =>
    slabPhysicalPairRecouplingPackageAtLink 5
      outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked

def outwardYZSwitchLinkedProductionSourceFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    FiniteBistochasticSourceAssignment
      (OutwardYZSwitchLinkedPackagesFrom linkedList) :=
  slabPhysicalPairRecouplingProductionSourceFrom 1 5
    outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical
    outwardYZSwitchLeftFineWitness.1 outwardYZSwitchRightFineWitness.1
    outwardYZSwitchLeftAssignment_mem outwardYZSwitchRightAssignment_mem
    linkedList

def outwardYZSwitchLinkedTargetFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    FiniteBistochasticTargetAssignment
      (OutwardYZSwitchLinkedPackagesFrom linkedList) :=
  outwardYZSwitchTargetAssignmentFrom linkedList

theorem outwardYZSwitchLinkedTargetFrom_mem
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    outwardYZSwitchLinkedTargetFrom linkedList ∈
      finiteBistochasticTargetAssignments
        (OutwardYZSwitchLinkedPackagesFrom linkedList) :=
  outwardYZSwitchTargetAssignmentFrom_mem linkedList

/-! ## 2. Exact positivity of the selected whole row coordinate -/

theorem outwardYZSwitchLinkedTargetFrom_coordinatewisePositive
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    FiniteBistochasticCoordinatewisePositive
      (outwardYZSwitchLinkedProductionSourceFrom linkedList)
      (outwardYZSwitchLinkedTargetFrom linkedList) :=
  outwardYZSwitchCoordinatewisePositive linkedList
    (outwardYZSwitchLinkedProductionSourceFrom linkedList)
    (outwardYZSwitchLinkedTargetFrom linkedList)

theorem outwardYZSwitchLinkedTargetFrom_weight_pos
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    (0 : Q') < finiteBistochasticProductWeight
      (outwardYZSwitchLinkedProductionSourceFrom linkedList)
      (outwardYZSwitchLinkedTargetFrom linkedList) :=
  finiteBistochasticProductWeight_pos_of_coordinatewise
    (outwardYZSwitchLinkedProductionSourceFrom linkedList)
    (outwardYZSwitchLinkedTargetFrom linkedList)
    (outwardYZSwitchLinkedTargetFrom_coordinatewisePositive linkedList)

/-! ## 3. One certificate contracts positivity and native geometry -/

/-- The same distinguished target compiler now has both halves required by
the finite channel argument: positive measure weight and native marked-face
disconnection.  Interpreting that native graph in the observable success
filter remains a separate, named semantic bridge. -/
structure OutwardYZPositiveRowFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) : Type where
  target_mem : outwardYZSwitchLinkedTargetFrom linkedList ∈
    finiteBistochasticTargetAssignments
      (OutwardYZSwitchLinkedPackagesFrom linkedList)
  coordinatewisePositive : FiniteBistochasticCoordinatewisePositive
    (outwardYZSwitchLinkedProductionSourceFrom linkedList)
    (outwardYZSwitchLinkedTargetFrom linkedList)
  weight_pos : (0 : Q') < finiteBistochasticProductWeight
    (outwardYZSwitchLinkedProductionSourceFrom linkedList)
    (outwardYZSwitchLinkedTargetFrom linkedList)

def outwardYZPositiveRowFrom
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) :
    OutwardYZPositiveRowFrom linkedList :=
  { target_mem := outwardYZSwitchLinkedTargetFrom_mem linkedList
    coordinatewisePositive :=
      outwardYZSwitchLinkedTargetFrom_coordinatewisePositive linkedList
    weight_pos := outwardYZSwitchLinkedTargetFrom_weight_pos linkedList }

structure OutwardYZNativePositiveRowCertificate : Type where
  positiveRow : OutwardYZPositiveRowFrom outwardYZSwitchLinkedList
  nativeDisconnection : OutwardYZNativeTargetDisconnectionCertificate

def outwardYZNativePositiveRowCertificate :
    OutwardYZNativePositiveRowCertificate :=
  { positiveRow := outwardYZPositiveRowFrom outwardYZSwitchLinkedList
    nativeDisconnection := outwardYZNativeTargetDisconnectionCertificate }

#print axioms outwardYZSwitchLinkedTargetFrom_mem
#print axioms outwardYZSwitchLinkedTargetFrom_coordinatewisePositive
#print axioms outwardYZSwitchLinkedTargetFrom_weight_pos
#print axioms outwardYZNativePositiveRowCertificate

end YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNativeTargetPositiveRow
