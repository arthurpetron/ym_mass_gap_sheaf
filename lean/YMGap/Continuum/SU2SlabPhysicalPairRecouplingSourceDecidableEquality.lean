/-
# Constructive equality for whole-slab physical-pair source assignments

Each actual slab link carries one of the complete source types at degrees
zero through six.  Their channel data already have constructive decidable
equality.  This module follows the literal link list and assembles those
local decisions into equality for the heterogeneous whole-slab source
assignment.

Constructive contract: finite channel codes and structural recursion only;
no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
import YMGap.Continuum.SU2CompleteCarrierDecidableEquality

namespace YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceDecidableEquality

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2CompleteCarrierDecidableEquality
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. Equality at one actual link -/

/-- Decidable equality for the source carrier of every geometrically
possible physical-pair package. -/
def slabPhysicalPairRecouplingKernelPackageSourceDecidableEq
    {extent : Nat} :
    (degree : Nat) → (D : SlabPhysicalPairRecouplingData extent degree) →
      DecidableEq
        (slabPhysicalPairRecouplingKernelPackage degree D).Source
  | 0, _ => by change DecidableEq Unit; infer_instance
  | 1, _ => by change DecidableEq Unit; infer_instance
  | 2, _ => by change DecidableEq Unit; infer_instance
  | 3, _ => by change DecidableEq Unit; infer_instance
  | 4, D => by
      change DecidableEq
        (slabPhysicalPairRecouplingKernelPackageFour D).Source
      unfold slabPhysicalPairRecouplingKernelPackageFour
      infer_instance
  | 5, D => by
      change DecidableEq
        (slabPhysicalPairRecouplingKernelPackageFive D).Source
      unfold slabPhysicalPairRecouplingKernelPackageFive
      infer_instance
  | 6, D => by
      change DecidableEq
        (slabPhysicalPairRecouplingKernelPackageSix D).Source
      unfold slabPhysicalPairRecouplingKernelPackageSix
      infer_instance
  | degree + 7, D => False.elim (by
      have hdegree := D.degree_le_six
      omega)

def slabPhysicalPairRecouplingPackageAtLinkSourceDecidableEq
    (extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (linked : {link // link ∈ boundaryCompleteSlabLinks extent}) :
    DecidableEq
      (slabPhysicalPairRecouplingPackageAtLink
        extent leftPhysical rightPhysical linked).Source := by
  unfold slabPhysicalPairRecouplingPackageAtLink
  exact slabPhysicalPairRecouplingKernelPackageSourceDecidableEq
    (slabIncidentPlaqIds extent linked.1).length
    (slabPhysicalPairRecouplingDataAtLink
      extent leftPhysical rightPhysical linked)

/-! ## 2. Equality for the dependent whole-slab product -/

def slabPhysicalPairRecouplingSourceAssignmentFromDecidableEq
    (extent : Nat) (leftPhysical rightPhysical : SlabLabelling) :
    (linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks extent}) →
      DecidableEq
        (FiniteBistochasticSourceAssignment
          (linkedList.map fun linked =>
            slabPhysicalPairRecouplingPackageAtLink
              extent leftPhysical rightPhysical linked))
  | [] => by change DecidableEq Unit; infer_instance
  | linked :: rest => by
      letI : DecidableEq
          (slabPhysicalPairRecouplingPackageAtLink
            extent leftPhysical rightPhysical linked).Source :=
        slabPhysicalPairRecouplingPackageAtLinkSourceDecidableEq
          extent leftPhysical rightPhysical linked
      letI : DecidableEq
          (FiniteBistochasticSourceAssignment
            (rest.map fun next =>
              slabPhysicalPairRecouplingPackageAtLink
                extent leftPhysical rightPhysical next)) :=
        slabPhysicalPairRecouplingSourceAssignmentFromDecidableEq
          extent leftPhysical rightPhysical rest
      change DecidableEq
        ((slabPhysicalPairRecouplingPackageAtLink
            extent leftPhysical rightPhysical linked).Source ×
          FiniteBistochasticSourceAssignment
            (rest.map fun next =>
              slabPhysicalPairRecouplingPackageAtLink
                extent leftPhysical rightPhysical next))
      infer_instance

/-- Constructive equality on the exact source carrier of the common
whole-slab physical-pair matrix. -/
def slabPhysicalPairRecouplingSourceAssignmentDecidableEq
    (extent : Nat) (leftPhysical rightPhysical : SlabLabelling) :
    DecidableEq
      (SlabPhysicalPairRecouplingSourceAssignment
        extent leftPhysical rightPhysical) :=
  slabPhysicalPairRecouplingSourceAssignmentFromDecidableEq
    extent leftPhysical rightPhysical
    (boundaryCompleteSlabLinks extent).attach

end YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceDecidableEquality

#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceDecidableEquality.slabPhysicalPairRecouplingKernelPackageSourceDecidableEq
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceDecidableEquality.slabPhysicalPairRecouplingSourceAssignmentFromDecidableEq
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceDecidableEquality.slabPhysicalPairRecouplingSourceAssignmentDecidableEq
