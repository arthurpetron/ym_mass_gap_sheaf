/-
# The closed dyadic cube as a thermodynamic cylinder coordinate

The side-two cube boundary constructed in
`Z4DyadicUnitCubeBlockGeometry` is a closed, connected canonical polymer.
This module evaluates predicates of its occurrence in the existing joint
cutoff/volume limit law.  The resulting functional is an exact normalized
probability coordinate at the fixed strong-coupling anchor.

This interface itself only packages the cylinder algebra.  The subsequent
`Z4SpinSummedDyadicUnitCubeJointNontriviality` module proves a positive floor
for its cube-occurrence event.  A comparison with a coarse,
coupling-shifted cube law remains the RG estimate required next.
-/

import YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
import YMGap.Continuum.Z4SpinSummedCylinderJointFunctional

namespace YMGap.Continuum.Z4DyadicUnitCubeCylinderInterface

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalCylinderFunctional
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderStability
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedCutoffTail
open YMGap.Continuum.Z4SpinSummedCylinderJointCofinal
open YMGap.Continuum.Z4SpinSummedCylinderJointFunctional

def dyadicUnitCubeCylinderRoots : List (List Nat) :=
  [dyadicUnitCubeSupportIds]

theorem dyadicUnitCubeCylinderRoots_length :
    dyadicUnitCubeCylinderRoots.length = 1 := by
  rfl

theorem dyadicUnitCubeCylinderRoots_nodup :
    dyadicUnitCubeCylinderRoots.Nodup := by
  exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

theorem dyadicUnitCubeCylinderRoots_allCanonical :
    ∀ root, root ∈ dyadicUnitCubeCylinderRoots →
      root ∈ canonicalSurfacePolymers 4 := by
  intro root hroot
  have hrootEq : root = dyadicUnitCubeSupportIds :=
    List.mem_singleton.mp hroot
  rw [hrootEq]
  exact dyadicUnitCubeSupportIds_mem_canonicalSurfacePolymers

/-- Predicates of the one closed cube coordinate in the joint thermodynamic
limit law. -/
def spinSummedDyadicUnitCubeCylinderLimit
    (predicate : List Bool → Bool) : CReal :=
  spinSummedJointCylinderLimitFunctional
    dyadicUnitCubeCylinderRoots_allCanonical predicate

@[simp] theorem spinSummedDyadicUnitCubeCylinderLimit_approx
    (stage : Nat) (predicate : List Bool → Bool) :
    (spinSummedDyadicUnitCubeCylinderLimit predicate).approx stage =
      parametricKCompatibleSupportEventProbability
        (spinSummedJointCutoff stage (4 + stage))
        (4 + stage)
        (targetCylinderEvent 4 (4 + stage)
          dyadicUnitCubeCylinderRoots predicate) := rfl

theorem spinSummedDyadicUnitCubeCylinderLimit_nonnegative
    (predicate : List Bool → Bool) :
    CReal.ofQ' 0 ≤ spinSummedDyadicUnitCubeCylinderLimit predicate :=
  spinSummedJointCylinderLimitFunctional_nonnegative
    dyadicUnitCubeCylinderRoots_allCanonical predicate

theorem spinSummedDyadicUnitCubeCylinderLimit_le_one
    (predicate : List Bool → Bool) :
    spinSummedDyadicUnitCubeCylinderLimit predicate ≤ CReal.ofQ' 1 :=
  spinSummedJointCylinderLimitFunctional_le_one
    dyadicUnitCubeCylinderRoots_allCanonical predicate

theorem spinSummedDyadicUnitCubeCylinderLimit_normalized :
    CReal.Equiv
      (spinSummedDyadicUnitCubeCylinderLimit (fun _ => true))
      (CReal.ofQ' 1) :=
  spinSummedJointCylinderLimitFunctional_normalized
    dyadicUnitCubeCylinderRoots_allCanonical

theorem spinSummedDyadicUnitCubeCylinderLimit_empty :
    CReal.Equiv
      (spinSummedDyadicUnitCubeCylinderLimit (fun _ => false))
      (CReal.ofQ' 0) :=
  spinSummedJointCylinderLimitFunctional_empty
    dyadicUnitCubeCylinderRoots_allCanonical

theorem spinSummedDyadicUnitCubeCylinderLimit_complement
    (predicate : List Bool → Bool) :
    CReal.Equiv
      (CReal.add
        (spinSummedDyadicUnitCubeCylinderLimit predicate)
        (spinSummedDyadicUnitCubeCylinderLimit
          (complementCylinderPredicate predicate)))
      (CReal.ofQ' 1) :=
  spinSummedJointCylinderLimitFunctional_complement
    dyadicUnitCubeCylinderRoots_allCanonical predicate

theorem spinSummedDyadicUnitCubeCylinderLimit_disjoint_additive
    (first second : List Bool → Bool)
    (hdisjoint : CylinderPredicatesDisjoint first second) :
    CReal.Equiv
      (spinSummedDyadicUnitCubeCylinderLimit
        (cylinderPredicateUnion first second))
      (CReal.add
        (spinSummedDyadicUnitCubeCylinderLimit first)
        (spinSummedDyadicUnitCubeCylinderLimit second)) :=
  spinSummedJointCylinderLimitFunctional_disjoint_additive
    dyadicUnitCubeCylinderRoots_allCanonical first second hdisjoint

#print axioms dyadicUnitCubeCylinderRoots_allCanonical
#print axioms spinSummedDyadicUnitCubeCylinderLimit_approx
#print axioms spinSummedDyadicUnitCubeCylinderLimit_nonnegative
#print axioms spinSummedDyadicUnitCubeCylinderLimit_normalized
#print axioms spinSummedDyadicUnitCubeCylinderLimit_disjoint_additive

end YMGap.Continuum.Z4DyadicUnitCubeCylinderInterface
