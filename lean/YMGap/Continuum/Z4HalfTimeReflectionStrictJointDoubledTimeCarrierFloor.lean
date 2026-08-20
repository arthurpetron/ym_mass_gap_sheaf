/-
# Linear carrier floor for the strict doubled-time OS geometry

The literal strict-cylinder time action has already been recoded as a mixed
reflection chart: the lower block stays below the reflection plane while the
upper block is translated forward by twice the semigroup shift.  This file
extracts the load-bearing geometric consequence.  Any connected plaquette
support meeting both blocks has size at least linear in the Euclidean-time
separation.

No connected-correlation or cluster-expansion assertion is made here.  The
remaining analytic bridge must show that vacuum centering cancels every
contribution whose carrier does not meet both blocks, and must then dominate
the surviving weighted carriers by a norm-relative geometric tail.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedEventRecoding
import YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeCarrierFloor

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedEventRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4UniformShiftPhysicalTransport
open Dir4

/-! ## 1. The upper block retains the full doubled-time displacement -/

/-- A face in the mixed upper block is at least `2 * shift + 3` slices above
the reflection plane.  This is stronger than merely knowing that it lies on
the upper side. -/
theorem strictJointDoubledTimeMixedUpperRoot_time_ge
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base)
    {face : Nat}
    (hface : face ∈ strictJointDoubledTimeMixedUpperRoot
      radius base shift root) :
    radius + 3 + (shift + shift) ≤
      (boxPlaquetteAt (centralAmbient radius) face).1.2.2.2 := by
  have hbase : strictQueryBase base ≤ radius := by
    unfold strictQueryBase uniformPaddedBase at hadmissible ⊢
    omega
  have hsame := centralStrictUpperCanonicalRoot_timeShift_sameRadius
    (shift := shift + shift) hadmissible hroot
  have hgeom : boxPlaquetteAt (centralAmbient radius) face ∈
      geometricPolymer (centralAmbient radius)
        (strictJointDoubledTimeMixedUpperRoot
          radius base shift root) :=
    List.mem_map.mpr ⟨face, hface, rfl⟩
  have hmapped := hsame.1 _ hgeom
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hmapped
  obtain ⟨sourceFace, hsourceFace, hsourceFaceEq⟩ :=
    List.mem_map.mp hsource
  have htime := centralStrictUpperCanonicalRoot_time_ge
    hbase hroot hsourceFace
  rw [hsourceFaceEq] at htime
  rw [← hsourceEq]
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := source
  change radius + 3 ≤ d at htime
  cases plane <;>
    simp [timeShiftPlaquette, timeShiftVertex] <;>
    omega

/-! ## 2. Separation and connected-support floors -/

/-- Every lower-block face and every doubled-time upper-block face are
separated by at least `2 * shift + 5` in the plaquette `L∞` metric.  The
fixed five-layer surplus comes from the strict three-layer source margin and
its reflected two-layer lower margin. -/
theorem strictJointDoubledTimeMixedRoots_linf_floor
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {lowerRoot upperRoot : List Nat}
    (hlowerRoot : lowerRoot ∈ canonicalSurfacePolymers base)
    (hupperRoot : upperRoot ∈ canonicalSurfacePolymers base)
    {lowerFace upperFace : Nat}
    (hlowerFace : lowerFace ∈ strictJointDoubledTimeMixedLowerRoot
      radius base shift lowerRoot)
    (hupperFace : upperFace ∈ strictJointDoubledTimeMixedUpperRoot
      radius base shift upperRoot) :
    shift + shift + 5 ≤ linfDist
      (boxPlaquetteAt (centralAmbient radius) lowerFace)
      (boxPlaquetteAt (centralAmbient radius) upperFace) := by
  have hbase : strictQueryBase base ≤ radius := by
    unfold strictQueryBase uniformPaddedBase at hadmissible ⊢
    omega
  have hlowerTime := centralStrictLowerCanonicalRoot_time_add_two_le
    hbase hlowerRoot hlowerFace
  have hupperTime := strictJointDoubledTimeMixedUpperRoot_time_ge
    hadmissible hupperRoot hupperFace
  have hmetric := le_linfDist_comp
    (boxPlaquetteAt (centralAmbient radius) lowerFace)
    (boxPlaquetteAt (centralAmbient radius) upperFace) x3
  simp only [natDist, cPlaq, vComp] at hmetric
  have horder :
      (boxPlaquetteAt (centralAmbient radius) lowerFace).1.2.2.2 ≤
        (boxPlaquetteAt (centralAmbient radius) upperFace).1.2.2.2 := by
    omega
  have hseparation :
      (boxPlaquetteAt (centralAmbient radius) lowerFace).1.2.2.2 +
          (shift + shift + 5) ≤
        (boxPlaquetteAt (centralAmbient radius) upperFace).1.2.2.2 := by
    omega
  have hdist : shift + shift + 5 ≤
      ((boxPlaquetteAt (centralAmbient radius) lowerFace).1.2.2.2 -
          (boxPlaquetteAt (centralAmbient radius) upperFace).1.2.2.2) +
        ((boxPlaquetteAt (centralAmbient radius) upperFace).1.2.2.2 -
          (boxPlaquetteAt (centralAmbient radius) lowerFace).1.2.2.2) := by
    rw [Nat.sub_eq_zero_of_le horder]
    simp only [Nat.zero_add]
    exact Nat.le_sub_of_add_le
      (by simpa only [Nat.add_comm] using hseparation)
  exact Nat.le_trans hdist hmetric

/-- A connected cutoff-one face support that meets both strict mixed blocks
has at least `2 * shift + 6` faces.  This is the exact geometric floor needed
after a future connected-correlation classifier produces the two endpoint
memberships. -/
theorem strictJointDoubledTimeConnectedSupport_size_floor
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {lowerRoot upperRoot : List Nat}
    (hlowerRoot : lowerRoot ∈ canonicalSurfacePolymers base)
    (hupperRoot : upperRoot ∈ canonicalSurfacePolymers base)
    {lowerFace upperFace : Nat}
    (hlowerFace : lowerFace ∈ strictJointDoubledTimeMixedLowerRoot
      radius base shift lowerRoot)
    (hupperFace : upperFace ∈ strictJointDoubledTimeMixedUpperRoot
      radius base shift upperRoot)
    {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports (centralAmbient radius))
    (hconnected : InternallyConnected
      (faceLinkAdjacentB (centralAmbient radius)) support)
    (hlowerMem : lowerFace ∈ support)
    (hupperMem : upperFace ∈ support) :
    shift + shift + 6 ≤ support.length := by
  apply connectedFaceSupport_linf_size_floor
    hsupport hconnected hlowerMem
  · exact List.mem_map.mpr ⟨upperFace, hupperMem, rfl⟩
  · exact strictJointDoubledTimeMixedRoots_linf_floor
      hadmissible hlowerRoot hupperRoot hlowerFace hupperFace

#print axioms strictJointDoubledTimeMixedUpperRoot_time_ge
#print axioms strictJointDoubledTimeMixedRoots_linf_floor
#print axioms strictJointDoubledTimeConnectedSupport_size_floor

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeCarrierFloor
