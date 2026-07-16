/-
# The canonical cutoff-one gas as an arbitrary-compatibility finite gas

The generic finite gas is instantiated with the corrected canonical
compatibility test (no common face and no shared actual link) and the exact
derived rational surface activity.  The resulting partition and event
numerator are identified with the already-constructed canonical objects.

This adapter is deliberately exact: it does not weaken the physical
compatibility to the older face-disjoint predicate.
-/

import YMGap.Continuum.FiniteCompatibilityGas
import YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure

namespace YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Definitional identification of predicates and activities -/

theorem genericFamilyCompatibleB_eq_canonical (n : Nat) :
    ∀ family : List (List Nat),
      familyCompatibleB (canonicalPolymerCompatibleB n) family =
        canonicalFamilyCompatibleB n family
  | [] => rfl
  | head :: tail => by
      change (tail.all (canonicalPolymerCompatibleB n head) &&
          familyCompatibleB (canonicalPolymerCompatibleB n) tail) =
        (tail.all (canonicalPolymerCompatibleB n head) &&
          canonicalFamilyCompatibleB n tail)
      rw [genericFamilyCompatibleB_eq_canonical n tail]

theorem genericFamilyWeight_eq_canonical (w : Q') (n : Nat) :
    ∀ family : List (List Nat),
      familyWeight (canonicalSurfaceActivity w n) family =
        canonicalSurfaceFamilyActivity w n family
  | [] => rfl
  | head :: tail => by
      change canonicalSurfaceActivity w n head *
          familyWeight (canonicalSurfaceActivity w n) tail =
        canonicalSurfaceActivity w n head *
          canonicalSurfaceFamilyActivity w n tail
      rw [genericFamilyWeight_eq_canonical w n tail]

theorem genericCompatibleFamilies_eq_canonical (n : Nat) :
    compatibleFamilies (canonicalPolymerCompatibleB n)
        (canonicalSurfacePolymers n) =
      canonicalCompatibleAmbientFamilies n := by
  unfold compatibleFamilies canonicalCompatibleAmbientFamilies
  apply List.filter_congr
  intro family _
  exact genericFamilyCompatibleB_eq_canonical n family

/-! ## 2. The exact generic presentation of the canonical gas -/

def canonicalPolymerPartition (w : Q') (n : Nat)
    (ambient : List (List Nat)) : Q' :=
  partition (canonicalPolymerCompatibleB n)
    (canonicalSurfaceActivity w n) ambient

def canonicalPolymerEventNumerator (w : Q') (n : Nat)
    (ambient : List (List Nat))
    (event : List (List Nat) → Bool) : Q' :=
  eventNumerator (canonicalPolymerCompatibleB n)
    (canonicalSurfaceActivity w n) ambient event

theorem canonicalPolymerPartition_eqv_parametric
    (w : Q') (n : Nat) :
    canonicalPolymerPartition w n (canonicalSurfacePolymers n) ≈
      parametricCanonicalCompatibleAmbientPartition w n := by
  unfold canonicalPolymerPartition partition
    parametricCanonicalCompatibleAmbientPartition
  rw [genericCompatibleFamilies_eq_canonical]
  exact listQSum_congr
    (fun family => Q'.eqv_of_eq
      (genericFamilyWeight_eq_canonical w n family)) _

theorem anchorCanonicalPartition_eqv_generic (n : Nat) :
    anchorCanonicalPartition n ≈
      canonicalPolymerPartition anchorCoupling n
        (canonicalSurfacePolymers n) := by
  exact Q'.eqv_symm
    (canonicalPolymerPartition_eqv_parametric anchorCoupling n)

theorem canonicalPolymerEventNumerator_eqv_anchor
    (n : Nat) (event : List (List Nat) → Bool) :
    canonicalPolymerEventNumerator anchorCoupling n
        (canonicalSurfacePolymers n) event ≈
      anchorEventNumerator n event := by
  unfold canonicalPolymerEventNumerator eventNumerator
    anchorEventNumerator
  rw [genericCompatibleFamilies_eq_canonical]
  exact listQSum_congr
    (fun family => Q'.eqv_of_eq
      (genericFamilyWeight_eq_canonical anchorCoupling n family)) _

/-! ## 3. Corrected-compatible deletion recurrence -/

theorem canonicalPolymerPartition_cons_split
    (w : Q') (n : Nat) (polymer : List Nat)
    (ambient : List (List Nat)) :
    canonicalPolymerPartition w n (polymer :: ambient) ≈
      canonicalPolymerPartition w n ambient +
        canonicalSurfaceActivity w n polymer *
          canonicalPolymerPartition w n
            (ambient.filter (canonicalPolymerCompatibleB n polymer)) := by
  exact partition_cons_split
    (canonicalPolymerCompatibleB n)
    (canonicalSurfaceActivity w n) polymer ambient

theorem anchorCanonicalPolymerPartition_nonnegative
    (n : Nat) (ambient : List (List Nat)) :
    (0 : Q') ≤ canonicalPolymerPartition anchorCoupling n ambient := by
  exact partition_nonnegative
    (canonicalPolymerCompatibleB n)
    (canonicalSurfaceActivity anchorCoupling n)
    (canonicalSurfacePolymer_activity_nonnegative n) ambient

theorem anchorCanonicalPolymerPartition_ge_one
    (n : Nat) (ambient : List (List Nat)) :
    (1 : Q') ≤ canonicalPolymerPartition anchorCoupling n ambient := by
  exact partition_ge_one
    (canonicalPolymerCompatibleB n)
    (canonicalSurfaceActivity anchorCoupling n)
    (canonicalSurfacePolymer_activity_nonnegative n) ambient

end YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas.genericCompatibleFamilies_eq_canonical
#print axioms YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas.canonicalPolymerPartition_eqv_parametric
#print axioms YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas.canonicalPolymerEventNumerator_eqv_anchor
#print axioms YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas.canonicalPolymerPartition_cons_split
#print axioms YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas.anchorCanonicalPolymerPartition_ge_one
