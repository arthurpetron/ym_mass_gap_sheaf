/-
# Dyadic plaquette blocks as genuine thermodynamic cylinder observables

The geometric dyadic carrier is promoted here to the already constructed
joint cutoff/volume probability law.  Every coarse plaquette becomes one
connected four-cell canonical support in the refined box, so a finite list of
coarse plaquettes supplies a well-typed list of cylinder coordinates.  The
resulting limit functional is normalized, positive, and finitely additive
because it is an instance of the exact spin-summed cylinder functional.

Canonical-support membership alone does not imply positive physical activity:
`dyadicPlaquetteCells_has_unpaired_boundary` proves that this planar patch is
open, so this module is only a support-algebra interface and not a non-vacuous
gauge-invariant block observable.  The physical route must instead use a
closed surface such as the unit-cube boundary.  This module also does not
assert RG invariance between coarse and refined laws; the coupling-indexed
block-kernel estimate remains an analytic obligation.
-/

import YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
import YMGap.Continuum.Z4SpinSummedCylinderJointFunctional

namespace YMGap.Continuum.Z4DyadicPlaquetteCylinderInterface

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalCylinderFunctional
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderStability
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedCutoffTail
open YMGap.Continuum.Z4SpinSummedCylinderJointCofinal
open YMGap.Continuum.Z4SpinSummedCylinderJointFunctional

/-- The refined connected-support coordinate attached to each coarse
plaquette.  It is not asserted to have nonzero physical activity. -/
def dyadicPlaquetteCylinderRoots
    (n : Nat) (plaquettes : List Z4Plaq) : List (List Nat) :=
  plaquettes.map (dyadicPlaquetteSupportIds n)

theorem dyadicPlaquetteCylinderRoots_length
    (n : Nat) (plaquettes : List Z4Plaq) :
    (dyadicPlaquetteCylinderRoots n plaquettes).length =
      plaquettes.length := by
  unfold dyadicPlaquetteCylinderRoots
  exact List.length_map _

/-- Every generated block coordinate belongs to the canonical support
universe of box `2*n`.  That universe includes zero-activity supports. -/
theorem dyadicPlaquetteCylinderRoots_allCanonical
    {n : Nat} {plaquettes : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ plaquettes →
      plaquette ∈ boxPlaquettes n) :
    ∀ root, root ∈ dyadicPlaquetteCylinderRoots n plaquettes →
      root ∈ canonicalSurfacePolymers (2 * n) := by
  intro root hroot
  unfold dyadicPlaquetteCylinderRoots at hroot
  obtain ⟨plaquette, hplaquette, hrootEq⟩ := List.mem_map.mp hroot
  rw [← hrootEq]
  exact dyadicPlaquetteSupportIds_mem_canonicalSurfacePolymers
    (hbox plaquette hplaquette)

/-- Two in-box coarse plaquettes cannot acquire the same refined canonical
root.  Equality of the numerical roots gives equality of their geometric
supports, and the collision-free dyadic cell encoding recovers the source
plaquette. -/
theorem dyadicPlaquetteSupportIds_injective_on_box
    {n : Nat} {left right : Z4Plaq}
    (hleft : left ∈ boxPlaquettes n)
    (hright : right ∈ boxPlaquettes n)
    (hroot : dyadicPlaquetteSupportIds n left =
      dyadicPlaquetteSupportIds n right) :
    left = right := by
  have hleftSupport := dyadicPlaquetteSupportIds_sameSupport hleft
  have hrightSupport := dyadicPlaquetteSupportIds_sameSupport hright
  have hleftCell : dyadicCell left .origin ∈
      geometricPolymer (2 * n) (dyadicPlaquetteSupportIds n left) :=
    hleftSupport.2 _ (dyadicCell_mem_cells left .origin)
  have hrightGeom : dyadicCell left .origin ∈
      geometricPolymer (2 * n) (dyadicPlaquetteSupportIds n right) := by
    rw [← hroot]
    exact hleftCell
  have hrightCell : dyadicCell left .origin ∈
      dyadicPlaquetteCells right :=
    hrightSupport.1 _ hrightGeom
  unfold dyadicPlaquetteCells at hrightCell
  obtain ⟨index, _, hcellEq⟩ := List.mem_map.mp hrightCell
  exact (dyadicCell_injective hcellEq.symm).1

private theorem dyadicPlaquetteCylinderRoots_nodup_local (n : Nat) :
    ∀ plaquettes : List Z4Plaq,
      plaquettes.Nodup →
      (∀ plaquette, plaquette ∈ plaquettes →
        plaquette ∈ boxPlaquettes n) →
      (dyadicPlaquetteCylinderRoots n plaquettes).Nodup
  | [], _, _ => List.nodup_nil
  | plaquette :: tail, hnodup, hbox => by
      have hparts := List.nodup_cons.mp hnodup
      unfold dyadicPlaquetteCylinderRoots
      apply List.nodup_cons.mpr
      refine ⟨?_, dyadicPlaquetteCylinderRoots_nodup_local n tail hparts.2
        (fun item hitem => hbox item (List.mem_cons_of_mem plaquette hitem))⟩
      intro hroot
      obtain ⟨other, hother, hrootEq⟩ := List.mem_map.mp hroot
      have heq := dyadicPlaquetteSupportIds_injective_on_box
        (hbox plaquette List.mem_cons_self)
        (hbox other (List.mem_cons_of_mem plaquette hother))
        hrootEq.symm
      exact hparts.1 (heq ▸ hother)

/-- Duplicate-free coarse plaquette coordinates remain duplicate-free after
conversion to refined canonical roots. -/
theorem dyadicPlaquetteCylinderRoots_nodup
    {n : Nat} {plaquettes : List Z4Plaq}
    (hnodup : plaquettes.Nodup)
    (hbox : ∀ plaquette, plaquette ∈ plaquettes →
      plaquette ∈ boxPlaquettes n) :
    (dyadicPlaquetteCylinderRoots n plaquettes).Nodup :=
  dyadicPlaquetteCylinderRoots_nodup_local n plaquettes hnodup hbox

/-- The joint cutoff/thermodynamic limit evaluated on the connected dyadic
block coordinates generated by a finite coarse plaquette list. -/
def spinSummedDyadicPlaquetteCylinderLimit
    {n : Nat} {plaquettes : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ plaquettes →
      plaquette ∈ boxPlaquettes n)
    (predicate : List Bool → Bool) : CReal :=
  spinSummedJointCylinderLimitFunctional
    (dyadicPlaquetteCylinderRoots_allCanonical hbox) predicate

/-- The approximation is the exact finite spin-summed probability of the
transported dyadic-block cylinder.  Thus the interface exposes the actual
finite event whose RG comparison must be controlled. -/
@[simp] theorem spinSummedDyadicPlaquetteCylinderLimit_approx
    {n stage : Nat} {plaquettes : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ plaquettes →
      plaquette ∈ boxPlaquettes n)
    (predicate : List Bool → Bool) :
    (spinSummedDyadicPlaquetteCylinderLimit hbox predicate).approx stage =
      parametricKCompatibleSupportEventProbability
        (spinSummedJointCutoff stage (2 * n + stage))
        (2 * n + stage)
        (targetCylinderEvent (2 * n) (2 * n + stage)
          (dyadicPlaquetteCylinderRoots n plaquettes) predicate) := rfl

theorem spinSummedDyadicPlaquetteCylinderLimit_nonnegative
    {n : Nat} {plaquettes : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ plaquettes →
      plaquette ∈ boxPlaquettes n)
    (predicate : List Bool → Bool) :
    CReal.ofQ' 0 ≤
      spinSummedDyadicPlaquetteCylinderLimit hbox predicate :=
  spinSummedJointCylinderLimitFunctional_nonnegative
    (dyadicPlaquetteCylinderRoots_allCanonical hbox) predicate

theorem spinSummedDyadicPlaquetteCylinderLimit_le_one
    {n : Nat} {plaquettes : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ plaquettes →
      plaquette ∈ boxPlaquettes n)
    (predicate : List Bool → Bool) :
    spinSummedDyadicPlaquetteCylinderLimit hbox predicate ≤
      CReal.ofQ' 1 :=
  spinSummedJointCylinderLimitFunctional_le_one
    (dyadicPlaquetteCylinderRoots_allCanonical hbox) predicate

theorem spinSummedDyadicPlaquetteCylinderLimit_normalized
    {n : Nat} {plaquettes : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ plaquettes →
      plaquette ∈ boxPlaquettes n) :
    CReal.Equiv
      (spinSummedDyadicPlaquetteCylinderLimit hbox (fun _ => true))
      (CReal.ofQ' 1) :=
  spinSummedJointCylinderLimitFunctional_normalized
    (dyadicPlaquetteCylinderRoots_allCanonical hbox)

theorem spinSummedDyadicPlaquetteCylinderLimit_empty
    {n : Nat} {plaquettes : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ plaquettes →
      plaquette ∈ boxPlaquettes n) :
    CReal.Equiv
      (spinSummedDyadicPlaquetteCylinderLimit hbox (fun _ => false))
      (CReal.ofQ' 0) :=
  spinSummedJointCylinderLimitFunctional_empty
    (dyadicPlaquetteCylinderRoots_allCanonical hbox)

theorem spinSummedDyadicPlaquetteCylinderLimit_complement
    {n : Nat} {plaquettes : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ plaquettes →
      plaquette ∈ boxPlaquettes n)
    (predicate : List Bool → Bool) :
    CReal.Equiv
      (CReal.add
        (spinSummedDyadicPlaquetteCylinderLimit hbox predicate)
        (spinSummedDyadicPlaquetteCylinderLimit hbox
          (complementCylinderPredicate predicate)))
      (CReal.ofQ' 1) :=
  spinSummedJointCylinderLimitFunctional_complement
    (dyadicPlaquetteCylinderRoots_allCanonical hbox) predicate

theorem spinSummedDyadicPlaquetteCylinderLimit_disjoint_additive
    {n : Nat} {plaquettes : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ plaquettes →
      plaquette ∈ boxPlaquettes n)
    (first second : List Bool → Bool)
    (hdisjoint : CylinderPredicatesDisjoint first second) :
    CReal.Equiv
      (spinSummedDyadicPlaquetteCylinderLimit hbox
        (cylinderPredicateUnion first second))
      (CReal.add
        (spinSummedDyadicPlaquetteCylinderLimit hbox first)
        (spinSummedDyadicPlaquetteCylinderLimit hbox second)) :=
  spinSummedJointCylinderLimitFunctional_disjoint_additive
    (dyadicPlaquetteCylinderRoots_allCanonical hbox)
    first second hdisjoint

#print axioms dyadicPlaquetteCylinderRoots_allCanonical
#print axioms dyadicPlaquetteSupportIds_injective_on_box
#print axioms dyadicPlaquetteCylinderRoots_nodup
#print axioms spinSummedDyadicPlaquetteCylinderLimit_approx
#print axioms spinSummedDyadicPlaquetteCylinderLimit_nonnegative
#print axioms spinSummedDyadicPlaquetteCylinderLimit_normalized
#print axioms spinSummedDyadicPlaquetteCylinderLimit_disjoint_additive

end YMGap.Continuum.Z4DyadicPlaquetteCylinderInterface
