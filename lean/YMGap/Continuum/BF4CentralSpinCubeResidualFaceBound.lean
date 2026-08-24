/-
# Allocate the BF4 spin-cube residual fusion charge to non-source faces

The source-spin-free link product is still written linkwise.  This module
flattens the residual incidences and uses a checked finite permutation of the
extent-one corrected slab: every non-source physical face occurs exactly at
its four boundary links, while every source-cube face has been removed.

The cubic local fusion envelope therefore becomes a twelfth-power charge on
each non-source face.  This is the face-factor form needed for independent
heat-activity summation.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4CentralSpinCubeResidualLinkBound
import YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate

namespace YMGap.Continuum.BF4CentralSpinCubeResidualFaceBound

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CentralLowerCubeRowDomination
open YMGap.Continuum.BF4CentralSpinCubeResidualLinkBound
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Exact residual incidence allocation -/

def centralSpinCubeNonSourceFaceIds : List Nat :=
  (slabPhysicalFaceEdges 1).filter
    (fun id => !decide (id ∈ centralLowerCubeFaceIds))

def centralSpinCubeResidualIncidenceIds : List Nat :=
  (boundaryCompleteSlabLinks 1).flatMap
    centralLowerCubeUnselectedIncidentIds

def fourfoldIds (ids : List Nat) : List Nat :=
  ids.flatMap (fun id => List.replicate 4 id)

/-- Checked finite incidence identity for the extent-one corrected slab. -/
theorem centralSpinCubeResidualIncidenceIds_perm_fourfoldNonSource :
    centralSpinCubeResidualIncidenceIds.Perm
      (fourfoldIds centralSpinCubeNonSourceFaceIds) := by
  exact natListPerm_of_check _ _ (by decide)

/-! ## 2. Natural-product algebra -/

private theorem natListProduct_append {A : Type}
    (value : A -> Nat) : forall left right : List A,
    natListProduct value (left ++ right) =
      natListProduct value left * natListProduct value right
  | [], right => by simp [natListProduct]
  | head :: tail, right => by
      simp only [List.cons_append, natListProduct]
      rw [natListProduct_append value tail right]
      exact (Nat.mul_assoc _ _ _).symm

private theorem natListProduct_flatMap {A B : Type}
    (value : B -> Nat) (block : A -> List B) : forall items : List A,
    natListProduct value (items.flatMap block) =
      natListProduct (fun item => natListProduct value (block item)) items
  | [] => rfl
  | head :: tail => by
      simp only [List.flatMap_cons, natListProduct]
      rw [natListProduct_append value (block head) (tail.flatMap block),
        natListProduct_flatMap value block tail]

private theorem natListProduct_replicate {A : Type}
    (value : A -> Nat) (item : A) : forall count : Nat,
    natListProduct value (List.replicate count item) = value item ^ count
  | 0 => rfl
  | count + 1 => by
      simp only [List.replicate_succ, natListProduct, Nat.pow_succ]
      rw [natListProduct_replicate value item count]
      exact Nat.mul_comm (value item) (value item ^ count)

private theorem sum_add_one_le_product_add_one : forall spins : List Nat,
    natListSum spins + 1 <=
      natListProduct (fun spin => spin + 1) spins
  | [] => Nat.le_refl 1
  | head :: tail => by
      simp only [natListSum, natListProduct]
      have ih := sum_add_one_le_product_add_one tail
      have hproduct : 1 <=
          natListProduct (fun spin => spin + 1) tail :=
        Nat.le_trans (by omega) ih
      have hscale : head <=
          head * natListProduct (fun spin => spin + 1) tail := by
        calc
          head = 1 * head := (Nat.one_mul head).symm
          _ <= natListProduct (fun spin => spin + 1) tail * head :=
            Nat.mul_le_mul_right head hproduct
          _ = head * natListProduct (fun spin => spin + 1) tail :=
            Nat.mul_comm _ _
      have hadd := Nat.add_le_add hscale ih
      calc
        head + natListSum tail + 1 =
            head + (natListSum tail + 1) := by omega
        _ <= head * natListProduct (fun spin => spin + 1) tail +
            natListProduct (fun spin => spin + 1) tail := hadd
        _ = (head + 1) *
            natListProduct (fun spin => spin + 1) tail := by
          rw [Nat.add_mul, Nat.one_mul]

private theorem spinSumCube_le_listProductCube (spins : List Nat) :
    spinSumCube (natListSum spins) <=
      spinProductCube
        (natListProduct (fun spin => spin + 1) spins) := by
  unfold spinSumCube spinProductCube
  have h := sum_add_one_le_product_add_one spins
  exact Nat.mul_le_mul h (Nat.mul_le_mul h h)

private theorem natListProduct_spinProductCube {A : Type}
    (weight : A -> Nat) : forall items : List A,
    natListProduct (fun item => spinProductCube (weight item)) items =
      spinProductCube (natListProduct weight items)
  | [] => rfl
  | head :: tail => by
      simp only [natListProduct]
      rw [natListProduct_spinProductCube weight tail]
      unfold spinProductCube
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem natListProduct_mono_on {A : Type}
    (left right : A -> Nat) : forall items : List A,
    (forall item, item ∈ items -> left item <= right item) ->
      natListProduct left items <= natListProduct right items
  | [], _ => Nat.le_refl 1
  | head :: tail, hle => by
      simp only [natListProduct]
      exact Nat.mul_le_mul
        (hle head List.mem_cons_self)
        (natListProduct_mono_on left right tail
          (fun item hitem =>
            hle item (List.mem_cons_of_mem head hitem)))

private theorem spinProductCube_pow_four_local (value : Nat) :
    spinProductCube (value ^ 4) = value ^ 12 := by
  unfold spinProductCube
  rw [show 12 = 4 + (4 + 4) by omega, Nat.pow_add, Nat.pow_add]

/-! ## 3. The residual link product becomes a face-twelfth product -/

def centralSpinCubeResidualFaceTwelfthProduct
    (boundary target : EdgeLabelling) : Nat :=
  natListProduct
    (fun id =>
      (centralVacuumSourcePhysical boundary target id + 1) ^ 12)
    centralSpinCubeNonSourceFaceIds

/-- Complete allocation of the source-free fusion residual to non-source
physical faces. -/
theorem centralSpinCubeResidualMultiplicityProduct_le_faceTwelfth
    (boundary target : EdgeLabelling) :
    centralSpinCubeResidualMultiplicityProduct boundary target <=
      centralSpinCubeResidualFaceTwelfthProduct boundary target := by
  let faceWeight : Nat -> Nat := fun id =>
    centralVacuumSourcePhysical boundary target id + 1
  let residualProduct : Z4Link -> Nat := fun link =>
    natListProduct faceWeight
      (centralLowerCubeUnselectedIncidentIds link)
  have hlink : forall link, link ∈ boundaryCompleteSlabLinks 1 ->
      centralSpinCubeResidualLinkBound boundary target link <=
        spinProductCube (residualProduct link) := by
    intro link _hlink
    unfold centralSpinCubeResidualLinkBound
      centralSpinCubeResidualIncidentSpins residualProduct faceWeight
    have h := spinSumCube_le_listProductCube
      ((centralLowerCubeUnselectedIncidentIds link).map
        (centralVacuumSourcePhysical boundary target))
    rw [natListProduct_map] at h
    exact h
  have hproduct := natListProduct_mono_on
    (centralSpinCubeResidualLinkBound boundary target)
    (fun link => spinProductCube (residualProduct link))
    (boundaryCompleteSlabLinks 1) hlink
  have hcubes := natListProduct_spinProductCube residualProduct
    (boundaryCompleteSlabLinks 1)
  rw [hcubes] at hproduct
  have hflatten :
      natListProduct residualProduct (boundaryCompleteSlabLinks 1) =
        natListProduct faceWeight centralSpinCubeResidualIncidenceIds := by
    unfold residualProduct centralSpinCubeResidualIncidenceIds
    exact (natListProduct_flatMap faceWeight
      centralLowerCubeUnselectedIncidentIds
      (boundaryCompleteSlabLinks 1)).symm
  rw [hflatten] at hproduct
  have hperm :
      natListProduct faceWeight centralSpinCubeResidualIncidenceIds =
        natListProduct faceWeight
          (fourfoldIds centralSpinCubeNonSourceFaceIds) :=
    natListProduct_perm faceWeight
      centralSpinCubeResidualIncidenceIds_perm_fourfoldNonSource
  rw [hperm] at hproduct
  have hfourfold :
      natListProduct faceWeight
          (fourfoldIds centralSpinCubeNonSourceFaceIds) =
        natListProduct (fun id => faceWeight id ^ 4)
          centralSpinCubeNonSourceFaceIds := by
    unfold fourfoldIds
    rw [natListProduct_flatMap]
    apply natListProduct_congr
    intro id _hid
    exact natListProduct_replicate faceWeight id 4
  rw [hfourfold] at hproduct
  have htwelfth :
      spinProductCube
          (natListProduct (fun id => faceWeight id ^ 4)
            centralSpinCubeNonSourceFaceIds) =
        centralSpinCubeResidualFaceTwelfthProduct boundary target := by
    rw [<- natListProduct_spinProductCube
      (fun id => faceWeight id ^ 4) centralSpinCubeNonSourceFaceIds]
    unfold centralSpinCubeResidualFaceTwelfthProduct faceWeight
    apply natListProduct_congr
    intro id _hid
    exact spinProductCube_pow_four_local (faceWeight id)
  rw [htwelfth] at hproduct
  simpa only [centralSpinCubeResidualMultiplicityProduct] using hproduct

end YMGap.Continuum.BF4CentralSpinCubeResidualFaceBound

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4CentralSpinCubeResidualFaceBound.centralSpinCubeResidualIncidenceIds_perm_fourfoldNonSource
#print axioms YMGap.Continuum.BF4CentralSpinCubeResidualFaceBound.centralSpinCubeResidualMultiplicityProduct_le_faceTwelfth
