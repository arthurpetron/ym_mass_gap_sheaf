/-
# Cutoff-uniform summation of the BF4 cube residual carrier

The decorated term majorant depends on a boundary channel and a target half
state only through the assembled non-source face labels.  This module embeds
that finite pair carrier into independent label vectors on all 66 non-source
faces.  Cartesian factorization and the exponent-thirteen one-face heat sum
then give a cutoff-uniform scalar ceiling.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4CentralSpinCubeTermDecoratedBound
import YMGap.Continuum.Z4BoundedEdgeLabellingNodup
import YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

namespace YMGap.Continuum.BF4CentralSpinCubeResidualCarrierSumBound

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CentralLowerCubeRowDomination
open YMGap.Continuum.BF4CentralSpinCubeResidualDecoratedFaceBound
open YMGap.Continuum.BF4CentralSpinCubeResidualFaceBound
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Independent vectors with labels zero through the cutoff -/

def allSpinValues (cutoff : Nat) : List Nat :=
  0 :: positiveSpinValues cutoff

theorem mem_allSpinValues_iff {cutoff spin : Nat} :
    spin ∈ allSpinValues cutoff ↔ spin <= cutoff := by
  constructor
  · intro hspin
    rcases List.mem_cons.mp hspin with hzero | hpositive
    · subst spin
      exact Nat.zero_le cutoff
    · exact (mem_positiveSpinValues_iff.mp hpositive).2
  · intro hspin
    by_cases hzero : spin = 0
    · subst spin
      exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      apply mem_positiveSpinValues_iff.mpr
      exact ⟨by omega, hspin⟩

def boundedSpinVectors (cutoff : Nat) : Nat -> List (List Nat)
  | 0 => [[]]
  | size + 1 =>
      (cartesian (allSpinValues cutoff)
        (boundedSpinVectors cutoff size)).map
          (fun pair => pair.1 :: pair.2)

theorem mem_boundedSpinVectors_iff (cutoff size : Nat)
    (vector : List Nat) :
    vector ∈ boundedSpinVectors cutoff size ↔
      vector.length = size ∧
        forall spin, spin ∈ vector -> spin <= cutoff := by
  induction size generalizing vector with
  | zero =>
      constructor
      · intro hvector
        change vector ∈ [[]] at hvector
        rcases List.mem_cons.mp hvector with hnil | himpossible
        · subst vector
          exact ⟨rfl, fun spin hspin =>
            absurd hspin List.not_mem_nil⟩
        · exact absurd himpossible List.not_mem_nil
      · intro hvector
        have hnil : vector = [] :=
          List.length_eq_zero_iff.mp hvector.1
        subst vector
        exact List.mem_cons_self
  | succ size ih =>
      constructor
      · intro hvector
        change vector ∈
          (cartesian (allSpinValues cutoff)
            (boundedSpinVectors cutoff size)).map
              (fun pair => pair.1 :: pair.2) at hvector
        obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hvector
        have hparts :=
          (mem_cartesian_iff (allSpinValues cutoff)
            (boundedSpinVectors cutoff size) pair).mp hpair
        have hhead := mem_allSpinValues_iff.mp hparts.1
        have htail := (ih pair.2).mp hparts.2
        constructor
        · exact congrArg Nat.succ htail.1
        · intro spin hspin
          rcases List.mem_cons.mp hspin with hheadEq | hrest
          · subst spin
            exact hhead
          · exact htail.2 spin hrest
      · intro hvector
        cases vector with
        | nil => exact absurd hvector.1 (fun h => Nat.noConfusion h)
        | cons head tail =>
            have htailLength : tail.length = size :=
              Nat.succ.inj hvector.1
            have hhead : head <= cutoff :=
              hvector.2 head List.mem_cons_self
            have htail : forall spin, spin ∈ tail -> spin <= cutoff := by
              intro spin hspin
              exact hvector.2 spin
                (List.mem_cons_of_mem head hspin)
            change head :: tail ∈
              (cartesian (allSpinValues cutoff)
                (boundedSpinVectors cutoff size)).map
                  (fun pair => pair.1 :: pair.2)
            apply List.mem_map.mpr
            refine ⟨(head, tail), ?_, rfl⟩
            exact (mem_cartesian_iff (allSpinValues cutoff)
              (boundedSpinVectors cutoff size) (head, tail)).mpr
              ⟨mem_allSpinValues_iff.mpr hhead,
                (ih tail).mpr ⟨htailLength, htail⟩⟩

theorem allSpinValues_weight_sum (cutoff : Nat) :
    listQSum anchorDecoratedFaceActivity (allSpinValues cutoff) ≈
      1 + anchorDecoratedPlaqActivity cutoff := by
  unfold allSpinValues
  change anchorDecoratedFaceActivity 0 +
      listQSum anchorDecoratedFaceActivity
        (positiveSpinValues cutoff) ≈
    1 + anchorDecoratedPlaqActivity cutoff
  exact Q'.add_eqv_congr'
    anchorDecoratedFaceActivity_zero_eqv_one
    (positiveSpinValues_weight_sum cutoff)

theorem boundedSpinVectors_weight_sum (cutoff : Nat) : forall size : Nat,
    listQSum anchorSpinVectorWeight (boundedSpinVectors cutoff size) ≈
      (1 + anchorDecoratedPlaqActivity cutoff) ^ size
  | 0 => by
      change (1 : Q') + 0 ≈ 1
      exact Q'.eqv_of_eq (Q'.add_zero' 1)
  | size + 1 => by
      unfold boundedSpinVectors
      rw [listQSum_map]
      refine Q'.eqv_trans _ _ _
        (listQSum_cartesian_product anchorDecoratedFaceActivity
          anchorSpinVectorWeight (allSpinValues cutoff)
          (boundedSpinVectors cutoff size)) ?_
      rw [Q'.pow_succ]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (allSpinValues_weight_sum cutoff))
        (Q'.mul_eqv_congr_left
          (1 + anchorDecoratedPlaqActivity cutoff) _ _
          (boundedSpinVectors_weight_sum cutoff size))

/-! ## 2. The actual boundary-target carrier embeds in those vectors -/

def centralSpinCubeBoundaryTargetPairs (cutoff : Nat) :
    List (EdgeLabelling × EdgeLabelling) :=
  cartesian (centralBoundaryChannels cutoff 0)
    (centralHalfStates cutoff 0)

theorem mem_centralSpinCubeBoundaryTargetPairs_iff
    {cutoff : Nat} {pair : EdgeLabelling × EdgeLabelling} :
    pair ∈ centralSpinCubeBoundaryTargetPairs cutoff ↔
      pair.1 ∈ centralBoundaryChannels cutoff 0 ∧
      pair.2 ∈ centralHalfStates cutoff 0 := by
  unfold centralSpinCubeBoundaryTargetPairs
  exact mem_cartesian_iff _ _ _

theorem centralSpinCubeBoundaryTargetPairs_nodup (cutoff : Nat) :
    (centralSpinCubeBoundaryTargetPairs cutoff).Nodup := by
  unfold centralSpinCubeBoundaryTargetPairs
  exact cartesian_nodup _ _
    (centralBoundaryChannels_nodup cutoff 0)
    (centralHalfStates_nodup cutoff 0)

def centralSpinCubePairVector
    (pair : EdgeLabelling × EdgeLabelling) : List Nat :=
  centralSpinCubeNonSourceFaceIds.map
    (centralVacuumSourcePhysical pair.1 pair.2)

private theorem centralVacuumSourcePhysical_zero_off_nonSource
    (boundary target : EdgeLabelling) {id : Nat}
    (hid : id ∉ centralSpinCubeNonSourceFaceIds) :
    centralVacuumSourcePhysical boundary target id = 0 := by
  by_cases hphysical : id ∈ slabPhysicalFaceEdges 1
  · have hcube : id ∈ centralLowerCubeFaceIds := by
      cases hcubeBool : decide (id ∈ centralLowerCubeFaceIds) with
      | false =>
          have hnonSource : id ∈ centralSpinCubeNonSourceFaceIds := by
            unfold centralSpinCubeNonSourceFaceIds
            apply List.mem_filter.mpr
            exact ⟨hphysical, by simp [hcubeBool]⟩
          exact absurd hnonSource hid
      | true => exact of_decide_eq_true hcubeBool
    exact centralVacuumSourcePhysical_eq_zero_on_cube
      boundary target hcube
  · unfold centralVacuumSourcePhysical
    exact assembleReflectedSlabLabelling_zero_off_physical
      0 zeroEdgeLabelling boundary target hphysical

private theorem map_values_eq_of_mem
    (left right : Nat -> Nat) : forall {ids : List Nat},
    ids.map left = ids.map right -> forall {id}, id ∈ ids ->
      left id = right id
  | [], _, _, hid => absurd hid List.not_mem_nil
  | head :: rest, heq, id, hid => by
      injection heq with hhead hrest
      rcases List.mem_cons.mp hid with hidHead | hidRest
      · subst id
        exact hhead
      · exact map_values_eq_of_mem left right hrest hidRest

private theorem centralSpinCubePairVector_injective_on
    {cutoff : Nat} {left right : EdgeLabelling × EdgeLabelling}
    (hleft : left ∈ centralSpinCubeBoundaryTargetPairs cutoff)
    (hright : right ∈ centralSpinCubeBoundaryTargetPairs cutoff)
    (heq : centralSpinCubePairVector left =
      centralSpinCubePairVector right) :
    left = right := by
  have hleftParts := mem_centralSpinCubeBoundaryTargetPairs_iff.mp hleft
  have hrightParts := mem_centralSpinCubeBoundaryTargetPairs_iff.mp hright
  have hphysical :
      centralVacuumSourcePhysical left.1 left.2 =
        centralVacuumSourcePhysical right.1 right.2 := by
    funext id
    by_cases hid : id ∈ centralSpinCubeNonSourceFaceIds
    · exact map_values_eq_of_mem
        (centralVacuumSourcePhysical left.1 left.2)
        (centralVacuumSourcePhysical right.1 right.2)
        heq hid
    · rw [centralVacuumSourcePhysical_zero_off_nonSource
          left.1 left.2 hid,
        centralVacuumSourcePhysical_zero_off_nonSource
          right.1 right.2 hid]
  let leftTriple : CentralReflectionTriple :=
    (zeroEdgeLabelling, (left.2, left.1))
  let rightTriple : CentralReflectionTriple :=
    (zeroEdgeLabelling, (right.2, right.1))
  have hzero : zeroEdgeLabelling ∈ centralHalfStates cutoff 0 := by
    unfold centralHalfStates
    apply boundedEdgeLabellings_complete
    · intro _id _hid
      change 0 < cutoff + 1
      omega
    · intro _id _hid
      rfl
  have hleftTriple : leftTriple ∈ centralReflectionTriples cutoff 0 :=
    mem_centralReflectionTriples.mpr
      ⟨hzero, hleftParts.2, hleftParts.1⟩
  have hrightTriple : rightTriple ∈ centralReflectionTriples cutoff 0 :=
    mem_centralReflectionTriples.mpr
      ⟨hzero, hrightParts.2, hrightParts.1⟩
  have htriple : leftTriple = rightTriple :=
    assembleCentralReflectionTriple_injective_on
      hleftTriple hrightTriple (by
        change assembleReflectedSlabLabelling 0
            zeroEdgeLabelling left.1 left.2 =
          assembleReflectedSlabLabelling 0
            zeroEdgeLabelling right.1 right.2
        simpa only [centralVacuumSourcePhysical] using hphysical)
  exact Prod.ext
    (congrArg (fun triple : CentralReflectionTriple => triple.2.2) htriple)
    (congrArg (fun triple : CentralReflectionTriple => triple.2.1) htriple)

private theorem centralSpinCubePairVector_mem
    {cutoff : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hpair : pair ∈ centralSpinCubeBoundaryTargetPairs cutoff) :
    centralSpinCubePairVector pair ∈
      boundedSpinVectors cutoff centralSpinCubeNonSourceFaceIds.length := by
  have hparts := mem_centralSpinCubeBoundaryTargetPairs_iff.mp hpair
  have hzero : zeroEdgeLabelling ∈ centralHalfStates cutoff 0 := by
    unfold centralHalfStates
    apply boundedEdgeLabellings_complete
    · intro _id _hid
      change 0 < cutoff + 1
      omega
    · intro _id _hid
      rfl
  have hbounded : SlabFaceLabellingBounded cutoff 1
      (centralVacuumSourcePhysical pair.1 pair.2) := by
    unfold centralVacuumSourcePhysical
    exact assembleReflectedSlabLabelling_bounded
      hzero hparts.1 hparts.2
  apply (mem_boundedSpinVectors_iff cutoff
    centralSpinCubeNonSourceFaceIds.length
    (centralSpinCubePairVector pair)).mpr
  constructor
  · unfold centralSpinCubePairVector
    simp only [List.length_map]
  · intro spin hspin
    obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hspin
    have hidPhysical : id ∈ slabPhysicalFaceEdges 1 :=
      (List.mem_filter.mp hid).1
    exact hbounded id hidPhysical

private theorem eliminateLinks_eq_vectorWeight
    (physical : EdgeLabelling) : forall ids : List Nat,
    eliminateLinks
        (fun id => anchorDecoratedFaceActivity (physical id)) ids =
      anchorSpinVectorWeight (ids.map physical)
  | [] => rfl
  | id :: rest => by
      simp only [eliminateLinks, List.map_cons, anchorSpinVectorWeight]
      rw [eliminateLinks_eq_vectorWeight physical rest]

theorem centralSpinCubeResidualCarrierSum_le_vectorPower
    (cutoff : Nat) :
    listQSum
        (fun pair => centralSpinCubeResidualDecoratedFaceProduct
          anchorCoupling pair.1 pair.2)
        (centralSpinCubeBoundaryTargetPairs cutoff) <=
      (1 + anchorDecoratedPlaqActivity cutoff) ^
        centralSpinCubeNonSourceFaceIds.length := by
  let source := centralSpinCubeBoundaryTargetPairs cutoff
  let target := boundedSpinVectors cutoff
    centralSpinCubeNonSourceFaceIds.length
  let sourceWeight := fun pair : EdgeLabelling × EdgeLabelling =>
    centralSpinCubeResidualDecoratedFaceProduct
      anchorCoupling pair.1 pair.2
  have hinjection :
      listQSum sourceWeight source <=
        listQSum anchorSpinVectorWeight target := by
    apply listQSum_le_of_injective source target
      sourceWeight anchorSpinVectorWeight centralSpinCubePairVector
    · exact centralSpinCubeBoundaryTargetPairs_nodup cutoff
    · intro pair hpair
      exact centralSpinCubePairVector_mem hpair
    · intro left hleft right hright heq
      exact centralSpinCubePairVector_injective_on hleft hright heq
    · intro pair _hpair
      apply Q'.le_of_eqv
      apply Q'.eqv_of_eq
      unfold sourceWeight centralSpinCubeResidualDecoratedFaceProduct
        centralSpinCubePairVector
      exact eliminateLinks_eq_vectorWeight
        (centralVacuumSourcePhysical pair.1 pair.2)
        centralSpinCubeNonSourceFaceIds
    · intro vector _hvector
      exact anchorSpinVectorWeight_nonnegative vector
  exact Q'.le_trans' _ _ _ hinjection
    (Q'.le_of_eqv
      (boundedSpinVectors_weight_sum cutoff
        centralSpinCubeNonSourceFaceIds.length))

/-! ## 3. The fixed 66-face uniform scalar ceiling -/

theorem centralSpinCubeNonSourceFaceIds_length :
    centralSpinCubeNonSourceFaceIds.length = 66 := by
  decide

def centralSpinCubeResidualCarrierCeiling : Q' :=
  (1 + anchorDecoratedFaceEnvelope) ^ 66

private theorem qpow_le_qpow_of_le
    {left right : Q'} (hleft0 : (0 : Q') <= left)
    (hle : left <= right) : forall exponent : Nat,
    left ^ exponent <= right ^ exponent
  | 0 => Q'.le_refl' 1
  | exponent + 1 => by
      rw [Q'.pow_succ, Q'.pow_succ]
      have hleftPow0 : (0 : Q') <= left ^ exponent :=
        Q'.pow_nonneg left hleft0 exponent
      have hright0 : (0 : Q') <= right :=
        Q'.le_trans' _ _ _ hleft0 hle
      have hfirst : left * left ^ exponent <=
          right * left ^ exponent :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hle hleftPow0
      have hsecond : right * left ^ exponent <=
          right * right ^ exponent :=
        Q'.mul_le_mul_of_nonneg_left _ _ _
          (qpow_le_qpow_of_le hleft0 hle exponent) hright0
      exact Q'.le_trans' _ _ _ hfirst hsecond

theorem centralSpinCubeResidualCarrierSum_le_ceiling (cutoff : Nat) :
    listQSum
        (fun pair => centralSpinCubeResidualDecoratedFaceProduct
          anchorCoupling pair.1 pair.2)
        (centralSpinCubeBoundaryTargetPairs cutoff) <=
      centralSpinCubeResidualCarrierCeiling := by
  have hsum := centralSpinCubeResidualCarrierSum_le_vectorPower cutoff
  rw [centralSpinCubeNonSourceFaceIds_length] at hsum
  have hbase :
      1 + anchorDecoratedPlaqActivity cutoff <=
        1 + anchorDecoratedFaceEnvelope :=
    Q'.add_le_add_left 1 _ _
      (anchorDecoratedPlaqActivity_le_envelope cutoff)
  have hbase0 : (0 : Q') <=
      1 + anchorDecoratedPlaqActivity cutoff :=
    Q'.zero_le_add _ _ Q'.zero_le_one
      (anchorDecoratedPlaqActivity_nonnegative cutoff)
  exact Q'.le_trans' _ _ _ hsum
    (qpow_le_qpow_of_le hbase0 hbase 66)

end YMGap.Continuum.BF4CentralSpinCubeResidualCarrierSumBound

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4CentralSpinCubeResidualCarrierSumBound.mem_boundedSpinVectors_iff
#print axioms YMGap.Continuum.BF4CentralSpinCubeResidualCarrierSumBound.centralSpinCubePairVector_injective_on
#print axioms YMGap.Continuum.BF4CentralSpinCubeResidualCarrierSumBound.centralSpinCubeResidualCarrierSum_le_vectorPower
#print axioms YMGap.Continuum.BF4CentralSpinCubeResidualCarrierSumBound.centralSpinCubeResidualCarrierSum_le_ceiling
