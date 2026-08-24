/-
# Absorb the BF4 cube residual into decorated non-source face activities

The preceding incidence theorem charges the source-free fusion product by a
twelfth power of `(spin + 1)` on every non-source face.  This module combines
that charge with the literal heat coefficient.  The six source-cube faces
factor exactly as `(coeffW w sourceSpin)^6`; every remaining face becomes the
degree-thirteen activity `tailTerm w 13 spin`.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4CentralSpinCubeResidualFaceBound
import YMGap.Continuum.Z4SpinSummedFaceActivityBound

namespace YMGap.Continuum.BF4CentralSpinCubeResidualDecoratedFaceBound

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CentralLowerCubeRowDomination
open YMGap.Continuum.BF4CentralSpinCubeResidualFaceBound
open YMGap.Continuum.BF4CentralSpinCubeResidualLinkBound
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4SpinSummedFaceActivityBound

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem eliminateLinks_congr_on
    (left right : Nat -> Q') : forall ids : List Nat,
    (forall id, id ∈ ids -> left id ≈ right id) ->
      eliminateLinks left ids ≈ eliminateLinks right ids
  | [], _ => Q'.eqv_refl 1
  | id :: rest, hagree =>
      qmul_congr (hagree id List.mem_cons_self)
        (eliminateLinks_congr_on left right rest
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem id hitem)))

private theorem eliminateLinks_indicator_pow
    (selected : List Nat) (coefficient : Q') : forall ids : List Nat,
    eliminateLinks
        (fun id => if id ∈ selected then coefficient else 1) ids ≈
      coefficient ^
        (ids.filter (fun id => decide (id ∈ selected))).length
  | [] => Q'.eqv_refl 1
  | id :: rest => by
      by_cases hselected : id ∈ selected
      · simp only [eliminateLinks, hselected, if_pos,
          List.filter_cons, decide_true, List.length_cons, Q'.pow_succ]
        exact qmul_congr (Q'.eqv_refl _)
          (eliminateLinks_indicator_pow selected coefficient rest)
      · simp only [eliminateLinks, hselected,
          List.filter_cons, decide_false]
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left 1 _ _
            (eliminateLinks_indicator_pow selected coefficient rest))
          (Q'.one_mul_eqv _)

private theorem eliminateLinks_pointwise_mul
    (left right : Nat -> Q') : forall ids : List Nat,
    eliminateLinks (fun id => left id * right id) ids ≈
      eliminateLinks left ids * eliminateLinks right ids
  | [] => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | id :: rest => by
      simp only [eliminateLinks]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (left id * right id) _ _
          (eliminateLinks_pointwise_mul left right rest)) ?_
      show ((left id * right id) *
          (eliminateLinks left rest * eliminateLinks right rest)) ≈
        (left id * eliminateLinks left rest) *
          (right id * eliminateLinks right rest)
      show ((left id * right id) *
          (eliminateLinks left rest * eliminateLinks right rest)).num *
          (((left id * eliminateLinks left rest) *
            (right id * eliminateLinks right rest)).den : Int) =
        ((left id * eliminateLinks left rest) *
          (right id * eliminateLinks right rest)).num *
          (((left id * right id) *
            (eliminateLinks left rest * eliminateLinks right rest)).den : Int)
      simp only [Q'.mul_num_cast, Q'.mul_den_cast]
      ac_rfl

private theorem ofNat_mul_eqv (left right : Nat) :
    Q'.ofNat left * Q'.ofNat right ≈ Q'.ofNat (left * right) := by
  show (Int.ofNat left * Int.ofNat right) * 1 =
    Int.ofNat (left * right) * (1 * 1)
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
  omega

private theorem mul_four_regroup (A B C D : Q') :
    (A * B) * (C * D) ≈ (A * C) * (B * D) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A B (C * D)) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.mul_assoc_eqv A C (B * D)))
  refine Q'.mul_eqv_congr_left A _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv B C D)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ D (Q'.mul_comm_eqv B C)) ?_
  exact Q'.mul_assoc_eqv C B D

private theorem eliminateLinks_pair_natProduct_eqv
    (value : Nat -> Q') (charge : Nat -> Nat) : forall ids : List Nat,
    eliminateLinks value ids * Q'.ofNat (natListProduct charge ids) ≈
      eliminateLinks
        (fun id => value id * Q'.ofNat (charge id)) ids
  | [] => by
      change ((1 : Q') * Q'.ofNat 1).eqv 1
      decide
  | id :: rest => by
      simp only [eliminateLinks, natListProduct]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (value id * eliminateLinks value rest)
          _ _ (Q'.eqv_symm
            (ofNat_mul_eqv (charge id) (natListProduct charge rest)))) ?_
      refine Q'.eqv_trans _ _ _
        (mul_four_regroup (value id) (eliminateLinks value rest)
          (Q'.ofNat (charge id))
          (Q'.ofNat (natListProduct charge rest))) ?_
      exact Q'.mul_eqv_congr_left
        (value id * Q'.ofNat (charge id)) _ _
        (eliminateLinks_pair_natProduct_eqv value charge rest)

private theorem eliminateLinks_eqv_filter_of_one
    (value : Nat -> Q') (test : Nat -> Bool) : forall ids : List Nat,
    (forall id, id ∈ ids -> test id = false -> value id ≈ 1) ->
      eliminateLinks value ids ≈ eliminateLinks value (ids.filter test)
  | [], _ => Q'.eqv_refl 1
  | id :: rest, hone => by
      have hrest := eliminateLinks_eqv_filter_of_one value test rest
        (fun item hitem =>
          hone item (List.mem_cons_of_mem id hitem))
      cases htest : test id with
      | false =>
          simp only [eliminateLinks, List.filter_cons, htest,
            Bool.false_eq_true, reduceIte]
          exact Q'.eqv_trans _ _ _
            (qmul_congr (hone id List.mem_cons_self htest) hrest)
            (Q'.one_mul_eqv _)
      | true =>
          simp only [eliminateLinks, List.filter_cons, htest, reduceIte]
          exact qmul_congr (Q'.eqv_refl _) hrest

/-! ## 1. Exact arbitrary-spin source factor -/

theorem centralSpinCube_faceCoefficient_factor
    (w : Q') {K spin : Nat} (hspin : spin <= K)
    (boundary target : EdgeLabelling) (id : Nat) :
    coeffAt (heatKernelPacket K w)
        (centralSpinCubeSourcePhysical spin boundary target id) ≈
      (if id ∈ centralLowerCubeFaceIds then coeffW w spin else 1) *
        coeffAt (heatKernelPacket K w)
          (centralVacuumSourcePhysical boundary target id) := by
  by_cases hcube : id ∈ centralLowerCubeFaceIds
  · rw [centralSpinCubeSourcePhysical_eq_spin_on_cube
        spin boundary target hcube,
      centralVacuumSourcePhysical_eq_zero_on_cube boundary target hcube,
      coeffAt_heatKernelPacket (Nat.lt_succ_of_le hspin),
      coeffAt_heatKernelPacket (Nat.zero_lt_succ K),
      coeffW_zero, if_pos hcube]
    exact Q'.eqv_symm (Q'.mul_one_eqv _)
  · rw [centralSpinCubeSourcePhysical_eq_vacuum_off_cube
        spin boundary target hcube, if_neg hcube]
    exact Q'.eqv_symm (Q'.one_mul_eqv _)

theorem centralSpinCubePhysicalFaceFactor_eqv_activity_mul_vacuum
    (w : Q') {K spin : Nat} (hspin : spin <= K)
    (boundary target : EdgeLabelling) :
    slabParametricKPhysicalFaceFactor w K 1
        (centralSpinCubeSourcePhysical spin boundary target) ≈
      (coeffW w spin) ^ 6 *
        slabParametricKPhysicalFaceFactor w K 1
          (centralVacuumSourcePhysical boundary target) := by
  unfold slabParametricKPhysicalFaceFactor
  have hpointwise :
      eliminateLinks
          (fun id => coeffAt (heatKernelPacket K w)
            (centralSpinCubeSourcePhysical spin boundary target id))
          (slabPhysicalFaceEdges 1) ≈
        eliminateLinks
          (fun id =>
            (if id ∈ centralLowerCubeFaceIds
              then coeffW w spin else 1) *
            coeffAt (heatKernelPacket K w)
              (centralVacuumSourcePhysical boundary target id))
          (slabPhysicalFaceEdges 1) := by
    apply eliminateLinks_congr_on
    intro id _hid
    exact centralSpinCube_faceCoefficient_factor
      w hspin boundary target id
  have hsplit := eliminateLinks_pointwise_mul
    (fun id => if id ∈ centralLowerCubeFaceIds
      then coeffW w spin else 1)
    (fun id => coeffAt (heatKernelPacket K w)
      (centralVacuumSourcePhysical boundary target id))
    (slabPhysicalFaceEdges 1)
  have hpower := eliminateLinks_indicator_pow
    centralLowerCubeFaceIds (coeffW w spin)
    (slabPhysicalFaceEdges 1)
  have hcount :
      ((slabPhysicalFaceEdges 1).filter
        (fun id => decide (id ∈ centralLowerCubeFaceIds))).length = 6 := by
    decide
  rw [hcount] at hpower
  exact Q'.eqv_trans _ _ _ hpointwise
    (Q'.eqv_trans _ _ _ hsplit
      (Q'.mul_eqv_congr_right _ _ _ hpower))

/-! ## 2. Twelfth powers become decorated non-source activities -/

def centralSpinCubeResidualDecoratedFaceProduct
    (w : Q') (boundary target : EdgeLabelling) : Q' :=
  eliminateLinks
    (fun id => tailTerm w 13
      (centralVacuumSourcePhysical boundary target id))
    centralSpinCubeNonSourceFaceIds

theorem centralVacuumFaceFactor_mul_twelfth_eqv_decorated
    (w : Q') {K : Nat}
    (boundary target : EdgeLabelling)
    (hboundary : boundary ∈ centralBoundaryChannels K 0)
    (htarget : target ∈ centralHalfStates K 0) :
    slabParametricKPhysicalFaceFactor w K 1
        (centralVacuumSourcePhysical boundary target) *
      Q'.ofNat
        (centralSpinCubeResidualFaceTwelfthProduct boundary target) ≈
      centralSpinCubeResidualDecoratedFaceProduct
        w boundary target := by
  let coefficient : Nat -> Q' := fun id =>
    coeffAt (heatKernelPacket K w)
      (centralVacuumSourcePhysical boundary target id)
  let charge : Nat -> Nat := fun id =>
    (centralVacuumSourcePhysical boundary target id + 1) ^ 12
  have hzeroSource :
      zeroEdgeLabelling ∈ centralHalfStates K 0 := by
    unfold centralHalfStates
    apply boundedEdgeLabellings_complete
    · intro _id _hid
      change 0 < K + 1
      omega
    · intro _id _hid
      rfl
  have hphysical : SlabFaceLabellingBounded K 1
      (centralVacuumSourcePhysical boundary target) := by
    unfold centralVacuumSourcePhysical
    exact assembleReflectedSlabLabelling_bounded
      hzeroSource hboundary htarget
  have hfilter :
      slabParametricKPhysicalFaceFactor w K 1
          (centralVacuumSourcePhysical boundary target) ≈
        eliminateLinks coefficient centralSpinCubeNonSourceFaceIds := by
    unfold slabParametricKPhysicalFaceFactor
      centralSpinCubeNonSourceFaceIds coefficient
    apply eliminateLinks_eqv_filter_of_one
    intro id hid htest
    have hcubeBool : decide (id ∈ centralLowerCubeFaceIds) = true := by
      cases hcube : decide (id ∈ centralLowerCubeFaceIds) <;>
        simp [hcube] at htest ⊢
    have hcube : id ∈ centralLowerCubeFaceIds :=
      of_decide_eq_true hcubeBool
    rw [centralVacuumSourcePhysical_eq_zero_on_cube
        boundary target hcube,
      coeffAt_heatKernelPacket (Nat.zero_lt_succ K), coeffW_zero]
    exact Q'.eqv_refl 1
  have hpair :
      eliminateLinks coefficient centralSpinCubeNonSourceFaceIds *
          Q'.ofNat
            (centralSpinCubeResidualFaceTwelfthProduct boundary target) ≈
        centralSpinCubeResidualDecoratedFaceProduct
          w boundary target := by
    unfold centralSpinCubeResidualFaceTwelfthProduct
      centralSpinCubeResidualDecoratedFaceProduct
    refine Q'.eqv_trans _ _ _
      (eliminateLinks_pair_natProduct_eqv coefficient
        (fun id =>
          (centralVacuumSourcePhysical boundary target id + 1) ^ 12)
        centralSpinCubeNonSourceFaceIds) ?_
    apply eliminateLinks_congr_on
    intro id hid
    have hidPhysical : id ∈ slabPhysicalFaceEdges 1 :=
      (List.mem_filter.mp hid).1
    have hbound := hphysical id hidPhysical
    unfold coefficient
    rw [coeffAt_heatKernelPacket (Nat.lt_succ_of_le hbound)]
    exact coeffW_mul_twelfth_eqv_decoratedActivity
      w (centralVacuumSourcePhysical boundary target id)
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hfilter) hpair

end YMGap.Continuum.BF4CentralSpinCubeResidualDecoratedFaceBound

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4CentralSpinCubeResidualDecoratedFaceBound.centralSpinCube_faceCoefficient_factor
#print axioms YMGap.Continuum.BF4CentralSpinCubeResidualDecoratedFaceBound.centralSpinCubePhysicalFaceFactor_eqv_activity_mul_vacuum
#print axioms YMGap.Continuum.BF4CentralSpinCubeResidualDecoratedFaceBound.centralVacuumFaceFactor_mul_twelfth_eqv_decorated
