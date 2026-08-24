/-
# A nonzero completed moving-centered BF4 cube observable

The moving rational centering construction changes only the distinguished
vacuum coordinate.  At cutoff one and half-extent zero, the canonical vacuum
component also contains the explicit central lower-cube state.  Its indicator
coordinate therefore remains exactly one at every moving-centering stage.

This module first proves a reusable coordinate compiler: the moving positive
row floor at `max base uniformFloorCutoff` times the square of any fixed
base-sector coordinate difference is bounded by the actual cutoff-removed
physical squared distance.  Applied to the cutoff-one cube coordinate, that
gives a stage-independent positive lower bound.  An equality of the completed
moving vector with completed zero would supply an explicit closeness modulus
at half that floor, which is impossible.

Together with the preceding orthogonality theorem this produces a concrete
nonzero vector in the actual completed vacuum complement.  It does not yet
identify same-object transfer moments, inhabit the dynamic observable pin, or
make a thermodynamic, continuum, or Clay claim.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumOrthogonal
import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorPresentation
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule
import YMGap.Continuum.TrueMarginRecursionPhysical

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSector
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumPairing
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A positive floor for every fixed base-sector coordinate -/

/-- Retain both the fixed base carrier and the already proved unit-tail
cutoff before measuring a coordinate. -/
def centralPhysicalVacuumSectorCoordinateAnchor
    (w : Q') (base half : Nat) : Nat :=
  max (centralPhysicalUniformRowFloorCutoff w half) base

/-- The moving positive-row floor at the retained coordinate anchor. -/
def centralPhysicalVacuumSectorCoordinateFloor
    (w : Q') (hw : (0 : Q') ≤ w) (base half : Nat) : Q' :=
  centralPhysicalMovingPositiveRowFloor w hw
    (centralPhysicalVacuumSectorCoordinateAnchor w base half) half

theorem centralPhysicalVacuumSectorCoordinateFloor_pos
    (w : Q') (hw : (0 : Q') ≤ w) (base half : Nat) :
    (0 : Q') <
      centralPhysicalVacuumSectorCoordinateFloor w hw base half := by
  exact centralPhysicalMovingPositiveRowFloor_pos w hw
    (centralPhysicalVacuumSectorCoordinateAnchor w base half) half

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A},
      item ∈ items → value item ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun tailItem _ => hvalue tailItem))
      · have ih := listQSum_member_le_nonnegative_local
          value hvalue tail htail
        have htailLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          exact Q'.le_trans' _ (listQSum value tail + value head) _
            (Q'.add_le_self_of_nonneg
              (listQSum value tail) (value head) (hvalue head))
            (Q'.le_of_eqv
              (Q'.add_comm_eqv (listQSum value tail) (value head)))
        exact Q'.le_trans' _ _ _ ih htailLe

/-- A fixed base-sector coordinate is continuously visible in the actual
cutoff-removed squared distance.  The only price is the explicit moving
positive-row floor at the first cutoff retaining both the coordinate and the
uniform unit-tail estimate. -/
theorem centralPhysicalVacuumSectorCylinder_coordinateDifferenceSq_floor_le_distSq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half index : Nat)
    (hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half)
    (left right : Nat → Q') :
    CReal.leEv
      (CReal.ofQ'
        (centralPhysicalVacuumSectorCoordinateFloor
            w (Q'.le_of_lt hw0) base half *
          ((left index + -(right index)) *
            (left index + -(right index)))))
      ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).distSq
        { base := base, coefficient := left }
        { base := base, coefficient := right }) := by
  intro epsilon hepsilon
  let anchor := centralPhysicalVacuumSectorCoordinateAnchor w base half
  refine ⟨anchor, fun later hlater => ?_⟩
  have hbaseAnchor : base ≤ anchor := Nat.le_max_right _ _
  have hfloorAnchor :
      centralPhysicalUniformRowFloorCutoff w half ≤ anchor :=
    Nat.le_max_left _ _
  have hbaseLater : base ≤ later := Nat.le_trans hbaseAnchor hlater
  have hindexLt : index < centralPhysicalFiniteCarrierSize
      w (Q'.le_of_lt hw0) base half :=
    centralPhysicalFiniteVacuumSectorIndex_lt
      w (Q'.le_of_lt hw0) base half hindex
  let target := centralPhysicalFiniteCutoffIndexMap
    w (Q'.le_of_lt hw0) base later half index
  have htargetLt : target < centralPhysicalFiniteCarrierSize
      w (Q'.le_of_lt hw0) later half :=
    centralPhysicalFiniteCutoffIndexMap_lt hbaseLater hindexLt
  let leftPresentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half := { base := base, coefficient := left }
  let rightPresentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half := { base := base, coefficient := right }
  let D := (centralPhysicalSmulGNS
    w (Q'.le_of_lt hw0) later half).toGNSData
  let difference := D.sub
    leftPresentation.toLinearObservable.value
    rightPresentation.toLinearObservable.value
  let coefficient := centralPhysicalFiniteCoefficient
    w (Q'.le_of_lt hw0) later half difference
  let weight := centralPhysicalFiniteWeight
    w (Q'.le_of_lt hw0) later half
  let delta := left index + -(right index)
  let floor := centralPhysicalVacuumSectorCoordinateFloor
    w (Q'.le_of_lt hw0) base half
  have hleftCoordinate :
      centralPhysicalFiniteCoefficient
          w (Q'.le_of_lt hw0) later half
          leftPresentation.toLinearObservable.value target ≈
        left index := by
    exact Q'.eqv_trans _ _ _
      (centralPhysicalFiniteCoefficient_linearObservable_eqv_extension
        hbaseLater left htargetLt)
      (centralPhysicalFiniteVacuumSectorCoefficientExtension_on_map
        hbaseLater hindex left)
  have hrightCoordinate :
      centralPhysicalFiniteCoefficient
          w (Q'.le_of_lt hw0) later half
          rightPresentation.toLinearObservable.value target ≈
        right index := by
    exact Q'.eqv_trans _ _ _
      (centralPhysicalFiniteCoefficient_linearObservable_eqv_extension
        hbaseLater right htargetLt)
      (centralPhysicalFiniteVacuumSectorCoefficientExtension_on_map
        hbaseLater hindex right)
  have hcoordinate : coefficient target ≈ delta := by
    change leftPresentation.toLinearObservable.value
          (centralPhysicalFiniteStateAt
            w (Q'.le_of_lt hw0) later half target) +
        -(rightPresentation.toLinearObservable.value
          (centralPhysicalFiniteStateAt
            w (Q'.le_of_lt hw0) later half target)) ≈ delta
    exact Q'.add_eqv_congr' hleftCoordinate
      (Q'.neg_eqv_congr _ _ hrightCoordinate)
  have hcoordinateSq :
      coefficient target * coefficient target ≈ delta * delta :=
    Q'.eqv_trans _ (delta * coefficient target) _
      (Q'.mul_eqv_congr_right _ _ _ hcoordinate)
      (Q'.mul_eqv_congr_left delta _ _ hcoordinate)
  have hsourceAnchor :
      centralPhysicalFiniteStateAt w (Q'.le_of_lt hw0) base half index ∈
        centralPositiveHalfStates w (Q'.le_of_lt hw0) anchor half := by
    exact mem_centralPositiveHalfStates_of_le (Q'.le_of_lt hw0)
      hbaseAnchor
      (centralPhysicalFiniteStateAt_mem_positive
        w (Q'.le_of_lt hw0) base half hindexLt)
  have hfloor : floor ≤ weight target := by
    have hrow := centralPhysicalMovingPositiveRowFloor_le
      hw0 hw1 half hfloorAnchor hlater hsourceAnchor
    unfold floor centralPhysicalVacuumSectorCoordinateFloor weight
      centralPhysicalFiniteWeight target
    rw [centralPhysicalFiniteStateAt_cutoffIndexMap_eq
      hbaseLater hindexLt]
    exact hrow
  have hterm :
      (coefficient target * coefficient target) * weight target ≤
        finiteDiagonalQuadratic
          (centralPhysicalFiniteCarrierSize
            w (Q'.le_of_lt hw0) later half)
          weight coefficient := by
    unfold finiteDiagonalQuadratic
    exact listQSum_member_le_nonnegative_local
      (fun item => (coefficient item * coefficient item) * weight item)
      (fun item => Q'.mul_nonneg _ _
        (q_mul_self_nonneg (coefficient item))
        (centralPhysicalRowMarginal_nonnegative
          (Q'.le_of_lt hw0) later half
          (centralPhysicalFiniteStateAt
            w (Q'.le_of_lt hw0) later half item)))
      (List.range
        (centralPhysicalFiniteCarrierSize
          w (Q'.le_of_lt hw0) later half))
      (List.mem_range.mpr htargetLt)
  have hfloorTerm : floor * (delta * delta) ≤
      (coefficient target * coefficient target) * weight target := by
    have hscaled : (delta * delta) * floor ≤
        (delta * delta) * weight target :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hfloor
        (q_mul_self_nonneg delta)
    exact le_of_eqv_le (Q'.mul_comm_eqv floor (delta * delta))
      (le_of_le_eqv hscaled
        (Q'.eqv_trans _
          ((coefficient target * coefficient target) * weight target) _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.eqv_symm hcoordinateSq))
          (Q'.eqv_refl _)))
  have hdiag : floor * (delta * delta) ≤ D.distSqQ
      leftPresentation.toLinearObservable.value
      rightPresentation.toLinearObservable.value := by
    have hbridge := centralPhysicalFiniteDiagonalQuadratic_eqv_weightedInner
      w (Q'.le_of_lt hw0) later half difference
    have hweighted := le_of_le_eqv hterm hbridge
    exact Q'.le_trans' _ _ _ hfloorTerm (by
      simpa only [D, GNSQuotient.GNSData.distSqQ, difference,
        centralPhysicalSmulGNS_B_eq] using hweighted)
  have hstage := physicalLinearDistSq_approx_eqv_stage
    hw0 hw1 half later leftPresentation.toLinearObservable
      rightPresentation.toLinearObservable
  exact Q'.le_trans' _ _ _ hdiag
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hstage)
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon)))

/-! ## 2. The concrete cutoff-one cube coordinate -/

/-- The constructive finite-carrier index of the central lower-cube state at
the exact cutoff-one, half-extent-zero carrier. -/
def centralPhysicalCutoffOneCubeIndex
    (w : Q') (hw0 : (0 : Q') < w) : Nat :=
  centralPhysicalFiniteIndexOfState w (Q'.le_of_lt hw0) 1 0
    centralLowerCubeState

theorem centralPhysicalCutoffOneCubeIndex_state
    (w : Q') (hw0 : (0 : Q') < w) :
    centralPhysicalFiniteStateAt w (Q'.le_of_lt hw0) 1 0
        (centralPhysicalCutoffOneCubeIndex w hw0) =
      centralLowerCubeState := by
  exact centralPhysicalFiniteStateAt_indexOfState_eq
    (centralLowerCubeState_mem_centralPositiveHalfStates hw0 (by decide))

theorem centralPhysicalCutoffOneCubeIndex_mem_vacuumSector
    (w : Q') (hw0 : (0 : Q') < w) :
    centralPhysicalCutoffOneCubeIndex w hw0 ∈
      centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw0) 1 0 := by
  have hcube := centralLowerCubeState_mem_cutoffOneCanonicalVacuumSector hw0
  rcases List.mem_map.mp hcube with ⟨index, hindex, hstate⟩
  have hcubeLt : centralPhysicalCutoffOneCubeIndex w hw0 <
      centralPhysicalFiniteCarrierSize w (Q'.le_of_lt hw0) 1 0 :=
    centralPhysicalFiniteIndexOfState_lt
      (centralLowerCubeState_mem_centralPositiveHalfStates hw0 (by decide))
  have hindexLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w (Q'.le_of_lt hw0) 1 0 hindex
  have heq : centralPhysicalCutoffOneCubeIndex w hw0 = index :=
    centralPhysicalFiniteStateAt_injective_of_lt hcubeLt hindexLt
      ((centralPhysicalCutoffOneCubeIndex_state w hw0).trans hstate.symm)
  exact heq ▸ hindex

theorem centralPhysicalCutoffOneCubeIndex_ne_zero
    (w : Q') (hw0 : (0 : Q') < w) :
    centralPhysicalCutoffOneCubeIndex w hw0 ≠ 0 := by
  intro heq
  have hstate := centralPhysicalCutoffOneCubeIndex_state w hw0
  rw [heq, centralPhysicalFiniteStateAt_zero_eq_vacuum] at hstate
  exact centralLowerCubeState_ne_zero hstate.symm

/-- The fixed raw cylinder is the indicator of the explicit cube coordinate
inside the cutoff-one canonical component. -/
def centralPhysicalCutoffOneCubeIndicatorCoefficient
    (w : Q') (hw0 : (0 : Q') < w) (index : Nat) : Q' :=
  if index = centralPhysicalCutoffOneCubeIndex w hw0 then 1 else 0

theorem centralPhysicalCutoffOneCubeIndicatorCoefficient_at_cube
    (w : Q') (hw0 : (0 : Q') < w) :
    centralPhysicalCutoffOneCubeIndicatorCoefficient
        w hw0 (centralPhysicalCutoffOneCubeIndex w hw0) = 1 := by
  unfold centralPhysicalCutoffOneCubeIndicatorCoefficient
  simp

/-- Moving root centering leaves the nonroot cube coordinate exactly one. -/
theorem centralPhysicalCutoffOneCubeMovingCenteredCoefficient_at_cube
    (w : Q') (hw0 : (0 : Q') < w) (stage : Nat) :
    (centralPhysicalVacuumSectorMovingCenteredPresentation
        hw0 1 0
        (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)
        stage).coefficient
        (centralPhysicalCutoffOneCubeIndex w hw0) ≈
      1 := by
  have hshift :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient_eqv_rootShift
      hw0 1 stage 0 (centralPhysicalCutoffOneCubeIndex w hw0)
      (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)
  refine Q'.eqv_trans _ _ _ hshift ?_
  unfold finiteRootIndicator
  rw [if_neg (centralPhysicalCutoffOneCubeIndex_ne_zero w hw0)]
  refine Q'.eqv_trans _
    (centralPhysicalCutoffOneCubeIndicatorCoefficient
      w hw0 (centralPhysicalCutoffOneCubeIndex w hw0) + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _)
  · rw [centralPhysicalCutoffOneCubeIndicatorCoefficient_at_cube]
    exact Q'.eqv_of_eq (Q'.add_zero' 1)

private theorem q_neg_zero_eqv : (-(0 : Q')) ≈ 0 := by decide

private theorem cubeMovingCentered_delta_eqv_one
    (w : Q') (hw0 : (0 : Q') < w) (stage : Nat) :
    (centralPhysicalVacuumSectorMovingCenteredPresentation
        hw0 1 0
        (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)
        stage).coefficient
          (centralPhysicalCutoffOneCubeIndex w hw0) + -(0 : Q') ≈
      1 := by
  refine Q'.eqv_trans _
    ((centralPhysicalVacuumSectorMovingCenteredPresentation
      hw0 1 0
      (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)
      stage).coefficient
        (centralPhysicalCutoffOneCubeIndex w hw0) + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _ q_neg_zero_eqv
  · exact Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (Q'.add_zero' _))
      (centralPhysicalCutoffOneCubeMovingCenteredCoefficient_at_cube
        w hw0 stage)

private theorem cubeMovingCentered_floorDeltaSq_eqv_floor
    (w : Q') (hw0 : (0 : Q') < w) (stage : Nat) :
    let floor := centralPhysicalVacuumSectorCoordinateFloor
      w (Q'.le_of_lt hw0) 1 0
    let delta :=
      (centralPhysicalVacuumSectorMovingCenteredPresentation
        hw0 1 0
        (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)
        stage).coefficient
          (centralPhysicalCutoffOneCubeIndex w hw0) + -(0 : Q')
    floor * (delta * delta) ≈ floor := by
  dsimp only
  have hdelta := cubeMovingCentered_delta_eqv_one w hw0 stage
  refine Q'.eqv_trans _
    (centralPhysicalVacuumSectorCoordinateFloor
      w (Q'.le_of_lt hw0) 1 0 * ((1 : Q') * 1)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ (1 * _) _
        (Q'.mul_eqv_congr_right _ _ _ hdelta)
        (Q'.mul_eqv_congr_left 1 _ _ hdelta))
  · refine Q'.eqv_trans _
      (centralPhysicalVacuumSectorCoordinateFloor
        w (Q'.le_of_lt hw0) 1 0 * 1) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv 1)
    · exact Q'.mul_one_eqv _

private theorem centralPhysicalFiniteVacuumSectorLinearObservable_zero_equivalent
    {w : Q'} {hw : (0 : Q') ≤ w} (base half : Nat) :
    Equivalent
      (centralPhysicalFiniteVacuumSectorLinearObservable
        w hw base half (fun _ => 0))
      zero := by
  intro state
  change
    (centralPhysicalFiniteVacuumSectorLinearObservable
      w hw base half (fun _ => 0)).value state ≈ 0
  refine Q'.eqv_trans _
    (listQSum
      (fun _index => (0 : Q'))
      (centralPhysicalFiniteVacuumSectorIndices w hw base half)) _ ?_ ?_
  · refine Q'.eqv_trans _
      (listQSum
        (fun index =>
          if labellingsAgreeOnB (centralLowerFaceIds half) state
              (centralPhysicalFiniteStateAt w hw base half index)
          then (0 : Q') else 0)
        (centralPhysicalFiniteVacuumSectorIndices w hw base half)) _ ?_ ?_
    · exact centralPhysicalStateCylinderLinearCombination_value
        half (centralPhysicalFiniteStateAt w hw base half)
        (fun _ => 0) state
        (centralPhysicalFiniteVacuumSectorIndices w hw base half)
    · apply listQSum_congr_on
      intro index _hindex
      by_cases hagree : labellingsAgreeOnB
          (centralLowerFaceIds half) state
          (centralPhysicalFiniteStateAt w hw base half index) = true
      · simp only [hagree, if_true]
        exact Q'.eqv_refl 0
      · have hfalse : labellingsAgreeOnB
            (centralLowerFaceIds half) state
            (centralPhysicalFiniteStateAt w hw base half index) = false := by
          cases hvalue : labellingsAgreeOnB
              (centralLowerFaceIds half) state
              (centralPhysicalFiniteStateAt w hw base half index)
          · rfl
          · exact False.elim (hagree hvalue)
        simp only [hfalse, Bool.false_eq_true, if_false]
        exact Q'.eqv_refl 0
  · exact listQSum_zero
      (centralPhysicalFiniteVacuumSectorIndices w hw base half)

/-- The canonical zero-valued cutoff-one sector presentation used to compare
the moving representative with zero before applying the injective global
embedding. -/
def centralPhysicalCutoffOneZeroPresentation
    {w : Q'} (hw0 : (0 : Q') < w) :
    CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) 0 :=
  { base := 1, coefficient := fun _ => 0 }

/-- At every moving stage, the sector squared distance to the canonical
zero-valued presentation has the same fixed positive cube-coordinate floor. -/
theorem centralPhysicalCutoffOneCubeMovingCentered_stage_floor_le_zeroPresentationDistSq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (stage : Nat) :
    CReal.leEv
      (CReal.ofQ' (centralPhysicalVacuumSectorCoordinateFloor
        w (Q'.le_of_lt hw0) 1 0))
      ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 0).distSq
        (centralPhysicalVacuumSectorMovingCenteredPresentation
          hw0 1 0
          (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)
          stage)
        (centralPhysicalCutoffOneZeroPresentation hw0)) := by
  have hlower :=
    centralPhysicalVacuumSectorCylinder_coordinateDifferenceSq_floor_le_distSq
      hw0 hw1 1 0 (centralPhysicalCutoffOneCubeIndex w hw0)
      (centralPhysicalCutoffOneCubeIndex_mem_vacuumSector w hw0)
      (centralPhysicalVacuumSectorMovingCenteredPresentation
        hw0 1 0
        (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)
        stage).coefficient
      (fun _ => 0)
  exact CReal.leEv_trans
    (CReal.leEv_of_equiv
      (CReal.ofQ'_equiv_of_eqv
        (Q'.eqv_symm
          (cubeMovingCentered_floorDeltaSq_eqv_floor w hw0 stage))))
    (by simpa only [centralPhysicalCutoffOneZeroPresentation] using hlower)

/-- Every dense stage representing the same moving-centered cube observable
has actual cutoff-removed squared distance from zero bounded below by one
fixed positive rational floor. -/
theorem centralPhysicalCutoffOneCubeMovingCentered_stage_floor_le_zeroDistSq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (stage : Nat) :
    CReal.leEv
      (CReal.ofQ' (centralPhysicalVacuumSectorCoordinateFloor
        w (Q'.le_of_lt hw0) 1 0))
      (physicalLinearDistSq hw0 hw1 0
        (centralPhysicalVacuumSectorMovingCenteredPresentation
          hw0 1 0
          (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)
          stage).toLinearObservable
        zero) := by
  have hlowerSector :=
    centralPhysicalCutoffOneCubeMovingCentered_stage_floor_le_zeroPresentationDistSq
      hw0 hw1 stage
  let moving :=
    (centralPhysicalVacuumSectorMovingCenteredPresentation
      hw0 1 0
      (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)
      stage).toLinearObservable
  let zeroPresentation := centralPhysicalCutoffOneZeroPresentation hw0
  have hleftNull : CReal.Equiv
      (physicalLinearDistSq hw0 hw1 0 moving moving) CReal.czero :=
    physicalLinearDistSq_refl hw0 hw1 0 moving
  have hrightNull : CReal.Equiv
      (physicalLinearDistSq hw0 hw1 0
        zeroPresentation.toLinearObservable zero) CReal.czero :=
    physicalLinearDistSq_equiv_czero_of_equivalent
      hw0 hw1 0
      (centralPhysicalFiniteVacuumSectorLinearObservable_zero_equivalent 1 0)
  have hreplace : CReal.Equiv
      (physicalLinearDistSq hw0 hw1 0
        moving zeroPresentation.toLinearObservable)
      (physicalLinearDistSq hw0 hw1 0 moving zero) :=
    physicalLinearDistSq_null_congr hw0 hw1 0 hleftNull hrightNull
  exact CReal.leEv_trans (by
    simpa only [centralPhysicalVacuumSectorCylinderSquaredSeminorm,
      moving, zeroPresentation] using hlowerSector)
    (CReal.leEv_of_equiv hreplace)

/-! ## 3. Completion anti-vacuity -/

private theorem q_half_mul_lt_self_local {value : Q'}
    (hvalue : (0 : Q') < value) :
    HalfPow.half * value < value := by
  have hscaled :=
    YMGap.Continuum.ClusteringImpliesGap.mul_lt_mul_of_pos_right
      hvalue (show HalfPow.half < (1 : Q') by decide)
  exact YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le hscaled
    (Q'.le_of_eqv (Q'.one_mul_eqv value))

/-- No explicit sector-closeness datum can identify the concrete moving cube
representative with the constant zero-valued sector representative. -/
theorem centralPhysicalCutoffOneCubeMovingCenteredSector_not_close_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    ¬ (centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 0).CompletionRel
      (centralPhysicalVacuumSectorMovingCenteredCauchy
        hw0 hw1 1 0
        (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))
      ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 0).constant
        (centralPhysicalCutoffOneZeroPresentation hw0)) := by
  intro hrel
  rcases hrel with ⟨hclose⟩
  let floor := centralPhysicalVacuumSectorCoordinateFloor
    w (Q'.le_of_lt hw0) 1 0
  have hfloor : (0 : Q') < floor :=
    centralPhysicalVacuumSectorCoordinateFloor_pos
      w (Q'.le_of_lt hw0) 1 0
  let epsilon := HalfPow.half * floor
  have hepsilon : (0 : Q') < epsilon :=
    ExpNeg.half_mul_pos floor hfloor
  let stage := hclose.modulus epsilon
  have hupper := hclose.close epsilon hepsilon stage (Nat.le_refl stage)
  change CReal.leEv
    ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 0).distSq
      (centralPhysicalVacuumSectorMovingCenteredPresentation
        hw0 1 0
        (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)
        stage)
      (centralPhysicalCutoffOneZeroPresentation hw0))
    (CReal.ofQ' epsilon) at hupper
  have hlower :=
    centralPhysicalCutoffOneCubeMovingCentered_stage_floor_le_zeroPresentationDistSq
      hw0 hw1 stage
  have hcollapsed : floor ≤ epsilon :=
    YMGap.Continuum.le_of_leEv_ofQ'
      (CReal.leEv_trans hlower hupper)
  have hbad : floor < floor := Q'.lt_of_le_of_lt hcollapsed
    (q_half_mul_lt_self_local hfloor)
  exact YMGap.Continuum.ClusteringImpliesGap.lt_irrefl' floor hbad

/-- The completed sector point represented by the canonical zero-valued
cutoff-one presentation. -/
def centralPhysicalCutoffOneSectorZeroCompletion
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 0 :=
  (centralPhysicalVacuumSectorCylinderSquaredSeminorm
    hw0 hw1 0).embedRep
    (centralPhysicalCutoffOneZeroPresentation hw0)

/-- The concrete moving sector completion is distinct from its zero-valued
sector point. -/
theorem centralPhysicalCutoffOneCubeMovingCenteredCompletion_ne_sectorZero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    centralPhysicalVacuumSectorMovingCenteredCompletion
        hw0 hw1 1 0
        (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0) ≠
      centralPhysicalCutoffOneSectorZeroCompletion hw0 hw1 := by
  intro hequal
  apply centralPhysicalCutoffOneCubeMovingCenteredSector_not_close_zero
    hw0 hw1
  exact Quotient.exact hequal

/-- The injective sector embedding sends the zero-valued sector point to the
public completed zero. -/
theorem centralPhysicalCutoffOneSectorZeroCompletion_toGlobal_eq_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    centralPhysicalVacuumSectorCylinderCompletionToGlobal
        (centralPhysicalCutoffOneSectorZeroCompletion hw0 hw1) =
      completedPhysicalLinearZero hw0 hw1 0 := by
  unfold centralPhysicalCutoffOneSectorZeroCompletion
  rw [centralPhysicalVacuumSectorCylinderCompletionToGlobal_embedRep]
  unfold completedPhysicalLinearZero embedCentralPhysicalLinearObservable
  apply (centralPhysicalCutoffLinearSquaredSeminorm
    hw0 hw1 0).embedRep_eq_of_null
  exact physicalLinearDistSq_equiv_czero_of_equivalent
    hw0 hw1 0
    (centralPhysicalFiniteVacuumSectorLinearObservable_zero_equivalent 1 0)

/-- The completed vector selected by the moving-centered cutoff-one cube
indicator is not the zero vector in the actual global physical completion. -/
theorem centralPhysicalCutoffOneCubeMovingCenteredGlobalVector_ne_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    centralPhysicalVacuumSectorMovingCenteredGlobalVector
        hw0 hw1 1 0
        (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0) ≠
      completedPhysicalLinearZero hw0 hw1 0 := by
  intro hequal
  apply centralPhysicalCutoffOneCubeMovingCenteredCompletion_ne_sectorZero
    hw0 hw1
  apply centralPhysicalVacuumSectorCylinderCompletionToGlobal_injective
  exact hequal.trans
    (centralPhysicalCutoffOneSectorZeroCompletion_toGlobal_eq_zero
      hw0 hw1).symm

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero.centralPhysicalVacuumSectorCylinder_coordinateDifferenceSq_floor_le_distSq
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero.centralPhysicalCutoffOneCubeMovingCentered_stage_floor_le_zeroDistSq
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero.centralPhysicalCutoffOneCubeMovingCenteredGlobalVector_ne_zero
