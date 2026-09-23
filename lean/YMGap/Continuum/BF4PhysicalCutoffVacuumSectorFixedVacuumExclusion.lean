/-
# Fixed-vector exclusion in the orthogonal completed BF4 sector

Transfer-fixed sector vectors have one common persistent coordinate.  The
completed dense-test formula therefore makes their functional a scalar
multiple of the ambient vacuum functional.  Conditional dense-vacuum
rigidity then excludes every such vector from the actual vacuum complement,
except for the genuine embedded sector zero.

No completed sector vacuum, uniform gap, or additional analytic hypothesis
is introduced here.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCompletedTestPairing
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorDenseVacuumRigidity
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFixedCoordinate

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFixedVacuumExclusion

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCompletedTestPairing
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorDenseTestPairingLimit
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorDenseVacuumRigidity
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFixedCoordinate
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentCoordinate
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

attribute [local irreducible] centralPhysicalFiniteCarrierSize
  centralPhysicalFiniteIndexCarrier centralPhysicalFiniteVacuumSectorIndices
  centralPositiveHalfStates

private theorem rc_mul_zero (a : CReal.RC) :
    CReal.RCmul a CReal.RCzero = CReal.RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound
    (Equiv_of_approx_eqv (fun _ => Q'.mul_zero_eqv _))

private theorem rc_one_mul (a : CReal.RC) :
    CReal.RCmul (Quotient.mk CReal.crealSetoid CReal.cone) a = a := by
  rw [CReal.RCmul_comm]
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (CRealAlg.cmul_cone A)

private theorem rc_mul_assoc (a b c : CReal.RC) :
    CReal.RCmul a (CReal.RCmul b c) =
      CReal.RCmul (CReal.RCmul a b) c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound
    (Equiv_of_approx_eqv (fun _ => Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))

private theorem rc_mul_add (a b c : CReal.RC) :
    CReal.RCmul a (CReal.RCadd b c) =
      CReal.RCadd (CReal.RCmul a b) (CReal.RCmul a c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound
    (Equiv_of_approx_eqv (fun _ => Q'.mul_add_eqv _ _ _))

private theorem finiteRCSum_congr_on
    {A : Type} {left right : A → CReal.RC} :
    ∀ items : List A,
      (∀ item, item ∈ items → left item = right item) →
      finiteRCSum left items = finiteRCSum right items
  | [], _ => rfl
  | head :: tail, h => by
      simp only [finiteRCSum]
      rw [h head List.mem_cons_self]
      rw [finiteRCSum_congr_on tail
        (fun item hitem => h item (List.mem_cons_of_mem head hitem))]

private theorem finiteRCSum_factor
    {A : Type} (scalar : CReal.RC) (value : A → CReal.RC) :
    ∀ items : List A,
      finiteRCSum (fun item => CReal.RCmul scalar (value item)) items =
        CReal.RCmul scalar (finiteRCSum value items)
  | [] => (rc_mul_zero scalar).symm
  | head :: tail => by
      simp only [finiteRCSum]
      rw [finiteRCSum_factor scalar value tail, rc_mul_add]

private theorem rc_scalar_vacuum_term
    (scalar coefficient weight : CReal.RC) :
    CReal.RCmul scalar
        (CReal.RCmul
          (CReal.RCmul
            (Quotient.mk CReal.crealSetoid CReal.cone) coefficient)
          weight) =
      CReal.RCmul (CReal.RCmul scalar coefficient) weight := by
  rw [rc_one_mul, rc_mul_assoc]

private theorem vacuum_completed_inner_eq_coordinate_sum
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (test : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalCutoffCompletedVacuum hw0 hw1 half)
        (embedCentralPhysicalLinearObservable hw0 hw1 half
          test.toLinearObservable) =
      Quotient.mk CReal.crealSetoid
        (centralPhysicalVacuumSectorDenseTestCoordinateSum
          hw0 hw1 half centralPhysicalLinearVacuum test) := by
  unfold centralPhysicalCutoffCompletedVacuum
    embedCentralPhysicalLinearObservable
  rw [centralPhysicalCutoffCompletedInner_embedRep]
  exact Quotient.sound
    (innerLimit_equiv_denseTestCoordinateSum
      hw0 hw1 half centralPhysicalLinearVacuum test)

/-- The proved common coordinate of a transfer-fixed sector vector supplies
the dense proportionality identity; no such identity is assumed. -/
theorem fixed_completed_pairing_is_vacuum_multiple
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (vector : CentralPhysicalCutoffVacuumSectorCylinderCompletion
      hw0 hw1 half)
    (hfixed : centralPhysicalVacuumSectorCylinderCompletedTransfer
      hw0 hw1 half vector = vector)
    (test : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        vector
        ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).embedRep test) =
      CReal.RCmul
        (completedCoordinate hw0 hw1 0 half 0
          (zero_mem_centralPhysicalFiniteVacuumSectorIndices
            w (Q'.le_of_lt hw0) 0 half) vector)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          (centralPhysicalCutoffCompletedVacuum hw0 hw1 half)
          (embedCentralPhysicalLinearObservable hw0 hw1 half
            test.toLinearObservable)) := by
  let common := completedCoordinate hw0 hw1 0 half 0
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) 0 half) vector
  rw [completedInner_embedRep_eq_completedDenseTestCoordinateSum]
  rw [vacuum_completed_inner_eq_coordinate_sum hw0 hw1 half test]
  unfold completedDenseTestCoordinateSum
    centralPhysicalVacuumSectorDenseTestCoordinateSum
  rw [← finiteRCSum_mk]
  rw [← finiteRCSum_factor common]
  apply finiteRCSum_congr_on
  intro index hindex
  have hindexLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w (Q'.le_of_lt hw0) test.base half hindex
  simp only [dif_pos hindex, dif_pos hindexLt]
  rw [← completedCoordinates_eq_across_bases_of_fixed
    hw0 hw1 0 test.base half 0 index
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) 0 half) hindex vector hfixed]
  change CReal.RCmul
      (CReal.RCmul common
        (Quotient.mk CReal.crealSetoid
          (CReal.ofQ' (test.coefficient index))))
      (Quotient.mk CReal.crealSetoid
        (centralPhysicalFinitePulledWeightCutoffLimit
          hw0 hw1 test.base half index hindexLt)) = _
  exact (rc_scalar_vacuum_term common
    (Quotient.mk CReal.crealSetoid
      (CReal.ofQ' (test.coefficient index)))
    (Quotient.mk CReal.crealSetoid
      (centralPhysicalFinitePulledWeightCutoffLimit
        hw0 hw1 test.base half index hindexLt))).symm

/-- An actual transfer-fixed vector in the ambient global-vacuum complement
is the genuine zero of the completed physical vacuum sector. -/
theorem fixed_eq_zero_of_global_vacuum_orthogonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (vector : CentralPhysicalCutoffVacuumSectorCylinderCompletion
      hw0 hw1 half)
    (hfixed : centralPhysicalVacuumSectorCylinderCompletedTransfer
      hw0 hw1 half vector = vector)
    (horthogonal : CentralPhysicalCutoffCompletedVacuumOrthogonal
      hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCompletionToGlobal vector)) :
    vector =
      (centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).embedRep
        (centralPhysicalVacuumSectorZeroPresentation
          (w := w) (hw := Q'.le_of_lt hw0) (half := half)) := by
  apply sector_eq_zero_of_orthogonal_and_dense_vacuum_proportional
    hw0 hw1 half
    (completedCoordinate hw0 hw1 0 half 0
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw0) 0 half) vector)
    vector horthogonal
  intro test
  exact fixed_completed_pairing_is_vacuum_multiple
    hw0 hw1 half vector hfixed test

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFixedVacuumExclusion

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFixedVacuumExclusion.fixed_completed_pairing_is_vacuum_multiple
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFixedVacuumExclusion.fixed_eq_zero_of_global_vacuum_orthogonal
