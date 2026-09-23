/-
# Dense BF4 sector tests read cutoff-limit retained coordinates

For a fixed finite-linear observable and a fixed canonical-sector cylinder,
the cutoff-removed pairing is the finite constructive-real sum of the
observable's retained rational coordinates, the test coefficients, and the
cutoff-removed pulled weights.  This is the cutoff-limit counterpart of the
same-stage finite identity and introduces no new estimate hypothesis.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFiniteTestPairing
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorDenseTestPairingLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFiniteTestPairing
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] centralPhysicalFiniteCarrierSize
  centralPhysicalFiniteIndexCarrier centralPhysicalFiniteVacuumSectorIndices
  centralPositiveHalfStates

/-- A deliberately small list sum on constructive reals. -/
def finiteCRealSum {A : Type} (value : A → CReal) : List A → CReal
  | [] => CReal.czero
  | head :: tail => CReal.add (value head) (finiteCRealSum value tail)

@[simp] theorem finiteCRealSum_approx {A : Type} (value : A → CReal) :
    ∀ (items : List A) (stage : Nat),
      (finiteCRealSum value items).approx stage =
        listQSum (fun item => (value item).approx stage) items
  | [], _ => rfl
  | head :: tail, stage => by
      change (value head).approx stage +
          (finiteCRealSum value tail).approx stage =
        (value head).approx stage +
          listQSum (fun item => (value item).approx stage) tail
      rw [finiteCRealSum_approx value tail stage]

/-- The retained-coordinate expression for pairing a fixed finite-linear
observable with one fixed sector presentation.  The totalized branch is read
only on canonical indices, where its carrier-bound proof is available. -/
def centralPhysicalVacuumSectorDenseTestCoordinateSum
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left : CentralPhysicalLinearObservable)
    (test : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) : CReal :=
  finiteCRealSum
    (fun index =>
      if hindex : index < centralPhysicalFiniteCarrierSize
          w (Q'.le_of_lt hw0) test.base half then
        CReal.mul
          (CReal.mul
            (CReal.ofQ' (left.value
              (centralPhysicalFiniteStateAt
                w (Q'.le_of_lt hw0) test.base half index)))
            (CReal.ofQ' (test.coefficient index)))
          (centralPhysicalFinitePulledWeightCutoffLimit
            hw0 hw1 test.base half index hindex)
      else CReal.czero)
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) test.base half)

private theorem cReal_equiv_of_eventual_approx_eqv
    {left right : CReal} (start : Nat)
    (h : ∀ stage, start ≤ stage →
      left.approx stage ≈ right.approx stage) :
    CReal.Equiv left right := by
  intro epsilon hepsilon
  refine ⟨start, fun stage hstage => ?_⟩
  have heq := h stage hstage
  exact
    ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
        (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon)),
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm heq))
        (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))⟩

/-- The cutoff-removed pairing with a fixed dense sector test is exactly its
finite retained-coordinate sum. -/
theorem innerLimit_equiv_denseTestCoordinateSum
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left : CentralPhysicalLinearObservable)
    (test : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    CReal.Equiv
      (innerLimit hw0 hw1 half left test.toLinearObservable)
      (centralPhysicalVacuumSectorDenseTestCoordinateSum
        hw0 hw1 half left test) := by
  apply cReal_equiv_of_eventual_approx_eqv test.base
  intro later hcutoff
  refine Q'.eqv_trans _
    ((centralPhysicalSmulGNS
      w (Q'.le_of_lt hw0) later half).toGNSData.B
      left.value test.toLinearObservable.value) _ ?_ ?_
  · exact innerLimit_approx_eqv_stage
      hw0 hw1 half later left test.toLinearObservable
  refine Q'.eqv_trans _
    (centralPhysicalWeightedInner w (Q'.le_of_lt hw0) later half
      left.value test.toLinearObservable.value) _ ?_ ?_
  · exact Q'.eqv_of_eq
      (centralPhysicalSmulGNS_B_eq
        w (Q'.le_of_lt hw0) later half _ _)
  refine Q'.eqv_trans _
    (listQSum
      (fun index =>
        (left.value (centralPhysicalFiniteStateAt
              w (Q'.le_of_lt hw0) test.base half index) *
            test.coefficient index) *
          centralPhysicalFinitePulledWeight
            w (Q'.le_of_lt hw0) test.base later half index)
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw0) test.base half)) _ ?_ ?_
  · exact weightedInner_linearObservable_eqv_coordinateSum
      hcutoff left.value test.coefficient
  unfold centralPhysicalVacuumSectorDenseTestCoordinateSum
  rw [finiteCRealSum_approx]
  apply listQSum_congr_on
  intro index hindex
  have hindexLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w (Q'.le_of_lt hw0) test.base half hindex
  simp only [dif_pos hindexLt]
  exact Q'.eqv_refl _

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorDenseTestPairingLimit

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorDenseTestPairingLimit.finiteCRealSum
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorDenseTestPairingLimit.finiteCRealSum_approx
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorDenseTestPairingLimit.centralPhysicalVacuumSectorDenseTestCoordinateSum
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorDenseTestPairingLimit.innerLimit_equiv_denseTestCoordinateSum
