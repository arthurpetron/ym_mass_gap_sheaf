/-
# The completed BF4 sector vacuum pairing is the pulled sector mean

The direct sector-local Poincare route uses moving coefficients whose pulled
mean is exactly zero.  To relate that finite condition to the actual completed
sector vacuum complement, this file identifies the completed global-vacuum
pairing of every dense root-sector cylinder with its pulled weighted-mean
cutoff limit.

This is the mean-form half of the moving head-centering bridge.  It does not
yet prove that the rational head corrections vanish in completed norm for an
orthogonal vector, nor a carrier-independent strict rate, thermodynamic
limit, continuum QFT, or Clay mass-gap theorem.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm
import YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseVacuumPairing

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFullCarrierContraction
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The finite dense mean identity -/

private theorem finiteWeightedMean_coefficient_congr_local
    (n : Nat) (weight left right : Nat → Q')
    (h : ∀ index, index < n → left index ≈ right index) :
    finiteWeightedMean n weight left ≈
      finiteWeightedMean n weight right := by
  unfold finiteWeightedMean
  apply listQSum_congr_on
  intro index hindex
  exact Q'.mul_eqv_congr_right _ _ _
    (h index (List.mem_range.mp hindex))

private theorem centralPhysicalFiniteVacuumSectorLinearObservable_fullMean_eqv_extension
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (coefficient : Nat → Q') :
    finiteWeightedMean
        (centralPhysicalFiniteCarrierSize w hw later half)
        (centralPhysicalFiniteWeight w hw later half)
        (centralPhysicalFiniteCoefficient w hw later half
          (centralPhysicalFiniteVacuumSectorLinearObservable
            w hw base half coefficient).value) ≈
      finiteWeightedMean
        (centralPhysicalFiniteCarrierSize w hw later half)
        (centralPhysicalFiniteWeight w hw later half)
        (centralPhysicalFiniteVacuumSectorCoefficientExtension
          w hw base later half coefficient) := by
  apply finiteWeightedMean_coefficient_congr_local
  intro target htarget
  exact centralPhysicalFiniteCoefficient_linearObservable_eqv_extension
    hcutoff coefficient htarget

/-- At every cutoff containing a root-sector presentation, pairing its dense
observable with the constant vacuum is exactly the pulled sector mean. -/
theorem centralPhysicalFiniteVacuumSectorLinearObservable_vacuumPairing_eqv_pulledMean
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (coefficient : Nat → Q') :
    centralPhysicalWeightedInner w hw later half
        (centralPhysicalFiniteVacuumSectorLinearObservable
          w hw base half coefficient).value
        centralPhysicalVacuumCarrier ≈
      centralPhysicalFinitePulledVacuumSectorWeightedMean
        w hw base later half coefficient := by
  refine Q'.eqv_trans _
    (centralPhysicalStationaryMean w hw later half
      (centralPhysicalFiniteVacuumSectorLinearObservable
        w hw base half coefficient).value) _
      (centralPhysicalWeightedInner_vacuum_right
        w hw later half
        (centralPhysicalFiniteVacuumSectorLinearObservable
          w hw base half coefficient).value) ?_
  refine Q'.eqv_trans _
    (finiteWeightedMean
      (centralPhysicalFiniteCarrierSize w hw later half)
      (centralPhysicalFiniteWeight w hw later half)
      (centralPhysicalFiniteCoefficient w hw later half
        (centralPhysicalFiniteVacuumSectorLinearObservable
          w hw base half coefficient).value)) _
      (Q'.eqv_symm
        (centralPhysicalFiniteWeightedMean_eqv_stationaryMean
          w hw later half
          (centralPhysicalFiniteVacuumSectorLinearObservable
            w hw base half coefficient).value)) ?_
  refine Q'.eqv_trans _
    (finiteWeightedMean
      (centralPhysicalFiniteCarrierSize w hw later half)
      (centralPhysicalFiniteWeight w hw later half)
      (centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw base later half coefficient)) _ ?_ ?_
  · exact
      centralPhysicalFiniteVacuumSectorLinearObservable_fullMean_eqv_extension
        hcutoff coefficient
  · exact centralPhysicalFiniteFullCarrierCoefficientExtensionMean_eqv_pulled
      hcutoff coefficient

/-! ## 2. Passage to the cutoff limit and actual completion -/

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

/-- The limiting pairing of a dense sector cylinder with the global vacuum is
the pulled sector weighted-mean cutoff limit. -/
theorem centralPhysicalVacuumSectorCylinder_innerLimitVacuum_equiv_pulledMean
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    CReal.Equiv
      (innerLimit hw0 hw1 half
        presentation.toLinearObservable centralPhysicalLinearVacuum)
      (centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit
        hw0 hw1 presentation.base half presentation.coefficient) := by
  apply cReal_equiv_of_eventual_approx_eqv presentation.base
  intro later hcutoff
  refine Q'.eqv_trans _
    ((centralPhysicalSmulGNS
      w (Q'.le_of_lt hw0) later half).toGNSData.B
      presentation.toLinearObservable.value
      centralPhysicalVacuumCarrier) _ ?_ ?_
  · exact innerLimit_approx_eqv_stage
      hw0 hw1 half later
      presentation.toLinearObservable centralPhysicalLinearVacuum
  refine Q'.eqv_trans _
    (centralPhysicalWeightedInner w (Q'.le_of_lt hw0) later half
      presentation.toLinearObservable.value centralPhysicalVacuumCarrier) _
      (Q'.eqv_of_eq (centralPhysicalSmulGNS_B_eq
        w (Q'.le_of_lt hw0) later half _ _)) ?_
  exact
    centralPhysicalFiniteVacuumSectorLinearObservable_vacuumPairing_eqv_pulledMean
      hcutoff presentation.coefficient

/-- On every dense root-sector cylinder, its actual completed pairing with
the normalized global vacuum is represented by the pulled sector mean limit. -/
theorem centralPhysicalVacuumSectorCylinder_completedVacuumPairing_embedRep_eq_pulled
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep presentation))
        (centralPhysicalCutoffCompletedVacuum hw0 hw1 half) =
      Quotient.mk CReal.crealSetoid
        (centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit
          hw0 hw1 presentation.base half presentation.coefficient) := by
  rw [centralPhysicalVacuumSectorCylinderCompletionToGlobal_embedRep]
  unfold centralPhysicalCutoffCompletedVacuum
    embedCentralPhysicalLinearObservable
  exact Eq.trans
    (centralPhysicalCutoffCompletedInner_embedRep
      hw0 hw1 half presentation.toLinearObservable
        centralPhysicalLinearVacuum)
    (Quotient.sound
      (centralPhysicalVacuumSectorCylinder_innerLimitVacuum_equiv_pulledMean
        hw0 hw1 half presentation))

/-- Completed global-vacuum orthogonality of a dense sector cylinder forces
its pulled weighted-mean cutoff limit to be the zero Bishop real. -/
theorem centralPhysicalVacuumSectorCylinder_pulledMean_equiv_zero_of_orthogonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half)
    (horthogonal : CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
      hw0 hw1 half
      ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).embedRep presentation)) :
    CReal.Equiv
      (centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit
        hw0 hw1 presentation.base half presentation.coefficient)
      CReal.czero := by
  unfold CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
    CentralPhysicalCutoffCompletedVacuumOrthogonal at horthogonal
  rw [centralPhysicalVacuumSectorCylinder_completedVacuumPairing_embedRep_eq_pulled
    hw0 hw1 half presentation] at horthogonal
  exact Quotient.exact horthogonal

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseVacuumPairing

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseVacuumPairing.centralPhysicalFiniteVacuumSectorLinearObservable_vacuumPairing_eqv_pulledMean
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseVacuumPairing.centralPhysicalVacuumSectorCylinder_innerLimitVacuum_equiv_pulledMean
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseVacuumPairing.centralPhysicalVacuumSectorCylinder_completedVacuumPairing_embedRep_eq_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseVacuumPairing.centralPhysicalVacuumSectorCylinder_pulledMean_equiv_zero_of_orthogonal
