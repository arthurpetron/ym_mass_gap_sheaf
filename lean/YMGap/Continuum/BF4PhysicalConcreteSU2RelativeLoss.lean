/-
# Relative loss for the concrete physical SU(2) carrier

The physical sector already has a concrete completed carrier, transfer,
vacuum complement, and same-object autocorrelation.  This file rewrites its
strict completed form estimate as a literal deficit bound on that same object.
The generic compiler consumes only a named form-gap certificate; the marginal
specialization supplies the repository's inhabited fixed-nome certificate.

This remains a finite SU(2) statement.  It does not identify an OS/GNS
continuum carrier, a physical Hamiltonian, a scaling-uniform rate, or a Clay
mass gap.
-/

import YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate
import YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap

namespace YMGap.Continuum.BF4PhysicalConcreteSU2RelativeLoss

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap
open YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap

local infix:50 " ≈ " => Q'.eqv

private theorem one_sub_mul (r a : Q') :
    (1 - r) * a ≈ a + -(r * a) := by
  exact Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 (-r) a)
    (Q'.add_eqv_congr' (Q'.one_mul_eqv a) (Q'.neg_mul_eqv r a))

private theorem deficit_lower (r : Q') (norm form : CReal.RC)
    (h : CReal.RCle form (CReal.RCscale r norm)) :
    CReal.RCle (CReal.RCscale (1 - r) norm)
      (CReal.RCsub norm form) := by
  revert h
  refine Quotient.inductionOn₂ norm form ?_
  intro N F h epsilon hepsilon
  obtain ⟨index, hN⟩ := h epsilon hepsilon
  refine ⟨index, fun n hn => ?_⟩
  have hf := hN n hn
  change F.approx n ≤ r * N.approx n + epsilon at hf
  have hneg := Q'.neg_le_neg_add hf
  have hsum := Q'.add_le_add_left (N.approx n) _ _ hneg
  change (1 - r) * N.approx n ≤
    (N.approx n + -F.approx n) + epsilon
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (one_sub_mul r (N.approx n)))
    (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv (Q'.add_assoc_eqv _ _ _)))

/-! ## Generic same-carrier compiler -/

theorem sector_relative_loss_of_form_gap
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (gap : CentralPhysicalVacuumSectorCylinderCompletedStrictFormGapData
      hw0 hw1 half)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      hw0 hw1 half) :
    CReal.RCle
      (CReal.RCscale (1 - gap.rate)
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          vector.1 vector.1))
      (CReal.RCsub
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          vector.1 vector.1)
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
            hw0 hw1 half vector).1 vector.1)) := by
  exact deficit_lower gap.rate
    (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
      vector.1 vector.1)
    (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
        hw0 hw1 half vector).1 vector.1)
    (gap.form_gap vector)

/-! ## Concrete observable specialization -/

theorem concreteSU2_relative_loss_of_marginalGap
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hw : w ≤ HalfPow.half) :
    CReal.RCle
      (CReal.RCscale
        (1 - cutoffUniformRate w (Q'.le_of_lt hw0))
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 0
          (concreteVacuumComplementVector hw0 hw1).1
          (concreteVacuumComplementVector hw0 hw1).1))
      (CReal.RCsub
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 0
          (concreteVacuumComplementVector hw0 hw1).1
          (concreteVacuumComplementVector hw0 hw1).1)
        (concreteSameObjectAutocorrelation hw0 hw1 1)) := by
  have h := sector_relative_loss_of_form_gap
    (completedSectorFormGap hw0 hw1 hw)
    (concreteVacuumComplementVector hw0 hw1)
  simpa only [concreteSameObjectAutocorrelation,
    centralPhysicalVacuumSectorCylinderCompletedAutocorrelation,
    centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower] using h

theorem concreteSU2_relative_loss_margin_positive
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hw : w ≤ HalfPow.half) :
    (0 : Q') < 1 - cutoffUniformRate w (Q'.le_of_lt hw0) :=
  HKPos.one_sub_pos (cutoffUniformRate_lt_one w (Q'.le_of_lt hw0))

#print axioms sector_relative_loss_of_form_gap
#print axioms concreteSU2_relative_loss_of_marginalGap
#print axioms concreteSU2_relative_loss_margin_positive

end YMGap.Continuum.BF4PhysicalConcreteSU2RelativeLoss
