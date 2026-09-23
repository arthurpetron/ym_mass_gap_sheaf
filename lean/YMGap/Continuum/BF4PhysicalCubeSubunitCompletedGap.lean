/-
# The all-subunit finite coercivity reaches the completed physical sector

For every rational nome 0<w<1 at half=0, the adaptive raw-tail estimate and
the rooted finite head give a cutoff-independent strict rate.  The existing
cofinal completion bridge then transports that rate to the literal completed
marginal vacuum complement and its same-object autocorrelation.

The onset and rate depend explicitly on w.  No spacing/volume uniformity,
geometric-time identification, continuum limit, or Clay claim is made.
-/

import YMGap.Continuum.BF4PhysicalCubeSubunitCoercivity
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge
import YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate

namespace YMGap.Continuum.BF4PhysicalCubeSubunitCompletedGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate
open YMGap.Continuum.BF4PhysicalCubeSubunitCoercivity
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

def subunitGapNumerator (w : Q') (hw : (0 : Q') ≤ w) : Q' :=
  1 + 6 * subunitHeadEnergyConstant w hw

theorem subunitGapNumerator_pos (w : Q') (hw : (0 : Q') ≤ w) :
    (0 : Q') < subunitGapNumerator w hw :=
  Q'.add_pos (by decide) (Q'.mul_pos (by decide) (subunitHeadEnergyConstant_pos w hw))

def subunitGapDenominator (w : Q') (hw : (0 : Q') ≤ w) : Q' :=
  1 + subunitGapNumerator w hw

theorem subunitGapDenominator_pos (w : Q') (hw : (0 : Q') ≤ w) :
    (0 : Q') < subunitGapDenominator w hw :=
  Q'.add_pos (by decide) (subunitGapNumerator_pos w hw)

/-- The explicit all-subunit rate `(1+6*C)/(2+6*C)`. -/
def subunitCutoffUniformRate (w : Q') (hw : (0 : Q') ≤ w) : Q' :=
  Q'.divPos (subunitGapNumerator w hw) (subunitGapDenominator w hw)
    (subunitGapDenominator_pos w hw)

theorem subunitCutoffUniformRate_pos (w : Q') (hw : (0 : Q') ≤ w) :
    (0 : Q') < subunitCutoffUniformRate w hw :=
  Q'.divPos_pos _ _ _ (subunitGapNumerator_pos w hw)

private theorem lt_one_add (a : Q') : a < 1 + a := by
  show a.num * (((1 : Q') + a).den : Int) < ((1 : Q') + a).num * (a.den : Int)
  rw [Q'.add_den_cast, Q'.add_num_cast]
  change a.num * (1 * (a.den : Int)) < (1 * (a.den : Int) + a.num * 1) * (a.den : Int)
  simp only [Int.one_mul, Int.mul_one, Int.add_mul]
  have hs := Int.mul_pos (show (0 : Int) < (a.den : Int) from by exact_mod_cast a.den_pos)
    (show (0 : Int) < (a.den : Int) from by exact_mod_cast a.den_pos)
  omega

theorem subunitCutoffUniformRate_lt_one (w : Q') (hw : (0 : Q') ≤ w) :
    subunitCutoffUniformRate w hw < (1 : Q') := by
  let p := subunitGapNumerator w hw
  let q := subunitGapDenominator w hw
  let hq := subunitGapDenominator_pos w hw
  have h := Q'.mul_lt_mul_of_pos_left (Q'.recipPos_pos q hq) (lt_one_add p)
  have hr : Q'.recipPos q hq * q ≈ (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv q hq)
  exact YMGap.Continuum.ContinuumClosureProgram.q'_lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv (Q'.mul_comm_eqv p (Q'.recipPos q hq))) h)
    (Q'.le_of_eqv hr)

private theorem gap_polynomial (C N P : Q') :
    (1 + 3 * C) * ((N + N) + -(P + P)) + -N ≈
      (1 + 6 * C) * N + -((1 + (1 + 6 * C)) * P) := by
  let c := PolyExpr.var 0
  let n := PolyExpr.var 1
  let p := PolyExpr.var 2
  let a : PolyExpr := .add (.const 1) (.mul (.const 3) c)
  let b : PolyExpr := .add (.const 1) (.mul (.const 6) c)
  let left : PolyExpr := .add (.mul a (.add (.add n n) (.neg (.add p p)))) (.neg n)
  let right : PolyExpr := .add (.mul b n) (.neg (.mul (.add (.const 1) b) p))
  let valuation := fun i => if i = 0 then C else if i = 1 then N else P
  have h := poly_identity_of_normal_eq left right (by decide) valuation
  simpa [left, right, a, b, c, n, p, valuation, RingNormaliser.eval] using h

private theorem division_regroup (p N q : Q') (hq : (0 : Q') < q) :
    Q'.divPos (p * N) q hq ≈ Q'.divPos p q hq * N := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ (p * (N * Q'.recipPos q hq)) _ (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (p * (Q'.recipPos q hq * N)) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

theorem matrix_le_subunitCutoffUniformRate {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : subunitHeadStart w ≤ K) (f : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean
      w (Q'.le_of_lt hw0) K 0 f ≈ 0) :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic w (Q'.le_of_lt hw0) K 0 f ≤
      subunitCutoffUniformRate w (Q'.le_of_lt hw0) *
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w (Q'.le_of_lt hw0) K 0 f := by
  let hw := Q'.le_of_lt hw0
  let N := centralPhysicalFiniteVacuumSectorDiagonalQuadratic w hw K 0 f
  let P := centralPhysicalFiniteVacuumSectorMatrixQuadratic w hw K 0 f
  let num := subunitGapNumerator w hw
  let den := subunitGapDenominator w hw
  have henergy := centralPhysicalFiniteVacuumSectorDirichlet_eqv_twice_deficit w hw K 0 f
  have hn := centered_norm_le_subunitCoercivity_mul_energy hw0 hw1 K hK f hcenter
  have hbound : N ≤ subunitCoercivityConstant w hw * ((N + N) + -(P + P)) :=
    Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ henergy))
  have hscaled : den * P ≤ num * N := by
    apply Q'.le_of_sub_nonneg
    exact Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le hbound)
      (Q'.le_of_eqv (gap_polynomial (subunitHeadEnergyConstant w hw) N P))
  have hdiv := Q'.le_divPos_of_mul_le (num * N) den (subunitGapDenominator_pos w hw)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv P den)) hscaled)
  exact Q'.le_trans' _ _ _ hdiv (Q'.le_of_eqv (division_regroup num N den _))

theorem abs_matrix_le_subunitCutoffUniformRate {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : subunitHeadStart w ≤ K) (f : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean
      w (Q'.le_of_lt hw0) K 0 f ≈ 0) :
    Q'.abs (centralPhysicalFiniteVacuumSectorMatrixQuadratic w (Q'.le_of_lt hw0) K 0 f) ≤
      subunitCutoffUniformRate w (Q'.le_of_lt hw0) *
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w (Q'.le_of_lt hw0) K 0 f := by
  unfold Q'.abs
  rw [if_pos (centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
    w (Q'.le_of_lt hw0) K 0 f)]
  exact matrix_le_subunitCutoffUniformRate hw0 hw1 K hK f hcenter

def subunitCofinalSectorGap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    FixedNomeCofinalVacuumSectorFiniteStrictGap w (Q'.le_of_lt hw0) 0
      (subunitCutoffUniformRate w (Q'.le_of_lt hw0)) where
  rate_nonnegative := Q'.le_of_lt (subunitCutoffUniformRate_pos w (Q'.le_of_lt hw0))
  rate_lt_one := subunitCutoffUniformRate_lt_one w (Q'.le_of_lt hw0)
  anchor request := max request (subunitHeadStart w)
  anchor_ge _request := Nat.le_max_left _ _
  sectorGap _request f hcenter :=
    abs_matrix_le_subunitCutoffUniformRate hw0 hw1 _ (Nat.le_max_right _ _) f hcenter

def subunitCompletedSectorFormGap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictFormGapData hw0 hw1 0 :=
  centralPhysicalVacuumSectorCylinderCompletedStrictFormGapDataAtRate hw0 hw1 0
    (subunitCofinalSectorGap hw0 hw1).toVacuumSectorCenteredStrictGap

theorem subunitCompletedSectorFormGap_rate {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) :
    (subunitCompletedSectorFormGap hw0 hw1).rate =
      subunitCutoffUniformRate w (Q'.le_of_lt hw0) := rfl

def subunitCompletedSectorContraction {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData hw0 hw1 0 :=
  centralPhysicalVacuumSectorCylinderCompletedStrictContractionData_of_formGap
    (centralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData hw0 hw1 0)
    (subunitCompletedSectorFormGap hw0 hw1)

theorem subunitCompletedSectorContraction_rate {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) :
    (subunitCompletedSectorContraction hw0 hw1).rate =
      subunitCutoffUniformRate w (Q'.le_of_lt hw0) := rfl

theorem subunitCompletedSector_power_decay {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (n : Nat)
    (x : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement hw0 hw1 0) :
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 0
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower hw0 hw1 0 n x).1
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower hw0 hw1 0 n x).1)
      (CReal.RCscale
        ((subunitCutoffUniformRate w (Q'.le_of_lt hw0) *
          subunitCutoffUniformRate w (Q'.le_of_lt hw0)) ^ n)
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 0 x.1 x.1)) :=
  centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower_norm_decay
    (subunitCompletedSectorContraction hw0 hw1) n x

theorem concreteSameObjectAutocorrelation_sq_decay_subunit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (n : Nat) :
    CReal.RCle
      (CReal.RCmul
        (concreteSameObjectAutocorrelation hw0 hw1 n)
        (concreteSameObjectAutocorrelation hw0 hw1 n))
      (CReal.RCmul
        (CReal.RCscale
          ((subunitCutoffUniformRate w (Q'.le_of_lt hw0) *
            subunitCutoffUniformRate w (Q'.le_of_lt hw0)) ^ n)
          (centralPhysicalCutoffCompletedInner hw0 hw1 0
            (centralPhysicalVacuumSectorMovingCenteredGlobalVector hw0 hw1 1 0
              (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))
            (centralPhysicalVacuumSectorMovingCenteredGlobalVector hw0 hw1 1 0
              (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))))
        (centralPhysicalCutoffCompletedInner hw0 hw1 0
          (centralPhysicalVacuumSectorMovingCenteredGlobalVector hw0 hw1 1 0
            (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))
          (centralPhysicalVacuumSectorMovingCenteredGlobalVector hw0 hw1 1 0
            (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)))) :=
  concreteSU2CompletedCarrierCertificate_autocorrelation_sq_decay
    hw0 hw1 (subunitCompletedSectorContraction hw0 hw1) n

end YMGap.Continuum.BF4PhysicalCubeSubunitCompletedGap

#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCompletedGap.subunitGapNumerator
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCompletedGap.subunitGapNumerator_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCompletedGap.subunitGapDenominator
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCompletedGap.subunitGapDenominator_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCompletedGap.subunitCutoffUniformRate
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCompletedGap.subunitCutoffUniformRate_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCompletedGap.subunitCutoffUniformRate_lt_one
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCompletedGap.matrix_le_subunitCutoffUniformRate
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCompletedGap.abs_matrix_le_subunitCutoffUniformRate
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCompletedGap.subunitCofinalSectorGap
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCompletedGap.subunitCompletedSectorFormGap
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCompletedGap.subunitCompletedSectorFormGap_rate
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCompletedGap.subunitCompletedSectorContraction
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCompletedGap.subunitCompletedSectorContraction_rate
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCompletedGap.subunitCompletedSector_power_decay
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCompletedGap.concreteSameObjectAutocorrelation_sq_decay_subunit
