/-
# Original-Haar coordinate first and second moments

The selected coordinate is integrated on the literal original quaternion
carrier while an arbitrary polynomial spectator remains independent of that
block.  This is only a coordinate moment adapter; it makes no claim about a
full character expansion or a lattice observable.
-/

import YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
import YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur
import YMGap.Continuum.SU2QuaternionGenericBlockOddValentHaarVanishing
import YMGap.Continuum.QuaternionHaarSquareCertificate
import YMGap.Continuum.SU2QuaternionSolidZonalCharacter

namespace YMGap.Continuum.SU2QuaternionOriginalBlockCoordinateMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionFiniteProductHaarParitySectors
open YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionFiniteProductHaarMultihomogeneousPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur
open YMGap.Continuum.SU2QuaternionGenericBlockOddValentHaarVanishing
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem local_variable (block : Nat) (i : Fin 4) :
    QuaternionBlockLocal block (polyVar (4 * block + i.val)) := by
  intro term hterm coordinate hout
  simp only [polyVar, List.mem_singleton] at hterm
  subst term
  rw [exponentAt_varMono]
  apply if_neg
  intro heq
  apply hout
  rw [heq]
  exact ⟨by omega, by omega⟩

private theorem local_mul {block : Nat} {p q : RatPoly}
    (hp : QuaternionBlockLocal block p)
    (hq : QuaternionBlockLocal block q) :
    QuaternionBlockLocal block (polyMul p q) := by
  intro term hterm coordinate hout
  unfold polyMul at hterm
  rw [List.mem_flatMap] at hterm
  obtain ⟨leftTerm, hleft, hterm⟩ := hterm
  rw [List.mem_map] at hterm
  obtain ⟨rightTerm, hright, rfl⟩ := hterm
  rw [SU2QuaternionFiniteProductHaarSphereIdeal.exponentAt_monoMul,
    hp leftTerm hleft coordinate hout,
    hq rightTerm hright coordinate hout]

private theorem integrated_variable_coefficientSum
    (block : Nat) (i : Fin 4) :
    coefficientSum (integrateQuaternionBlock block
      (polyVar (4 * block + i.val))) ≈
      quaternionBlockMoment block (varMono (4 * block + i.val)) := by
  change
    (1 * quaternionBlockMoment block (varMono (4 * block + i.val))) + 0 ≈ _
  exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)) (Q'.one_mul_eqv _)

private theorem integrated_variable_pair_coefficientSum
    (block : Nat) (i j : Fin 4) :
    coefficientSum (integrateQuaternionBlock block
      (polyMul (polyVar (4 * block + i.val))
        (polyVar (4 * block + j.val)))) ≈
      quaternionBlockMoment block
        (monoMul (varMono (4 * block + i.val))
          (varMono (4 * block + j.val))) := by
  change
    ((1 * 1) * quaternionBlockMoment block
      (monoMul (varMono (4 * block + i.val))
        (varMono (4 * block + j.val)))) + 0 ≈ _
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_of_eq (Q'.add_zero' _))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv (1 : Q')))
      (Q'.one_mul_eqv _))

theorem variable_mul
    (blocks block : Nat) (hb : block < blocks) (i : Fin 4)
    (r : RatPoly) (hr : QuaternionBlockIndependent block r) :
    quaternionHaar blocks
        (polyMul (polyVar (4 * block + i.val)) r) ≈ 0 := by
  refine Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_comm
      (polyVar (4 * block + i.val)) r)) ?_
  have hMarginal := quaternionHaar_polyMul_eq_after_integratingBlock blocks block hb
    r (polyVar (4 * block + i.val)) hr
  have hall := integrateQuaternionBlock_allZero_of_local block
    (local_variable block i)
  have hzero := finiteProductHaar_polyMul_allZero_right blocks r
    (integrateQuaternionBlock block (polyVar (4 * block + i.val))) hall
  have hsum := integrated_variable_coefficientSum block i
  have hprod := Q'.mul_eqv_congr_left
    (finiteProductHaar blocks r) _ _ hsum
  have hodd : quaternionBlockDegree block
      (varMono (4 * block + i.val)) % 2 = 1 := by
    have hdegree :=
      SU2QuaternionSolidZonalCharacter.quaternionBlockDegree_varMono
        block i.val block i.isLt
    have hone : quaternionBlockDegree block
        (varMono (4 * block + i.val)) = 1 := by
      change
        exponentAt (varMono (4 * block + i.val)) (4 * block) +
            exponentAt (varMono (4 * block + i.val)) (4 * block + 1) +
            exponentAt (varMono (4 * block + i.val)) (4 * block + 2) +
            exponentAt (varMono (4 * block + i.val)) (4 * block + 3) = 1
      simpa only [YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity.quaternionBlockDegree,
        if_pos rfl] using hdegree
    rw [hone]
  have hmoment := quaternionBlockMoment_zero_of_odd_degree block
    (varMono (4 * block + i.val)) hodd
  have hEqIntegrated := quaternionHaar_eq_finiteProductHaar blocks
    (polyMul r (integrateQuaternionBlock block
      (polyVar (4 * block + i.val))))
  have hEqSpectator := quaternionHaar_eq_finiteProductHaar blocks r
  refine Q'.eqv_trans _ _ _ hMarginal ?_
  refine Q'.eqv_trans _ _ _ hEqIntegrated ?_
  refine Q'.eqv_trans _ _ _ hzero ?_
  refine Q'.eqv_trans _ _ _ hprod ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hEqSpectator)) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_of_eq hmoment))
    (Q'.mul_zero_eqv _)

theorem variable_pair_mul
    (blocks block : Nat) (hb : block < blocks) (i j : Fin 4)
    (r : RatPoly) (hr : QuaternionBlockIndependent block r) :
    quaternionHaar blocks
        (polyMul (polyMul (polyVar (4 * block + i.val))
          (polyVar (4 * block + j.val))) r) ≈
      (if i.val = j.val then
        SU2PeterWeylWilsonBlock.quarter else 0) *
        quaternionHaar blocks r := by
  refine Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_comm
      (polyMul (polyVar (4 * block + i.val))
        (polyVar (4 * block + j.val))) r)) ?_
  have hMarginal := quaternionHaar_polyMul_eq_after_integratingBlock blocks block hb
    r (polyMul (polyVar (4 * block + i.val))
      (polyVar (4 * block + j.val))) hr
  have hall := integrateQuaternionBlock_allZero_of_local block
    (local_mul (local_variable block i) (local_variable block j))
  have hzero := finiteProductHaar_polyMul_allZero_right blocks r
    (integrateQuaternionBlock block
      (polyMul (polyVar (4 * block + i.val))
        (polyVar (4 * block + j.val)))) hall
  have hsum := integrated_variable_pair_coefficientSum block i j
  have hprod := Q'.mul_eqv_congr_left
    (finiteProductHaar blocks r) _ _ hsum
  have hpair := quaternionBlockMoment_blockVariablePair block i j
  have hEqIntegrated := quaternionHaar_eq_finiteProductHaar blocks
    (polyMul r (integrateQuaternionBlock block
      (polyMul (polyVar (4 * block + i.val))
        (polyVar (4 * block + j.val)))))
  have hEqSpectator := quaternionHaar_eq_finiteProductHaar blocks r
  refine Q'.eqv_trans _ _ _ hMarginal ?_
  refine Q'.eqv_trans _ _ _ hEqIntegrated ?_
  refine Q'.eqv_trans _ _ _ hzero ?_
  refine Q'.eqv_trans _ _ _ hprod ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (finiteProductHaar blocks r) _ _ hpair) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hEqSpectator))
    (Q'.mul_comm_eqv _ _)

end YMGap.Continuum.SU2QuaternionOriginalBlockCoordinateMoments

#print axioms YMGap.Continuum.SU2QuaternionOriginalBlockCoordinateMoments.variable_mul
#print axioms YMGap.Continuum.SU2QuaternionOriginalBlockCoordinateMoments.variable_pair_mul
