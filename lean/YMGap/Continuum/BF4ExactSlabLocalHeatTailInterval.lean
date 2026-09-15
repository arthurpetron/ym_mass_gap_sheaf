/-
# Geometric cutoff tails on a FIXED original face region

The spin-only character bound gives delta(w)*2^(-K) for every omitted
face-heat block above K, independently of extent and tail length. The
actual shared-variable product remainder has cap S(w,number of faces)*2^(-K).
No surrounding action, partition reciprocal or volume occurs in S.

These interval certificates are intended for original-observable OS-norm
estimates. They are not OS multiplication operators or transfer preimages.
-/

import YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval
import YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail

namespace YMGap.Continuum.BF4ExactSlabLocalHeatTailInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail
open YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BondMovingStep (coeffW coeffW_nonneg)

local infix:50 " ≈ " => Q'.eqv

theorem heatBlock_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (K L : Nat) :
    finSum (fun i => heatTermBound w (K+1+i)) L ≤ heatRemainderBound w * HalfPow.half^K := by
  have ht := ExpNeg.finSum_le_finSum_of_termwise
    (fun i => heatTermBound w (K+1+i)) (fun i => heatTermBound w 1 * HalfPow.half^(K+i))
    (fun i => by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using heatTermBound_geometric hw0 hw1 hsmall (K+i)) L
  have hg : finSum (fun i => heatTermBound w 1 * HalfPow.half^(K+i)) L ≤
      geoTailBase (heatTermBound w 1) HalfPow.half K := by
    simpa only [geoIncrBase] using geoTailBase_series_le (heatTermBound_nonnegative hw0 1)
      (by decide : (0 : Q') < HalfPow.half) (by decide : HalfPow.half < (1 : Q')) K L
  have he : geoTailBase (heatTermBound w 1) HalfPow.half K ≈ heatRemainderBound w * HalfPow.half^K :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (by decide : HKConv.divPos (1 : Q') (1 + -HalfPow.half) ≈ (2 : Q')))
      (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.const 2))
        (.mul (.mul (.var 0) (.const 2)) (.var 1)) (by decide)
        (fun | 0 => heatTermBound w 1 | _ => HalfPow.half^K))
  exact Q'.le_trans' _ _ _ ht (Q'.le_trans' _ _ _ hg (Q'.le_of_eqv he))

def faceTailInterval {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (extent id : Nat)
    (hi : id ∈ slabPhysicalFaceEdges extent) (K L : Nat) :
    Interval (boundaryCompleteSlabLinks extent).length (faceHeatTail w extent id (K+1) L)
      (heatRemainderBound w * HalfPow.half^K) :=
  (Interval.finiteRange (fun i => faceHeatTerm w extent id (K+1+i))
    (fun i => heatTermBound w (K+1+i)) (fun i => Interval.smul (coeffW w (K+1+i)) (coeffW_nonneg hw0 _)
      (characterInterval (.scalar (supported_slabPlaquette _ _) (haarNorm_slabPlaquette (slabPlaquetteAt_mem hi))) _)) L).weaken
    (heatBlock_bound hw0 hw1 hsmall K L)

/-- Sensitivity times one-face tail cap, computed without subtraction. -/
def tailConstant (w : Q') : Nat → Q'
  | 0 => 0
  | n+1 => (1+heatRemainderBound w)*tailConstant w n + heatRemainderBound w*(1+heatRemainderBound w)^n

theorem tailConstant_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) : ∀ n,(0 : Q') ≤ tailConstant w n
  | 0 => Q'.le_refl' _
  | n+1 => Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (Q'.zero_le_add _ _ Q'.zero_le_one (heatRemainderBound_nonnegative hw)) (tailConstant_nonnegative hw n))
      (Q'.mul_nonneg _ _ (heatRemainderBound_nonnegative hw)
        (Q'.pow_nonneg _ (Q'.zero_le_add _ _ Q'.zero_le_one (heatRemainderBound_nonnegative hw)) n))

/-- Original product remainder, with every overlapping variable retained. -/
def productTailInterval {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (K L extent : Nat) :
    (ids : List Nat) → (∀ id,id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
      Interval (boundaryCompleteSlabLinks extent).length (heatProductRemainder w extent K L ids)
        (tailConstant w ids.length * HalfPow.half^K)
  | [], _ => (Interval.zero _).changeCap (Q'.eqv_symm (Q'.zero_mul_eqv _))
  | id::ids, hi =>
      ((faceInterval hw0 hw1 hsmall K extent id (hi id List.mem_cons_self)).mul
        (productTailInterval hw0 hw1 hsmall K L extent ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))).add
        ((faceTailInterval hw0 hw1 hsmall extent id (hi id List.mem_cons_self) K L).mul
          (productInterval hw0 hw1 hsmall (K+L) extent ids (fun j hj => hi j (List.mem_cons_of_mem id hj))))
      |>.changeCap (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.mul (.var 3) (.var 2)) (.var 4)))
        (.mul (.add (.mul (.var 0) (.var 1)) (.mul (.var 3) (.var 4))) (.var 2)) (by decide)
        (fun | 0 => 1+heatRemainderBound w | 1 => tailConstant w ids.length | 2 => HalfPow.half^K
             | 3 => heatRemainderBound w | _ => (1+heatRemainderBound w)^ids.length))

end YMGap.Continuum.BF4ExactSlabLocalHeatTailInterval

#print axioms YMGap.Continuum.BF4ExactSlabLocalHeatTailInterval.heatBlock_bound
#print axioms YMGap.Continuum.BF4ExactSlabLocalHeatTailInterval.faceTailInterval
#print axioms YMGap.Continuum.BF4ExactSlabLocalHeatTailInterval.tailConstant
#print axioms YMGap.Continuum.BF4ExactSlabLocalHeatTailInterval.tailConstant_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabLocalHeatTailInterval.productTailInterval
