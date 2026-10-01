/-
# Complete original-block weighted Casimir Ward identity

The weight and its partition are the supplied original polynomials.  The
signed term differentiating the complete weight is retained at every plane
of every original block.  The eigenpin is an explicit hypothesis on the
same finite Haar carrier; this is a finite identity, not a gap estimate.
-/

import YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
import YMGap.Continuum.SU2QuaternionChannelCasimirLocality
import YMGap.Continuum.QuaternionHaarCenteredLinearWard
import YMGap.Continuum.QuaternionHaarFamilySquare

namespace YMGap.Continuum.SU2QuaternionWeightedCasimirWard

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarCenteredLinearWard
open YMGap.Continuum.QuaternionHaarFamilySquare
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The full, signed derivative-of-weight residual at an original block. -/
def blockResidual (n block : Nat) (W f : RatPoly) (c : Q') : Q' :=
  sixValue (fun i j => H n
    (polyMul (polyMul (polyAdd f (polySmul (-c) polyOne))
      (blockAngularDerivative block i j W))
      (blockAngularDerivative block i j f)))

/-- Haar energy in the six original angular planes of one block. -/
def blockEnergy (n block : Nat) (W f : RatPoly) : Q' :=
  H n (polyMul W (blockAngularSquare block f))

/-- Summation over precisely the original blocks in the supplied list. -/
def totalEnergy (n : Nat) (W f : RatPoly) : Q' :=
  qListSum ((List.range n).map fun block => blockEnergy n block W f)

def totalResidual (n : Nat) (W f : RatPoly) (c : Q') : Q' :=
  qListSum ((List.range n).map fun block => blockResidual n block W f c)

private theorem qsum_append : ∀ left right : List Q',
    qListSum (left ++ right) ≈ qListSum left + qListSum right
  | [], _ => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | _::xs, right => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (qsum_append xs right))
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem qsum_map_range (value : Nat → Q') : ∀ count,
    qListSum ((List.range count).map value) ≈ finSum value count
  | 0 => Q'.eqv_refl _
  | count+1 => by
      rw [List.range_succ, List.map_append]
      exact Q'.eqv_trans _ _ _ (qsum_append _ _)
        (Q'.add_eqv_congr' (qsum_map_range value count)
          (QPoly.q_add_zero_eqv _))

/-- Adapter to the original odd-marginal `finSum` convention. -/
theorem totalEnergy_finSum (n : Nat) (W f : RatPoly) :
    totalEnergy n W f ≈ finSum (fun block => blockEnergy n block W f) n :=
  qsum_map_range _ n

theorem totalResidual_finSum (n : Nat) (W f : RatPoly) (c : Q') :
    totalResidual n W f c ≈
      finSum (fun block => blockResidual n block W f c) n :=
  qsum_map_range _ n

private theorem angular_centered (block i j : Nat) (f : RatPoly) (c : Q') :
    RatPolyCoeffEqv
      (blockAngularDerivative block i j
        (polyAdd f (polySmul (-c) polyOne)))
      (blockAngularDerivative block i j f) := by
  unfold blockAngularDerivative
  have hz : RatPolyCoeffEqv
      (angularDerivative (4*block+i) (4*block+j)
        (polySmul (-c) polyOne)) polyZero :=
    (angularDerivative_smul _ _ (-c) polyOne).trans
      (((angularDerivative_one _ _).smul (-c)).trans
        (RatPolyCoeffEqv.smul_zero (-c)))
  exact (angularDerivative_add _ _ f (polySmul (-c) polyOne)).trans
    (((RatPolyCoeffEqv.refl _).add hz).trans
      (RatPolyCoeffEqv.add_zero _))

private theorem plane_ward {n block : Nat} (hb : block < n)
    (i j : Nat) (hi : i < 4) (hj : j < 4)
    (W f : RatPoly) (c : Q') :
    H n (polyMul W
        (polyMul (blockAngularDerivative block i j f)
          (blockAngularDerivative block i j f))) +
      H n (polyMul
        (polyMul (polyAdd f (polySmul (-c) polyOne))
          (blockAngularDerivative block i j W))
        (blockAngularDerivative block i j f)) ≈
      -(H n (polyMul
        (polyMul W (polyAdd f (polySmul (-c) polyOne)))
        (blockAngularDerivative block i j
          (blockAngularDerivative block i j f)))) := by
  let fc := polyAdd f (polySmul (-c) polyOne)
  let df := blockAngularDerivative block i j f
  let dW := blockAngularDerivative block i j W
  let ddf := blockAngularDerivative block i j df
  have hfc := angular_centered block i j f c
  have hd : RatPolyCoeffEqv
      (polyMul (blockAngularDerivative block i j (polyMul W fc)) df)
      (polyAdd (polyMul (polyMul fc dW) df)
        (polyMul W (polyMul df df))) := by
    exact (((angularDerivative_mul (4*block+i) (4*block+j) W fc).trans
      ((RatPolyCoeffEqv.refl _).add (hfc.mul_left W))).mul_right df).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (.var 3))
        (.add (.mul (.mul (.var 2) (.var 0)) (.var 3))
          (.mul (.var 1) (.mul (.var 3) (.var 3))))
        (by decide) (fun | 0 => dW | 1 => W | 2 => fc | _ => df))
  have hzero := quaternionHaar_weighted_angular_at hb hi hj (polyMul W fc) df
  have hsum :
      (H n (polyMul (polyMul fc dW) df) +
        H n (polyMul W (polyMul df df))) +
          H n (polyMul (polyMul W fc) ddf) ≈ 0 := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (haar_of_coeff hd)
          (quaternionHaar_append n _ _))
        (Q'.eqv_refl _)))
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm (quaternionHaar_append n _ _)) hzero)
  apply QPoly.q_eqv_of_sub_zero
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.add (.add (.var 1) (.var 0)) (.neg (.neg (.var 2))))
      (.add (.add (.var 0) (.var 1)) (.var 2)) (by decide)
      (fun | 0 => H n (polyMul (polyMul fc dW) df)
           | 1 => H n (polyMul W (polyMul df df))
           | _ => H n (polyMul (polyMul W fc) ddf))) hsum

private theorem sixValue_add (a b : Nat → Nat → Q') :
    sixValue a + sixValue b ≈ sixValue (fun i j => a i j + b i j) :=
  poly_identity_of_normal_eq
    (.add
      (.add (.var 0) (.add (.var 1) (.add (.var 2)
        (.add (.var 3) (.add (.var 4) (.var 5))))))
      (.add (.var 6) (.add (.var 7) (.add (.var 8)
        (.add (.var 9) (.add (.var 10) (.var 11)))))))
    (.add (.add (.var 0) (.var 6))
      (.add (.add (.var 1) (.var 7))
        (.add (.add (.var 2) (.var 8))
          (.add (.add (.var 3) (.var 9))
            (.add (.add (.var 4) (.var 10)) (.add (.var 5) (.var 11)))))))
    (by decide) (fun
      | 0 => a 0 1 | 1 => a 0 2 | 2 => a 0 3
      | 3 => a 1 2 | 4 => a 1 3 | 5 => a 2 3
      | 6 => b 0 1 | 7 => b 0 2 | 8 => b 0 3
      | 9 => b 1 2 | 10 => b 1 3 | _ => b 2 3)

private theorem sixValue_neg (a : Nat → Nat → Q') :
    sixValue (fun i j => -(a i j)) ≈ -(sixValue a) :=
  poly_identity_of_normal_eq
    (.add (.neg (.var 0)) (.add (.neg (.var 1)) (.add (.neg (.var 2))
      (.add (.neg (.var 3)) (.add (.neg (.var 4)) (.neg (.var 5)))))))
    (.neg (.add (.var 0) (.add (.var 1) (.add (.var 2)
      (.add (.var 3) (.add (.var 4) (.var 5)))))))
    (by decide) (fun
      | 0 => a 0 1 | 1 => a 0 2 | 2 => a 0 3
      | 3 => a 1 2 | 4 => a 1 3 | _ => a 2 3)

/-- Exact one-block Ward relation, with the weight derivative retained. -/
theorem block_ward {n block : Nat} (hb : block < n)
    (W f : RatPoly) (c : Q') :
    blockEnergy n block W f + blockResidual n block W f c ≈
      H n (polyMul
        (polyMul W (polyAdd f (polySmul (-c) polyOne)))
        (polyNeg (blockAngularLaplacian block f))) := by
  let insertion := polyMul W (polyAdd f (polySmul (-c) polyOne))
  let energy := fun i j => H n (polyMul W
    (polyMul (blockAngularDerivative block i j f)
      (blockAngularDerivative block i j f)))
  let residual := fun i j => H n (polyMul
    (polyMul (polyAdd f (polySmul (-c) polyOne))
      (blockAngularDerivative block i j W))
    (blockAngularDerivative block i j f))
  let second := fun i j => H n (polyMul insertion
    (blockAngularDerivative block i j
      (blockAngularDerivative block i j f)))
  have he := haar_six n W (fun i j =>
    polyMul (blockAngularDerivative block i j f)
      (blockAngularDerivative block i j f))
  have hp := sixValue_congr (fun i j => energy i j + residual i j)
    (fun i j => -(second i j))
    (fun i j hi hj => plane_ward hb i j hi hj W f c)
  have hs : sixValue second ≈ H n (polyMul insertion
      (blockAngularLaplacian block f)) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (haar_six n insertion (fun i j =>
        blockAngularDerivative block i j
          (blockAngularDerivative block i j f))))
      (haar_of_coeff
        ((RatPolyCoeffEqv.refl insertion).mul
          (blockAngularLaplacian_eq_six block f).symm))
  have hneg : -(H n (polyMul insertion (blockAngularLaplacian block f))) ≈
      H n (polyMul insertion (polyNeg (blockAngularLaplacian block f))) := by
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _
      (haar_of_coeff (((neg_smul _).mul_left insertion).trans
        (RatPolyCoeffEqv.polyMul_smul_right (-1) insertion _)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-1) _)
        (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
          (.neg (.var 0)) (by decide)
          (fun _ => H n (polyMul insertion (blockAngularLaplacian block f))))))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' he (Q'.eqv_refl _))
    (Q'.eqv_trans _ _ _ (sixValue_add energy residual)
      (Q'.eqv_trans _ _ _ hp
        (Q'.eqv_trans _ _ _ (sixValue_neg second)
          (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hs) hneg))))

/-- The complete original-list identity before using any eigenpin. -/
theorem complete_ward_raw (n : Nat) (W f : RatPoly) (c : Q') :
    totalEnergy n W f + totalResidual n W f c ≈
      H n (polyMul
        (polyMul W (polyAdd f (polySmul (-c) polyOne)))
        (activeCasimirPolynomial (List.range n) f)) := by
  let insertion := polyMul W (polyAdd f (polySmul (-c) polyOne))
  have hp := qListSum_congr (List.range n)
    (fun block => blockEnergy n block W f + blockResidual n block W f c)
    (fun block => H n (polyMul insertion
      (polyNeg (blockAngularLaplacian block f))))
    (fun block hb => block_ward (List.mem_range.mp hb) W f c)
  have hs := haar_weighted_sum_indexed n insertion
    (fun block => polyNeg (blockAngularLaplacian block f)) (List.range n)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (qListSum_add (List.range n)
      (fun block => blockEnergy n block W f)
      (fun block => blockResidual n block W f c)))
    (Q'.eqv_trans _ _ _ hp (Q'.eqv_symm hs))

/-- The complete weight on the same original Haar carrier pays its exact
Casimir eigenvalue against its own centered variance.  The signed residual
is retained; no bound on it is asserted. -/
theorem complete_ward_own_mean {n : Nat} (hn : 0 < n)
    (W f : RatPoly) (hZ : (0 : Q') < H n W) (kappa : Q')
    (hEigen : HaarCarrierEqv n
      (activeCasimirPolynomial (List.range n) f) (polySmul kappa f)) :
    let c := normalizedMoment n W f hZ
    totalEnergy n W f + totalResidual n W f c ≈
      kappa * (H n W * normalizedVariance n W f hZ) := by
  let c := normalizedMoment n W f hZ
  let insertion := polyMul W (polyAdd f (polySmul (-c) polyOne))
  have hw := complete_ward_raw n W f c
  have he := hEigen insertion
  have hk : H n (polyMul insertion (polySmul kappa f)) ≈
      kappa * H n (polyMul insertion f) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right kappa insertion f))
      (quaternionHaar_polySmul n kappa _)
  have hcross : H n (polyMul insertion f) ≈
      H n W * normalizedVariance n W f hZ := by
    cases n with
    | zero => omega
    | succ tail =>
        have hnorm := normalized_centered_cross_own_mean tail W f hZ
        have hnorm' :
            (H (tail+1) (polyMul W
              (polyMul (polyAdd f (polySmul (-c) polyOne)) f))) *
                Q'.recipPos (H (tail+1) W) hZ ≈
              normalizedVariance (tail+1) W f hZ := by
          simpa only [normalizedMoment, c] using hnorm
        have hclear :
            H (tail+1) (polyMul W
              (polyMul (polyAdd f (polySmul (-c) polyOne)) f)) ≈
            H (tail+1) W * normalizedVariance (tail+1) W f hZ := by
          exact Q'.eqv_trans _ _ _
            (Q'.eqv_symm (Q'.eqv_trans _ _ _
              (poly_identity_of_normal_eq
                (.mul (.var 0) (.mul (.var 1) (.var 2)))
                (.mul (.var 1) (.mul (.var 0) (.var 2)))
                (by decide)
                (fun | 0 => H (tail+1) W
                     | 1 => H (tail+1) (polyMul W
                         (polyMul (polyAdd f (polySmul (-c) polyOne)) f))
                     | _ => Q'.recipPos (H (tail+1) W) hZ))
              (Q'.eqv_trans _ _ _
                (Q'.mul_eqv_congr_left _ _
                  _ (Q'.mul_recipPos_eqv (H (tail+1) W) hZ))
                (Q'.mul_one_eqv _))))
            (Q'.mul_eqv_congr_left _ _ _ hnorm')
        exact Q'.eqv_trans _ _ _
          (haar_of_coeff (RatPolyCoeffEqv.mul_assoc W
            (polyAdd f (polySmul (-c) polyOne)) f)) hclear
  exact Q'.eqv_trans _ _ _ hw
    (Q'.eqv_trans _ _ _ he
      (Q'.eqv_trans _ _ _ hk
        (Q'.mul_eqv_congr_left kappa _ _ hcross)))

/-- Direct `finSum` presentation for the existing original odd-marginal
angular functional. -/
theorem complete_ward_own_mean_finSum {n : Nat} (hn : 0 < n)
    (W f : RatPoly) (hZ : (0 : Q') < H n W) (kappa : Q')
    (hEigen : HaarCarrierEqv n
      (activeCasimirPolynomial (List.range n) f) (polySmul kappa f)) :
    let c := normalizedMoment n W f hZ
    finSum (fun block => blockEnergy n block W f) n +
      finSum (fun block => blockResidual n block W f c) n ≈
        kappa * (H n W * normalizedVariance n W f hZ) := by
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_symm (totalEnergy_finSum n W f))
      (Q'.eqv_symm (totalResidual_finSum n W f
        (normalizedMoment n W f hZ))))
    (complete_ward_own_mean hn W f hZ kappa hEigen)

end YMGap.Continuum.SU2QuaternionWeightedCasimirWard

#print axioms YMGap.Continuum.SU2QuaternionWeightedCasimirWard.block_ward
#print axioms YMGap.Continuum.SU2QuaternionWeightedCasimirWard.complete_ward_raw
#print axioms YMGap.Continuum.SU2QuaternionWeightedCasimirWard.complete_ward_own_mean
#print axioms YMGap.Continuum.SU2QuaternionWeightedCasimirWard.complete_ward_own_mean_finSum
