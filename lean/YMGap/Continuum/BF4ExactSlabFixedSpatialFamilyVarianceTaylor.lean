/-
# Original temporal energy versus the SAME signed-family variance

Combine the original-marginal Taylor identity with the actual signed-family
Casimir Ward identity. The leading term is 12*(1-w)*Var_W(f). The remaining
signed quantity includes BOTH Taylor remainders, the angular weight defect,
and the complete-weight Ward residual, all over the original partition.

No term is bounded separately or discarded. In particular the combined
remainder is not asserted to be positive, small, or uniformly quadratic.
The relative upper estimate and justified scaling family remain OPEN.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceTaylor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (RatPoly)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin (familyExpression)
open YMGap.Continuum.BF4WilsonPlaquetteFamilyIncrement (finite_family_increment_pin)
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement (squareAt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit (originalWindowScalar)

local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] originalWindowScalar

/-- The combined SIGNED correction after replacing angular energy by the
actual interacting variance. This definition asserts no estimate. -/
def varianceRemainder {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  normalizedRemainder hw0 hw1 K width hK n f +
    -(((1 : Q')-w)*normalizedWardResidual hw0 hw1 K width hK n f)

/-- Every term is divided by the SAME original odd partition, with the
derivative-of-weight correction SUBTRACTED from the rebased Taylor remainder. -/
theorem varianceRemainder_raw {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) :
    varianceRemainder hw0 hw1 K width hK n f ≈
      (signedRemainder w K width n f +
        -(((1 : Q')-w)*wardResidual hw0 hw1 K width hK n f)) *
        Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n) :=
  poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 3))
      (.neg (.mul (.var 1) (.mul (.var 2) (.var 3)))))
    (.mul (.add (.var 0) (.neg (.mul (.var 1) (.var 2)))) (.var 3))
    (by decide) (fun
      | 0 => signedRemainder w K width n f
      | 1 => (1 : Q')-w
      | 2 => wardResidual hw0 hw1 K width hK n f
      | _ => Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n))

/-- Exact source-specific energy/variance identity for the entire signed
family, including repetitions and all off-diagonal correlations. -/
theorem padded_family_energy_variance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    normalizedEnergy hw0 hw1 K width hK n (spatialSpan width c qs) ≈
      12*(((1 : Q')-w)*oddVariance hw0 hw1 K width hK n (spatialSpan width c qs)) +
        varianceRemainder hw0 hw1 K width hK n (spatialSpan width c qs) := by
  let a := normalizedAngular hw0 hw1 K width hK n (spatialSpan width c qs)
  let b := normalizedWardResidual hw0 hw1 K width hK n (spatialSpan width c qs)
  let r := normalizedRemainder hw0 hw1 K width hK n (spatialSpan width c qs)
  let v := oddVariance hw0 hw1 K width hK n (spatialSpan width c qs)
  have hj := family_normalized_ward hw0 hw1 K width hK n qs c
    (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
  have halg : ((1 : Q')-w)*a+r ≈
      ((1 : Q')-w)*(a+b)+(r+ -(((1 : Q')-w)*b)) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.var 3))
      (.add (.mul (.var 0) (.add (.var 1) (.var 2)))
        (.add (.var 3) (.neg (.mul (.var 0) (.var 2)))))
      (by decide) (fun | 0 => (1 : Q')-w | 1 => a | 2 => b | _ => r)
  exact Q'.eqv_trans _ _ _
    (padded_family_normalized_taylor hw0 hw1 K hwidth hK n qs c hqs)
    (Q'.eqv_trans _ _ _ halg
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hj)
          (poly_identity_of_normal_eq
            (.mul (.var 0) (.mul (.const 12) (.var 1)))
            (.mul (.const 12) (.mul (.var 0) (.var 1)))
            (by decide) (fun | 0 => (1 : Q')-w | _ => v)))
        (Q'.eqv_refl _)))

/-- The identity reaches the EXISTING normalized finite Wilson window on its
original cutoff/depth schedule. It is not a new law or conditional wrapper. -/
theorem finite_family_increment_variance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {base width : Nat}
    (hwidth : base < width) (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) (stage depth : Nat) :
    originalWindowScalar hw0 hw1 1
        (squareAt (familyExpression width qs c
          (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))) 1)
        stage depth depth ≈
      2*(12*(((1 : Q')-w)*oddVariance hw0 hw1 (headCutoff w+stage) width
          (Nat.le_add_right _ _) depth (spatialSpan width c qs)) +
        varianceRemainder hw0 hw1 (headCutoff w+stage) width
          (Nat.le_add_right _ _) depth (spatialSpan width c qs)) :=
  Q'.eqv_trans _ _ _
    (finite_family_increment_pin hw0 hw1 width qs c
      (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp)) stage depth)
    (Q'.mul_eqv_congr_left _ _ _
      (padded_family_energy_variance hw0 hw1 _ hwidth (Nat.le_add_right _ _)
        depth qs c hqs))

#print axioms varianceRemainder
#print axioms varianceRemainder_raw
#print axioms padded_family_energy_variance
#print axioms finite_family_increment_variance

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceTaylor
