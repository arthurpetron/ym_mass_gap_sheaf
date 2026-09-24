/-
# Shifted complementary moment of the dyadic Wilson square

For the actual padded dyadic-square character and the unchanged selected-link
heat complement, the exact free-link moments evaluate every rationally shifted
square.  This is an unnormalized spectator identity used before the later
interacting comparison; it is not a full-action variance or scaling result.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareSingleLinkMoments
import YMGap.Continuum.QuaternionHaarDensityVariance

namespace YMGap.Continuum.BF4DyadicWilsonSquareShiftedMoment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (character)
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry (complementHeat)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareUniqueEdge (selectedLink)
open YMGap.Continuum.BF4DyadicWilsonSquareSingleLinkMoments
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
  (weightedPair weighted_symm weighted_add_left weighted_smul_left)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem weighted_add_right (blocks : Nat) (W a b c : RatPoly) :
    weightedPair blocks W a (polyAdd b c) ≈
      weightedPair blocks W a b + weightedPair blocks W a c :=
  Q'.eqv_trans _ _ _ (weighted_symm blocks W a (polyAdd b c))
    (Q'.eqv_trans _ _ _ (weighted_add_left blocks W b c a)
      (Q'.add_eqv_congr' (weighted_symm blocks W b a)
        (weighted_symm blocks W c a)))

private theorem weighted_smul_right (blocks : Nat) (W : RatPoly)
    (c : Q') (p q : RatPoly) :
    weightedPair blocks W p (polySmul c q) ≈
      c*weightedPair blocks W p q :=
  Q'.eqv_trans _ _ _ (weighted_symm blocks W p (polySmul c q))
    (Q'.eqv_trans _ _ _ (weighted_smul_left blocks W c q p)
      (Q'.mul_eqv_congr_left c _ _ (weighted_symm blocks W q p)))

private theorem weighted_smul_both (blocks : Nat) (W : RatPoly)
    (a b : Q') (p q : RatPoly) :
    weightedPair blocks W (polySmul a p) (polySmul b q) ≈
      a*(b*weightedPair blocks W p q) :=
  Q'.eqv_trans _ _ _ (weighted_smul_left blocks W a p (polySmul b q))
    (Q'.mul_eqv_congr_left a _ _ (weighted_smul_right blocks W b p q))

private theorem shifted_pair_expand (blocks : Nat) (W p : RatPoly) (c : Q') :
    weightedPair blocks W (shifted p c) (shifted p c) ≈
      (1*(1*weightedPair blocks W p p) +
        1*((-c)*weightedPair blocks W p polyOne)) +
      ((-c)*(1*weightedPair blocks W polyOne p) +
        (-c)*((-c)*weightedPair blocks W polyOne polyOne)) := by
  unfold shifted
  exact Q'.eqv_trans _ _ _
    (weighted_add_left blocks W (polySmul 1 p) (polySmul (-c) polyOne)
      (polyAdd (polySmul 1 p) (polySmul (-c) polyOne)))
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _
        (weighted_add_right blocks W (polySmul 1 p) (polySmul 1 p)
          (polySmul (-c) polyOne))
        (Q'.add_eqv_congr'
          (weighted_smul_both blocks W 1 1 p p)
          (weighted_smul_both blocks W 1 (-c) p polyOne)))
      (Q'.eqv_trans _ _ _
        (weighted_add_right blocks W (polySmul (-c) polyOne) (polySmul 1 p)
          (polySmul (-c) polyOne))
        (Q'.add_eqv_congr'
          (weighted_smul_both blocks W (-c) 1 polyOne p)
          (weighted_smul_both blocks W (-c) (-c) polyOne polyOne))))

/-- Exact shifted-square identity against the unchanged selected-link heat
complement.  No positivity certificate is needed for this algebraic moment. -/
theorem paddedSquare_shifted_complement_moment
    (w : Q') (K scale width extent : Nat)
    (hwidth : side scale < width) (hambient : width ≤ extent) (c : Q') :
    let chi := character extent (paddedSquare scale width hwidth).edges 1
    let R := complementHeat w K extent selectedLink
    quaternionHaar (B extent)
      (polyMul (polyMul (shifted chi c) (shifted chi c)) R) ≈
      (1+c*c)*quaternionHaar (B extent) R := by
  let chi := character extent (paddedSquare scale width hwidth).edges 1
  let R := complementHeat w K extent selectedLink
  let Z := quaternionHaar (B extent) R
  have hsq : weightedPair (B extent) R chi chi ≈ Z :=
    paddedSquare_complement_second_moment w K scale width extent hwidth hambient
  have hmean0 : quaternionHaar (B extent) (polyMul chi R) ≈ 0 :=
    paddedSquare_complement_first_moment w K scale width extent hwidth hambient
  have hm : weightedPair (B extent) R chi polyOne ≈ 0 :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff ((RatPolyCoeffEqv.mul_one chi).mul_right R)) hmean0
  have hm' : weightedPair (B extent) R polyOne chi ≈ 0 :=
    Q'.eqv_trans _ _ _ (weighted_symm (B extent) R polyOne chi) hm
  have hz : weightedPair (B extent) R polyOne polyOne ≈ Z :=
    haar_of_coeff (((RatPolyCoeffEqv.one_mul polyOne).mul_right R).trans
      (RatPolyCoeffEqv.one_mul R))
  have hexpand := shifted_pair_expand (B extent) R chi c
  have hsub : weightedPair (B extent) R (shifted chi c) (shifted chi c) ≈
      (1*(1*Z) + 1*((-c)*0)) + ((-c)*(1*0) + (-c)*((-c)*Z)) :=
    Q'.eqv_trans _ _ _ hexpand
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (qmul (Q'.eqv_refl 1) (qmul (Q'.eqv_refl 1) hsq))
          (qmul (Q'.eqv_refl 1) (qmul (Q'.eqv_refl (-c)) hm)))
        (Q'.add_eqv_congr' (qmul (Q'.eqv_refl (-c)) (qmul (Q'.eqv_refl 1) hm'))
          (qmul (Q'.eqv_refl (-c)) (qmul (Q'.eqv_refl (-c)) hz))))
  exact Q'.eqv_trans _ _ _ hsub
    (poly_identity_of_normal_eq
      (.add (.add (.mul (.const 1) (.mul (.const 1) (.var 0)))
        (.mul (.const 1) (.mul (.neg (.var 1)) (.const 0))))
        (.add (.mul (.neg (.var 1)) (.mul (.const 1) (.const 0)))
          (.mul (.neg (.var 1)) (.mul (.neg (.var 1)) (.var 0)))))
      (.mul (.add (.const 1) (.mul (.var 1) (.var 1))) (.var 0))
      (by decide) (fun | 0 => Z | _ => c))

#print axioms paddedSquare_shifted_complement_moment

end YMGap.Continuum.BF4DyadicWilsonSquareShiftedMoment
