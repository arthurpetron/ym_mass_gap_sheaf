/-
# The actual kinetic comparison fraction and its strict rational rate

The checked full kinetic floor certificate and cap certificate imply
kineticFloor <= kineticCap by integrating their cancelled difference on
the SAME two-slice Haar carrier. Thus the displayed fraction is exactly
kineticFloor / kineticCap, without an auxiliary shrink or new hypothesis.

The resulting rate lies in [0,1), independently of the late heat cutoff.
It depends on nome and spatial width. This is the scalar rate consumed by
the actual transfer's certificate-bracket argument; no contraction theorem,
stationary normalization, OS identification, or physical gap is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (quaternionHaar_append)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder (kineticInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

private theorem haar_cap (blocks : Nat) (c : Q') :
    quaternionHaar blocks (cap c) ≈ c := by
  change (c*1)*quaternionHaarMono blocks [] + 0 ≈ c
  exact Q'.eqv_trans _ _ _ (QPoly.q_add_zero_eqv _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (c*1) _ _ (quaternionHaarMono_one blocks))
      (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (Q'.mul_one_eqv c)))

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1)) (haar_neg blocks p))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

/-- Compare the two actual constants using the same certified kinetic polynomial. -/
theorem kineticFloor_le_cap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) : kineticFloor w width ≤ kineticCap w width := by
  let K := headCutoff w
  let A := kineticFloorCertificate hw0 hw1 K width (Nat.le_refl _)
  let B := (kineticInterval hw0 hw1 K width).upper
  let C : Certificate (N width+N width)
      (polyAdd (cap (kineticCap w width)) (polyNeg (cap (kineticFloor w width)))) :=
    .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq (.add (.var 1) (.neg (.var 2)))
      (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 0))))
      (by decide) (fun
        | 0 => kineticWeight w K width
        | 1 => cap (kineticCap w width)
        | _ => cap (kineticFloor w width))) (A.add B)
  have h : quaternionHaar (N width+N width)
      (polyAdd (cap (kineticCap w width)) (polyNeg (cap (kineticFloor w width)))) ≈
      kineticCap w width + -kineticFloor w width :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' (haar_cap _ _)
        (Q'.eqv_trans _ _ _ (haar_neg _ _) (Q'.neg_eqv_congr _ _ (haar_cap _ _))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ C.haar_nonnegative (Q'.le_of_eqv h))

theorem kineticCap_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) : (0 : Q') < kineticCap w width :=
  Q'.pos_of_lt_of_le (kineticFloor_positive hw0 hw1 width) (kineticFloor_le_cap hw0 hw1 width)

/-- Exact floor/cap fraction; its reciprocal uses the proved positive actual cap. -/
def mixFraction {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat) : Q' :=
  kineticFloor w width * Q'.recipPos (kineticCap w width) (kineticCap_positive hw0 hw1 width)

theorem mixFraction_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) : (0 : Q') < mixFraction hw0 hw1 width :=
  Q'.mul_pos (kineticFloor_positive hw0 hw1 width)
    (Q'.recipPos_pos _ (kineticCap_positive hw0 hw1 width))

theorem mixFraction_le_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) : mixFraction hw0 hw1 width ≤ (1 : Q') :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (kineticFloor_le_cap hw0 hw1 width)
      (Q'.le_of_lt (Q'.recipPos_pos _ (kineticCap_positive hw0 hw1 width))))
    (Q'.le_of_eqv (Q'.mul_recipPos_eqv _ (kineticCap_positive hw0 hw1 width)))

/-- Exact cancellation needed by the certificate-bracket comparison. -/
theorem mixFraction_mul_cap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) : mixFraction hw0 hw1 width * kineticCap w width ≈ kineticFloor w width :=
  Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.var 0) (.mul (.var 2) (.var 1))) (by decide)
    (fun
      | 0 => kineticFloor w width
      | 1 => Q'.recipPos (kineticCap w width) (kineticCap_positive hw0 hw1 width)
      | _ => kineticCap w width))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_recipPos_eqv _ (kineticCap_positive hw0 hw1 width))) (Q'.mul_one_eqv _))

/-- Cutoff-independent rate, with its nome and width dependence retained. -/
def mixRate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat) : Q' :=
  1 + -mixFraction hw0 hw1 width

theorem mixRate_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) : (0 : Q') ≤ mixRate hw0 hw1 width :=
  Q'.sub_nonneg_of_le (mixFraction_le_one hw0 hw1 width)

private theorem one_sub_lt (e : Q') (he : (0 : Q') < e) : 1 + -e < (1 : Q') := by
  have hp : (0 : Int) < e.num := Q'.num_pos_of_pos he
  change (((1 : Int) * (e.den : Int) + (-e.num) * (1 : Int)) * (1 : Int)) <
    ((1 : Int) * (((1 : Nat) * e.den : Nat) : Int))
  simp only [Nat.one_mul, Int.one_mul, Int.mul_one]
  omega

theorem mixRate_lt_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) : mixRate hw0 hw1 width < (1 : Q') :=
  one_sub_lt _ (mixFraction_positive hw0 hw1 width)

end YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate.kineticFloor_le_cap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate.kineticCap_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate.mixFraction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate.mixFraction_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate.mixFraction_le_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate.mixFraction_mul_cap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate.mixRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate.mixRate_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate.mixRate_lt_one
