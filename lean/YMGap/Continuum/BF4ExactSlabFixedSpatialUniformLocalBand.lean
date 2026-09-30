/-
# Size-only local band for the original endpoint message

The original endpoint is compared with the SAME exterior-retaining spectator
as in `BF4ExactSlabFixedSpatialLocalSpectator`. Only the number of selected
links is charged. This does not assert a response, a spatial limit, or a gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator
import YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
import YMGap.Continuum.BF4ExactSlabStarRateObstruction
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitTailBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
open YMGap.Continuum.BF4ExactSlabStarRateObstruction
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitTailBound (pow_add_eqv)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage

/-- A lower scalar depending only on nome and selected-link-list size. -/
def localLower (w : Q') (size : Nat) : Q' := (headFloor w)^(7*size)

/-- A matching upper scalar depending only on nome and list size. -/
def localUpper (w : Q') (size : Nat) : Q' := (prefixCap w)^(7*size)

theorem localLower_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (size : Nat) :
    (0 : Q') < localLower w size :=
  HKPos.pow_pos (headFloor_positive hw0 hw1) _

private theorem one_le_pow (r : Q') (hr : (1 : Q') ≤ r) :
    ∀ k : Nat, (1 : Q') ≤ r^k
  | 0 => Q'.le_refl' _
  | k+1 => by
      rw [Q'.pow_succ]
      have hr0 : (0 : Q') ≤ r :=
        Q'.le_trans' _ _ _ Q'.zero_le_one hr
      have hm := Q'.mul_le_mul_of_nonneg_right _ _ _ hr
        (Q'.pow_nonneg r hr0 k)
      exact Q'.le_trans' _ _ _ (one_le_pow r hr k)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _).symm) hm)

private theorem pow_exponent_mono (r : Q') (hr : (1 : Q') ≤ r)
    {m n : Nat} (hm : m ≤ n) : r^m ≤ r^n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hr0 : (0 : Q') ≤ r := Q'.le_trans' _ _ _ Q'.zero_le_one hr
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ _ (one_le_pow r hr d)
    (Q'.pow_nonneg r hr0 m)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _).symm)
    (Q'.le_trans' _ _ _ hmul (Q'.ge_of_eqv (pow_add_eqv r m d)))

theorem localUpper_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (size : Nat) :
    (0 : Q') < localUpper w size :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (one_le_pow (prefixCap w) (prefixCap_ge_one hw0 hw1) _)

/-- At least the explicitly counted local floor, uniformly in width and
terminal depth. The selected list may repeat links. -/
theorem localLower_le_lowerFactor {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width : Nat) (selected : List Z4Link) {size : Nat}
    (hsize : selected.length ≤ size) :
    localLower w size ≤ lowerFactor w width selected := by
  let q := headFloor w
  let count := (BF4ExactSlabFixedSpatialLocalCollarGeometry.spatialCollarFaces
    width selected).length + (localBlocks width selected).length
  have hcount : count ≤ 7*size := by
    have h := comparison_count_le width selected
    omega
  have hq0 : (0 : Q') ≤ q := Q'.le_of_lt (headFloor_positive hw0 hw1)
  have hq1 : q ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (headFloor_le_oneThirtySecond hw0 hw1) (by decide)
  have hp := HKConvGen.pow_base_antitone hq0 hq1 hcount
  exact Q'.le_trans' _ _ _ hp
    (Q'.le_of_eqv (pow_add_eqv q
      (BF4ExactSlabFixedSpatialLocalCollarGeometry.spatialCollarFaces
        width selected).length (localBlocks width selected).length))

/-- The original local cap is no larger than the size-only cap. -/
theorem upperFactor_le_localUpper {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width : Nat) (selected : List Z4Link) {size : Nat}
    (hsize : selected.length ≤ size) :
    upperFactor w width selected ≤ localUpper w size := by
  let q := prefixCap w
  let count := (BF4ExactSlabFixedSpatialLocalCollarGeometry.spatialCollarFaces
    width selected).length + (localBlocks width selected).length
  have hcount : count ≤ 7*size := by
    have h := comparison_count_le width selected
    omega
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (pow_add_eqv q
      (BF4ExactSlabFixedSpatialLocalCollarGeometry.spatialCollarFaces
        width selected).length (localBlocks width selected).length))
    (pow_exponent_mono q (prefixCap_ge_one hw0 hw1) hcount)

private theorem cap_neg (a : Q') : RatPolyCoeffEqv (polyNeg (cap a)) (cap (-a)) := by
  intro weight
  change (-(a*1))*weight []+0 ≈ ((-a)*1)*weight []+0
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv a 1)))
    (Q'.eqv_refl _)

private theorem cap_sub (a b : Q') :
    RatPolyCoeffEqv (cap (a + -b)) (polyAdd (cap a) (polyNeg (cap b))) :=
  (cap_add a (-b)).symm.trans
    ((RatPolyCoeffEqv.refl _).add (cap_neg b).symm)

private def weaken_lower {blocks : Nat} {p q : RatPoly} {a b : Q'}
    (h : b ≤ a) (Q : Certificate blocks q)
    (P : Certificate blocks (polyAdd p (polyNeg (polySmul a q)))) :
    Certificate blocks (polyAdd p (polyNeg (polySmul b q))) := by
  let delta := a + -b
  have hd : (0 : Q') ≤ delta := Q'.sub_nonneg_of_le h
  have hscale : RatPolyCoeffEqv (polySmul delta q)
      (polyMul (polyAdd (cap a) (polyNeg (cap b))) q) :=
    (cap_mul_left delta q).symm.trans ((cap_sub a b).mul_right q)
  have hleft : RatPolyCoeffEqv
      (polyAdd (polyAdd p (polyNeg (polySmul a q))) (polySmul delta q))
      (polyAdd (polyAdd p (polyNeg (polyMul (cap a) q)))
        (polyMul (polyAdd (cap a) (polyNeg (cap b))) q)) :=
    ((RatPolyCoeffEqv.refl p).add
      (RatPolyCoeffEqv.neg (cap_mul_left a q).symm)).add hscale
  have hring : RatPolyCoeffEqv
      (polyAdd (polyAdd p (polyNeg (polyMul (cap a) q)))
        (polyMul (polyAdd (cap a) (polyNeg (cap b))) q))
      (polyAdd p (polyNeg (polyMul (cap b) q))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.neg (.mul (.var 2) (.var 1))))
        (.mul (.add (.var 2) (.neg (.var 3))) (.var 1)))
      (.add (.var 0) (.neg (.mul (.var 3) (.var 1))))
      (by decide) (fun | 0 => p | 1 => q | 2 => cap a | _ => cap b)
  exact .ofCoeff ((hleft.trans hring).trans
    ((RatPolyCoeffEqv.refl p).add
      (RatPolyCoeffEqv.neg (cap_mul_left b q)))).symm
    (P.add (.smul delta hd Q))

private def weaken_upper {blocks : Nat} {p q : RatPoly} {a b : Q'}
    (h : a ≤ b) (Q : Certificate blocks q)
    (P : Certificate blocks (polyAdd (polySmul a q) (polyNeg p))) :
    Certificate blocks (polyAdd (polySmul b q) (polyNeg p)) := by
  let delta := b + -a
  have hd : (0 : Q') ≤ delta := Q'.sub_nonneg_of_le h
  have hscale : RatPolyCoeffEqv (polySmul delta q)
      (polyMul (polyAdd (cap b) (polyNeg (cap a))) q) :=
    (cap_mul_left delta q).symm.trans ((cap_sub b a).mul_right q)
  have hleft : RatPolyCoeffEqv
      (polyAdd (polyAdd (polySmul a q) (polyNeg p)) (polySmul delta q))
      (polyAdd (polyAdd (polyMul (cap a) q) (polyNeg p))
        (polyMul (polyAdd (cap b) (polyNeg (cap a))) q)) :=
    (((cap_mul_left a q).symm.add (RatPolyCoeffEqv.refl _)).add hscale)
  have hring : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyMul (cap a) q) (polyNeg p))
        (polyMul (polyAdd (cap b) (polyNeg (cap a))) q))
      (polyAdd (polyMul (cap b) q) (polyNeg p)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.mul (.var 2) (.var 1)) (.neg (.var 0)))
        (.mul (.add (.var 3) (.neg (.var 2))) (.var 1)))
      (.add (.mul (.var 3) (.var 1)) (.neg (.var 0)))
      (by decide) (fun | 0 => p | 1 => q | 2 => cap a | _ => cap b)
  exact .ofCoeff ((hleft.trans hring).trans
    ((cap_mul_left b q).add (RatPolyCoeffEqv.refl _))).symm
    (P.add (.smul delta hd Q))

/-- Size-only lower certificate on the ORIGINAL endpoint against the SAME
exterior-retaining spectator. -/
def endpoint_localLowerCertificate {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n : Nat) (selected : List Z4Link) (size : Nat)
    (hsize : selected.length ≤ size) :
    Certificate (N width)
      (polyAdd (polyMul (spatialWeight w K width)
        (terminalMessage w K width (n+1)))
        (polyNeg (polySmul (localLower w size)
          (spectator w K width n selected)))) :=
  weaken_lower (localLower_le_lowerFactor hw0 hw1 width selected hsize)
    (spectator_certificate hw0 hw1 K width hK n selected)
    (endpoint_lowerCertificate hw0 hw1 K width hK n selected)

/-- Matching size-only upper certificate with no replaced exterior law. -/
def endpoint_localUpperCertificate {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n : Nat) (selected : List Z4Link) (size : Nat)
    (hsize : selected.length ≤ size) :
    Certificate (N width)
      (polyAdd (polySmul (localUpper w size)
        (spectator w K width n selected))
        (polyNeg (polyMul (spatialWeight w K width)
          (terminalMessage w K width (n+1))))) :=
  weaken_upper (upperFactor_le_localUpper hw0 hw1 width selected hsize)
    (spectator_certificate hw0 hw1 K width hK n selected)
    (endpoint_upperCertificate hw0 hw1 K width hK n selected)

#print axioms localLower
#print axioms localUpper
#print axioms localLower_positive
#print axioms localUpper_positive
#print axioms localLower_le_lowerFactor
#print axioms upperFactor_le_localUpper
#print axioms endpoint_localLowerCertificate
#print axioms endpoint_localUpperCertificate

end YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
