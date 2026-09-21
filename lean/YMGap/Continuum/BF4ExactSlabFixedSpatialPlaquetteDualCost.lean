/-
# Exact cost of the fundamental plaquette dual test

The explicit inverse-heat plaquette test has bare kinetic cost
`w^(-12) + m^2`.  This is an exact finite-cutoff identity for the original
selected-link product heat.  The optional cap below uses only the explicitly
supplied character interval `-2 <= m <= 2`; it makes no limiting or uniform
response claim.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive
import YMGap.Continuum.QuaternionHaarSharpCharacterInterval
import YMGap.Constructive.AbsQ

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_certificate terminalPair_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialResponseDual (testCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive
  (source dualTest source_supported dualTest_supported dualTest_preimage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar
  (plaquette_supported plaquette_mean_zero plaquette_square_one)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage weightedMass

private theorem power_positive {w : Q'} (hw : (0 : Q') < w) :
    ∀ k, (0 : Q') < qpow w k
  | 0 => by change (0 : Q') < 1; decide
  | k+1 => Q'.mul_pos (power_positive hw k) hw

/-- The explicit inverse eigenvalue used by the plaquette dual test. -/
def inverseRate {w : Q'} (hw0 : (0 : Q') < w) : Q' :=
  Q'.recipPos (qpow w 12) (power_positive hw0 12)

/-- A convenient cost cap when the center lies in the fundamental-character
interval. -/
def costCap {w : Q'} (hw0 : (0 : Q') < w) : Q' := inverseRate hw0 + 5

theorem costCap_positive {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') < costCap hw0 :=
  Q'.add_pos (Q'.recipPos_pos _ (power_positive hw0 12)) (by decide)

/-- The fundamental character of the literal plaquette has its sharp
dimension-two interval even when the face uses the supported unit fallback. -/
def plaquetteCharacterInterval (width : Nat) (face : Z4Plaq) :
    Interval (N width) (characterPolynomial (plaquette width face).scalar 1) 2 :=
  Interval.changeCap (by decide)
    (sharpCharacterInterval
      (.scalar
        (BF4ExactSlabFixedSpatialSpatialOrder.plaquette_supported
          width (N width) (Nat.le_refl _) face)
        (BF4ExactSlabFixedSpatialSpatialOrder.plaquette_unit
          width (N width) (Nat.le_refl _) face)) 1)

private theorem cancel_right (c Z r : Q') (h : Z*r ≈ 1) : (c*Z)*r ≈ c :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ h) (Q'.mul_one_eqv c))

/-- Any certified polynomial interval bounds its normalized moment in the
actual two-message middle slice.  The same positive terminal-pair mass is
used on both sides and canceled only after the weighted Haar estimate. -/
theorem middleRatio_interval_bounds {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (left right : Nat)
    {p : RatPoly} {c : Q'} (I : Interval (N width) p c) :
    -c ≤ middleRatio hw0 hw1 K width hK left right p ∧
      middleRatio hw0 hw1 K width hK left right p ≤ c := by
  let gl := terminalMessage w K width left
  let gr := terminalMessage w K width right
  let A := weightedMass w K width (polyMul (polyMul gl p) gr)
  let Z := weightedMass w K width (polyMul gl gr)
  let r := Q'.recipPos Z (terminalPair_positive hw0 hw1 K width hK left right)
  let P : Certificate (N width)
      (polyMul (BF4ExactSlabFixedSpatialSliceHeat.spatialWeight w K width)
        (polyMul gl gr)) :=
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
      ((terminalMessage_certificate hw0 hw1 K width hK left).mul
        (terminalMessage_certificate hw0 hw1 K width hK right))
  have hpin : A ≈ quaternionHaar (N width)
      (polyMul
        (polyMul (BF4ExactSlabFixedSpatialSliceHeat.spatialWeight w K width)
          (polyMul gl gr)) p) := by
    unfold A weightedMass
    exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 3)) (.var 2)))
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
      (by decide) (fun
        | 0 => BF4ExactSlabFixedSpatialSliceHeat.spatialWeight w K width
        | 1 => gl | 2 => gr | _ => p))
  have hweighted := I.weighted_haar_bound P
  have habs : Q'.abs A ≤ c*Z := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hpin))
      (by simpa only [Z, weightedMass] using hweighted)
  have hupper : A ≤ c*Z :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self A) habs
  have hlower : (-c)*Z ≤ A := by
    have hnegabs : -(Q'.abs A) ≤ A :=
      Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.neg_le_abs A))
        (Q'.le_of_eqv (Q'.neg_neg_eqv A))
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.neg_mul_eqv c Z))
      (Q'.le_trans' _ _ _ (Q'.neg_le_neg habs) hnegabs)
  have hr0 : (0 : Q') ≤ r := Q'.le_of_lt (Q'.recipPos_pos Z _)
  have hcancel (d : Q') : (d*Z)*r ≈ d :=
    cancel_right d Z r (Q'.mul_recipPos_eqv Z _)
  change -c ≤ A*r ∧ A*r ≤ c
  exact
    ⟨Q'.le_trans' _ _ _ (Q'.ge_of_eqv (hcancel (-c)))
        (Q'.mul_le_mul_of_nonneg_right _ _ r hlower hr0),
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ r hupper hr0)
        (Q'.le_of_eqv (hcancel c))⟩

/-- The actual fundamental-plaquette center lies in its sharp character
interval.  No face-membership or active-link premise is required. -/
theorem plaquette_middleRatio_bounds {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (left right : Nat)
    (face : Z4Plaq) :
    -(2 : Q') ≤ middleRatio hw0 hw1 K width hK left right
        (characterPolynomial (plaquette width face).scalar 1) ∧
      middleRatio hw0 hw1 K width hK left right
        (characterPolynomial (plaquette width face).scalar 1) ≤ (2 : Q') :=
  middleRatio_interval_bounds hw0 hw1 K width hK left right
    (plaquetteCharacterInterval width face)

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
      c * weightedPair blocks W p q :=
  Q'.eqv_trans _ _ _ (weighted_symm blocks W p (polySmul c q))
    (Q'.eqv_trans _ _ _ (weighted_smul_left blocks W c q p)
      (Q'.mul_eqv_congr_left c _ _ (weighted_symm blocks W q p)))

private theorem affine_pair (blocks : Nat) (W p q : RatPoly)
    (a b c d : Q') :
    weightedPair blocks W
        (polyAdd (polySmul a p) (polySmul b q))
        (polyAdd (polySmul c p) (polySmul d q)) ≈
      a * (c * weightedPair blocks W p p + d * weightedPair blocks W p q) +
        b * (c * weightedPair blocks W q p + d * weightedPair blocks W q q) := by
  have hp : weightedPair blocks W p
      (polyAdd (polySmul c p) (polySmul d q)) ≈
      c * weightedPair blocks W p p + d * weightedPair blocks W p q :=
    Q'.eqv_trans _ _ _ (weighted_add_right blocks W p (polySmul c p) (polySmul d q))
      (Q'.add_eqv_congr' (weighted_smul_right blocks W c p p)
        (weighted_smul_right blocks W d p q))
  have hq : weightedPair blocks W q
      (polyAdd (polySmul c p) (polySmul d q)) ≈
      c * weightedPair blocks W q p + d * weightedPair blocks W q q :=
    Q'.eqv_trans _ _ _ (weighted_add_right blocks W q (polySmul c p) (polySmul d q))
      (Q'.add_eqv_congr' (weighted_smul_right blocks W c q p)
        (weighted_smul_right blocks W d q q))
  exact Q'.eqv_trans _ _ _
    (weighted_add_left blocks W (polySmul a p) (polySmul b q)
      (polyAdd (polySmul c p) (polySmul d q)))
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _
        (weighted_smul_left blocks W a p
          (polyAdd (polySmul c p) (polySmul d q)))
        (Q'.mul_eqv_congr_left a _ _ hp))
      (Q'.eqv_trans _ _ _
        (weighted_smul_left blocks W b q
          (polyAdd (polySmul c p) (polySmul d q)))
        (Q'.mul_eqv_congr_left b _ _ hq)))

/-- Exact cost of the actual inverse-heat plaquette test. -/
theorem plaquette_dualTest_cost {w : Q'} (hw0 : (0 : Q') < w)
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (hactive : ∀ l, l ∈ edgesOf face →
      (baseLinks width).idxOf l ∈ activeBlocks width)
    (K : Nat) (hK : 1 ≤ K) (m : Q') :
    testCost w K width (dualTest hw0 width face m) ≈
      inverseRate hw0 + m*m := by
  let f := characterPolynomial (plaquette width face).scalar 1
  let r := inverseRate hw0
  have hpre : testCost w K width (dualTest hw0 width face m) ≈
      quaternionHaar (N width)
        (polyMul (dualTest hw0 width face m) (source width face m)) := by
    unfold testCost SU2QuaternionProductHeatDualForm.kineticPair
    exact (dualTest_preimage hw0 width face hf hactive K hK m)
      (dualTest hw0 width face m) (dualTest_supported hw0 width face m)
  have hff : weightedPair (N width) polyOne f f ≈ 1 :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_one (polyMul f f)))
      (plaquette_square_one width face hf)
  have hfo : weightedPair (N width) polyOne f polyOne ≈ 0 :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (((RatPolyCoeffEqv.mul_one f).mul_right polyOne).trans
        (RatPolyCoeffEqv.mul_one f)))
      (plaquette_mean_zero width face hf)
  have hof : weightedPair (N width) polyOne polyOne f ≈ 0 :=
    Q'.eqv_trans _ _ _ (weighted_symm (N width) polyOne polyOne f) hfo
  have hoo : weightedPair (N width) polyOne polyOne polyOne ≈ 1 :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (((RatPolyCoeffEqv.one_mul polyOne).mul_right polyOne).trans
        (RatPolyCoeffEqv.one_mul polyOne)))
      (QPolyHaarPositiveSubstitution.haar_one (N width))
  have hpair : quaternionHaar (N width)
      (polyMul (dualTest hw0 width face m) (source width face m)) ≈
      r * ((1 : Q') * weightedPair (N width) polyOne f f +
          (-m) * weightedPair (N width) polyOne f polyOne) +
        (-m) * ((1 : Q') * weightedPair (N width) polyOne polyOne f +
          (-m) * weightedPair (N width) polyOne polyOne polyOne) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (haar_of_coeff
        (RatPolyCoeffEqv.mul_one
          (polyMul (dualTest hw0 width face m) (source width face m))))) ?_
    unfold dualTest source QuaternionHaarDensityVariance.shifted r inverseRate
    exact affine_pair (N width) polyOne f polyOne
      (Q'.recipPos (qpow w 12) (power_positive hw0 12)) (-m) 1 (-m)
  have hmom := Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left r _ _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left 1 _ _ hff)
        (Q'.mul_eqv_congr_left (-m) _ _ hfo)))
    (Q'.mul_eqv_congr_left (-m) _ _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left 1 _ _ hof)
        (Q'.mul_eqv_congr_left (-m) _ _ hoo)))
  exact Q'.eqv_trans _ _ _ hpre (Q'.eqv_trans _ _ _ hpair
    (Q'.eqv_trans _ _ _ hmom
      (poly_identity_of_normal_eq
        (.add
          (.mul (.var 0)
            (.add (.mul (.const 1) (.const 1))
              (.mul (.neg (.var 1)) (.const 0))))
          (.mul (.neg (.var 1))
            (.add (.mul (.const 1) (.const 0))
              (.mul (.neg (.var 1)) (.const 1)))))
        (.add (.var 0) (.mul (.var 1) (.var 1)))
        (by decide) (fun | 0 => r | _ => m))))

/-- With an explicit fundamental-character interval, the regularized cost is
bounded by the computable cap `w^(-12)+5`. -/
theorem one_add_plaquette_dualTest_cost_le_cap {w : Q'} (hw0 : (0 : Q') < w)
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (hactive : ∀ l, l ∈ edgesOf face →
      (baseLinks width).idxOf l ∈ activeBlocks width)
    (K : Nat) (hK : 1 ≤ K) (m : Q')
    (hm0 : -(2 : Q') ≤ m) (hm1 : m ≤ (2 : Q')) :
    1 + testCost w K width (dualTest hw0 width face m) ≤ costCap hw0 := by
  have hsquare : m*m ≤ (2 : Q')*2 :=
    Q'.mul_le_of_bounds (by decide) (by decide) hm0 hm1 hm0 hm1
  have hraw : 1 + (inverseRate hw0 + m*m) ≤ inverseRate hw0 + 5 := by
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left 1 _ _
        (Q'.add_le_add_left (inverseRate hw0) _ _ hsquare))
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.const 1) (.add (.var 0) (.mul (.const 2) (.const 2))))
        (.add (.var 0) (.const 5)) (by decide) (fun _ => inverseRate hw0)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_eqv_congr_left 1 _ _
      (plaquette_dualTest_cost hw0 width face hf hactive K hK m))) hraw

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost.inverseRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost.costCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost.costCap_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost.plaquetteCharacterInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost.middleRatio_interval_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost.plaquette_middleRatio_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost.plaquette_dualTest_cost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost.one_add_plaquette_dualTest_cost_le_cap
