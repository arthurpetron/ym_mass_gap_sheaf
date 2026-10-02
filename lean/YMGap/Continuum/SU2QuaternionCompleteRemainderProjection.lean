/-
# A computed projection gain in the complete source remainder

The overlap of the original source-observable vector with the completed
commutator gives a computable nonnegative gain.  A positive rational
regularizer avoids dividing by a potentially zero raw Haar norm.  The gain
is paid from the EXISTING negative completed square; cubic, omitted-mode,
and angular-pair debts are untouched.  No comparison to the interacting
variance, near-one rate, or continuum claim is made.
-/

import YMGap.Continuum.SU2QuaternionCompleteRemainderSquare
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

namespace YMGap.Continuum.SU2QuaternionCompleteRemainderProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairBudget)
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder (sourceErrorBudget)
open YMGap.Continuum.SU2QuaternionSecondOrderCancellation (commutatorPolynomial)
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor (sourceFirstOrder)
open YMGap.Continuum.SU2QuaternionCompleteRemainderCancellation
open YMGap.Continuum.SU2QuaternionCompleteRemainderSquare
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

/-- The literal raw-Haar overlap. It is not an OWN-marginal covariance. -/
def projectionOverlap (tail : Nat) (q f : RatPoly) : Q' :=
  H (tail+1) (polyMul (polyMul q f) (completedCommutator tail q f))

/-- The raw source-observable square is nonnegative at every supported input. -/
theorem observableSquare_nonnegative (tail : Nat) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    (0 : Q') ≤ observableSquare tail q f := by
  let v := polyMul q f
  have hv : SupportedQuaternionBlocks (tail+1) v := supported_polyMul hq hf
  exact (Certificate.square v hv).haar_nonnegative

/-- The positive regularizer makes the denominator constructive even if the
raw source-observable vector is zero. -/
theorem projectionDenom_pos (tail : Nat) (q f : RatPoly) (epsilon : Q')
    (hε : (0 : Q') < epsilon)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    (0 : Q') < observableSquare tail q f + epsilon := by
  have hB := observableSquare_nonnegative tail q f hq hf
  have hstep : epsilon ≤ epsilon + observableSquare tail q f :=
    Q'.add_le_self_of_nonneg epsilon _ hB
  exact Q'.pos_of_lt_of_le hε
    (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

/-- Finite rational projection data. The caller may choose the actual original
partition as `epsilon`, but no normalization is performed here. -/
def projectionGain (tail : Nat) (q f : RatPoly) (epsilon : Q')
    (hε : (0 : Q') < epsilon)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) : Q' :=
  Q'.divPos (projectionOverlap tail q f * projectionOverlap tail q f)
    (observableSquare tail q f + epsilon)
    (projectionDenom_pos tail q f epsilon hε hq hf)

/-- The computed overlap is first order minus half of the same raw square.
This is a source-specific algebraic pin, not an eigenvector assumption. -/
theorem projection_overlap_pin (tail : Nat) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    projectionOverlap tail q f ≈
      sourceFirstOrder tail q f - HalfPow.half * observableSquare tail q f := by
  let n := tail+1
  let v := polyMul q f
  let C := commutatorPolynomial (List.range n) q f
  have hpoly : RatPolyCoeffEqv
      (polyMul v (completedCommutator tail q f))
      (polyAdd (polyMul v C)
        (polySmul (-HalfPow.half) (polyMul v v))) := by
    unfold completedCommutator
    exact (RatPolyCoeffEqv.mul_add_right v C (polySmul (-HalfPow.half) v)).trans
      ((RatPolyCoeffEqv.refl _).add
        (RatPolyCoeffEqv.polyMul_smul_right (-HalfPow.half) v v))
  have hpair := sourceFirstOrder_commutator_pair tail q f hq hf
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hpoly)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' hpair.symm
          (quaternionHaar_polySmul n (-HalfPow.half) _))
        (poly_identity_of_normal_eq
          (.add (.var 0) (.mul (.neg (.var 1)) (.var 2)))
          (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))
          (by decide)
          (fun | 0 => sourceFirstOrder tail q f
               | 1 => HalfPow.half
               | _ => observableSquare tail q f))))

theorem projectionGain_nonnegative (tail : Nat) (q f : RatPoly)
    (epsilon : Q') (hε : (0 : Q') < epsilon)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    (0 : Q') ≤ projectionGain tail q f epsilon hε hq hf :=
  Q'.mul_nonneg _ _
    (SumOfSquares.q_mul_self_nonneg (projectionOverlap tail q f))
    (Q'.le_of_lt (Q'.recipPos_pos _
      (projectionDenom_pos tail q f epsilon hε hq hf)))

/-- Unweighted Haar Cauchy--Schwarz bounds the gain by the ORIGINAL negative
completed square, with no lower bound on the raw observable norm. -/
theorem projectionGain_le_squareCompletionMass (tail : Nat) (q f : RatPoly)
    (epsilon : Q') (hε : (0 : Q') < epsilon)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    projectionGain tail q f epsilon hε hq hf ≤
      squareCompletionMass tail q f := by
  let n := tail+1
  let v := polyMul q f
  let T := completedCommutator tail q f
  let B := observableSquare tail q f
  let S := squareCompletionMass tail q f
  let d := projectionOverlap tail q f
  let D := B+epsilon
  have hv : SupportedQuaternionBlocks n v := supported_polyMul hq hf
  have hT : SupportedQuaternionBlocks n T :=
    completedCommutator_supported tail q f hq hf
  have hcs := weighted_cauchySchwarz n polyOne v T (Certificate.one n) hv hT
  have hpair : weightedPair n polyOne v T ≈ d :=
    haar_of_coeff (RatPolyCoeffEqv.mul_one (polyMul v T))
  have hB : weightedPair n polyOne v v ≈ B :=
    haar_of_coeff (RatPolyCoeffEqv.mul_one (polyMul v v))
  have hS : weightedPair n polyOne T T ≈ S :=
    haar_of_coeff (RatPolyCoeffEqv.mul_one (polyMul T T))
  have hcs' : d*d ≤ B*S :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (qmul hpair.symm hpair.symm))
      (Q'.le_trans' _ _ _ hcs
        (Q'.le_of_eqv (qmul hB hS)))
  have hS0 := squareCompletionMass_nonnegative tail q f hq hf
  have hB0 := observableSquare_nonnegative tail q f hq hf
  have hBD : B ≤ D := Q'.add_le_self_of_nonneg B epsilon (Q'.le_of_lt hε)
  have hDS : B*S ≤ S*D :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right B D S hBD hS0)
      (Q'.le_of_eqv (Q'.mul_comm_eqv D S))
  unfold projectionGain
  exact Q'.divPos_le_of_le_mul (d*d) D
    (projectionDenom_pos tail q f epsilon hε hq hf)
    (Q'.le_trans' _ _ _ hcs' hDS)

/-- The full cutoff remainder pays the same cubic, omitted-mode, and angular
pair budgets as before, but retains a computable nonnegative portion of the
negative completed square. This does not compare the cost with OWN variance. -/
theorem completeRemainder_le_projectionCeiling (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (epsilon : Q') (hε : (0 : Q') < epsilon) :
    completeRemainder tail w K q f ≤
      squareCeiling tail w K q f -
        (HalfPow.half * (((1 : Q')-w)*((1 : Q')-w))) *
          projectionGain tail q f epsilon hε hq hf := by
  let h := (1 : Q')-w
  let alpha := HalfPow.half*(h*h)
  let S := squareCompletionMass tail q f
  let g := projectionGain tail q f epsilon hε hq hf
  let B := sourceSquareMass tail q f
  let E := sourceErrorBudget tail w K q f
  let T := h*((h*h)*pairBudget tail q (polyMul q (angularSquare tail f)))
  have hbase := completeRemainder_le_retained tail hw0 hw1 K hK q f hq hf
  have hsquare := sourceFirstOrder_sub_square_complete tail q f hq hf
  have hjoin : retainedCeiling tail w K q f ≈ squareCeiling tail w K q f - alpha*S := by
    unfold retainedCeiling squareCeiling
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left alpha _ _ hsquare)
          (Q'.eqv_refl _)) (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.var 0)
          (.add (.mul (.var 1) (.var 2)) (.neg (.var 3)))) (.var 4)) (.var 5))
        (.add
          (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 4)) (.var 5))
          (.neg (.mul (.var 0) (.var 3))))
        (by decide)
        (fun | 0 => alpha | 1 => quarter | 2 => B | 3 => S | 4 => E | _ => T))
  have halpha : (0 : Q') ≤ alpha :=
    Q'.mul_nonneg _ _ HalfPow.half_nonneg
      (Q'.mul_nonneg _ _
        (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
        (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)))
  have hgain := projectionGain_le_squareCompletionMass tail q f epsilon hε hq hf
  have hscaled := Q'.mul_le_mul_of_nonneg_left g S alpha hgain halpha
  have hless : squareCeiling tail w K q f - alpha*S ≤
      squareCeiling tail w K q f - alpha*g :=
    Q'.add_le_add_left _ _ _ (Q'.neg_le_neg hscaled)
  exact Q'.le_trans' _ _ _ hbase
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hjoin) hless)

#print axioms projectionOverlap
#print axioms observableSquare_nonnegative
#print axioms projectionDenom_pos
#print axioms projectionGain
#print axioms projection_overlap_pin
#print axioms projectionGain_nonnegative
#print axioms projectionGain_le_squareCompletionMass
#print axioms completeRemainder_le_projectionCeiling

end YMGap.Continuum.SU2QuaternionCompleteRemainderProjection
