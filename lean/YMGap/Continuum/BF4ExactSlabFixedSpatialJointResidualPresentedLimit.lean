/-
# The actual residual preserves represented norm limits

The original map x -> x - T^2 x is continuous in the SAME completed norm.
Its representative-level estimate uses only the proved squared triangle for
addition, exact rational negative-scaling isometry, and the actual time
contraction.  Explicit tolerance loss supplies both Cauchy and convergence
moduli.  This is the continuity needed to turn convergent finite approximate
preimages into an exact preimage; no inverse or continuum estimate is assumed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedLimitLaws
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointResidualPresentedLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear (addSpan smulSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (physicalTime)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedLimitLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation (residual)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width

attribute [local irreducible]
  BF4ExactSlabFixedSpatialJointPairingLimit.representativeInner
  BF4ExactSlabFixedSpatialChartJointLimits.jointPairing

def quarter (epsilon : Q') : Q' := HalfPow.half * (HalfPow.half * epsilon)

def residualTolerance (epsilon : Q') : Q' := HalfPow.half * quarter epsilon

theorem residualTolerance_pos {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < residualTolerance epsilon :=
  ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon he))

private theorem four_quarters (epsilon : Q') :
    ((quarter epsilon + quarter epsilon) +
      (quarter epsilon + quarter epsilon)).eqv epsilon :=
  Q'.eqv_trans _ _ _
    (QPoly.q_add_congr (ExpNeg.two_halves (HalfPow.half * epsilon))
      (ExpNeg.two_halves (HalfPow.half * epsilon))) (ExpNeg.two_halves epsilon)

private theorem negative_distance (x y : PhysicalSpan width) :
    Equiv ((D).distSq (smulSpan (-1) x) (smulSpan (-1) y)) ((D).distSq x y) :=
  (jointDistSq_smul hw0 hw1 width (-1) x y).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right ((-1 : Q') * (-1)) 1 (((D).distSq x y).approx n)
          (by decide))
        (Q'.one_mul_eqv (((D).distSq x y).approx n))))

/-- Representative of the original residual; all moduli are inherited from
the actual linear/time constructions. -/
def residualRepresentative (X : (D).Cauchy) : (D).Cauchy :=
  differenceCauchy hw0 hw1 width X ((jointTimeNonexpansive hw0 hw1 width 2).mapCauchy X)

theorem residualRepresentative_pin (X : (D).Cauchy) :
    Quotient.mk (D).completionSetoid (residualRepresentative hw0 hw1 width X) =
      residual hw0 hw1 width (Quotient.mk (D).completionSetoid X) := rfl

/-- Explicit continuity on supplied representatives, measured in the actual
completed norm.  The factor eight includes the representative-limit error. -/
theorem residual_small (X Y : (D).Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon)
    (hXY : RCle (completedDistSq hw0 hw1 width
        (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y))
      (Quotient.mk crealSetoid (ofQ' (residualTolerance epsilon)))) :
    RCle (completedDistSq hw0 hw1 width
        (Quotient.mk (D).completionSetoid (residualRepresentative hw0 hw1 width X))
        (Quotient.mk (D).completionSetoid (residualRepresentative hw0 hw1 width Y)))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  apply completedDistSq_le_of_eventual hw0 hw1 width _ _ epsilon
    (distanceRate hw0 hw1 width X Y (residualTolerance epsilon))
  intro n hn
  have hquarter : (0 : Q') < quarter epsilon :=
    ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon he)
  have hd := late_distSq_le hw0 hw1 width X Y (quarter epsilon) hquarter hXY n hn
  have ht := leEv_trans (jointPhysicalTime_contraction hw0 hw1 width 2 (X.seq n) (Y.seq n)) hd
  have hneg := leEv_trans
    (leEv_of_equiv (negative_distance hw0 hw1 width
      (physicalTime 2 (X.seq n)) (physicalTime 2 (Y.seq n)))) ht
  have h := leEv_trans
    (jointDistSq_add hw0 hw1 width (X.seq n) (Y.seq n)
      (smulSpan (-1) (physicalTime 2 (X.seq n)))
      (smulSpan (-1) (physicalTime 2 (Y.seq n))))
    (leEv_add (leEv_add hd hd) (leEv_add hneg hneg))
  exact leEv_trans h (leEv_of_equiv (ofQ'_equiv_of_eqv (four_quarters epsilon)))

variable (X : PresentedNormCauchy hw0 hw1 width)

def mapResidual : PresentedNormCauchy hw0 hw1 width where
  pt p := residualRepresentative hw0 hw1 width (X.pt p)
  modulus epsilon := X.modulus (residualTolerance epsilon)
  cauchy := fun epsilon he p q hp hq =>
    residual_small hw0 hw1 width (X.pt p) (X.pt q) epsilon he
      (X.cauchy _ (residualTolerance_pos he) p q hp hq)

def residualCandidate : CandidateLimit hw0 hw1 width (mapResidual hw0 hw1 width X) where
  representative := residualRepresentative hw0 hw1 width (X.toPresented hw0 hw1 width).diagonal
  modulus epsilon := X.limitRate hw0 hw1 width (residualTolerance epsilon)
  converges := fun epsilon he p hp =>
    residual_small hw0 hw1 width (X.pt p) (X.toPresented hw0 hw1 width).diagonal epsilon he
      (X.limit_converges hw0 hw1 width _ (residualTolerance_pos he) p hp)

/-- Passage of the actual residual through the represented limit, as equality
of vectors on the existing reflected carrier. -/
theorem mapResidual_limit :
    (mapResidual hw0 hw1 width X).limit hw0 hw1 width =
      residual hw0 hw1 width (X.limit hw0 hw1 width) :=
  ((residualCandidate hw0 hw1 width X).eq_constructed_limit
    hw0 hw1 width (mapResidual hw0 hw1 width X)).symm

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointResidualPresentedLimit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointResidualPresentedLimit.residual_small
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointResidualPresentedLimit.residualRepresentative_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointResidualPresentedLimit.mapResidual
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointResidualPresentedLimit.residualCandidate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointResidualPresentedLimit.mapResidual_limit
