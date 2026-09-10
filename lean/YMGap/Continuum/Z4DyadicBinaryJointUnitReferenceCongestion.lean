/-
# Cancel heat coupling from the remaining joint reference congestion

The reference-congestion ratio left by parity-ground normalization has the
same strictly positive coarse parity-ground heat power in numerator and
denominator.  This file cancels that common factor constructively and then
separates the result into

* the two coupling-one fine source weights, and
* a coupling-one target weight divided by its oriented ground-target weight.

Thus the remaining pointwise obstruction is a finite SU(2) multiplicity and
corrected-slab link-congestion problem, not another hidden heat-coupling
constant.  No ceiling on that congestion or connected-carrier sum is proved
here.

Constructive contract: positivity-guarded rational cancellation and exact
finite weight identities only; no `Classical`, choice, `native_decide`, proof
hole, noncomputable declaration, trusted external computation, enlarged
heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryJointParityGroundNormalization

namespace YMGap.Continuum.Z4DyadicBinaryJointUnitReferenceCongestion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinaryJointParityGroundNormalization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinaryTargetExcitationCasimirExcess

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast_local, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private theorem qpow_pos_local {value : Q'}
    (hvalue : (0 : Q') < value) : ∀ exponent : Nat,
    (0 : Q') < qpow value exponent
  | 0 => by
      change (0 : Q') < 1
      decide
  | exponent + 1 =>
      Q'.mul_pos (qpow_pos_local hvalue exponent) hvalue

private theorem q_right_pos_of_mul_pos_local
    {left right : Q'}
    (hleft : (0 : Q') ≤ left)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < right := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hleftNum : (0 : Int) ≤ left.num :=
    (Q'.zero_le_iff_num_nonneg left).mp hleft
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hrightNonpos
  have hmulNonpos : left.num * right.num ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos hleftNum hrightNonpos
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

private theorem divPos_eqv_of_eqv_mul_local {p q c : Q'}
    (hq : (0 : Q') < q) (h : p ≈ c * q) :
    Q'.divPos p q hq ≈ c := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv c q (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _
      (Q'.mul_recipPos_eqv q hq)) ?_
  exact Q'.mul_one_eqv c

/-- Cancel one common strictly positive factor from a constructive rational
ratio. -/
private theorem divPos_common_left_cancel_local
    (common numerator denominator : Q')
    (hcommon : (0 : Q') < common)
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos (common * numerator) (common * denominator)
        (Q'.mul_pos hcommon hdenominator) ≈
      Q'.divPos numerator denominator hdenominator := by
  let ratio := Q'.divPos numerator denominator hdenominator
  have hratio : ratio * denominator ≈ numerator :=
    Q'.divPos_mul_eqv numerator denominator hdenominator
  apply divPos_eqv_of_eqv_mul_local
  refine Q'.eqv_trans _ (common * (ratio * denominator)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left common _ _ (Q'.eqv_symm hratio)
  · ring_qeqv

/-! ## 1. The positive coupling-one ground target weight -/

def finePacketOrientedGroundUnitTargetWeight
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling) : Q' :=
  finePacketOrientedUnitCouplingTargetRawPairWeight
    S orientation first second
    (finePacketOrientedParityGroundTargetPair
      S orientation first second)

theorem finePacketOrientedGroundUnitTargetWeight_pos
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S) :
    (0 : Q') < finePacketOrientedGroundUnitTargetWeight
      S orientation first.1 second.1 := by
  have hnormalizer :=
    finePacketOrientedParityGroundReferenceNormalizationMass_pos
      S hfineCutoff hcoarseCoupling orientation first second
  unfold finePacketOrientedParityGroundReferenceNormalizationMass at hnormalizer
  unfold finePacketOrientedGroundUnitTargetWeight
  exact q_right_pos_of_mul_pos_local
    (Q'.le_of_lt
      (qpow_pos_local hcoarseCoupling
        (finePacketOrientedTotalTargetParityGroundCasimir
          S orientation first.1 second.1)))
    hnormalizer

/-! ## 2. The heat-free target and joint congestion factors -/

/-- Relative coupling-one target congestion above the literal oriented
ground target.  This contains all target fusion and corrected-slab link
multiplicity growth. -/
def finePacketOrientedUnitTargetCongestionRatio
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  Q'.divPos
    (finePacketOrientedUnitCouplingTargetRawPairWeight
      S orientation first.1 second.1 pair)
    (finePacketOrientedGroundUnitTargetWeight
      S orientation first.1 second.1)
    (finePacketOrientedGroundUnitTargetWeight_pos
      S hfineCutoff hcoarseCoupling orientation first second)

/-- The complete heat-free congestion: coupling-one fine source mass times
relative coupling-one target congestion. -/
def finePacketOrientedJointUnitReferenceCongestion
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  finePacketFineSourceUnitCouplingPairWeight S first.1 second.1 *
    finePacketOrientedUnitTargetCongestionRatio
      S hfineCutoff hcoarseCoupling orientation first second pair

/-- The congestion ratio from milestone 330 contains no residual heat power:
it is exactly the coupling-one fine source weight times a coupling-one target
ratio relative to the literal ground target. -/
theorem finePacketOrientedJointReferenceCongestionRatio_eqv_unitReferenceCongestion
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling) :
    finePacketOrientedJointReferenceCongestionRatio
        S hfineCutoff hcoarseCoupling orientation first second pair ≈
      finePacketOrientedJointUnitReferenceCongestion
        S hfineCutoff hcoarseCoupling orientation first second pair := by
  let common := qpow S.coarse.coupling
    (finePacketOrientedTotalTargetParityGroundCasimir
      S orientation first.1 second.1)
  let fineUnit := finePacketFineSourceUnitCouplingPairWeight
    S first.1 second.1
  let targetUnit := finePacketOrientedUnitCouplingTargetRawPairWeight
    S orientation first.1 second.1 pair
  let groundUnit := finePacketOrientedGroundUnitTargetWeight
    S orientation first.1 second.1
  have hcommon : (0 : Q') < common :=
    qpow_pos_local hcoarseCoupling _
  have hground : (0 : Q') < groundUnit :=
    finePacketOrientedGroundUnitTargetWeight_pos
      S hfineCutoff hcoarseCoupling orientation first second
  have hcancel :
      Q'.divPos (common * (fineUnit * targetUnit))
          (common * groundUnit) (Q'.mul_pos hcommon hground) ≈
        Q'.divPos (fineUnit * targetUnit) groundUnit hground :=
    divPos_common_left_cancel_local
      common (fineUnit * targetUnit) groundUnit hcommon hground
  unfold finePacketOrientedJointReferenceCongestionRatio
    finePacketOrientedJointParityGroundReferenceWeight
    finePacketOrientedParityGroundReferenceNormalizationMass
    finePacketOrientedJointUnitReferenceCongestion
    finePacketOrientedUnitTargetCongestionRatio
    finePacketOrientedGroundUnitTargetWeight
  refine Q'.eqv_trans _
    (Q'.divPos (common * (fineUnit * targetUnit))
      (common * groundUnit) (Q'.mul_pos hcommon hground)) _ ?_ ?_
  · exact Q'.eqv_refl _
  refine Q'.eqv_trans _
    (Q'.divPos (fineUnit * targetUnit) groundUnit hground) _ hcancel ?_
  unfold Q'.divPos
  exact Q'.mul_assoc_eqv fineUnit targetUnit (Q'.recipPos groundUnit hground)

/-! ## 3. Axiom audit -/

#print axioms finePacketOrientedGroundUnitTargetWeight
#print axioms finePacketOrientedGroundUnitTargetWeight_pos
#print axioms finePacketOrientedUnitTargetCongestionRatio
#print axioms finePacketOrientedJointUnitReferenceCongestion
#print axioms finePacketOrientedJointReferenceCongestionRatio_eqv_unitReferenceCongestion

end YMGap.Continuum.Z4DyadicBinaryJointUnitReferenceCongestion
