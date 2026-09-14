/-
# The large original core remainder costs less than half the tube reference

At the explicit SU(2) nome 1/1024, every core of size at least 33 can be
summed under w^36/4 times the SAME full partition square. Scalar powers
are controlled in small blocks; all cutoff and volume parameters remain
quantified in the original signed remainder theorem.

After this tail is absorbed, only other cores of sizes 12 through 32
remain in the original numerator lower bound. Their signed sum is NOT
bounded here. Positive full response and continuum/Clay remain open.
-/

import YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
import YMGap.Continuum.BF4ExactSlabOriginalTubeReferenceFloor

namespace YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabOriginalTubeReferenceFloor
open YMGap.Continuum.BF4ExactSlabOriginalTubeCoreSplit
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound
open YMGap.Continuum.BF4ExactSlabSummableCoreRate
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation "hd₀" => (And.right existingNome_guards)
local notation "hs₀" => (And.right existingNome_entropyRate)
local notation "r₀" => inverseFaceFloor nome hd₀
local notation "s₀" => entropyRate 625 (adjustedCoreRate nome hd₀)

def blockCeiling : Q' := Q'.mkPos 1025 1024 (by decide)

theorem inverse_eighth_le_block : r₀^8 ≤ blockCeiling := by decide

theorem inverse_fortyeighth_le : r₀^48 ≤ Q'.mkPos 17 16 (by decide) := by
  have h := TotalMajorantClose.pow_le_pow_base
    (Q'.pow_nonneg _ (Q'.le_of_lt (inverseFaceFloor_pos nome hd₀)) 8) inverse_eighth_le_block 6
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (TotalMajorantClose.pow_mul r₀ 8 6))
    (Q'.le_trans' _ _ _ h (by decide : blockCeiling^6 ≤ Q'.mkPos 17 16 (by decide)))

theorem probe_prefactor_le_two : probePrefactor nome hd₀ 8 ≤ 2 := by
  have h := TotalMajorantClose.pow_le_pow_base
    (Q'.pow_nonneg _ (Q'.le_of_lt (inverseFaceFloor_pos nome hd₀)) 8) inverse_eighth_le_block 12
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (TotalMajorantClose.pow_mul r₀ 8 12))
    (Q'.le_trans' _ _ _ h (by decide : blockCeiling^12 ≤ (2 : Q')))

theorem entropy_le_dyadic : s₀ ≤ Q'.invSucc 4095 := by
  have h := Q'.mul_le_mul_of_nonneg_left _ _ (625 : Q')
    (Q'.mul_le_mul_of_nonneg_left _ _ (pairedHeatRate nome) inverse_fortyeighth_le
      (pairedHeatRate_nonnegative (Q'.le_of_lt nome_pos))) (by decide)
  exact Q'.le_trans' _ _ _ h
    (by decide : (625 : Q')*(pairedHeatRate nome * Q'.mkPos 17 16 (by decide)) ≤ Q'.invSucc 4095)

theorem entropy_reciprocal_le_two : Q'.recipPos (1 + -s₀) (HKPos.one_sub_pos hs₀) ≤ 2 := by
  have h := Q'.mul_le_mul_of_nonneg_right _ _ (2 : Q')
    (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg entropy_le_dyadic)) (by decide)
  apply Q'.le_of_mul_le_mul_left (c := 1 + -s₀) _ (HKPos.one_sub_pos hs₀)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_recipPos_eqv _ _))
    (Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ (1 + -(Q'.invSucc 4095))*2) h)

/-- Explicit scalar witness used by the large-core bound; not a full-response floor. -/
def tailAllowance : Q' := Q'.invSucc 3 * RingNormaliser.qpow nome 36

theorem tailAllowance_pos : (0 : Q') < tailAllowance := by
  have h : tailAllowance ≈ HalfPow.half * referenceFloor nome :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (by decide : Q'.invSucc 3 ≈ HalfPow.half*HalfPow.half)) (Q'.mul_assoc_eqv _ _ _)
  exact Q'.pos_of_lt_of_le (Q'.mul_pos (by decide) (referenceFloor_pos nome_pos)) (Q'.ge_of_eqv h)

theorem tailCoefficient_le_dyadic (threshold : Nat) :
    tailCoefficient nome hd₀ hs₀ threshold ≤
      (16 : Q') * ((1562500*(Q'.invSucc 4095)^threshold)*2) := by
  have hp : (((2 : Q')*2+2*2)*probePrefactor nome hd₀ 8) ≤ 16 :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ probe_prefactor_le_two (by decide))
      (by decide : (((2 : Q')*2+2*2)*2) ≤ 16)
  have hpow := TotalMajorantClose.pow_le_pow_base
    (Q'.le_of_lt existingNome_entropyRate.1) entropy_le_dyadic threshold
  have hb : tailBudget 1562500 625 threshold (adjustedCoreRate nome hd₀) hs₀ ≤
      (1562500*(Q'.invSucc 4095)^threshold)*2 := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ (1562500 : Q') hpow (by decide))
        (Q'.le_of_lt (Q'.recipPos_pos _ _)))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ entropy_reciprocal_le_two
        (Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg _ (by decide) threshold)))
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hp
      (tailBudget_nonnegative 1562500 625 threshold (adjustedCoreRate_nonnegative (Q'.le_of_lt nome_pos) hd₀) hs₀))
    (Q'.mul_le_mul_of_nonneg_left _ _ (16 : Q') hb (by decide))

theorem size33_scalar_guard :
    (16 : Q') * ((1562500*(Q'.invSucc 4095)^33)*2) ≤ tailAllowance := by decide

theorem size33_tailCoefficient_le : tailCoefficient nome hd₀ hs₀ 33 ≤ tailAllowance :=
  Q'.le_trans' _ _ _ (tailCoefficient_le_dyadic 33) size33_scalar_guard

/-- Uniform in cutoff and margin for the ACTUAL large signed other-core sum. -/
theorem largeOtherRemainder_size33_bound (K margin : Nat) :
    Q'.abs (largeOtherRemainder nome K 33 margin) ≤
      tailAllowance * partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)) :=
  Q'.le_trans' _ _ _ (largeOtherRemainder_bound (Q'.le_of_lt nome_pos) (Q'.le_of_lt nome_lt_one)
    existingNome_guards.1 hd₀ hs₀ K 33 margin)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ size33_tailCoefficient_le (SumOfSquares.q_mul_self_nonneg _))

private theorem absorb_tail (A C Z E S L N : Q') (href : A ≈ 2*C)
    (hsplit : E ≈ S+L) (htail : Q'.abs L ≤ C*Z) (hN : A*Z+E ≤ N) : C*Z+S ≤ N := by
  have hl : -(C*Z) ≤ L := Q'.le_trans' _ _ _ (Q'.neg_le_neg htail) (ExpNeg.neg_abs_le _)
  have h := Q'.add_le_add_left (A*Z) _ _ (Q'.add_le_add_left S _ _ hl)
  have he : C*Z+S ≈ (2*C)*Z+(S + -(C*Z)) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.var 2))
      (.add (.mul (.mul (.const 2) (.var 0)) (.var 1))
        (.add (.var 2) (.neg (.mul (.var 0) (.var 1)))))
      (by decide) (fun i => if i=0 then C else if i=1 then Z else S)
  have he' := Q'.eqv_trans _ _ _ he
    (Q'.add_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_right _ _ Z (Q'.eqv_symm href)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he') (Q'.le_trans' _ _ _ h
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_eqv_congr_left _ _ _ hsplit)) hN))

/-- All cores of size >=33 are absorbed; only the original 12..32-face remainder remains. -/
theorem original_numerator_lower_with_short_remainder (K margin : Nat) (hK : 1 ≤ K) :
    tailAllowance * partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)) +
      shortOtherRemainder nome K 33 margin ≤
    connectedNumerator nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) := by
  have href : referenceFloor nome ≈ 2*tailAllowance :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (by decide : HalfPow.half ≈ 2*Q'.invSucc 3)) (Q'.mul_assoc_eqv _ _ _)
  exact absorb_tail (referenceFloor nome) tailAllowance
    (partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)))
    (otherCoreRemainder nome K margin) (shortOtherRemainder nome K 33 margin) (largeOtherRemainder nome K 33 margin)
    (connectedNumerator nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)))
    href (otherCoreRemainder_split nome K 33 margin) (largeOtherRemainder_size33_bound K margin)
    (original_numerator_lower_with_remainder K margin hK)

end YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate

#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate.blockCeiling
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate.inverse_eighth_le_block
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate.inverse_fortyeighth_le
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate.probe_prefactor_le_two
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate.entropy_le_dyadic
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate.entropy_reciprocal_le_two
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate.tailAllowance
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate.tailAllowance_pos
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate.tailCoefficient_le_dyadic
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate.size33_scalar_guard
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate.size33_tailCoefficient_le
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate.largeOtherRemainder_size33_bound
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCoreTailCertificate.original_numerator_lower_with_short_remainder
