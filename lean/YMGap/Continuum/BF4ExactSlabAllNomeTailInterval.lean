/-
# Arbitrary-nome high-spin tails in ORIGINAL Haar order

Sharp SU(2) character intervals turn the existing squared-dimension
majorant into an actual polynomial Interval on every physical face.
The computed high-spin cutoff and geometric-tail modulus depend on the
nome and tolerance, not the slab extent, face or later tail length.
The complete low-spin head is retained, with an explicit possibly large
prefix cap; it is not treated as a small perturbation of one.

This removes the small-nome guard for LOCAL cutoff tails. It does not
provide thermodynamic decay, a physical spacing schedule, or Clay closure.
-/

import YMGap.Continuum.QuaternionHaarSharpCharacterInterval
import YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
import YMGap.Continuum.SU2PointwiseHeatSpacingTailBound

namespace YMGap.Continuum.BF4ExactSlabAllNomeTailInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RGTransport
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (faceHeatPolynomial)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor (pointwiseHeatMajorant)
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
open YMGap.Continuum.SU2PointwiseHeatSpacingTailBound
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem heat_dimension_majorant (w : Q') (n : Nat) :
    coeffW w n * dimQ n ≈ pointwiseHeatMajorant w n := by
  have hs : dimQ n * dimQ n ≈ Q'.ofNat ((n+1)^2) := by
    simpa only [dimQ, Nat.pow_two] using (SU3CharFactor.ofNat_mul_eqv (n+1) (n+1))
  exact Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 0))
    (.mul (.mul (.var 0) (.var 0)) (.var 1)) (by decide)
    (fun | 0 => dimQ n | _ => qpow w (c4 n)))
    (Q'.mul_eqv_congr_right _ _ _ hs)

/-- No scalar pointwise-to-Haar inference: these are original square certificates. -/
def heatTermInterval {w : Q'} (hw : (0 : Q') ≤ w) (extent id : Nat)
    (hi : id ∈ slabPhysicalFaceEdges extent) (n : Nat) :
    Interval (boundaryCompleteSlabLinks extent).length (faceHeatTerm w extent id n)
      (pointwiseHeatMajorant w n) :=
  ((sharpCharacterInterval (.scalar (supported_slabPlaquette _ _)
    (haarNorm_slabPlaquette (slabPlaquetteAt_mem hi))) n).smul (coeffW w n) (coeffW_nonneg hw n))
    |>.changeCap (heat_dimension_majorant w n)

theorem shiftedMajorant_block {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (M L : Nat) :
    finSum (fun i => pointwiseHeatMajorant w (spacingLabelCutoff w + (M+i))) L ≤ spacingClosedTail w M :=
  Q'.le_trans' _ _ _
    (ExpNeg.finSum_le_finSum_of_termwise _ _ (fun i => shiftedMajorant_le_geometric hw0 hw1 (M+i)) L)
    (geoTailBase_series_le (spacingTailHead_nonnegative hw0) (spacingTailRatio_pos hw0)
      (spacingTailRatio_lt_one hw0 hw1) M L)

def shiftedFaceTailInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) (M L : Nat) :
    Interval (boundaryCompleteSlabLinks extent).length
      (faceHeatTail w extent id (spacingLabelCutoff w + M) L) (spacingClosedTail w M) :=
  (Interval.finiteRange (fun i => faceHeatTerm w extent id (spacingLabelCutoff w+M+i))
    (fun i => pointwiseHeatMajorant w (spacingLabelCutoff w+M+i))
    (fun i => heatTermInterval (Q'.le_of_lt hw0) extent id hi _) L).weaken
      (by simpa only [Nat.add_assoc] using shiftedMajorant_block hw0 hw1 M L)

theorem closedTail_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (M : Nat)
    (hM : spacingTailCauchyCutoff w epsilon ≤ M) : spacingClosedTail w M ≤ epsilon := by
  have hr0 := spacingTailRatio_pos hw0
  have hr1 := spacingTailRatio_lt_one hw0 hw1
  have hd : (0 : Q') < spacingTailRescale w epsilon ∧
      spacingTailScale w * spacingTailRescale w epsilon ≤ epsilon :=
    (spacingTailRescaleData hw0 epsilon he).2
  have hp := Q'.le_trans' _ _ _
    (pow_base_antitone (Q'.le_of_lt hr0) (Q'.le_of_lt hr1) hM)
    (pow_base_le_cutoff hr0 hr1 hd.1)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
    (fun | 0 => spacingTailHead w | 1 => spacingTailRatio w ^ M
         | _ => HKConv.divPos 1 (1 + -spacingTailRatio w))))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hp
      (Q'.le_of_lt (spacingTailScale_pos hw0))) hd.2)

/-- Same computed cutoff for every face and slab extent, at fixed nome/tolerance. -/
def tailCutoff (w epsilon : Q') : Nat := spacingLabelCutoff w + spacingTailCauchyCutoff w epsilon

def faceTailInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent)
    (epsilon : Q') (he : (0 : Q') < epsilon) (K L : Nat) (hK : tailCutoff w epsilon ≤ K) :
    Interval (boundaryCompleteSlabLinks extent).length (faceHeatTail w extent id (K+1) L) epsilon := by
  have hN : spacingLabelCutoff w ≤ K+1 := by unfold tailCutoff at hK; omega
  have hM : spacingTailCauchyCutoff w epsilon ≤ K+1-spacingLabelCutoff w := by
    unfold tailCutoff at hK
    omega
  have R := (shiftedFaceTailInterval hw0 hw1 extent id hi (K+1-spacingLabelCutoff w) L).weaken
    (closedTail_small hw0 hw1 epsilon he _ hM)
  simpa only [Nat.add_sub_of_le hN] using R

/-- Full original prefix cap: the finite head is kept, not assumed small. -/
def prefixCap (w : Q') : Q' :=
  finSum (pointwiseHeatMajorant w) (spacingLabelCutoff w) + spacingClosedTail w 0

theorem prefixCap_nonnegative {w : Q'} (hw0 : (0 : Q') < w) : (0 : Q') ≤ prefixCap w :=
  Q'.zero_le_add _ _
    (finSum_monotone_of_nonneg _ (fun n => tailTerm_nonneg (Q'.le_of_lt hw0) 2 n) 0 _ (Nat.zero_le _))
    (spacingClosedTail_nonnegative hw0 0)

theorem majorant_prefix_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) :
    finSum (pointwiseHeatMajorant w) K ≤ prefixCap w := by
  by_cases hK : K ≤ spacingLabelCutoff w
  · exact Q'.le_trans' _ _ _
      (finSum_monotone_of_nonneg _ (fun n => tailTerm_nonneg (Q'.le_of_lt hw0) 2 n) _ _ hK)
      (Q'.add_le_self_of_nonneg _ _ (spacingClosedTail_nonnegative hw0 0))
  · have he : spacingLabelCutoff w + (K-spacingLabelCutoff w) = K := Nat.add_sub_of_le (by omega)
    have hs := finSum_split (pointwiseHeatMajorant w) (spacingLabelCutoff w) (K-spacingLabelCutoff w)
    rw [he] at hs
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hs)
      (Q'.add_le_add_left _ _ _ (by
        simpa only [Nat.zero_add] using shiftedMajorant_block hw0 hw1 0 (K-spacingLabelCutoff w)))

def facePrefixInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) :
    Interval (boundaryCompleteSlabLinks extent).length (faceHeatPolynomial w K extent id) (prefixCap w) := by
  rw [faceHeatPolynomial_eq_sum]
  exact (Interval.finiteRange (faceHeatTerm w extent id) (pointwiseHeatMajorant w)
    (heatTermInterval (Q'.le_of_lt hw0) extent id hi) (K+1)).weaken (majorant_prefix_bound hw0 hw1 (K+1))

end YMGap.Continuum.BF4ExactSlabAllNomeTailInterval

#print axioms YMGap.Continuum.BF4ExactSlabAllNomeTailInterval.heat_dimension_majorant
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeTailInterval.heatTermInterval
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeTailInterval.shiftedMajorant_block
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeTailInterval.shiftedFaceTailInterval
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeTailInterval.closedTail_small
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeTailInterval.tailCutoff
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeTailInterval.faceTailInterval
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeTailInterval.prefixCap
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeTailInterval.prefixCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeTailInterval.majorant_prefix_bound
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeTailInterval.facePrefixInterval
