/-
# Paying the finite OWN-mean residue in the original filtered gain

The odd-window mean does not center the mixed/even window. Its discrepancy
is paid by the ORIGINAL right-boundary comparison with sharp fundamental
cap two. The result retains the SAME even partition and the factor 1-a:
  |(a-1)*c*ell(A*b)| <= 8*(1-a)*mixRate^n*evenPartition.
This closes the boundary correction needed by a finite heat covariance
estimate; it supplies no changing-family source-loss/reserve comparison.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredGainSourcePair
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowEndpointMean
import YMGap.Continuum.QuaternionHaarSharpCharacterInterval
import YMGap.Constructive.CRealAbs
import YMGap.Continuum.PositiveContractionResidual

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredMeanResidueBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (link orientedLink spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins (middleRatio_swap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowEndpointMean
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial (mean_pin mean_square_le_four)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung (ownMean)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
  (evenPartition evenPartition_positive evenPartition_middle_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain (centeredMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredGainSourcePair (centeredMeanPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadWindowContraction (windowMessage_iterate)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare (Supported)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval
open YMGap.Continuum.QuaternionHaarWordDifference (word_unit)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage sourceCharacter

private def fundamentalInterval (width blocks : Nat) (hblocks : N width ≤ blocks)
    (loop : SourceLoop width) :
    Interval blocks (sourceCharacter width loop.edges 1) 2 := by
  have hu (e : OrientedBF4Link) (he : e ∈ loop.edges) :
      HaarCarrierEqv blocks (polyQuaternionNorm (orientedLink width e)) polyOne := by
    have hmem := loop.physical e he
    have hi := List.idxOf_lt_length_of_mem hmem
    have h := haarNorm_coordinate (Nat.lt_of_lt_of_le hi hblocks)
    unfold orientedLink link
    rw [if_pos hmem]
    split
    · exact (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)).trans h
    · exact h
  let hp := sourceWord_supported width loop.edges
  unfold sourceCharacter
  exact Interval.changeCap (by decide : RGTransport.dimQ 1 ≈ (2 : Q'))
    (sharpCharacterInterval (SquareBound.scalar
      (show Supported blocks (sourceWord width loop.edges) from
        ⟨fun t ht => Nat.le_trans (hp.scalar t ht) (Nat.mul_le_mul_left 4 hblocks),
         fun t ht => Nat.le_trans (hp.iPart t ht) (Nat.mul_le_mul_left 4 hblocks),
         fun t ht => Nat.le_trans (hp.jPart t ht) (Nat.mul_le_mul_left 4 hblocks),
         fun t ht => Nat.le_trans (hp.kPart t ht) (Nat.mul_le_mul_left 4 hblocks)⟩)
      (word_unit (orientedLink width) loop.edges hu)) 1)

private theorem centeredMeanPair_window_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (f : RatPoly) (c : Q') :
    centeredMeanPair w K width n f c * Q'.recipPos (evenPartition w K width n)
      (evenPartition_positive hw0 hw1 K width hK n) ≈
        windowRatio hw0 hw1 K width hK n 1 (n+1) f - c := by
  let psi := shifted f c
  have ho : RatPolyCoeffEqv (observedMessage w K width n 1 psi)
      (centeredMessage w K width n f c) := by
    simpa only [observedMessage, Nat.one_mul, iterateStep] using
      (windowMessage_iterate (N width) (kineticWeight w K width) (spatialWeight w K width)
        1 (terminalMessage w K width n) psi)
  have hn : centeredMeanPair w K width n f c ≈
      weightedMass w K width (polyMul (observedMessage w K width n 1 psi)
        (terminalMessage w K width (n+1))) := by
    unfold centeredMeanPair
    rw [← terminalMessage_next w K width n]
    exact weightedMass_congr w K width
      ((RatPolyCoeffEqv.mul_comm _ _).trans (ho.symm.mul_right _))
  have hZ := evenPartition_middle_pin w K width n
  rw [terminalMessage_next w K width n] at hZ
  have hr : centeredMeanPair w K width n f c *
      Q'.recipPos (evenPartition w K width n) (evenPartition_positive hw0 hw1 K width hK n) ≈
      windowRatio hw0 hw1 K width hK n 1 (n+1) psi :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hn)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.recipPos_eqv_congr _ _
        (evenPartition_positive hw0 hw1 K width hK n)
        (terminalPair_positive hw0 hw1 K width hK (n+1) (n+1)) hZ))
  have hs : windowRatio hw0 hw1 K width hK n 1 (n+1) psi ≈
      1*windowRatio hw0 hw1 K width hK n 1 (n+1) f + (-c)*1 :=
    Q'.eqv_trans _ _ _ (windowRatio_add hw0 hw1 K width hK n 1 (n+1) _ _)
      (Q'.add_eqv_congr' (windowRatio_smul hw0 hw1 K width hK n 1 (n+1) 1 f)
        (Q'.eqv_trans _ _ _ (windowRatio_smul hw0 hw1 K width hK n 1 (n+1) (-c) polyOne)
          (Q'.mul_eqv_congr_left _ _ _ (windowRatio_one hw0 hw1 K width hK n 1 (n+1)))))
  exact Q'.eqv_trans _ _ _ hr (Q'.eqv_trans _ _ _ hs
    (poly_identity_of_normal_eq (.add (.mul (.const 1) (.var 0))
      (.mul (.neg (.var 1)) (.const 1))) (.add (.var 0) (.neg (.var 1)))
      (by decide) (fun | 0 => windowRatio hw0 hw1 K width hK n 1 (n+1) f | _ => c)))

/-- The original odd center's actual mixed/even discrepancy. No partition
identification or finite stationarity is assumed. -/
theorem own_centeredMeanPair_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width) :
    Q'.abs (centeredMeanPair w K width n (sourceCharacter width loop.edges 1)
      (ownMean hw0 hw1 K width hK n loop)) ≤
        4*mixRate hw0 hw1 width^n*evenPartition w K width n := by
  let f := sourceCharacter width loop.edges 1
  let c := ownMean hw0 hw1 K width hK n loop
  let M := centeredMeanPair w K width n f c
  let E := evenPartition w K width n
  let e := mixRate hw0 hw1 width^n*4
  have hf := sourceCharacter_supported width loop.edges 1
  have hm : windowRatio hw0 hw1 K width hK n 1 n f ≈ c :=
    Q'.eqv_trans _ _ _ (lower_endpoint_mean hw0 hw1 K width hK n hf)
      (Q'.eqv_trans _ _ _ (middleRatio_swap hw0 hw1 K width hK n (n+1) f)
        (Q'.eqv_symm (mean_pin hw0 hw1 K width hK n hf)))
  let I : Interval ((1+1)*(N width)) f 2 :=
    fundamentalInterval width ((1+1)*(N width)) (by omega) loop
  have hb := windowRatio_right_commonTail hw0 hw1 K width hK n 1 n (n+1) n I
    (by omega) (Nat.le_refl n)
  have hup : windowRatio hw0 hw1 K width hK n 1 (n+1) f ≤ c+e :=
    Q'.le_trans' _ _ _ hb.1 (Q'.le_of_eqv
      (Q'.add_eqv_congr' hm (Q'.mul_eqv_congr_left _ _ _ (by decide : (2 : Q')+2 ≈ 4))))
  have hlo : c ≤ windowRatio hw0 hw1 K width hK n 1 (n+1) f+e :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hm) (Q'.le_trans' _ _ _ hb.2
      (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (by decide : (2 : Q')+2 ≈ 4)))))
  have hneg : -e ≤ windowRatio hw0 hw1 K width hK n 1 (n+1) f-c := by
    have h := Q'.neg_le_neg (Q'.sub_le_of_le_add hlo)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.neg (.add (.var 0) (.neg (.var 1)))) (.add (.var 1) (.neg (.var 0)))
      (by decide) (fun | 0 => c | _ => windowRatio hw0 hw1 K width hK n 1 (n+1) f)))
  have hdiff := Q'.abs_le_of_bounds hneg (Q'.sub_le_of_le_add hup)
  have hp := centeredMeanPair_window_pin hw0 hw1 K width hK n f c
  have hnorm : Q'.abs (M*Q'.recipPos E (evenPartition_positive hw0 hw1 K width hK n)) ≤ e :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hp)) hdiff
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ E hnorm
    (Q'.le_of_lt (evenPartition_positive hw0 hw1 K width hK n))
  have hc : (M*Q'.recipPos E (evenPartition_positive hw0 hw1 K width hK n))*E ≈ M :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left M _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv E _)))
        (Q'.mul_one_eqv M))
  have hab : Q'.abs (M*Q'.recipPos E (evenPartition_positive hw0 hw1 K width hK n))*E ≈ Q'.abs M :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (TsumDeriv.abs_mul_nonneg_right
      (M*Q'.recipPos E (evenPartition_positive hw0 hw1 K width hK n))
      (Q'.le_of_lt (evenPartition_positive hw0 hw1 K width hK n))))
      (Q'.abs_eqv_congr hc)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hab) (Q'.le_trans' _ _ _ hs
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.const 4)) (.var 1))
      (.mul (.mul (.const 4) (.var 0)) (.var 1)) (by decide)
      (fun | 0 => mixRate hw0 hw1 width^n | _ => E))))

/-- Pay the literal moving-mean residue, including its heat-reference loss.
The coefficient is cutoff/loop independent; its mixing rate still depends
on nome and spatial width. -/
theorem own_meanResidue_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width)
    (a : Q') (ha : a ≤ (1 : Q')) :
    let c := ownMean hw0 hw1 K width hK n loop
    Q'.abs ((a-1)*c*centeredMeanPair w K width n (sourceCharacter width loop.edges 1) c) ≤
      8*(1-a)*mixRate hw0 hw1 width^n*evenPartition w K width n := by
  let c := ownMean hw0 hw1 K width hK n loop
  let M := centeredMeanPair w K width n (sourceCharacter width loop.edges 1) c
  let r := mixRate hw0 hw1 width^n
  let E := evenPartition w K width n
  have hc : Q'.abs c ≤ (2 : Q') := Q'.abs_le_of_sq_le_sq (by decide)
    (mean_square_le_four hw0 hw1 K width hK n loop)
  have hM := own_centeredMeanPair_bound hw0 hw1 K width hK n loop
  have hprod : Q'.abs ((a-1)*c*M) ≤ (Q'.abs (a-1)*Q'.abs c)*Q'.abs M :=
    Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
      (Q'.mul_le_mul_of_nonneg_right _ _ (Q'.abs M) (ExpNeg.abs_mul_le _ _) (Q'.abs_nonneg M))
  have hg : Q'.abs (a-1) ≈ 1-a :=
    Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr (poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.const 1))) (.neg (.add (.const 1) (.neg (.var 0))))
      (by decide) (fun _ => a)))
      (Q'.eqv_trans _ _ _ (Q'.abs_neg' (1-a))
        (Q'.eqv_of_eq (ExpNeg.abs_of_nonneg (Q'.sub_nonneg_of_le ha))))
  have hcoef : Q'.abs (a-1)*Q'.abs c ≤ (1-a)*2 :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.abs (a-1)) hc (Q'.abs_nonneg _))
      (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ hg))
  have hb := Q'.le_trans' _ _ _ hprod
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ (Q'.abs M) hcoef (Q'.abs_nonneg M))
      (Q'.mul_le_mul_of_nonneg_left _ _ ((1-a)*2) hM
        (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le ha) (by decide))))
  exact Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.mul (.mul (.add (.const 1) (.neg (.var 0))) (.const 2))
      (.mul (.mul (.const 4) (.var 1)) (.var 2)))
    (.mul (.mul (.mul (.const 8) (.add (.const 1) (.neg (.var 0)))) (.var 1)) (.var 2))
    (by decide) (fun | 0 => a | 1 => r | _ => E)))

/-- An explicit original-transfer depth onset, independent of heat cutoff
and loop size, but NOT nome or width. -/
def meanResidueDepthCutoff {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (epsilon : Q') : Nat :=
  geometricCutoff (mixRate hw0 hw1 width) 8 epsilon

/-- The constructed onset pays the boundary error without any division by
variance or comparison of odd/even laws. -/
theorem own_meanResidue_tolerance_bound {w epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (he : (0 : Q') < epsilon)
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width)
    (a : Q') (ha : a ≤ (1 : Q'))
    (hn : meanResidueDepthCutoff hw0 hw1 width epsilon ≤ n) :
    let c := ownMean hw0 hw1 K width hK n loop
    Q'.abs ((a-1)*c*centeredMeanPair w K width n (sourceCharacter width loop.edges 1) c) ≤
      (1-a)*epsilon*evenPartition w K width n := by
  have h := geometric_bound (mixRate_nonnegative hw0 hw1 width)
    (mixRate_lt_one hw0 hw1 width) (by decide : (0 : Q') ≤ 8) he n hn
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ (evenPartition w K width n)
    (Q'.mul_le_mul_of_nonneg_left _ _ (1-a) h (Q'.sub_nonneg_of_le ha))
    (Q'.le_of_lt (evenPartition_positive hw0 hw1 K width hK n))
  have hp : 8*(1-a)*mixRate hw0 hw1 width^n*evenPartition w K width n ≈
      (1-a)*(mixRate hw0 hw1 width^n*8)*evenPartition w K width n :=
    poly_identity_of_normal_eq (.mul (.mul (.mul (.const 8) (.var 0)) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.mul (.var 1) (.const 8))) (.var 2)) (by decide)
      (fun | 0 => 1-a | 1 => mixRate hw0 hw1 width^n | _ => evenPartition w K width n)
  exact Q'.le_trans' _ _ _ (own_meanResidue_bound hw0 hw1 K width hK n loop a ha)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) hs)

end YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredMeanResidueBound

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredMeanResidueBound.own_centeredMeanPair_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredMeanResidueBound.own_meanResidue_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredMeanResidueBound.meanResidueDepthCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredMeanResidueBound.own_meanResidue_tolerance_bound
