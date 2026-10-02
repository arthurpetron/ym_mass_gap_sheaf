/-
# Pay the original mixed-depth first chord moment

The entire unit-word chord has certified cap four. A right common-tail
comparison transports the original matched-word quadratic budget to the
mixed window (n,1,n+1), with error 8*mixRate^n and its SAME even partition.
The kinetic onset and K>=1 are explicit; they are not inferred from the
quartic onset. The complete OWN-centered Young consumer retains U, Y and D.
No useful relative physical scaling or survival estimate is asserted.
-/

import YMGap.Continuum.QuaternionHaarChordalInterval
import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanQuartic

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialMixedDepthChordalInsertion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (orientedLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (sourcePolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement (upperOriented)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLinkQuartic
  (lower_supported upper_supported lower_unit upper_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement (wordChordal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial
  (edgeMoment mean_square_le_four)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanQuartic
  (wordQuadraticRate word_quadratic_nome_normalized)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (edgeDensity)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredRadialDrift
  (mixedDensity mixedDensity_window_pairing terminalEdge_probe_pairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredQuarticCeiling (mixedWordQuarticRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMixedDepthQuarticInsertion (mixedQuarticDepthCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4WilsonAllNomeFilteredIncrement (filteredExpression)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.SU2HeatJacobiOriginalHaarQuarticCutoff (quarticCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarWordDifference (word_supported word_unit)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarChordalInterval (chord_interval)
open YMGap.Continuum.PositiveContractionResidual (geometric_bound)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks
attribute [local irreducible] baseLinks terminalMessage oddMass weightedMass mixRate windowRatio

/-- Constructed interval for the literal whole word, not a length-dependent cap. -/
def wordChordal_interval (width : Nat) (loop : SourceLoop width) :
    Interval (N width+N width) (wordChordal width loop) 4 :=
  chord_interval
    (word_supported (orientedLink width) loop.edges
      (fun e he => lower_supported (loop.physical e he)))
    (word_supported (upperOriented width) loop.edges
      (fun e he => upper_supported (loop.physical e he)))
    (word_unit (orientedLink width) loop.edges
      (fun e he => lower_unit (loop.physical e he)))
    (word_unit (upperOriented width) loop.edges
      (fun e he => upper_unit (loop.physical e he)))

private theorem matched_window_pin {w : Q'} (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (K width : Nat) (hK : headCutoff w≤K) (n : Nat) (loop : SourceLoop width) :
    windowRatio hw0 hw1 K width hK n 1 n (wordChordal width loop) ≈
      edgeMoment hw0 hw1 K width hK n (wordChordal width loop) := by
  have hp := terminalEdge_probe_pairing w K width n n (wordChordal_interval width loop).support
  unfold windowRatio massRatio edgeMoment oddMass
  exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hp)

private theorem matched_nome_bound {w : Q'} (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (K width : Nat) (hK : headCutoff w≤K) (hK1 : 1≤K)
    (hkin : sufficientCutoff w≤K) (n : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e∈loop.edges → (baseLinks width).idxOf e.link∈activeBlocks width) :
    windowRatio hw0 hw1 K width hK n 1 n (wordChordal width loop)≤wordQuadraticRate w loop := by
  have he : K-1+1=K := by omega
  have h := word_quadratic_nome_normalized hw0 hw1 (K-1) width n
    (by omega : sufficientCutoff w≤K-1+1) (by omega : headCutoff w≤K-1+1) loop hactive
  have h' : edgeMoment hw0 hw1 K width hK n (wordChordal width loop) ≤
      wordQuadraticRate w loop := by
    simpa only [he] using h
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (matched_window_pin hw0 hw1 K width hK n loop)) h'

private theorem clear_bound (M Z b : Q') (hz : (0 : Q')<Z)
    (h : M*Q'.recipPos Z hz≤b) : M≤b*Z := by
  have hb := Q'.mul_le_mul_of_nonneg_right _ _ Z h (Q'.le_of_lt hz)
  have hc : (M*Q'.recipPos Z hz)*Z ≈ M :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv Z hz)))
        (Q'.mul_one_eqv M))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hc) hb

/-- The original mixed first chord moment, with explicit transfer-tail error. -/
theorem mixedChordMoment_nome_bound {w : Q'} (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (K width : Nat) (hK : headCutoff w≤K) (hK1 : 1≤K)
    (hkin : sufficientCutoff w≤K) (n : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e∈loop.edges → (baseLinks width).idxOf e.link∈activeBlocks width) :
    mixedChordMoment w K width n loop≤
      (wordQuadraticRate w loop+mixRate hw0 hw1 width^n*8)*evenPartition w K width n := by
  let I := wordChordal_interval width loop
  have hb := (windowRatio_right_commonTail hw0 hw1 K width hK n 1 n (n+1) n
    (by simpa only [Nat.one_add, Nat.two_mul] using I) (by omega) (Nat.le_refl n)).1
  have hm := matched_nome_bound hw0 hw1 K width hK hK1 hkin n loop hactive
  have hs : windowRatio hw0 hw1 K width hK n 1 (n+1) (wordChordal width loop)≤
      wordQuadraticRate w loop+mixRate hw0 hw1 width^n*8 :=
    Q'.le_trans' _ _ _ hb (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hm)
      (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (by decide : (4 : Q')+4 ≈ 8)))))
  let Z := weightedMass w K width (polyMul (terminalMessage w K width (n+1))
    (terminalMessage w K width (n+1)))
  let M := weightedMass w K width (polyMul (observedMessage w K width n 1 (wordChordal width loop))
    (terminalMessage w K width (n+1)))
  let hz := terminalPair_positive hw0 hw1 K width hK (n+1) (n+1)
  have hh : M*Q'.recipPos Z hz≤wordQuadraticRate w loop+mixRate hw0 hw1 width^n*8 := by
    simpa only [windowRatio, massRatio] using hs
  have hZ : Z ≈ evenPartition w K width n := by
    have h := evenPartition_middle_pin w K width n
    rw [terminalMessage_next w K width n] at h
    exact Q'.eqv_symm h
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (mixedDensity_window_pairing w K width n I.support))
    (Q'.le_trans' _ _ _ (clear_bound M Z _ hz hh)
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hZ)))

/-- The SAME quartic depth cutoff also pays the smaller cap-four tail error. -/
theorem mixedChordMoment_nome_tolerance_bound {w epsilon : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q')) (he : (0 : Q')<epsilon)
    (K width : Nat) (hK : headCutoff w≤K) (hK1 : 1≤K)
    (hkin : sufficientCutoff w≤K) (n : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e∈loop.edges → (baseLinks width).idxOf e.link∈activeBlocks width)
    (hn : mixedQuarticDepthCutoff hw0 hw1 width epsilon≤n) :
    mixedChordMoment w K width n loop≤
      (wordQuadraticRate w loop+epsilon)*evenPartition w K width n := by
  have hs := geometric_bound (mixRate_nonnegative hw0 hw1 width)
    (mixRate_lt_one hw0 hw1 width) (by decide : (0 : Q')≤32) he n hn
  have hsmall : mixRate hw0 hw1 width^n*8≤epsilon :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
      (by decide : (8 : Q')≤32) (Q'.pow_nonneg _ (mixRate_nonnegative hw0 hw1 width) n)) hs
  exact Q'.le_trans' _ _ _ (mixedChordMoment_nome_bound hw0 hw1 K width hK hK1 hkin n loop hactive)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.add_le_add_left (wordQuadraticRate w loop) _ _ hsmall)
      (Q'.le_of_lt (evenPartition_positive hw0 hw1 K width hK n)))

/-- Complete original filtered-source ceiling with both chord moments paid.
The SAME finite OWN variance and all three favorable corrections remain;
the explicit coefficients are not claimed to furnish physical survival. -/
theorem filtered_loop_own_young_fully_paid {w epsilon : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (hw : Q'.mkPos 16 17 (by decide)≤w) (he : (0 : Q')<epsilon)
    (K width : Nat) (hK : headCutoff w≤K) (hK1 : 1≤K) (hkin : sufficientCutoff w≤K)
    (n : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e∈loop.edges → (baseLinks width).idxOf e.link∈activeBlocks width)
    (hcut : quarticCutoff w epsilon≤K)
    (hn : mixedQuarticDepthCutoff hw0 hw1 width epsilon≤n) (t : Q') (ht : (0 : Q')≤t) :
    let c := ownMean hw0 hw1 K width hK n loop
    ((t*numerator w K width n (sourcePolynomial (filteredExpression (.loop 0 loop 1)))+
      2*(t*mixedRadialCenteredMoment hw0 hw1 K width hK n loop))+
      2*mixedYoungSquareMoment hw0 hw1 K width hK n loop t)+
      2*(t*driftSquare w K width n (sourceCharacter width loop.edges 1))≤
    2*(evenPartition w K width n*
      ((t*t)*(oddVariance hw0 hw1 K width hK n (sourceCharacter width loop.edges 1)+epsilon)+
        (t+c*c)*mixedWordQuarticRate w epsilon loop+
        (t*(4-c*c))*(wordQuadraticRate w loop+epsilon))) := by
  let c := ownMean hw0 hw1 K width hK n loop
  let Z := evenPartition w K width n
  let v := oddVariance hw0 hw1 K width hK n (sourceCharacter width loop.edges 1)
  let b := mixedWordQuarticRate w epsilon loop
  let l := wordQuadraticRate w loop+epsilon
  have hgap : (0 : Q')≤t*(4-c*c) :=
    Q'.mul_nonneg _ _ ht (Q'.sub_nonneg_of_le (mean_square_le_four hw0 hw1 K width hK n loop))
  have hl := Q'.mul_le_mul_of_nonneg_left _ _ (t*(4-c*c))
    (mixedChordMoment_nome_tolerance_bound hw0 hw1 he K width hK hK1 hkin n loop hactive hn) hgap
  have hb := Q'.mul_le_mul_of_nonneg_left _ _ 2
    (Q'.add_le_add_left (Z*((t*t)*(v+epsilon)+(t+c*c)*b)) _ _ hl) (by decide)
  have hc : 2*(Z*((t*t)*(v+epsilon)+(t+c*c)*b)+(t*(4-c*c))*(l*Z)) ≈
      2*(Z*((t*t)*(v+epsilon)+(t+c*c)*b+(t*(4-c*c))*l)) :=
    poly_identity_of_normal_eq
      (.mul (.const 2) (.add (.mul (.var 0) (.var 1))
        (.mul (.var 2) (.mul (.var 3) (.var 0)))))
      (.mul (.const 2) (.mul (.var 0) (.add (.var 1) (.mul (.var 2) (.var 3)))))
      (by decide) (fun
        | 0 => Z
        | 1 => (t*t)*(v+epsilon)+(t+c*c)*b
        | 2 => t*(4-c*c)
        | _ => l)
  exact Q'.le_trans' _ _ _ (filtered_loop_own_young_paid hw0 hw1 hw he K width hK n loop
    hactive hcut hn t ht) (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv hc))

#print axioms wordChordal_interval
#print axioms mixedChordMoment_nome_bound
#print axioms mixedChordMoment_nome_tolerance_bound
#print axioms filtered_loop_own_young_fully_paid

end YMGap.Continuum.BF4ExactSlabFixedSpatialMixedDepthChordalInsertion
