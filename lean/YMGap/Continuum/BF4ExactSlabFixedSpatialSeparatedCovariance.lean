/-
# Connected correlation decay between two actual finite windows

Contract the left window, cross g unobserved transitions of the ORIGINAL
transfer, and test its shrinking comparison bracket against the right
window. The common unobserved partition cancels exactly. Signed insertions
and zero residual mass are allowed; no observed mass is inverted.

The explicit envelope is 4*cp*cq*mixRate^g. It is independent of boundary
lengths and late heat cutoff, but depends on nome, spatial width and probe
caps. Here g is insertion separation, not receding boundary distance.
This is not a reflected-norm strict bound, a continuum-uniform rate, or a
physical Hamiltonian gap. Passing to physical time correlators still needs
the literal reflected-probe placement and limit consumers.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialInputCovariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedWindowPins
import YMGap.Continuum.RationalCommonPartitionCovariance

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder (iterateStep_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary
open YMGap.Continuum.BF4ExactSlabFixedSpatialInputCovariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedWindowPins
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] baseLinks kineticWeight spatialWeight inputNumerator inputPartition

/-- The actual propagated left insertion obeys a separation estimate under
the one unobserved partition, with both probe caps retained explicitly. -/
theorem separated_input_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L g R n : Nat)
    {p q : RatPoly} {cp cq : Q'}
    (P : Interval ((L+1)*(N width)) p cp) (Q : Interval ((R+1)*(N width)) q cq)
    (hZ : (0 : Q') < inputPartition w K width R n (terminalMessage w K width (m+L+g))) :
    let r := Q'.recipPos _ hZ
    Q'.abs (inputNumerator w K width R n (separatedMessage w K width m L g p) q * r +
      -((inputPartition w K width R n (separatedMessage w K width m L g p) * r) *
        (inputNumerator w K width R n (terminalMessage w K width (m+L+g)) q * r))) ≤
      (cq+cq)*(mixRate hw0 hw1 width ^ g * (cp+cp)) := by
  let f := iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) g
    (observedMessage w K width m L p)
  let u := iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) g
    (terminalMessage w K width (m+L))
  have hu : u = terminalMessage w K width (m+L+g) := by
    unfold u terminalMessage
    rw [← iterateStep_add]
  have hf := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) g (observedMessage_supported w K width m L P.support)
  have hus := iterateStep_supported (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) g (terminalMessage_supported w K width (m+L))
  have U := iterateStep_certificate hw0 hw1 K width hK g _
    (terminalMessage_supported w K width (m+L))
    (terminalMessage_certificate hw0 hw1 K width hK (m+L))
  have hb := inputCovariance_bracket_bound hw0 hw1 K width hK R n hf hus U Q
    (windowBracket hw0 hw1 K width hK m L g P)
  have he := Q'.mul_eqv_congr_right _ _
    (inputPartition w K width R n u * inputPartition w K width R n u)
    (Q'.mul_eqv_congr_left (cq+cq) _ _
      (windowBracket_width hw0 hw1 K width hK m L g P))
  have hraw := Q'.le_trans' _ _ _ hb (Q'.le_of_eqv he)
  change Q'.abs (inputNumerator w K width R n f q * inputPartition w K width R n u +
      -(inputPartition w K width R n f * inputNumerator w K width R n u q)) ≤
    ((cq+cq)*(mixRate hw0 hw1 width ^ g * (cp+cp))) *
      (inputPartition w K width R n u * inputPartition w K width R n u) at hraw
  rw [hu] at hraw
  exact RationalCommonPartitionCovariance.covariance_bound _ _ _ _ _ hZ hraw

/-- Separation decay of the actual connected finite expectation. All three
ratios have identical left/right boundaries, total length, action and
partition. The only strict positivity used is the proved unobserved mass. -/
theorem windowRatio_covariance_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L g R n : Nat)
    {p q : RatPoly} {cp cq : Q'}
    (P : Interval ((L+1)*(N width)) p cp) (Q : Interval ((R+1)*(N width)) q cq) :
    Q'.abs (windowRatio hw0 hw1 K width hK m (L+g+R) n
        (polyMul p (liftBoundary ((L+g)*(N width)) q)) +
      -(windowRatio hw0 hw1 K width hK m (L+g+R) n p *
        windowRatio hw0 hw1 K width hK m (L+g+R) n
          (liftBoundary ((L+g)*(N width)) q))) ≤
      (cq+cq)*(mixRate hw0 hw1 width ^ g * (cp+cp)) := by
  have hZ := inputPartition_terminal_positive hw0 hw1 K width hK R n (m+L+g)
  have hj := windowRatio_separated_joint hw0 hw1 K width hK m L g R n p q hZ
  have hl := windowRatio_separated_left hw0 hw1 K width hK m L g R n p hZ
  have hr := windowRatio_separated_right hw0 hw1 K width hK m L g R n q hZ
  have hm := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hl)
    (Q'.mul_eqv_congr_left _ _ _ hr)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.add_eqv_congr' hj (Q'.neg_eqv_congr _ _ hm))))
    (separated_input_bound hw0 hw1 K width hK m L g R n P Q hZ)

/-- Every supported pair receives the separation bound with its computed
polynomial caps. No supplied interval, covariance estimate or gap is needed. -/
theorem polynomialWindow_covariance_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L g R n : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks ((L+1)*(N width)) p)
    (hq : SupportedQuaternionBlocks ((R+1)*(N width)) q) :
    Q'.abs (windowRatio hw0 hw1 K width hK m (L+g+R) n
        (polyMul p (liftBoundary ((L+g)*(N width)) q)) +
      -(windowRatio hw0 hw1 K width hK m (L+g+R) n p *
        windowRatio hw0 hw1 K width hK m (L+g+R) n
          (liftBoundary ((L+g)*(N width)) q))) ≤
      (polynomialCap q+polynomialCap q) *
        (mixRate hw0 hw1 width ^ g * (polynomialCap p+polynomialCap p)) :=
  windowRatio_covariance_bound hw0 hw1 K width hK m L g R n
    (polynomialInterval ((L+1)*(N width)) p hp)
    (polynomialInterval ((R+1)*(N width)) q hq)

end YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedCovariance

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedCovariance.separated_input_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedCovariance.windowRatio_covariance_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedCovariance.polynomialWindow_covariance_bound
