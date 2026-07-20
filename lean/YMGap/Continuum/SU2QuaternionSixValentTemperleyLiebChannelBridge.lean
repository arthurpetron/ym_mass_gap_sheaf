/-
# Temperley--Lieb channel diagonalization of the six-valent SU(2) projector

The five independent permutation pairings of
`SU2QuaternionSixValentPairingGram` are now identified with an orthogonal
channel basis inside the genuine faithful `TL3` algebra:

    p3, A, B, X, Y,

with Gram weights

    4, 2, 2, 3/2, 3/2.

Consequently the inverse pairing Gram matrix has the positive resolution

    G^-1 = C^T diag(1/4,1/2,1/2,2/3,2/3) C.

This is an exact rational statement.  It retains the signed permutation-basis
entries while exposing five positive rank-one channel weights.  The complete
left/right recoupling matrix is also certified as an involution preserving
the diagonal Gram; its `X/Y` interference terms are therefore explicit and
cannot be silently discarded.

Only five-element sums and `5 x 5` closed tables are reduced.  No six- or
twelve-Bool tensor sum is unfolded, evaluated, or printed.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjector
import YMGap.Continuum.JWTowerInduction

namespace YMGap.Continuum.SU2QuaternionSixValentTemperleyLiebChannelBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.JWTowerInduction
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector
open YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjector
open YMGap.Continuum.SU2QuaternionSixValentPairingGram

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast,
               Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## 1. Five orthogonal channels in the genuine `TL3` algebra -/

def channelOneHalf : Q' := Q'.mkPos 1 2 (by decide)
def channelThreeHalves : Q' := Q'.mkPos 3 2 (by decide)
def channelTwoThirds : Q' := Q'.mkPos 2 3 (by decide)
def channelThreeEighths : Q' := Q'.mkPos 3 8 (by decide)

/-- Frozen channel order. -/
inductive SixValentTLChannel where
  | spinThreeHalves
  | leftA
  | leftB
  | leftX
  | leftY
  deriving DecidableEq

/-- Five-term channel sum in the frozen order. -/
def sixValentTLChannelSum
    (family : SixValentTLChannel → Q') : Q' :=
  (((family .spinThreeHalves + family .leftA) + family .leftB) +
      family .leftX) + family .leftY

def sixValentTLChannelDelta
    (left right : SixValentTLChannel) : Q' :=
  if left = right then 1 else 0

/-- Closed value of the genuine Wenzl projector `p3`. -/
def tl3TopClosed : TL3 :=
  ⟨1, Q'.mkPos (-2) 3 (by decide), Q'.mkPos (-2) 3 (by decide),
    oneThird, oneThird⟩

/-- `A=e1/2`. -/
def tl3ChannelA : TL3 := ⟨0, channelOneHalf, 0, 0, 0⟩

/-- `A'=e2/2`, used to construct both left and right channel families. -/
def tl3ChannelAPrime : TL3 := ⟨0, 0, channelOneHalf, 0, 0⟩

/-- `B=1-p3-A`. -/
def tl3ChannelB : TL3 :=
  ⟨0, oneSixth, channelTwoThirds, -oneThird, -oneThird⟩

/-- `X=2 A A' B=-e1/4+u/2`. -/
def tl3ChannelX : TL3 :=
  ⟨0, -oneQuarter, 0, channelOneHalf, 0⟩

/-- `Y=2 B A' A=-e1/4+v/2`. -/
def tl3ChannelY : TL3 :=
  ⟨0, -oneQuarter, 0, 0, channelOneHalf⟩

/-- The orthogonal left-channel family as concrete `TL3` elements. -/
def sixValentTLChannelElement : SixValentTLChannel → TL3
  | .spinThreeHalves => tl3TopClosed
  | .leftA => tl3ChannelA
  | .leftB => tl3ChannelB
  | .leftX => tl3ChannelX
  | .leftY => tl3ChannelY

/-- The closed top channel is the actual Wenzl-recursive `p3`. -/
theorem p3_eqv_tl3TopClosed : tl3eqv p3 tl3TopClosed := by
  unfold tl3TopClosed
  exact p3_value

theorem tl3ChannelA_constructed :
    tl3eqv tl3ChannelA (tl3smul channelOneHalf tl3e1) := by
  decide

theorem tl3ChannelB_constructed :
    tl3eqv tl3ChannelB
      (tl3sub (tl3sub tl3id p3) tl3ChannelA) := by
  decide

theorem tl3ChannelX_constructed :
    tl3eqv tl3ChannelX
      (tl3smul 2
        (tl3mul (tl3mul tl3ChannelA tl3ChannelAPrime) tl3ChannelB)) := by
  decide

theorem tl3ChannelY_constructed :
    tl3eqv tl3ChannelY
      (tl3smul 2
        (tl3mul (tl3mul tl3ChannelB tl3ChannelAPrime) tl3ChannelA)) := by
  decide

/-- Diagram reflection fixes `1,e1,e2` and exchanges `u=e1e2` with
`v=e2e1`. -/
def tl3Star (value : TL3) : TL3 :=
  ⟨value.c1, value.ce1, value.ce2, value.cv, value.cu⟩

/-- Positive Markov pairing `tr(x* y)`. -/
def tl3Inner (left right : TL3) : Q' :=
  mtr3 (tl3mul (tl3Star left) right)

def sixValentTLChannelNorm : SixValentTLChannel → Q'
  | .spinThreeHalves => 4
  | .leftA => 2
  | .leftB => 2
  | .leftX => channelThreeHalves
  | .leftY => channelThreeHalves

def sixValentTLChannelGram
    (left right : SixValentTLChannel) : Q' :=
  if left = right then sixValentTLChannelNorm left else 0

/-- The genuine `TL3` Markov pairing is diagonal on `p3,A,B,X,Y`. -/
theorem tl3Channel_gram_exact
    (left right : SixValentTLChannel) :
    tl3Inner (sixValentTLChannelElement left)
        (sixValentTLChannelElement right) ≈
      sixValentTLChannelGram left right := by
  cases left <;> cases right <;>
    unfold tl3Inner tl3Star sixValentTLChannelElement
      sixValentTLChannelGram sixValentTLChannelNorm tl3TopClosed
      tl3ChannelA tl3ChannelB tl3ChannelX tl3ChannelY
      mtr3 tl3mul channelOneHalf channelThreeHalves <;>
    decide

/-! ## 2. Exact map from `TL3` diagrams to permutation pairings -/

/-- Coefficients of a `TL3` element in the retained permutation-pairing
basis.  The generator images are

`e1=P0-P1`, `e2=P0-P2`, `u=P0-P1-P2+P4`,
and `v=P0-P1-P2+P3`. -/
def tl3PairingCoefficient
    (value : TL3) : SixValentPairing → Q'
  | .identity =>
      (((value.c1 + value.ce1) + value.ce2) + value.cu) + value.cv
  | .swapFirstTwo => ((-value.ce1) + (-value.cu)) + (-value.cv)
  | .swapLastTwo => ((-value.ce2) + (-value.cu)) + (-value.cv)
  | .cycleForward => value.cv
  | .cycleBackward => value.cu

/-- Frozen coefficient matrix `C` from orthogonal TL channels to retained
pairings. -/
def sixValentTLChannelCoefficient :
    SixValentTLChannel → SixValentPairing → Q'
  | .spinThreeHalves, .identity => oneThird
  | .spinThreeHalves, .swapFirstTwo => 0
  | .spinThreeHalves, .swapLastTwo => 0
  | .spinThreeHalves, .cycleForward => oneThird
  | .spinThreeHalves, .cycleBackward => oneThird
  | .leftA, .identity => channelOneHalf
  | .leftA, .swapFirstTwo => -channelOneHalf
  | .leftA, .swapLastTwo => 0
  | .leftA, .cycleForward => 0
  | .leftA, .cycleBackward => 0
  | .leftB, .identity => oneSixth
  | .leftB, .swapFirstTwo => channelOneHalf
  | .leftB, .swapLastTwo => 0
  | .leftB, .cycleForward => -oneThird
  | .leftB, .cycleBackward => -oneThird
  | .leftX, .identity => oneQuarter
  | .leftX, .swapFirstTwo => -oneQuarter
  | .leftX, .swapLastTwo => -channelOneHalf
  | .leftX, .cycleForward => 0
  | .leftX, .cycleBackward => channelOneHalf
  | .leftY, .identity => oneQuarter
  | .leftY, .swapFirstTwo => -oneQuarter
  | .leftY, .swapLastTwo => -channelOneHalf
  | .leftY, .cycleForward => channelOneHalf
  | .leftY, .cycleBackward => 0

/-- The frozen coefficient matrix is the actual diagram-to-pairing map of the
five genuine `TL3` channel elements. -/
theorem sixValentTLChannelCoefficient_from_tl3
    (channel : SixValentTLChannel) (pairing : SixValentPairing) :
    tl3PairingCoefficient (sixValentTLChannelElement channel) pairing ≈
      sixValentTLChannelCoefficient channel pairing := by
  cases channel <;> cases pairing <;>
    unfold tl3PairingCoefficient sixValentTLChannelElement
      sixValentTLChannelCoefficient tl3TopClosed tl3ChannelA tl3ChannelB
      tl3ChannelX tl3ChannelY channelOneHalf channelTwoThirds
      oneQuarter oneThird oneSixth <;>
    decide

/-- The channel pairing tensor represented in the original five-pairing
basis. -/
def sixValentTLChannelOrientedPairing
    (channel : SixValentTLChannel)
    (first second third firstConjugate secondConjugate thirdConjugate : Bool) :
    Q' :=
  sixValentPairingSum (fun pairing =>
    sixValentTLChannelCoefficient channel pairing *
      tripleOrientedPairing pairing first second third
        firstConjugate secondConjugate thirdConjugate)

/-- Pull the pairing Gram matrix back along `C`. -/
def sixValentTLChannelPulledBackGram
    (left right : SixValentTLChannel) : Q' :=
  sixValentPairingSum (fun leftPairing =>
    sixValentPairingSum (fun rightPairing =>
      sixValentTLChannelCoefficient left leftPairing *
        (sixValentPairingGram leftPairing rightPairing *
          sixValentTLChannelCoefficient right rightPairing)))

/-- `C G C^T = diag(4,2,2,3/2,3/2)`, independently matching the genuine
`TL3` Markov pairing above. -/
theorem sixValentTLChannel_pulledBackGram_exact
    (left right : SixValentTLChannel) :
    sixValentTLChannelPulledBackGram left right ≈
      sixValentTLChannelGram left right := by
  cases left <;> cases right <;>
    unfold sixValentTLChannelPulledBackGram sixValentPairingSum
      sixValentTLChannelCoefficient sixValentPairingGram
      sixValentTLChannelGram sixValentTLChannelNorm
      channelOneHalf channelThreeHalves oneQuarter oneThird oneSixth <;>
    decide

/-! ## 3. Positive resolution of the inverse Gram projector -/

def sixValentTLChannelInverseWeight : SixValentTLChannel → Q'
  | .spinThreeHalves => oneQuarter
  | .leftA => channelOneHalf
  | .leftB => channelOneHalf
  | .leftX => channelTwoThirds
  | .leftY => channelTwoThirds

/-- Every normalized rank-one channel summand has trace one. -/
theorem sixValentTLChannel_weighted_trace_one
    (channel : SixValentTLChannel) :
    sixValentTLChannelInverseWeight channel *
        sixValentTLChannelNorm channel ≈ 1 := by
  cases channel <;>
    unfold sixValentTLChannelInverseWeight sixValentTLChannelNorm
      oneQuarter channelOneHalf channelTwoThirds channelThreeHalves <;>
    decide

/-- The five normalized rank-one channels have total trace five. -/
theorem sixValentTLChannel_total_weighted_trace_five :
    sixValentTLChannelSum (fun channel =>
      sixValentTLChannelInverseWeight channel *
        sixValentTLChannelNorm channel) ≈ 5 := by
  unfold sixValentTLChannelSum sixValentTLChannelInverseWeight
    sixValentTLChannelNorm oneQuarter channelOneHalf channelTwoThirds
    channelThreeHalves
  decide

/-- The positive channel resolution `C^T D^-1 C`. -/
def sixValentTLResolvedPairingGramInverse
    (row column : SixValentPairing) : Q' :=
  sixValentTLChannelSum (fun channel =>
    sixValentTLChannelInverseWeight channel *
      (sixValentTLChannelCoefficient channel row *
        sixValentTLChannelCoefficient channel column))

/-- Exact diagonal channel decomposition of the signed inverse pairing Gram
matrix. -/
theorem sixValentPairingGramInverse_eqv_TL_resolution
    (row column : SixValentPairing) :
    sixValentPairingGramInverse row column ≈
      sixValentTLResolvedPairingGramInverse row column := by
  cases row <;> cases column <;>
    unfold sixValentTLResolvedPairingGramInverse sixValentTLChannelSum
      sixValentTLChannelInverseWeight sixValentTLChannelCoefficient
      sixValentPairingGramInverse oneQuarter oneTwelfth oneThird oneSixth
      channelOneHalf channelTwoThirds <;>
    decide

theorem sixValentPairingSum_eqv_congr
    (left right : SixValentPairing → Q')
    (h : ∀ pairing, left pairing ≈ right pairing) :
    sixValentPairingSum left ≈ sixValentPairingSum right := by
  unfold sixValentPairingSum
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (h .identity) (h .swapFirstTwo))
        (h .swapLastTwo))
      (h .cycleForward))
    (h .cycleBackward)

theorem sixValentTLChannelSum_eqv_congr
    (left right : SixValentTLChannel → Q')
    (h : ∀ channel, left channel ≈ right channel) :
    sixValentTLChannelSum left ≈ sixValentTLChannelSum right := by
  unfold sixValentTLChannelSum
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (h .spinThreeHalves) (h .leftA))
        (h .leftB))
      (h .leftX))
    (h .leftY)

/-- Multiplication distributes through the frozen five-channel sum. -/
theorem sixValentTLChannelSum_mul_right
    (family : SixValentTLChannel → Q') (factor : Q') :
    sixValentTLChannelSum family * factor ≈
      sixValentTLChannelSum (fun channel => family channel * factor) := by
  unfold sixValentTLChannelSum
  ring_qeqv

/-- Exact Fubini exchange between the frozen pairing and channel sums. -/
theorem sixValentPairingTLChannelSum_swap
    (family : SixValentPairing → SixValentTLChannel → Q') :
    sixValentPairingSum (fun pairing =>
      sixValentTLChannelSum (fun channel => family pairing channel)) ≈
    sixValentTLChannelSum (fun channel =>
      sixValentPairingSum (fun pairing => family pairing channel)) := by
  unfold sixValentPairingSum sixValentTLChannelSum
  ring_qeqv

/-- A weighted double pairing sum with separated row/column dependence is
the corresponding rank-one product. -/
theorem sixValentPairingDoubleSum_rankOne
    (weight : Q')
    (rowCoefficient columnCoefficient rowValue columnValue :
      SixValentPairing → Q') :
    sixValentPairingSum (fun rowPairing =>
      sixValentPairingSum (fun columnPairing =>
        (weight *
            (rowCoefficient rowPairing *
              columnCoefficient columnPairing)) *
          (rowValue rowPairing * columnValue columnPairing))) ≈
    weight *
      (sixValentPairingSum (fun rowPairing =>
          rowCoefficient rowPairing * rowValue rowPairing) *
        sixValentPairingSum (fun columnPairing =>
          columnCoefficient columnPairing * columnValue columnPairing)) := by
  unfold sixValentPairingSum
  ring_qeqv

/-- Structural rank-one factorization of the resolved inverse-Gram kernel.
This is independent of the Boolean realization of the pairing tensors. -/
theorem sixValentTLResolvedKernel_eqv_factorized
    (rowValue columnValue : SixValentPairing → Q') :
    sixValentPairingSum (fun rowPairing =>
      sixValentPairingSum (fun columnPairing =>
        sixValentTLResolvedPairingGramInverse rowPairing columnPairing *
          (rowValue rowPairing * columnValue columnPairing))) ≈
    sixValentTLChannelSum (fun channel =>
      sixValentTLChannelInverseWeight channel *
        (sixValentPairingSum (fun rowPairing =>
            sixValentTLChannelCoefficient channel rowPairing *
              rowValue rowPairing) *
          sixValentPairingSum (fun columnPairing =>
            sixValentTLChannelCoefficient channel columnPairing *
              columnValue columnPairing))) := by
  unfold sixValentTLResolvedPairingGramInverse
  refine Q'.eqv_trans _
    (sixValentPairingSum (fun rowPairing =>
      sixValentPairingSum (fun columnPairing =>
        sixValentTLChannelSum (fun channel =>
          (sixValentTLChannelInverseWeight channel *
              (sixValentTLChannelCoefficient channel rowPairing *
                sixValentTLChannelCoefficient channel columnPairing)) *
            (rowValue rowPairing * columnValue columnPairing))))) _ ?_ ?_
  · exact sixValentPairingSum_eqv_congr _ _ (fun rowPairing =>
      sixValentPairingSum_eqv_congr _ _ (fun columnPairing =>
        sixValentTLChannelSum_mul_right _ _))
  · refine Q'.eqv_trans _
      (sixValentPairingSum (fun rowPairing =>
        sixValentTLChannelSum (fun channel =>
          sixValentPairingSum (fun columnPairing =>
            (sixValentTLChannelInverseWeight channel *
                (sixValentTLChannelCoefficient channel rowPairing *
                  sixValentTLChannelCoefficient channel columnPairing)) *
              (rowValue rowPairing * columnValue columnPairing))))) _ ?_ ?_
    · exact sixValentPairingSum_eqv_congr _ _ (fun rowPairing =>
        sixValentPairingTLChannelSum_swap _)
    · refine Q'.eqv_trans _
        (sixValentTLChannelSum (fun channel =>
          sixValentPairingSum (fun rowPairing =>
            sixValentPairingSum (fun columnPairing =>
              (sixValentTLChannelInverseWeight channel *
                  (sixValentTLChannelCoefficient channel rowPairing *
                    sixValentTLChannelCoefficient channel columnPairing)) *
                (rowValue rowPairing * columnValue columnPairing))))) _ ?_ ?_
      · exact sixValentPairingTLChannelSum_swap _
      · exact sixValentTLChannelSum_eqv_congr _ _ (fun channel =>
          sixValentPairingDoubleSum_rankOne
            (sixValentTLChannelInverseWeight channel)
            (sixValentTLChannelCoefficient channel)
            (sixValentTLChannelCoefficient channel)
            rowValue columnValue)

/-- The original externally oriented kernel with its inverse Gram coefficient
replaced by the exact positive TL-channel resolution. -/
def orientedSixFundamentalHaarProjectorTLResolvedScalar
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) : Q' :=
  sixValentPairingSum (fun rowPairing =>
    sixValentPairingSum (fun columnPairing =>
      sixValentTLResolvedPairingGramInverse rowPairing columnPairing *
        (tripleOrientedPairing rowPairing
            firstForwardRow secondForwardRow thirdForwardRow
            firstReverseColumn secondReverseColumn thirdReverseColumn *
          tripleOrientedPairing columnPairing
            firstForwardColumn secondForwardColumn thirdForwardColumn
            firstReverseRow secondReverseRow thirdReverseRow)))

/-- Exact TL-channel resolution of the full twelve-index scalar kernel,
proved structurally with no Boolean case split. -/
theorem orientedSixFundamentalHaarProjectorScalar_eqv_TL_resolution
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    orientedSixFundamentalHaarProjectorScalar
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn ≈
    orientedSixFundamentalHaarProjectorTLResolvedScalar
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn := by
  unfold orientedSixFundamentalHaarProjectorScalar
    orientedSixFundamentalHaarProjectorTLResolvedScalar
  exact sixValentPairingSum_eqv_congr _ _ (fun rowPairing =>
    sixValentPairingSum_eqv_congr _ _ (fun columnPairing =>
      Q'.mul_eqv_congr_right _ _ _
        (sixValentPairingGramInverse_eqv_TL_resolution
          rowPairing columnPairing)))

/-- The fully factorized positive channel kernel.  Each summand is the
inverse channel norm times one left pairing tensor and one transposed right
pairing tensor. -/
def orientedSixFundamentalHaarProjectorTLFactorizedScalar
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) : Q' :=
  sixValentTLChannelSum (fun channel =>
    sixValentTLChannelInverseWeight channel *
      (sixValentTLChannelOrientedPairing channel
          firstForwardRow secondForwardRow thirdForwardRow
          firstReverseColumn secondReverseColumn thirdReverseColumn *
        sixValentTLChannelOrientedPairing channel
          firstForwardColumn secondForwardColumn thirdForwardColumn
          firstReverseRow secondReverseRow thirdReverseRow))

/-- The coefficient-resolved kernel is exactly the manifest five-term
rank-one channel factorization, without any Boolean case split. -/
theorem orientedSixFundamentalHaarProjectorTLResolvedScalar_eqv_factorized
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    orientedSixFundamentalHaarProjectorTLResolvedScalar
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn ≈
    orientedSixFundamentalHaarProjectorTLFactorizedScalar
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn := by
  unfold orientedSixFundamentalHaarProjectorTLResolvedScalar
    orientedSixFundamentalHaarProjectorTLFactorizedScalar
    sixValentTLChannelOrientedPairing
  exact sixValentTLResolvedKernel_eqv_factorized
    (fun rowPairing =>
      tripleOrientedPairing rowPairing
        firstForwardRow secondForwardRow thirdForwardRow
        firstReverseColumn secondReverseColumn thirdReverseColumn)
    (fun columnPairing =>
      tripleOrientedPairing columnPairing
        firstForwardColumn secondForwardColumn thirdForwardColumn
        firstReverseRow secondReverseRow thirdReverseRow)

/-- Rational-complex form of the TL-resolved projector. -/
def orientedSixFundamentalHaarProjectorTLResolved
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) : RationalComplex :=
  (orientedSixFundamentalHaarProjectorTLResolvedScalar
    firstForwardRow firstForwardColumn
    secondForwardRow secondForwardColumn
    thirdForwardRow thirdForwardColumn
    firstReverseRow firstReverseColumn
    secondReverseRow secondReverseColumn
    thirdReverseRow thirdReverseColumn, 0)

/-- Rational-complex form of the manifest rank-one channel factorization. -/
def orientedSixFundamentalHaarProjectorTLFactorized
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) : RationalComplex :=
  (orientedSixFundamentalHaarProjectorTLFactorizedScalar
    firstForwardRow firstForwardColumn
    secondForwardRow secondForwardColumn
    thirdForwardRow thirdForwardColumn
    firstReverseRow firstReverseColumn
    secondReverseRow secondReverseColumn
    thirdReverseRow thirdReverseColumn, 0)

theorem orientedSixFundamentalHaarProjectorTLResolved_eqv_factorized
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    RationalComplexEqv
      (orientedSixFundamentalHaarProjectorTLResolved
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        thirdForwardRow thirdForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn
        thirdReverseRow thirdReverseColumn)
      (orientedSixFundamentalHaarProjectorTLFactorized
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        thirdForwardRow thirdForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn
        thirdReverseRow thirdReverseColumn) :=
  ⟨orientedSixFundamentalHaarProjectorTLResolvedScalar_eqv_factorized
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn,
    Q'.eqv_refl 0⟩

/-- Rational-complex channel resolution of the abstract oriented projector. -/
theorem orientedSixFundamentalHaarProjector_eqv_TL_resolution
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    RationalComplexEqv
      (orientedSixFundamentalHaarProjector
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        thirdForwardRow thirdForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn
        thirdReverseRow thirdReverseColumn)
      (orientedSixFundamentalHaarProjectorTLResolved
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        thirdForwardRow thirdForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn
        thirdReverseRow thirdReverseColumn) := by
  exact
    ⟨orientedSixFundamentalHaarProjectorScalar_eqv_TL_resolution
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        thirdForwardRow thirdForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn
        thirdReverseRow thirdReverseColumn,
      Q'.eqv_refl 0⟩

/-- **Exact channel-resolved sixth moment.**  The literal normalized
`F F F R R R` Haar integral equals the positive TL-channel resolution of the
signed kernel. -/
theorem oneLink_threeForward_threeReverse_fundamental_projector_TL_resolved
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        (threeForwardThreeReverseFundamentalTerm 0
          firstForwardRow firstForwardColumn
          secondForwardRow secondForwardColumn
          thirdForwardRow thirdForwardColumn
          firstReverseRow firstReverseColumn
          secondReverseRow secondReverseColumn
          thirdReverseRow thirdReverseColumn))
      (orientedSixFundamentalHaarProjectorTLResolved
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        thirdForwardRow thirdForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn
        thirdReverseRow thirdReverseColumn) := by
  exact rationalComplexEqv_trans
    (oneLink_threeForward_threeReverse_fundamental_projector
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn)
    (orientedSixFundamentalHaarProjector_eqv_TL_resolution
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn)

/-- **Manifest positive-channel sixth moment.**  The literal normalized Haar
integral is the sum of the five rank-one TL-channel tensors with positive
weights `1/4,1/2,1/2,2/3,2/3`. -/
theorem oneLink_threeForward_threeReverse_fundamental_projector_TL_factorized
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        (threeForwardThreeReverseFundamentalTerm 0
          firstForwardRow firstForwardColumn
          secondForwardRow secondForwardColumn
          thirdForwardRow thirdForwardColumn
          firstReverseRow firstReverseColumn
          secondReverseRow secondReverseColumn
          thirdReverseRow thirdReverseColumn))
      (orientedSixFundamentalHaarProjectorTLFactorized
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        thirdForwardRow thirdForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn
        thirdReverseRow thirdReverseColumn) := by
  exact rationalComplexEqv_trans
    (oneLink_threeForward_threeReverse_fundamental_projector_TL_resolved
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn)
    (orientedSixFundamentalHaarProjectorTLResolved_eqv_factorized
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn)

/-! ## 4. Exact left/right recoupling with interference retained -/

/-- Right-associated channel elements `p3,A',B',X',Y'`. -/
def sixValentTLRightChannelElement : SixValentTLChannel → TL3
  | .spinThreeHalves => tl3TopClosed
  | .leftA => tl3ChannelAPrime
  | .leftB =>
      ⟨0, channelTwoThirds, oneSixth, -oneThird, -oneThird⟩
  | .leftX =>
      ⟨0, 0, -oneQuarter, 0, channelOneHalf⟩
  | .leftY =>
      ⟨0, 0, -oneQuarter, channelOneHalf, 0⟩

/-- Pairing coefficients of the right-associated channel family. -/
def sixValentTLRightChannelCoefficient :
    SixValentTLChannel → SixValentPairing → Q'
  | .spinThreeHalves, .identity => oneThird
  | .spinThreeHalves, .swapFirstTwo => 0
  | .spinThreeHalves, .swapLastTwo => 0
  | .spinThreeHalves, .cycleForward => oneThird
  | .spinThreeHalves, .cycleBackward => oneThird
  | .leftA, .identity => channelOneHalf
  | .leftA, .swapFirstTwo => 0
  | .leftA, .swapLastTwo => -channelOneHalf
  | .leftA, .cycleForward => 0
  | .leftA, .cycleBackward => 0
  | .leftB, .identity => oneSixth
  | .leftB, .swapFirstTwo => 0
  | .leftB, .swapLastTwo => channelOneHalf
  | .leftB, .cycleForward => -oneThird
  | .leftB, .cycleBackward => -oneThird
  | .leftX, .identity => oneQuarter
  | .leftX, .swapFirstTwo => -channelOneHalf
  | .leftX, .swapLastTwo => -oneQuarter
  | .leftX, .cycleForward => channelOneHalf
  | .leftX, .cycleBackward => 0
  | .leftY, .identity => oneQuarter
  | .leftY, .swapFirstTwo => -channelOneHalf
  | .leftY, .swapLastTwo => -oneQuarter
  | .leftY, .cycleForward => 0
  | .leftY, .cycleBackward => channelOneHalf

theorem sixValentTLRightChannelCoefficient_from_tl3
    (channel : SixValentTLChannel) (pairing : SixValentPairing) :
    tl3PairingCoefficient (sixValentTLRightChannelElement channel) pairing ≈
      sixValentTLRightChannelCoefficient channel pairing := by
  cases channel <;> cases pairing <;>
    unfold tl3PairingCoefficient sixValentTLRightChannelElement
      sixValentTLRightChannelCoefficient tl3TopClosed tl3ChannelAPrime
      channelOneHalf channelTwoThirds oneQuarter oneThird oneSixth <;>
    decide

/-- Full left-to-right recoupling matrix.  Rows are `p3',A',B',X',Y'`; columns
are `p3,A,B,X,Y`. -/
def sixValentTLRecoupling :
    SixValentTLChannel → SixValentTLChannel → Q'
  | .spinThreeHalves, .spinThreeHalves => 1
  | .spinThreeHalves, _ => 0
  | .leftA, .spinThreeHalves => 0
  | .leftA, .leftA => oneQuarter
  | .leftA, .leftB => threeQuarters
  | .leftA, .leftX => channelOneHalf
  | .leftA, .leftY => channelOneHalf
  | .leftB, .spinThreeHalves => 0
  | .leftB, .leftA => threeQuarters
  | .leftB, .leftB => oneQuarter
  | .leftB, .leftX => -channelOneHalf
  | .leftB, .leftY => -channelOneHalf
  | .leftX, .spinThreeHalves => 0
  | .leftX, .leftA => channelThreeEighths
  | .leftX, .leftB => -channelThreeEighths
  | .leftX, .leftX => -oneQuarter
  | .leftX, .leftY => threeQuarters
  | .leftY, .spinThreeHalves => 0
  | .leftY, .leftA => channelThreeEighths
  | .leftY, .leftB => -channelThreeEighths
  | .leftY, .leftX => threeQuarters
  | .leftY, .leftY => -oneQuarter

/-- The right channel coefficients are exactly the displayed recoupling of
the left channel coefficients.  In particular this contains
`A'=A/4+3B/4+X/2+Y/2` and
`B'=3A/4+B/4-X/2-Y/2`. -/
theorem sixValentTLRightCoefficient_eqv_recoupled
    (rightChannel : SixValentTLChannel) (pairing : SixValentPairing) :
    sixValentTLRightChannelCoefficient rightChannel pairing ≈
      sixValentTLChannelSum (fun leftChannel =>
        sixValentTLRecoupling rightChannel leftChannel *
          sixValentTLChannelCoefficient leftChannel pairing) := by
  cases rightChannel <;> cases pairing <;>
    unfold sixValentTLRightChannelCoefficient sixValentTLChannelSum
      sixValentTLRecoupling sixValentTLChannelCoefficient oneQuarter
      threeQuarters channelOneHalf channelThreeEighths oneThird oneSixth <;>
    decide

/-- The complete recoupling matrix is an exact involution. -/
theorem sixValentTLRecoupling_involutive
    (row column : SixValentTLChannel) :
    sixValentTLChannelSum (fun middle =>
      sixValentTLRecoupling row middle *
        sixValentTLRecoupling middle column) ≈
      sixValentTLChannelDelta row column := by
  cases row <;> cases column <;>
    unfold sixValentTLChannelSum sixValentTLRecoupling
      sixValentTLChannelDelta oneQuarter threeQuarters
      channelOneHalf channelThreeEighths <;>
    decide

/-- `R D R^T=D`: recoupling preserves the orthogonal channel Gram exactly. -/
theorem sixValentTLRecoupling_preserves_gram
    (row column : SixValentTLChannel) :
    sixValentTLChannelSum (fun middle =>
      sixValentTLRecoupling row middle *
        (sixValentTLChannelNorm middle *
          sixValentTLRecoupling column middle)) ≈
      sixValentTLChannelGram row column := by
  cases row <;> cases column <;>
    unfold sixValentTLChannelSum sixValentTLRecoupling
      sixValentTLChannelNorm sixValentTLChannelGram oneQuarter
      threeQuarters channelOneHalf channelThreeEighths
      channelThreeHalves <;>
    decide

/-- The right-associated concrete `TL3` channels have the same diagonal
Markov Gram. -/
theorem tl3RightChannel_gram_exact
    (left right : SixValentTLChannel) :
    tl3Inner (sixValentTLRightChannelElement left)
        (sixValentTLRightChannelElement right) ≈
      sixValentTLChannelGram left right := by
  cases left <;> cases right <;>
    unfold tl3Inner tl3Star sixValentTLRightChannelElement
      sixValentTLChannelGram sixValentTLChannelNorm tl3TopClosed
      tl3ChannelAPrime mtr3 tl3mul channelOneHalf channelTwoThirds
      channelThreeHalves oneQuarter oneThird oneSixth <;>
    decide

#print axioms p3_eqv_tl3TopClosed
#print axioms tl3ChannelX_constructed
#print axioms tl3ChannelY_constructed
#print axioms tl3Channel_gram_exact
#print axioms sixValentTLChannelCoefficient_from_tl3
#print axioms sixValentTLChannel_pulledBackGram_exact
#print axioms sixValentTLChannel_weighted_trace_one
#print axioms sixValentTLChannel_total_weighted_trace_five
#print axioms sixValentPairingGramInverse_eqv_TL_resolution
#print axioms sixValentTLResolvedKernel_eqv_factorized
#print axioms orientedSixFundamentalHaarProjectorScalar_eqv_TL_resolution
#print axioms orientedSixFundamentalHaarProjectorTLResolvedScalar_eqv_factorized
#print axioms orientedSixFundamentalHaarProjector_eqv_TL_resolution
#print axioms oneLink_threeForward_threeReverse_fundamental_projector_TL_resolved
#print axioms oneLink_threeForward_threeReverse_fundamental_projector_TL_factorized
#print axioms sixValentTLRightChannelCoefficient_from_tl3
#print axioms sixValentTLRightCoefficient_eqv_recoupled
#print axioms sixValentTLRecoupling_involutive
#print axioms sixValentTLRecoupling_preserves_gram
#print axioms tl3RightChannel_gram_exact

end YMGap.Continuum.SU2QuaternionSixValentTemperleyLiebChannelBridge
