/-
# Fundamental SU(2) local channels as symbolic Boolean tensors

This leaf places the positive invariant channels at balanced fundamental
links of valence two, four, and six in one coordinate calculus.  Coordinates
are always ordered with every operator output first and every operator input
second:

* valence two: `(output,input)`;
* valence four: `(firstOutput,secondOutput,firstInput,secondInput)`;
* valence six: `(firstOutput,secondOutput,thirdOutput,
    firstInput,secondInput,thirdInput)`.

The six-valent Gram bridge is structural.  It distributes the symbolic tensor
dot product through the frozen five-pairing sum and then invokes the existing
pairing Gram theorem.  In particular, it does not enumerate the sixty-four
Boolean coordinates or assert raw six-valent projector idempotence.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SymbolicFiniteBoolTensor
import YMGap.Continuum.SU2QuaternionBivalentOperatorKernel
import YMGap.Continuum.SU2QuaternionFourValentOperatorKernel
import YMGap.Continuum.SU2QuaternionSixValentOperatorKernel

namespace YMGap.Continuum.SU2QuaternionLocalChannelBoolTensor

open YMGap.Constructive
open YMGap.Continuum.SymbolicFiniteBoolTensor
open YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector
open YMGap.Continuum.SU2QuaternionFourValentChannelDiagonalization
open YMGap.Continuum.SU2QuaternionBivalentOperatorKernel
open YMGap.Continuum.SU2QuaternionFourValentOperatorKernel
open YMGap.Continuum.SU2QuaternionSixValentPairingGram
open YMGap.Continuum.SU2QuaternionSixValentTemperleyLiebChannelBridge
open YMGap.Continuum.SU2QuaternionSixValentOperatorKernel

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Structural bilinearity needed by the five-channel bridge -/

/-- Pointwise addition of symbolic Boolean tensors. -/
def channelTensorAdd :
    (n : Nat) -> BoolTensor n -> BoolTensor n -> BoolTensor n
  | 0, left, right => (show Q' from left) + (show Q' from right)
  | n + 1, left, right => fun bit =>
      channelTensorAdd n (left bit) (right bit)

/-- The recursive Boolean tensor dot product is additive in its left slot. -/
theorem boolTensorDot_channelTensorAdd_left
    (n : Nat) (left right test : BoolTensor n) :
    boolTensorDot n (channelTensorAdd n left right) test ≈
      boolTensorDot n left test + boolTensorDot n right test := by
  induction n with
  | zero =>
      change
        ((show Q' from left) + (show Q' from right)) *
            (show Q' from test) ≈
          (show Q' from left) * (show Q' from test) +
            (show Q' from right) * (show Q' from test)
      exact QPoly.q_add_mul
        (show Q' from left) (show Q' from right) (show Q' from test)
  | succ n ih =>
      change
        boolTensorDot n
              (channelTensorAdd n (left false) (right false))
              (test false) +
            boolTensorDot n
              (channelTensorAdd n (left true) (right true))
              (test true) ≈
          (boolTensorDot n (left false) (test false) +
              boolTensorDot n (left true) (test true)) +
            (boolTensorDot n (right false) (test false) +
              boolTensorDot n (right true) (test true))
      refine Q'.eqv_trans _
        ((boolTensorDot n (left false) (test false) +
            boolTensorDot n (right false) (test false)) +
          (boolTensorDot n (left true) (test true) +
            boolTensorDot n (right true) (test true))) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (ih (left := left false) (right := right false)
            (test := test false))
          (ih (left := left true) (right := right true)
            (test := test true))
      · exact Q'.add_swap_inner
          (boolTensorDot n (left false) (test false))
          (boolTensorDot n (right false) (test false))
          (boolTensorDot n (left true) (test true))
          (boolTensorDot n (right true) (test true))

/-- The recursive Boolean tensor dot product is additive in its right slot. -/
theorem boolTensorDot_channelTensorAdd_right
    (n : Nat) (test left right : BoolTensor n) :
    boolTensorDot n test (channelTensorAdd n left right) ≈
      boolTensorDot n test left + boolTensorDot n test right := by
  induction n with
  | zero =>
      change
        (show Q' from test) *
            ((show Q' from left) + (show Q' from right)) ≈
          (show Q' from test) * (show Q' from left) +
            (show Q' from test) * (show Q' from right)
      exact Q'.mul_add_eqv
        (show Q' from test) (show Q' from left) (show Q' from right)
  | succ n ih =>
      change
        boolTensorDot n (test false)
              (channelTensorAdd n (left false) (right false)) +
            boolTensorDot n (test true)
              (channelTensorAdd n (left true) (right true)) ≈
          (boolTensorDot n (test false) (left false) +
              boolTensorDot n (test true) (left true)) +
            (boolTensorDot n (test false) (right false) +
              boolTensorDot n (test true) (right true))
      refine Q'.eqv_trans _
        ((boolTensorDot n (test false) (left false) +
            boolTensorDot n (test false) (right false)) +
          (boolTensorDot n (test true) (left true) +
            boolTensorDot n (test true) (right true))) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (ih (test := test false) (left := left false)
            (right := right false))
          (ih (test := test true) (left := left true)
            (right := right true))
      · exact Q'.add_swap_inner
          (boolTensorDot n (test false) (left false))
          (boolTensorDot n (test false) (right false))
          (boolTensorDot n (test true) (left true))
          (boolTensorDot n (test true) (right true))

private theorem fiveChannelTensorSum_dot_left
    (n : Nat) (first second third fourth fifth test : BoolTensor n) :
    boolTensorDot n
        (channelTensorAdd n
          (channelTensorAdd n
            (channelTensorAdd n
              (channelTensorAdd n first second) third) fourth) fifth)
        test ≈
      ((((boolTensorDot n first test + boolTensorDot n second test) +
          boolTensorDot n third test) + boolTensorDot n fourth test) +
        boolTensorDot n fifth test) := by
  refine Q'.eqv_trans _
    (boolTensorDot n
        (channelTensorAdd n
          (channelTensorAdd n
            (channelTensorAdd n first second) third) fourth) test +
      boolTensorDot n fifth test) _
    (boolTensorDot_channelTensorAdd_left n _ _ test) ?_
  refine Q'.add_eqv_congr' ?_ (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    (boolTensorDot n
        (channelTensorAdd n
          (channelTensorAdd n first second) third) test +
      boolTensorDot n fourth test) _
    (boolTensorDot_channelTensorAdd_left n _ _ test) ?_
  refine Q'.add_eqv_congr' ?_ (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    (boolTensorDot n (channelTensorAdd n first second) test +
      boolTensorDot n third test) _
    (boolTensorDot_channelTensorAdd_left n _ _ test) ?_
  exact Q'.add_eqv_congr'
    (boolTensorDot_channelTensorAdd_left n first second test)
    (Q'.eqv_refl _)

private theorem fiveChannelTensorSum_dot_right
    (n : Nat) (test first second third fourth fifth : BoolTensor n) :
    boolTensorDot n test
        (channelTensorAdd n
          (channelTensorAdd n
            (channelTensorAdd n
              (channelTensorAdd n first second) third) fourth) fifth) ≈
      ((((boolTensorDot n test first + boolTensorDot n test second) +
          boolTensorDot n test third) + boolTensorDot n test fourth) +
        boolTensorDot n test fifth) := by
  refine Q'.eqv_trans _
    (boolTensorDot n test
        (channelTensorAdd n
          (channelTensorAdd n
            (channelTensorAdd n first second) third) fourth) +
      boolTensorDot n test fifth) _
    (boolTensorDot_channelTensorAdd_right n test _ _) ?_
  refine Q'.add_eqv_congr' ?_ (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    (boolTensorDot n test
        (channelTensorAdd n
          (channelTensorAdd n first second) third) +
      boolTensorDot n test fourth) _
    (boolTensorDot_channelTensorAdd_right n test _ _) ?_
  refine Q'.add_eqv_congr' ?_ (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    (boolTensorDot n test (channelTensorAdd n first second) +
      boolTensorDot n test third) _
    (boolTensorDot_channelTensorAdd_right n test _ _) ?_
  exact Q'.add_eqv_congr'
    (boolTensorDot_channelTensorAdd_right n test first second)
    (Q'.eqv_refl _)

/-- Frozen five-pairing sum in the symbolic tensor carrier. -/
def sixValentPairingTensorSum {n : Nat}
    (family : SixValentPairing -> BoolTensor n) : BoolTensor n :=
  channelTensorAdd n
    (channelTensorAdd n
      (channelTensorAdd n
        (channelTensorAdd n
          (family .identity) (family .swapFirstTwo))
        (family .swapLastTwo))
      (family .cycleForward))
    (family .cycleBackward)

/-- A frozen five-pairing tensor sum pulls out of the left dot slot. -/
theorem sixValentPairingTensorSum_dot_left {n : Nat}
    (family : SixValentPairing -> BoolTensor n) (test : BoolTensor n) :
    boolTensorDot n (sixValentPairingTensorSum family) test ≈
      sixValentPairingSum (fun pairing =>
        boolTensorDot n (family pairing) test) := by
  unfold sixValentPairingTensorSum sixValentPairingSum
  exact fiveChannelTensorSum_dot_left n
    (family .identity) (family .swapFirstTwo) (family .swapLastTwo)
    (family .cycleForward) (family .cycleBackward) test

/-- A frozen five-pairing tensor sum pulls out of the right dot slot. -/
theorem sixValentPairingTensorSum_dot_right {n : Nat}
    (test : BoolTensor n) (family : SixValentPairing -> BoolTensor n) :
    boolTensorDot n test (sixValentPairingTensorSum family) ≈
      sixValentPairingSum (fun pairing =>
        boolTensorDot n test (family pairing)) := by
  unfold sixValentPairingTensorSum sixValentPairingSum
  exact fiveChannelTensorSum_dot_right n test
    (family .identity) (family .swapFirstTwo) (family .swapLastTwo)
    (family .cycleForward) (family .cycleBackward)

/-! ## 2. Bivalent scalar channel -/

/-- The bivalent invariant vector in output-first/input-second coordinates. -/
def bivalentInvariantDeltaBoolTensor : BoolTensor 2 :=
  fun output input => bivalentInvariantDelta ⟨output, input⟩

/-- Pointwise identification with the operator-kernel delta coordinate. -/
theorem bivalentInvariantDeltaBoolTensor_apply
    (output input : Bool) :
    bivalentInvariantDeltaBoolTensor output input =
      bivalentInvariantDelta ⟨output, input⟩ := rfl

/-- The symbolic tensor dot is exactly the existing two-index contraction. -/
theorem bivalentInvariantDeltaBoolTensor_dot_eq_squaredNorm :
    boolTensorDot 2 bivalentInvariantDeltaBoolTensor
        bivalentInvariantDeltaBoolTensor =
      bivalentInvariantDeltaSquaredNorm := by
  rfl

/-- The bivalent channel has exact symbolic squared norm two. -/
theorem bivalentInvariantDeltaBoolTensor_norm_exact :
    boolTensorDot 2 bivalentInvariantDeltaBoolTensor
        bivalentInvariantDeltaBoolTensor ≈ 2 := by
  rw [bivalentInvariantDeltaBoolTensor_dot_eq_squaredNorm]
  exact bivalentInvariantDeltaSquaredNorm_exact

/-- Its inverse-Gram weight times its symbolic norm is one. -/
theorem bivalentInvariantDeltaBoolTensor_weighted_norm_exact :
    bivalentInvariantChannelWeight *
        boolTensorDot 2 bivalentInvariantDeltaBoolTensor
          bivalentInvariantDeltaBoolTensor ≈ 1 := by
  refine Q'.eqv_trans _
    (bivalentInvariantChannelWeight * 2) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left bivalentInvariantChannelWeight _ _
      bivalentInvariantDeltaBoolTensor_norm_exact
  · unfold bivalentInvariantChannelWeight
    decide

/-! ## 3. Four-valent singlet and triplet channels -/

/-- Frozen local channel order for a balanced four-valent link. -/
inductive FourValentOperatorBoolChannel where
  | singlet
  | triplet
  deriving DecidableEq

/-- Singlet tensor in output-output-input-input coordinates. -/
def fourValentSingletBoolTensor : BoolTensor 4 :=
  fun firstOutput secondOutput firstInput secondInput =>
    twoLegOperatorSingletCoordinate
      ⟨firstOutput, firstInput, secondOutput, secondInput⟩

/-- Triplet tensor in output-output-input-input coordinates. -/
def fourValentTripletBoolTensor : BoolTensor 4 :=
  fun firstOutput secondOutput firstInput secondInput =>
    twoLegOperatorTripletCoordinate
      ⟨firstOutput, firstInput, secondOutput, secondInput⟩

/-- Symbolic vector of a frozen four-valent channel. -/
def fourValentOperatorChannelBoolTensor :
    FourValentOperatorBoolChannel -> BoolTensor 4
  | .singlet => fourValentSingletBoolTensor
  | .triplet => fourValentTripletBoolTensor

/-- Existing operator-coordinate value of a frozen four-valent channel. -/
def fourValentOperatorBoolChannelCoordinate
    (channel : FourValentOperatorBoolChannel)
    (index : TwoLegOperatorIndex) : Q' :=
  match channel with
  | .singlet => twoLegOperatorSingletCoordinate index
  | .triplet => twoLegOperatorTripletCoordinate index

/-- Pointwise identification in the exact output-first/input-second order. -/
theorem fourValentOperatorChannelBoolTensor_apply
    (channel : FourValentOperatorBoolChannel)
    (firstOutput secondOutput firstInput secondInput : Bool) :
    fourValentOperatorChannelBoolTensor channel
        firstOutput secondOutput firstInput secondInput =
      fourValentOperatorBoolChannelCoordinate channel
        ⟨firstOutput, firstInput, secondOutput, secondInput⟩ := by
  cases channel <;> rfl

/-- Exact squared norm attached to each four-valent channel. -/
def fourValentOperatorBoolChannelNorm :
    FourValentOperatorBoolChannel -> Q'
  | .singlet => 1
  | .triplet => 3

/-- Diagonal Gram table for the four-valent channels. -/
def fourValentOperatorBoolChannelGram
    (left right : FourValentOperatorBoolChannel) : Q' :=
  if left = right then fourValentOperatorBoolChannelNorm left else 0

/-- Exact symbolic Gram `diag(1,3)` for singlet and triplet. -/
theorem fourValentOperatorChannelBoolTensor_gram_exact
    (left right : FourValentOperatorBoolChannel) :
    boolTensorDot 4
        (fourValentOperatorChannelBoolTensor left)
        (fourValentOperatorChannelBoolTensor right) ≈
      fourValentOperatorBoolChannelGram left right := by
  cases left <;> cases right
  · change orientedPairingInner singletOrientedPairing
      singletOrientedPairing ≈ 1
    exact fourValentOperatorChannelGram_exact.1
  · change orientedPairingInner singletOrientedPairing
      tripletOrientedPairing ≈ 0
    exact fourValentOperatorChannelGram_exact.2.1
  · change orientedPairingInner tripletOrientedPairing
      singletOrientedPairing ≈ 0
    exact fourValentOperatorChannelGram_exact.2.2.1
  · change orientedPairingInner tripletOrientedPairing
      tripletOrientedPairing ≈ 3
    exact fourValentOperatorChannelGram_exact.2.2.2

/-- Symbolic squared norm of one four-valent channel. -/
theorem fourValentOperatorChannelBoolTensor_norm_exact
    (channel : FourValentOperatorBoolChannel) :
    boolTensorDot 4
        (fourValentOperatorChannelBoolTensor channel)
        (fourValentOperatorChannelBoolTensor channel) ≈
      fourValentOperatorBoolChannelNorm channel := by
  cases channel
  · exact fourValentOperatorChannelBoolTensor_gram_exact
      .singlet .singlet
  · exact fourValentOperatorChannelBoolTensor_gram_exact
      .triplet .triplet

/-- Positive inverse-Gram weight of each four-valent channel. -/
def fourValentOperatorBoolChannelWeight :
    FourValentOperatorBoolChannel -> Q'
  | .singlet => 1
  | .triplet => oneThird

theorem fourValentOperatorBoolChannelWeight_nonneg
    (channel : FourValentOperatorBoolChannel) :
    (0 : Q') <= fourValentOperatorBoolChannelWeight channel := by
  cases channel
  · decide
  · unfold fourValentOperatorBoolChannelWeight oneThird
    decide

/-- Each normalized four-valent rank-one channel has unit trace mass. -/
theorem fourValentOperatorChannelBoolTensor_weighted_norm_exact
    (channel : FourValentOperatorBoolChannel) :
    fourValentOperatorBoolChannelWeight channel *
        boolTensorDot 4
          (fourValentOperatorChannelBoolTensor channel)
          (fourValentOperatorChannelBoolTensor channel) ≈ 1 := by
  cases channel
  · refine Q'.eqv_trans _ ((1 : Q') * 1) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left 1 _ _
        (fourValentOperatorChannelBoolTensor_norm_exact .singlet)
    · decide
  · refine Q'.eqv_trans _ (oneThird * 3) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left oneThird _ _
        (fourValentOperatorChannelBoolTensor_norm_exact .triplet)
    · unfold oneThird
      decide

/-! ## 4. Six-valent Temperley--Lieb channels -/

/-- One permutation pairing as a six-coordinate symbolic tensor. -/
def sixValentPairingBoolTensor
    (pairing : SixValentPairing) : BoolTensor 6 :=
  fun first second third firstConjugate secondConjugate thirdConjugate =>
    tripleOrientedPairing pairing first second third
      firstConjugate secondConjugate thirdConjugate

/-- Its symbolic dot is definitionally the existing factored contraction. -/
theorem sixValentPairingBoolTensor_dot_eq_inner
    (left right : SixValentPairing) :
    boolTensorDot 6
        (sixValentPairingBoolTensor left)
        (sixValentPairingBoolTensor right) =
      tripleOrientedPairingInner left right := by
  rfl

/-- The symbolic pairing tensors realize the frozen `5 x 5` Gram table. -/
theorem sixValentPairingBoolTensor_gram_exact
    (left right : SixValentPairing) :
    boolTensorDot 6
        (sixValentPairingBoolTensor left)
        (sixValentPairingBoolTensor right) ≈
      sixValentPairingGram left right := by
  rw [sixValentPairingBoolTensor_dot_eq_inner]
  exact tripleOrientedPairing_gram_exact left right

/-- A six-valent TL channel as the structural sum of its five weighted
permutation-pairing tensors. -/
def sixValentOperatorChannelBoolTensor
    (channel : SixValentTLChannel) : BoolTensor 6 :=
  sixValentPairingTensorSum (fun pairing =>
    tensorScale 6 (sixValentTLChannelCoefficient channel pairing)
      (sixValentPairingBoolTensor pairing))

/-- Pointwise identification with the canonical operator channel in the
output-output-output-input-input-input convention. -/
theorem sixValentOperatorChannelBoolTensor_apply
    (channel : SixValentTLChannel)
    (firstOutput secondOutput thirdOutput
      firstInput secondInput thirdInput : Bool) :
    sixValentOperatorChannelBoolTensor channel
        firstOutput secondOutput thirdOutput
        firstInput secondInput thirdInput =
      sixValentOperatorChannelCoordinate channel
        ⟨firstOutput, firstInput, secondOutput, secondInput,
          thirdOutput, thirdInput⟩ := by
  rfl

private theorem weightedPairingBoolTensor_dot_exact
    (leftChannel rightChannel : SixValentTLChannel)
    (leftPairing rightPairing : SixValentPairing) :
    boolTensorDot 6
        (tensorScale 6
          (sixValentTLChannelCoefficient leftChannel leftPairing)
          (sixValentPairingBoolTensor leftPairing))
        (tensorScale 6
          (sixValentTLChannelCoefficient rightChannel rightPairing)
          (sixValentPairingBoolTensor rightPairing)) ≈
      sixValentTLChannelCoefficient leftChannel leftPairing *
        (sixValentPairingGram leftPairing rightPairing *
          sixValentTLChannelCoefficient rightChannel rightPairing) := by
  let leftCoefficient :=
    sixValentTLChannelCoefficient leftChannel leftPairing
  let rightCoefficient :=
    sixValentTLChannelCoefficient rightChannel rightPairing
  refine Q'.eqv_trans _
    ((leftCoefficient * rightCoefficient) *
      boolTensorDot 6
        (sixValentPairingBoolTensor leftPairing)
        (sixValentPairingBoolTensor rightPairing)) _ ?_ ?_
  · exact boolTensorDot_scale 6 leftCoefficient rightCoefficient
      (sixValentPairingBoolTensor leftPairing)
      (sixValentPairingBoolTensor rightPairing)
  · refine Q'.eqv_trans _
      ((leftCoefficient * rightCoefficient) *
        sixValentPairingGram leftPairing rightPairing) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left
        (leftCoefficient * rightCoefficient) _ _
        (sixValentPairingBoolTensor_gram_exact leftPairing rightPairing)
    · refine Q'.eqv_trans _
        (leftCoefficient *
          (rightCoefficient *
            sixValentPairingGram leftPairing rightPairing)) _
        (Q'.mul_assoc_eqv leftCoefficient rightCoefficient
          (sixValentPairingGram leftPairing rightPairing)) ?_
      exact Q'.mul_eqv_congr_left leftCoefficient _ _
        (Q'.mul_comm_eqv rightCoefficient
          (sixValentPairingGram leftPairing rightPairing))

/-- **Six-valent shallow-sum Gram bridge.**  The actual six-coordinate
symbolic channel dot is the pulled-back pairing Gram, proved solely by
bilinearity, the frozen five-pairing sum, and the pairing Gram theorem. -/
theorem sixValentOperatorChannelBoolTensor_dot_eqv_pulledBackGram
    (left right : SixValentTLChannel) :
    boolTensorDot 6
        (sixValentOperatorChannelBoolTensor left)
        (sixValentOperatorChannelBoolTensor right) ≈
      sixValentTLChannelPulledBackGram left right := by
  unfold sixValentOperatorChannelBoolTensor
  refine Q'.eqv_trans _
    (sixValentPairingSum (fun leftPairing =>
      boolTensorDot 6
        (tensorScale 6
          (sixValentTLChannelCoefficient left leftPairing)
          (sixValentPairingBoolTensor leftPairing))
        (sixValentPairingTensorSum (fun rightPairing =>
          tensorScale 6
            (sixValentTLChannelCoefficient right rightPairing)
            (sixValentPairingBoolTensor rightPairing))))) _ ?_ ?_
  · exact sixValentPairingTensorSum_dot_left _ _
  · refine Q'.eqv_trans _
      (sixValentPairingSum (fun leftPairing =>
        sixValentPairingSum (fun rightPairing =>
          boolTensorDot 6
            (tensorScale 6
              (sixValentTLChannelCoefficient left leftPairing)
              (sixValentPairingBoolTensor leftPairing))
            (tensorScale 6
              (sixValentTLChannelCoefficient right rightPairing)
              (sixValentPairingBoolTensor rightPairing))))) _ ?_ ?_
    · exact sixValentPairingSum_eqv_congr _ _ (fun leftPairing =>
        sixValentPairingTensorSum_dot_right _ _)
    · unfold sixValentTLChannelPulledBackGram
      exact sixValentPairingSum_eqv_congr _ _ (fun leftPairing =>
        sixValentPairingSum_eqv_congr _ _ (fun rightPairing =>
          weightedPairingBoolTensor_dot_exact
            left right leftPairing rightPairing))

/-- The five actual symbolic TL tensors are orthogonal with exact norms
`4,2,2,3/2,3/2`.  This closes the previously separate pulled-back-Gram
interface without a six-Bool reduction. -/
theorem sixValentOperatorChannelBoolTensor_gram_exact
    (left right : SixValentTLChannel) :
    boolTensorDot 6
        (sixValentOperatorChannelBoolTensor left)
        (sixValentOperatorChannelBoolTensor right) ≈
      sixValentTLChannelGram left right := by
  exact Q'.eqv_trans _ _ _
    (sixValentOperatorChannelBoolTensor_dot_eqv_pulledBackGram left right)
    (sixValentTLChannel_pulledBackGram_exact left right)

/-- Exact symbolic squared norm of one TL channel. -/
theorem sixValentOperatorChannelBoolTensor_norm_exact
    (channel : SixValentTLChannel) :
    boolTensorDot 6
        (sixValentOperatorChannelBoolTensor channel)
        (sixValentOperatorChannelBoolTensor channel) ≈
      sixValentTLChannelNorm channel := by
  refine Q'.eqv_trans _ (sixValentTLChannelGram channel channel) _
    (sixValentOperatorChannelBoolTensor_gram_exact channel channel) ?_
  unfold sixValentTLChannelGram
  rw [if_pos rfl]
  exact Q'.eqv_refl _

/-- Each normalized six-valent symbolic TL channel has unit trace mass. -/
theorem sixValentOperatorChannelBoolTensor_weighted_norm_exact
    (channel : SixValentTLChannel) :
    sixValentTLChannelInverseWeight channel *
        boolTensorDot 6
          (sixValentOperatorChannelBoolTensor channel)
          (sixValentOperatorChannelBoolTensor channel) ≈ 1 := by
  refine Q'.eqv_trans _
    (sixValentTLChannelInverseWeight channel *
      sixValentTLChannelNorm channel) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left
      (sixValentTLChannelInverseWeight channel) _ _
      (sixValentOperatorChannelBoolTensor_norm_exact channel)
  · exact sixValentTLChannel_weighted_trace_one channel

#print axioms boolTensorDot_channelTensorAdd_left
#print axioms boolTensorDot_channelTensorAdd_right
#print axioms sixValentPairingTensorSum_dot_left
#print axioms bivalentInvariantDeltaBoolTensor_norm_exact
#print axioms fourValentOperatorChannelBoolTensor_gram_exact
#print axioms fourValentOperatorChannelBoolTensor_weighted_norm_exact
#print axioms sixValentPairingBoolTensor_gram_exact
#print axioms sixValentOperatorChannelBoolTensor_dot_eqv_pulledBackGram
#print axioms sixValentOperatorChannelBoolTensor_gram_exact
#print axioms sixValentOperatorChannelBoolTensor_weighted_norm_exact

end YMGap.Continuum.SU2QuaternionLocalChannelBoolTensor
