/-
# Completed finite cross-Gram matrix and Loewner quadratic

`BF4CompletedFiniteGramLimitBridge` proves that every literal finite cutoff
Gram quadratic converges to a manifest positive completed sum of squares.
This module exposes the completed matrix whose quadratic form that limit is.

For supplied completed half-amplitudes `A(state, channel)`, define

    K(left,right) =
      sum_channel weight(channel) * A(left,channel) * A(right,channel).

Using shared bounds on the cutoff and completed half-amplitudes, the literal
rational cutoff Gram entries converge entrywise to `K`.  Finite signed
coefficient sums then show that the literal cutoff matrix quadratic converges
to the quadratic formed from the completed cross entries.

The same cutoff quadratic already converges to the manifest completed SOS.
Constructive uniqueness of limits therefore proves that the completed matrix
quadratic is `CReal.Equiv` to the completed SOS, for every finite state list
and every signed rational coefficient function.  This is the honest finite
Loewner/Gram statement: the completed matrix is positive on every supplied
finite rational test vector.

Crucial fence: all half-amplitudes and their bounds/convergence remain supplied
data.  No theorem identifies them with the interacting physical BF4 slab
amplitudes, and scalar Harnack order is not used to manufacture the Gram
factorization.

## Axiom gate

Only finite-list algebra, constructive limit uniqueness, and exact rational
bounds are used.  There is no `Classical.*`, `Real`, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.BF4CompletedFiniteGramLimitBridge

namespace YMGap.Continuum.BF4CompletedCrossGramMatrixLimit

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4CompletedConditionalGramLimitBridge
open YMGap.Continuum.BF4CompletedConditionalLimitBridge
open YMGap.Continuum.BF4CompletedFiniteGramLimitBridge
open YMGap.Continuum.BF4CompletedRetainedConditionalOrder
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

/-! ## 1. Completed cross entries and their finite bound -/

/-- Completed cross-Gram entry formed from the supplied channel
half-amplitudes. -/
def completedCrossGramEntry
    {State Channel : Type}
    (channels : List Channel)
    (channelWeight : Channel → Q')
    (completedAmplitude : State → Channel → CReal)
    (left right : State) : CReal :=
  completedWeightedQuadraticPathSum
    channels channelWeight
    (fun channel =>
      CReal.mul
        (completedAmplitude left channel)
        (completedAmplitude right channel))

/-- Common finite absolute bound for completed cross entries when every
half-amplitude is bounded by `amplitudeBound`. -/
def finiteCrossGramEntryBound
    {Channel : Type}
    (channels : List Channel)
    (channelWeight : Channel → Q')
    (amplitudeBound : Q') : Q' :=
  listQSum
    (fun channel =>
      Q'.abs (channelWeight channel) *
        (amplitudeBound * amplitudeBound))
    channels

theorem finiteCrossGramEntryBound_nonnegative
    {Channel : Type}
    (channelWeight : Channel → Q')
    (amplitudeBound : Q')
    (amplitudeBound_nonnegative :
      (0 : Q') ≤ amplitudeBound) :
    ∀ channels : List Channel,
      (0 : Q') ≤
        finiteCrossGramEntryBound
          channels channelWeight amplitudeBound
  | [] => Q'.le_refl' 0
  | channel :: tail =>
      Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _
          (Q'.abs_nonneg (channelWeight channel))
          (Q'.mul_nonneg _ _
            amplitudeBound_nonnegative
            amplitudeBound_nonnegative))
        (finiteCrossGramEntryBound_nonnegative
          channelWeight amplitudeBound
          amplitudeBound_nonnegative tail)

private theorem completedCrossProduct_abs_le
    {State Channel : Type}
    (completedAmplitude : State → Channel → CReal)
    (amplitudeBound : Q')
    (amplitudeBound_nonnegative :
      (0 : Q') ≤ amplitudeBound)
    (left right : State) (channel : Channel)
    (leftBound :
      ∀ approximation,
        Q'.abs
            ((completedAmplitude
              left channel).approx approximation) ≤
          amplitudeBound)
    (rightBound :
      ∀ approximation,
        Q'.abs
            ((completedAmplitude
              right channel).approx approximation) ≤
          amplitudeBound)
    (approximation : Nat) :
    Q'.abs
        ((CReal.mul
          (completedAmplitude left channel)
          (completedAmplitude right channel)).approx approximation) ≤
      amplitudeBound * amplitudeBound := by
  change
    Q'.abs
        ((completedAmplitude left channel).approx approximation *
          (completedAmplitude right channel).approx approximation) ≤
      amplitudeBound * amplitudeBound
  refine Q'.le_trans' _ _ _
    (ExpNeg.abs_mul_le
      ((completedAmplitude left channel).approx approximation)
      ((completedAmplitude right channel).approx approximation)) ?_
  exact Q'.mul_le_mul_of_nonneg
    (leftBound approximation)
    (rightBound approximation)
    amplitudeBound_nonnegative
    (Q'.abs_nonneg
      ((completedAmplitude right channel).approx approximation))

/-- Every approximation of a completed cross entry obeys the explicit finite
channel bound. -/
theorem completedCrossGramEntry_abs_approx_le
    {State Channel : Type}
    (channelWeight : Channel → Q')
    (completedAmplitude : State → Channel → CReal)
    (amplitudeBound : Q')
    (amplitudeBound_nonnegative :
      (0 : Q') ≤ amplitudeBound)
    (left right : State) :
    ∀ channels : List Channel,
      (∀ channel, channel ∈ channels →
        ∀ approximation,
          Q'.abs
              ((completedAmplitude
                left channel).approx approximation) ≤
            amplitudeBound) →
      (∀ channel, channel ∈ channels →
        ∀ approximation,
          Q'.abs
              ((completedAmplitude
                right channel).approx approximation) ≤
            amplitudeBound) →
      ∀ approximation,
        Q'.abs
            ((completedCrossGramEntry
              channels channelWeight completedAmplitude
              left right).approx approximation) ≤
          finiteCrossGramEntryBound
            channels channelWeight amplitudeBound
  | [], _, _, approximation => by
      change Q'.abs 0 ≤ 0
      rw [ExpNeg.abs_of_nonneg (Q'.le_refl' 0)]
      exact Q'.le_refl' 0
  | channel :: tail, leftBound, rightBound, approximation => by
      change
        Q'.abs
            (channelWeight channel *
                ((completedAmplitude
                    left channel).approx approximation *
                  (completedAmplitude
                    right channel).approx approximation) +
              (completedCrossGramEntry
                tail channelWeight completedAmplitude
                left right).approx approximation) ≤
          Q'.abs (channelWeight channel) *
              (amplitudeBound * amplitudeBound) +
            finiteCrossGramEntryBound
              tail channelWeight amplitudeBound
      refine Q'.le_trans' _ _ _
        (ExpNeg.abs_add_le
          (channelWeight channel *
            ((completedAmplitude
                left channel).approx approximation *
              (completedAmplitude
                right channel).approx approximation))
          ((completedCrossGramEntry
            tail channelWeight completedAmplitude
            left right).approx approximation)) ?_
      apply Q'.add_le_add
      · refine Q'.le_trans' _ _ _
          (ExpNeg.abs_mul_le
            (channelWeight channel)
            ((completedAmplitude
                left channel).approx approximation *
              (completedAmplitude
                right channel).approx approximation)) ?_
        exact Q'.mul_le_mul_of_nonneg_left
          _ _ _
          (completedCrossProduct_abs_le
            completedAmplitude
            amplitudeBound amplitudeBound_nonnegative
            left right channel
            (leftBound channel List.mem_cons_self)
            (rightBound channel List.mem_cons_self)
            approximation)
          (Q'.abs_nonneg (channelWeight channel))
      · exact completedCrossGramEntry_abs_approx_le
          channelWeight completedAmplitude
          amplitudeBound amplitudeBound_nonnegative
          left right tail
          (fun item hitem =>
            leftBound item
              (List.mem_cons_of_mem channel hitem))
          (fun item hitem =>
            rightBound item
              (List.mem_cons_of_mem channel hitem))
          approximation

/-! ## 2. Entrywise cutoff convergence -/

private theorem rationalCrossAmplitudeProduct_converges
    {State Channel : Type}
    (cutoffAmplitude : State → Channel → Nat → Q')
    (completedAmplitude : State → Channel → CReal)
    (amplitudeBound : Q')
    (amplitudeBound_nonnegative :
      (0 : Q') ≤ amplitudeBound)
    (left right : State) (channel : Channel)
    (leftCutoffBound :
      ∀ cutoff,
        Q'.abs
            (cutoffAmplitude left channel cutoff) ≤
          amplitudeBound)
    (rightCompletedBound :
      ∀ approximation,
        Q'.abs
            ((completedAmplitude
              right channel).approx approximation) ≤
          amplitudeBound)
    (leftConverges :
      CReal.ConvergesTo
        (fun cutoff =>
          CReal.ofQ'
            (cutoffAmplitude left channel cutoff))
        (completedAmplitude left channel))
    (rightConverges :
      CReal.ConvergesTo
        (fun cutoff =>
          CReal.ofQ'
            (cutoffAmplitude right channel cutoff))
        (completedAmplitude right channel)) :
    CReal.ConvergesTo
      (fun cutoff =>
        CReal.ofQ'
          (cutoffAmplitude left channel cutoff *
            cutoffAmplitude right channel cutoff))
      (CReal.mul
        (completedAmplitude left channel)
        (completedAmplitude right channel)) := by
  have multipliedConverges :
      CReal.ConvergesTo
        (fun cutoff =>
          CReal.mul
            (CReal.ofQ'
              (cutoffAmplitude left channel cutoff))
            (CReal.ofQ'
              (cutoffAmplitude right channel cutoff)))
        (CReal.mul
          (completedAmplitude left channel)
          (completedAmplitude right channel)) :=
    CReal.convergesTo_mul
      amplitudeBound_nonnegative
      (fun cutoff approximation =>
        leftCutoffBound cutoff)
      rightCompletedBound
      leftConverges rightConverges
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s :=
      fun cutoff =>
        CReal.mul
          (CReal.ofQ'
            (cutoffAmplitude left channel cutoff))
          (CReal.ofQ'
            (cutoffAmplitude right channel cutoff)))
  · intro cutoff
    exact CReal.Equiv.symm
      (CRealAlg.ofQ'_mul
        (cutoffAmplitude left channel cutoff)
        (cutoffAmplitude right channel cutoff))
  · exact multipliedConverges

private theorem rationalWeightedCross_eq_weightedGram
    {State Channel : Type}
    (channels : List Channel)
    (channelWeight : Channel → Q')
    (cutoffAmplitude : State → Channel → Nat → Q')
    (left right : State) (cutoff : Nat) :
    rationalWeightedQuadraticPathSum
        channels channelWeight
        (fun channel cutoff' =>
          cutoffAmplitude left channel cutoff' *
            cutoffAmplitude right channel cutoff')
        cutoff =
      weightedGram
        channels channelWeight
        (fun state channel =>
          cutoffAmplitude state channel cutoff)
        left right := by
  unfold rationalWeightedQuadraticPathSum
  unfold weightedGram
  rw [rationalPathSum_eq_listQSum]

/-- Literal cutoff cross-Gram entries converge to the completed cross-Gram
matrix, entry by entry. -/
theorem rationalCutoffCrossGramEntry_converges
    {State Channel : Type}
    (channels : List Channel)
    (channelWeight : Channel → Q')
    (channelWeight_nonnegative :
      ∀ channel, channel ∈ channels →
        (0 : Q') ≤ channelWeight channel)
    (cutoffAmplitude : State → Channel → Nat → Q')
    (completedAmplitude : State → Channel → CReal)
    (amplitudeBound : Q')
    (amplitudeBound_nonnegative :
      (0 : Q') ≤ amplitudeBound)
    (left right : State)
    (leftCutoffBound :
      ∀ channel, channel ∈ channels →
        ∀ cutoff,
          Q'.abs
              (cutoffAmplitude left channel cutoff) ≤
            amplitudeBound)
    (leftCompletedBound :
      ∀ channel, channel ∈ channels →
        ∀ approximation,
          Q'.abs
              ((completedAmplitude
                left channel).approx approximation) ≤
            amplitudeBound)
    (rightCompletedBound :
      ∀ channel, channel ∈ channels →
        ∀ approximation,
          Q'.abs
              ((completedAmplitude
                right channel).approx approximation) ≤
            amplitudeBound)
    (leftConverges :
      ∀ channel, channel ∈ channels →
        CReal.ConvergesTo
          (fun cutoff =>
            CReal.ofQ'
              (cutoffAmplitude left channel cutoff))
          (completedAmplitude left channel))
    (rightConverges :
      ∀ channel, channel ∈ channels →
        CReal.ConvergesTo
          (fun cutoff =>
            CReal.ofQ'
              (cutoffAmplitude right channel cutoff))
          (completedAmplitude right channel)) :
    CReal.ConvergesTo
      (fun cutoff =>
        CReal.ofQ'
          (weightedGram
            channels channelWeight
            (fun state channel =>
              cutoffAmplitude state channel cutoff)
            left right))
      (completedCrossGramEntry
        channels channelWeight completedAmplitude
        left right) := by
  have hweighted :=
    rationalWeightedQuadraticPathSum_converges
      channels channelWeight channelWeight_nonnegative
      (fun channel cutoff =>
        cutoffAmplitude left channel cutoff *
          cutoffAmplitude right channel cutoff)
      (fun channel =>
        CReal.mul
          (completedAmplitude left channel)
          (completedAmplitude right channel))
      (amplitudeBound * amplitudeBound)
      (Q'.mul_nonneg _ _
        amplitudeBound_nonnegative
        amplitudeBound_nonnegative)
      (fun channel hchannel approximation =>
        completedCrossProduct_abs_le
          completedAmplitude
          amplitudeBound amplitudeBound_nonnegative
          left right channel
          (leftCompletedBound channel hchannel)
          (rightCompletedBound channel hchannel)
          approximation)
      (fun channel hchannel =>
        rationalCrossAmplitudeProduct_converges
          cutoffAmplitude completedAmplitude
          amplitudeBound amplitudeBound_nonnegative
          left right channel
          (leftCutoffBound channel hchannel)
          (rightCompletedBound channel hchannel)
          (leftConverges channel hchannel)
          (rightConverges channel hchannel))
  unfold completedCrossGramEntry
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s :=
      fun cutoff =>
        CReal.ofQ'
          (rationalWeightedQuadraticPathSum
            channels channelWeight
            (fun channel cutoff' =>
              cutoffAmplitude left channel cutoff' *
                cutoffAmplitude right channel cutoff')
            cutoff))
  · intro cutoff
    apply SumOfSquares.Equiv_of_approx_eqv
    intro approximation
    rw [rationalWeightedCross_eq_weightedGram]
    exact Q'.eqv_refl _
  · exact hweighted

/-! ## 3. The completed finite matrix quadratic -/

/-- Finite signed quadratic formed from the completed cross-Gram entries. -/
def completedCrossGramQuadratic
    {State Channel : Type}
    (states : List State)
    (channels : List Channel)
    (channelWeight : Channel → Q')
    (completedAmplitude : State → Channel → CReal)
    (coefficient : State → Q') : CReal :=
  completedPathSum
    (fun left =>
      completedPathSum
        (fun right =>
          CReal.mul
            (CReal.ofQ'
              (coefficient left * coefficient right))
            (completedCrossGramEntry
              channels channelWeight completedAmplitude
              left right))
        states)
    states

private theorem convergesTo_const (value : CReal) :
    CReal.ConvergesTo (fun _ => value) value := by
  intro ε hε
  refine ⟨0, fun _ _ => ⟨0, fun approximation _ => ⟨?_, ?_⟩⟩⟩
  · exact Q'.add_le_self_of_nonneg
      (value.approx approximation) ε (Q'.le_of_lt hε)
  · exact Q'.add_le_self_of_nonneg
      (value.approx approximation) ε (Q'.le_of_lt hε)

private theorem signedScaleSequence_converges
    (scale : Q')
    (sequence : Nat → Q')
    (limit : CReal)
    (limitBound : Q')
    (limitBound_nonnegative :
      (0 : Q') ≤ limitBound)
    (limit_abs_bound :
      ∀ approximation,
        Q'.abs (limit.approx approximation) ≤
          limitBound)
    (sequenceConverges :
      CReal.ConvergesTo
        (fun cutoff => CReal.ofQ' (sequence cutoff))
        limit) :
    CReal.ConvergesTo
      (fun cutoff =>
        CReal.ofQ' (scale * sequence cutoff))
      (CReal.mul (CReal.ofQ' scale) limit) := by
  let commonBound : Q' :=
    Q'.max' (Q'.abs scale) limitBound
  have commonBound_nonnegative :
      (0 : Q') ≤ commonBound :=
    Q'.le_trans' _ _ _
      limitBound_nonnegative
      (Q'.le_max'_right (Q'.abs scale) limitBound)
  have scaleBound :
      ∀ cutoff approximation : Nat,
        Q'.abs
            ((CReal.ofQ' scale).approx approximation) ≤
          commonBound := by
    intro cutoff approximation
    change Q'.abs scale ≤ commonBound
    exact Q'.le_max'_left (Q'.abs scale) limitBound
  have targetBound :
      ∀ approximation,
        Q'.abs (limit.approx approximation) ≤
          commonBound := by
    intro approximation
    exact Q'.le_trans' _ _ _
      (limit_abs_bound approximation)
      (Q'.le_max'_right (Q'.abs scale) limitBound)
  have multipliedConverges :
      CReal.ConvergesTo
        (fun cutoff =>
          CReal.mul
            (CReal.ofQ' scale)
            (CReal.ofQ' (sequence cutoff)))
        (CReal.mul (CReal.ofQ' scale) limit) :=
    CReal.convergesTo_mul
      commonBound_nonnegative
      scaleBound targetBound
      (convergesTo_const (CReal.ofQ' scale))
      sequenceConverges
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s :=
      fun cutoff =>
        CReal.mul
          (CReal.ofQ' scale)
          (CReal.ofQ' (sequence cutoff)))
  · intro cutoff
    exact CReal.Equiv.symm
      (CRealAlg.ofQ'_mul scale (sequence cutoff))
  · exact multipliedConverges

/-- The literal cutoff finite Gram matrix quadratic converges to the
quadratic formed entrywise from the completed cross-Gram matrix. -/
theorem rationalCutoffCrossGramQuadratic_converges
    {State Channel : Type}
    (states : List State)
    (channels : List Channel)
    (channelWeight : Channel → Q')
    (channelWeight_nonnegative :
      ∀ channel, channel ∈ channels →
        (0 : Q') ≤ channelWeight channel)
    (coefficient : State → Q')
    (cutoffAmplitude : State → Channel → Nat → Q')
    (completedAmplitude : State → Channel → CReal)
    (amplitudeBound : Q')
    (amplitudeBound_nonnegative :
      (0 : Q') ≤ amplitudeBound)
    (cutoffAmplitudeBound :
      ∀ state, state ∈ states →
        ∀ channel, channel ∈ channels →
          ∀ cutoff,
            Q'.abs
                (cutoffAmplitude state channel cutoff) ≤
              amplitudeBound)
    (completedAmplitudeBound :
      ∀ state, state ∈ states →
        ∀ channel, channel ∈ channels →
          ∀ approximation,
            Q'.abs
                ((completedAmplitude
                  state channel).approx approximation) ≤
              amplitudeBound)
    (amplitudeConverges :
      ∀ state, state ∈ states →
        ∀ channel, channel ∈ channels →
          CReal.ConvergesTo
            (fun cutoff =>
              CReal.ofQ'
                (cutoffAmplitude
                  state channel cutoff))
            (completedAmplitude state channel)) :
    CReal.ConvergesTo
      (fun cutoff =>
        CReal.ofQ'
          (rationalCutoffFiniteGramQuadratic
            states channels channelWeight
            coefficient cutoffAmplitude cutoff))
      (completedCrossGramQuadratic
        states channels channelWeight
        completedAmplitude coefficient) := by
  let entryBound : Q' :=
    finiteCrossGramEntryBound
      channels channelWeight amplitudeBound
  have entryBound_nonnegative :
      (0 : Q') ≤ entryBound :=
    finiteCrossGramEntryBound_nonnegative
      channelWeight amplitudeBound
      amplitudeBound_nonnegative channels
  have entryConverges :
      ∀ left, left ∈ states →
        ∀ right, right ∈ states →
          CReal.ConvergesTo
            (fun cutoff =>
              CReal.ofQ'
                (weightedGram
                  channels channelWeight
                  (fun state channel =>
                    cutoffAmplitude state channel cutoff)
                  left right))
            (completedCrossGramEntry
              channels channelWeight completedAmplitude
              left right) := by
    intro left hleft right hright
    exact rationalCutoffCrossGramEntry_converges
      channels channelWeight channelWeight_nonnegative
      cutoffAmplitude completedAmplitude
      amplitudeBound amplitudeBound_nonnegative
      left right
      (fun channel hchannel cutoff =>
        cutoffAmplitudeBound left hleft
          channel hchannel cutoff)
      (fun channel hchannel approximation =>
        completedAmplitudeBound left hleft
          channel hchannel approximation)
      (fun channel hchannel approximation =>
        completedAmplitudeBound right hright
          channel hchannel approximation)
      (fun channel hchannel =>
        amplitudeConverges left hleft
          channel hchannel)
      (fun channel hchannel =>
        amplitudeConverges right hright
          channel hchannel)
  have entryAbsBound :
      ∀ left, left ∈ states →
        ∀ right, right ∈ states →
          ∀ approximation,
            Q'.abs
                ((completedCrossGramEntry
                  channels channelWeight completedAmplitude
                  left right).approx approximation) ≤
              entryBound := by
    intro left hleft right hright approximation
    exact completedCrossGramEntry_abs_approx_le
      channelWeight completedAmplitude
      amplitudeBound amplitudeBound_nonnegative
      left right channels
      (fun channel hchannel itemApproximation =>
        completedAmplitudeBound left hleft
          channel hchannel itemApproximation)
      (fun channel hchannel itemApproximation =>
        completedAmplitudeBound right hright
          channel hchannel itemApproximation)
      approximation
  let rationalRow :
      State → Nat → Q' :=
    fun left cutoff =>
      listQSum
        (fun right =>
          (coefficient left * coefficient right) *
            weightedGram
              channels channelWeight
              (fun state channel =>
                cutoffAmplitude state channel cutoff)
              left right)
        states
  let completedRow :
      State → CReal :=
    fun left =>
      completedPathSum
        (fun right =>
          CReal.mul
            (CReal.ofQ'
              (coefficient left * coefficient right))
            (completedCrossGramEntry
              channels channelWeight completedAmplitude
              left right))
        states
  have rowConverges :
      ∀ left, left ∈ states →
        CReal.ConvergesTo
          (fun cutoff => CReal.ofQ' (rationalRow left cutoff))
          (completedRow left) := by
    intro left hleft
    have hsum :=
      rationalPathSum_converges
        (fun right cutoff =>
          (coefficient left * coefficient right) *
            weightedGram
              channels channelWeight
              (fun state channel =>
                cutoffAmplitude state channel cutoff)
              left right)
        (fun right =>
          CReal.mul
            (CReal.ofQ'
              (coefficient left * coefficient right))
            (completedCrossGramEntry
              channels channelWeight completedAmplitude
              left right))
        states
        (fun right hright =>
          signedScaleSequence_converges
            (coefficient left * coefficient right)
            (fun cutoff =>
              weightedGram
                channels channelWeight
                (fun state channel =>
                  cutoffAmplitude state channel cutoff)
                left right)
            (completedCrossGramEntry
              channels channelWeight completedAmplitude
              left right)
            entryBound entryBound_nonnegative
            (entryAbsBound left hleft right hright)
            (entryConverges left hleft right hright))
    unfold rationalRow
    unfold completedRow
    simpa only [rationalPathSum_eq_listQSum] using hsum
  have houter :=
    rationalPathSum_converges
      rationalRow completedRow states rowConverges
  unfold rationalCutoffFiniteGramQuadratic
  unfold weightedGramQuadratic
  unfold completedCrossGramQuadratic
  simpa only [rationalPathSum_eq_listQSum] using houter

/-! ## 4. Completed Gram-to-SOS identity and positivity -/

/-- The completed finite matrix quadratic is equivalent to the manifest
completed weighted sum of channel squares.  Both are limits of the exact same
literal cutoff Gram quadratic. -/
theorem completedCrossGramQuadratic_equiv_completedFiniteGramSOS
    {State Channel : Type}
    (states : List State)
    (channels : List Channel)
    (channelWeight : Channel → Q')
    (channelWeight_nonnegative :
      ∀ channel, channel ∈ channels →
        (0 : Q') ≤ channelWeight channel)
    (coefficient : State → Q')
    (cutoffAmplitude : State → Channel → Nat → Q')
    (completedAmplitude : State → Channel → CReal)
    (amplitudeBound : Q')
    (amplitudeBound_nonnegative :
      (0 : Q') ≤ amplitudeBound)
    (cutoffAmplitudeBound :
      ∀ state, state ∈ states →
        ∀ channel, channel ∈ channels →
          ∀ cutoff,
            Q'.abs
                (cutoffAmplitude state channel cutoff) ≤
              amplitudeBound)
    (completedAmplitudeBound :
      ∀ state, state ∈ states →
        ∀ channel, channel ∈ channels →
          ∀ approximation,
            Q'.abs
                ((completedAmplitude
                  state channel).approx approximation) ≤
              amplitudeBound)
    (amplitudeConverges :
      ∀ state, state ∈ states →
        ∀ channel, channel ∈ channels →
          CReal.ConvergesTo
            (fun cutoff =>
              CReal.ofQ'
                (cutoffAmplitude
                  state channel cutoff))
            (completedAmplitude state channel)) :
    CReal.Equiv
      (completedCrossGramQuadratic
        states channels channelWeight
        completedAmplitude coefficient)
      (completedFiniteGramSOS
        states channels channelWeight
        coefficient completedAmplitude) := by
  let cutoffSequence : Nat → CReal :=
    fun cutoff =>
      CReal.ofQ'
        (rationalCutoffFiniteGramQuadratic
          states channels channelWeight
          coefficient cutoffAmplitude cutoff)
  have hcross :
      CReal.ConvergesTo
        cutoffSequence
        (completedCrossGramQuadratic
          states channels channelWeight
          completedAmplitude coefficient) :=
    rationalCutoffCrossGramQuadratic_converges
      states channels
      channelWeight channelWeight_nonnegative
      coefficient cutoffAmplitude completedAmplitude
      amplitudeBound amplitudeBound_nonnegative
      cutoffAmplitudeBound completedAmplitudeBound
      amplitudeConverges
  have hsos :
      CReal.ConvergesTo
        cutoffSequence
        (completedFiniteGramSOS
          states channels channelWeight
          coefficient completedAmplitude) :=
    (finiteGramLimitCertificate
      states channels
      channelWeight channelWeight_nonnegative
      coefficient cutoffAmplitude completedAmplitude
      amplitudeBound amplitudeBound_nonnegative
      cutoffAmplitudeBound completedAmplitudeBound
      amplitudeConverges).convergence
  exact CReal.Equiv_of_limit_of_equal
    (fun cutoff =>
      SumOfSquares.Equiv_of_approx_eqv
        (fun approximation => Q'.eqv_refl _))
    hcross hsos

/-- Honest finite completed Loewner/Gram positivity: every finite rational
coefficient vector has a nonnegative completed cross-matrix quadratic. -/
theorem completedCrossGramQuadratic_nonnegative
    {State Channel : Type}
    (states : List State)
    (channels : List Channel)
    (channelWeight : Channel → Q')
    (channelWeight_nonnegative :
      ∀ channel, channel ∈ channels →
        (0 : Q') ≤ channelWeight channel)
    (coefficient : State → Q')
    (cutoffAmplitude : State → Channel → Nat → Q')
    (completedAmplitude : State → Channel → CReal)
    (amplitudeBound : Q')
    (amplitudeBound_nonnegative :
      (0 : Q') ≤ amplitudeBound)
    (cutoffAmplitudeBound :
      ∀ state, state ∈ states →
        ∀ channel, channel ∈ channels →
          ∀ cutoff,
            Q'.abs
                (cutoffAmplitude state channel cutoff) ≤
              amplitudeBound)
    (completedAmplitudeBound :
      ∀ state, state ∈ states →
        ∀ channel, channel ∈ channels →
          ∀ approximation,
            Q'.abs
                ((completedAmplitude
                  state channel).approx approximation) ≤
              amplitudeBound)
    (amplitudeConverges :
      ∀ state, state ∈ states →
        ∀ channel, channel ∈ channels →
          CReal.ConvergesTo
            (fun cutoff =>
              CReal.ofQ'
                (cutoffAmplitude
                  state channel cutoff))
            (completedAmplitude state channel)) :
    ExpPos.geRat
      (completedCrossGramQuadratic
        states channels channelWeight
        completedAmplitude coefficient)
      0 := by
  have hequiv :=
    completedCrossGramQuadratic_equiv_completedFiniteGramSOS
      states channels
      channelWeight channelWeight_nonnegative
      coefficient cutoffAmplitude completedAmplitude
      amplitudeBound amplitudeBound_nonnegative
      cutoffAmplitudeBound completedAmplitudeBound
      amplitudeConverges
  have hsos :=
    (finiteGramLimitCertificate
      states channels
      channelWeight channelWeight_nonnegative
      coefficient cutoffAmplitude completedAmplitude
      amplitudeBound amplitudeBound_nonnegative
      cutoffAmplitudeBound completedAmplitudeBound
      amplitudeConverges).completedNonnegative
  exact SU3CharFactor.geRat_of_equiv hequiv hsos

end YMGap.Continuum.BF4CompletedCrossGramMatrixLimit

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4CompletedCrossGramMatrixLimit.rationalCutoffCrossGramEntry_converges
#print axioms YMGap.Continuum.BF4CompletedCrossGramMatrixLimit.rationalCutoffCrossGramQuadratic_converges
#print axioms YMGap.Continuum.BF4CompletedCrossGramMatrixLimit.completedCrossGramQuadratic_equiv_completedFiniteGramSOS
#print axioms YMGap.Continuum.BF4CompletedCrossGramMatrixLimit.completedCrossGramQuadratic_nonnegative
