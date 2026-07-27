/-
# Finite signed Gram quadratics survive cutoff removal

This module lifts `FiniteWeightedGramSOS` through the constructive cutoff
limit.  The input consists of:

* a finite state list and a finite channel list;
* signed rational test coefficients on the states;
* nonnegative rational channel weights;
* rational cutoff half-amplitudes and completed `CReal` half-amplitudes;
* explicit uniform cutoff/completed amplitude bounds and factorwise
  convergence.

For every channel, the signed state coefficients are first combined into a
finite channel-linear half-amplitude.  These linear forms converge and have an
explicit finite absolute bound.  They are then squared and summed with the
nonnegative channel weights.  The exact finite Gram-to-SOS identity transports
the resulting cutoff convergence from the manifest sum of squares to the
literal finite Gram quadratic.

The final Type-level certificate contains:

* nonnegativity of every literal rational cutoff Gram quadratic;
* convergence of those cutoff Gram quadratics;
* nonnegativity of the completed weighted sum of channel squares.

Crucial fence: the theorem constructs a genuine finite Gram from supplied
half-amplitudes, but does not identify those amplitudes with the physical BF4
slab law.  It does not infer a Gram/Loewner statement from scalar entrywise
Harnack bounds.

## Axiom gate

Only finite-list algebra, exact rational bounds, and constructive `CReal`
limit operations are used.  There is no `Classical.*`, `Real`,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.BF4CompletedRankOneGramLimitBridge
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.BF4CompletedFiniteGramLimitBridge

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4CompletedConditionalGramLimitBridge
open YMGap.Continuum.BF4CompletedConditionalLimitBridge
open YMGap.Continuum.BF4CompletedRetainedConditionalOrder
open YMGap.Continuum.BF4CompletedRankOneGramLimitBridge
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

/-! ## 1. Exact list-sum compatibility -/

/-- The rational list sum used by the cutoff-limit layer is definitionally
the same fold as the one used by `FiniteWeightedGramSOS`. -/
theorem rationalPathSum_eq_listQSum
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      rationalPathSum value items =
        listQSum value items
  | [] => rfl
  | item :: tail => by
      change
        value item + rationalPathSum value tail =
          value item + listQSum value tail
      rw [rationalPathSum_eq_listQSum value tail]

/-! ## 2. Cutoff and completed channel-linear half-amplitudes -/

/-- Signed finite state combination of cutoff half-amplitudes in one
channel. -/
def rationalCutoffChannelLinear
    {State Channel : Type}
    (states : List State)
    (coefficient : State → Q')
    (cutoffAmplitude : State → Channel → Nat → Q')
    (channel : Channel) (cutoff : Nat) : Q' :=
  listQSum
    (fun state =>
      coefficient state *
        cutoffAmplitude state channel cutoff)
    states

/-- The corresponding completed signed finite state combination. -/
def completedChannelLinear
    {State Channel : Type}
    (states : List State)
    (coefficient : State → Q')
    (completedAmplitude : State → Channel → CReal)
    (channel : Channel) : CReal :=
  completedPathSum
    (fun state =>
      CReal.mul
        (CReal.ofQ' (coefficient state))
        (completedAmplitude state channel))
    states

/-- Explicit finite absolute bound for every channel-linear form when all
half-amplitudes are bounded by `amplitudeBound`. -/
def finiteChannelLinearBound
    {State : Type}
    (states : List State)
    (coefficient : State → Q')
    (amplitudeBound : Q') : Q' :=
  listQSum
    (fun state =>
      Q'.abs (coefficient state) * amplitudeBound)
    states

theorem finiteChannelLinearBound_nonnegative
    {State : Type}
    (coefficient : State → Q')
    (amplitudeBound : Q')
    (amplitudeBound_nonnegative :
      (0 : Q') ≤ amplitudeBound) :
    ∀ states : List State,
      (0 : Q') ≤
        finiteChannelLinearBound
          states coefficient amplitudeBound
  | [] => Q'.le_refl' 0
  | state :: tail =>
      Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _
          (Q'.abs_nonneg (coefficient state))
          amplitudeBound_nonnegative)
        (finiteChannelLinearBound_nonnegative
          coefficient amplitudeBound
          amplitudeBound_nonnegative tail)

/-- A finite signed rational channel-linear form is bounded by the sum of the
absolute coefficient bounds. -/
theorem rationalCutoffChannelLinear_abs_le
    {State Channel : Type}
    (coefficient : State → Q')
    (cutoffAmplitude : State → Channel → Nat → Q')
    (amplitudeBound : Q')
    (amplitudeBound_nonnegative :
      (0 : Q') ≤ amplitudeBound)
    (channel : Channel) :
    ∀ states : List State,
      (∀ state, state ∈ states →
        ∀ cutoff,
          Q'.abs
              (cutoffAmplitude state channel cutoff) ≤
            amplitudeBound) →
      ∀ cutoff,
        Q'.abs
            (rationalCutoffChannelLinear
              states coefficient cutoffAmplitude
              channel cutoff) ≤
          finiteChannelLinearBound
            states coefficient amplitudeBound
  | [], _, cutoff => by
      change Q'.abs 0 ≤ 0
      rw [ExpNeg.abs_of_nonneg (Q'.le_refl' 0)]
      exact Q'.le_refl' 0
  | state :: tail, cutoffAmplitudeBound, cutoff => by
      change
        Q'.abs
            (coefficient state *
                cutoffAmplitude state channel cutoff +
              rationalCutoffChannelLinear
                tail coefficient cutoffAmplitude
                channel cutoff) ≤
          Q'.abs (coefficient state) * amplitudeBound +
            finiteChannelLinearBound
              tail coefficient amplitudeBound
      refine Q'.le_trans' _ _ _
        (ExpNeg.abs_add_le
          (coefficient state *
            cutoffAmplitude state channel cutoff)
          (rationalCutoffChannelLinear
            tail coefficient cutoffAmplitude
            channel cutoff)) ?_
      apply Q'.add_le_add
      · refine Q'.le_trans' _ _ _
          (ExpNeg.abs_mul_le
            (coefficient state)
            (cutoffAmplitude state channel cutoff)) ?_
        exact Q'.mul_le_mul_of_nonneg_left
          _ _ _
          (cutoffAmplitudeBound
            state List.mem_cons_self
            cutoff)
          (Q'.abs_nonneg (coefficient state))
      · exact rationalCutoffChannelLinear_abs_le
          coefficient cutoffAmplitude
          amplitudeBound amplitudeBound_nonnegative
          channel
          tail
          (fun item hitem =>
            cutoffAmplitudeBound item
              (List.mem_cons_of_mem state hitem))
          cutoff

/-- The same finite bound controls every approximation of the completed
channel-linear form. -/
theorem completedChannelLinear_abs_approx_le
    {State Channel : Type}
    (coefficient : State → Q')
    (completedAmplitude : State → Channel → CReal)
    (amplitudeBound : Q')
    (amplitudeBound_nonnegative :
      (0 : Q') ≤ amplitudeBound)
    (channel : Channel) :
    ∀ states : List State,
      (∀ state, state ∈ states →
        ∀ approximation,
          Q'.abs
              ((completedAmplitude
                state channel).approx approximation) ≤
            amplitudeBound) →
      ∀ approximation,
        Q'.abs
            ((completedChannelLinear
              states coefficient completedAmplitude
              channel).approx approximation) ≤
          finiteChannelLinearBound
            states coefficient amplitudeBound
  | [], _, approximation => by
      change Q'.abs 0 ≤ 0
      rw [ExpNeg.abs_of_nonneg (Q'.le_refl' 0)]
      exact Q'.le_refl' 0
  | state :: tail, completedAmplitudeBound, approximation => by
      change
        Q'.abs
            (coefficient state *
                (completedAmplitude
                  state channel).approx approximation +
              (completedChannelLinear
                tail coefficient completedAmplitude
                channel).approx approximation) ≤
          Q'.abs (coefficient state) * amplitudeBound +
            finiteChannelLinearBound
              tail coefficient amplitudeBound
      refine Q'.le_trans' _ _ _
        (ExpNeg.abs_add_le
          (coefficient state *
            (completedAmplitude
              state channel).approx approximation)
          ((completedChannelLinear
            tail coefficient completedAmplitude
            channel).approx approximation)) ?_
      apply Q'.add_le_add
      · refine Q'.le_trans' _ _ _
          (ExpNeg.abs_mul_le
            (coefficient state)
            ((completedAmplitude
              state channel).approx approximation)) ?_
        exact Q'.mul_le_mul_of_nonneg_left
          _ _ _
          (completedAmplitudeBound
            state List.mem_cons_self
            approximation)
          (Q'.abs_nonneg (coefficient state))
      · exact completedChannelLinear_abs_approx_le
          coefficient completedAmplitude
          amplitudeBound amplitudeBound_nonnegative
          channel
          tail
          (fun item hitem =>
            completedAmplitudeBound item
              (List.mem_cons_of_mem state hitem))
          approximation

/-! ## 3. Signed channel-linear convergence -/

private theorem convergesTo_const (value : CReal) :
    CReal.ConvergesTo (fun _ => value) value := by
  intro ε hε
  refine ⟨0, fun _ _ => ⟨0, fun approximation _ => ⟨?_, ?_⟩⟩⟩
  · exact Q'.add_le_self_of_nonneg
      (value.approx approximation) ε (Q'.le_of_lt hε)
  · exact Q'.add_le_self_of_nonneg
      (value.approx approximation) ε (Q'.le_of_lt hε)

/-- Multiplication by one fixed signed rational coefficient preserves
half-amplitude convergence. -/
theorem signedScaledAmplitude_converges
    {State Channel : Type}
    (coefficient : State → Q')
    (cutoffAmplitude : State → Channel → Nat → Q')
    (completedAmplitude : State → Channel → CReal)
    (amplitudeBound : Q')
    (amplitudeBound_nonnegative :
      (0 : Q') ≤ amplitudeBound)
    (state : State) (channel : Channel)
    (completedAmplitudeBound :
      ∀ approximation,
        Q'.abs
            ((completedAmplitude
              state channel).approx approximation) ≤
          amplitudeBound)
    (amplitudeConverges :
      CReal.ConvergesTo
        (fun cutoff =>
          CReal.ofQ'
            (cutoffAmplitude state channel cutoff))
        (completedAmplitude state channel)) :
    CReal.ConvergesTo
      (fun cutoff =>
        CReal.ofQ'
          (coefficient state *
            cutoffAmplitude state channel cutoff))
      (CReal.mul
        (CReal.ofQ' (coefficient state))
        (completedAmplitude state channel)) := by
  let commonBound : Q' :=
    Q'.max' (Q'.abs (coefficient state)) amplitudeBound
  have commonBound_nonnegative :
      (0 : Q') ≤ commonBound :=
    Q'.le_trans' _ _ _
      amplitudeBound_nonnegative
      (Q'.le_max'_right
        (Q'.abs (coefficient state))
        amplitudeBound)
  have coefficientBound :
      ∀ cutoff approximation : Nat,
        Q'.abs
            ((CReal.ofQ'
              (coefficient state)).approx approximation) ≤
          commonBound := by
    intro cutoff approximation
    change Q'.abs (coefficient state) ≤ commonBound
    exact Q'.le_max'_left
      (Q'.abs (coefficient state))
      amplitudeBound
  have completedBound :
      ∀ approximation,
        Q'.abs
            ((completedAmplitude
              state channel).approx approximation) ≤
          commonBound := by
    intro approximation
    exact Q'.le_trans' _ _ _
      (completedAmplitudeBound approximation)
      (Q'.le_max'_right
        (Q'.abs (coefficient state))
        amplitudeBound)
  have multipliedConverges :
      CReal.ConvergesTo
        (fun cutoff =>
          CReal.mul
            (CReal.ofQ' (coefficient state))
            (CReal.ofQ'
              (cutoffAmplitude
                state channel cutoff)))
        (CReal.mul
          (CReal.ofQ' (coefficient state))
          (completedAmplitude state channel)) :=
    CReal.convergesTo_mul
      commonBound_nonnegative
      coefficientBound completedBound
      (convergesTo_const
        (CReal.ofQ' (coefficient state)))
      amplitudeConverges
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s :=
      fun cutoff =>
        CReal.mul
          (CReal.ofQ' (coefficient state))
          (CReal.ofQ'
            (cutoffAmplitude state channel cutoff)))
  · intro cutoff
    exact CReal.Equiv.symm
      (CRealAlg.ofQ'_mul
        (coefficient state)
        (cutoffAmplitude state channel cutoff))
  · exact multipliedConverges

/-- A finite signed state combination converges channel by channel. -/
theorem rationalCutoffChannelLinear_converges
    {State Channel : Type}
    (states : List State)
    (coefficient : State → Q')
    (cutoffAmplitude : State → Channel → Nat → Q')
    (completedAmplitude : State → Channel → CReal)
    (amplitudeBound : Q')
    (amplitudeBound_nonnegative :
      (0 : Q') ≤ amplitudeBound)
    (channel : Channel)
    (completedAmplitudeBound :
      ∀ state, state ∈ states →
        ∀ approximation,
          Q'.abs
              ((completedAmplitude
                state channel).approx approximation) ≤
            amplitudeBound)
    (amplitudeConverges :
      ∀ state, state ∈ states →
        CReal.ConvergesTo
          (fun cutoff =>
            CReal.ofQ'
              (cutoffAmplitude state channel cutoff))
          (completedAmplitude state channel)) :
    CReal.ConvergesTo
      (fun cutoff =>
        CReal.ofQ'
          (rationalCutoffChannelLinear
            states coefficient cutoffAmplitude
            channel cutoff))
      (completedChannelLinear
        states coefficient completedAmplitude
        channel) := by
  have hsum :=
    rationalPathSum_converges
      (fun state cutoff =>
        coefficient state *
          cutoffAmplitude state channel cutoff)
      (fun state =>
        CReal.mul
          (CReal.ofQ' (coefficient state))
          (completedAmplitude state channel))
      states
      (fun state hstate =>
        signedScaledAmplitude_converges
          coefficient cutoffAmplitude completedAmplitude
          amplitudeBound amplitudeBound_nonnegative
          state channel
          (completedAmplitudeBound
            state hstate)
          (amplitudeConverges
            state hstate))
  unfold rationalCutoffChannelLinear
  unfold completedChannelLinear
  simpa only [rationalPathSum_eq_listQSum] using hsum

/-! ## 4. Exact cutoff Gram and completed Gram/SOS -/

/-- Literal finite rational Gram quadratic at one common cutoff. -/
def rationalCutoffFiniteGramQuadratic
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (channelWeight : Channel → Q')
    (coefficient : State → Q')
    (cutoffAmplitude : State → Channel → Nat → Q')
    (cutoff : Nat) : Q' :=
  weightedGramQuadratic
    states channels channelWeight
    (fun state channel =>
      cutoffAmplitude state channel cutoff)
    coefficient

/-- Completed weighted sum of squared channel-linear forms. -/
def completedFiniteGramSOS
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (channelWeight : Channel → Q')
    (coefficient : State → Q')
    (completedAmplitude : State → Channel → CReal) : CReal :=
  completedWeightedQuadraticPathSum
    channels channelWeight
    (completedRankOnePathQuadratic
      (completedChannelLinear
        states coefficient completedAmplitude))

/-- The cutoff value used by the rank-one certificate is exactly the manifest
rational weighted Gram SOS. -/
theorem rationalWeightedChannelSquares_eq_weightedGramSOS
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (channelWeight : Channel → Q')
    (coefficient : State → Q')
    (cutoffAmplitude : State → Channel → Nat → Q')
    (cutoff : Nat) :
    rationalWeightedQuadraticPathSum
        channels channelWeight
        (rationalRankOnePathQuadratic
          (rationalCutoffChannelLinear
            states coefficient cutoffAmplitude))
        cutoff =
      weightedGramSOS
        states channels channelWeight
        (fun state channel =>
          cutoffAmplitude state channel cutoff)
        coefficient := by
  unfold rationalWeightedQuadraticPathSum
  rw [rationalPathSum_eq_listQSum]
  rfl

/-- Type-level cutoff/completed certificate for the literal finite Gram
quadratic, after transport through the exact Gram-to-SOS rearrangement. -/
def finiteGramLimitCertificate
    {State Channel : Type}
    (states : List State) (channels : List Channel)
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
                (cutoffAmplitude
                  state channel cutoff) ≤
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
    WeightedQuadraticGramLimitCertificate
      (rationalCutoffFiniteGramQuadratic
        states channels channelWeight
        coefficient cutoffAmplitude)
      (completedFiniteGramSOS
        states channels channelWeight
        coefficient completedAmplitude) := by
  let linearBound : Q' :=
    finiteChannelLinearBound
      states coefficient amplitudeBound
  have linearBound_nonnegative :
      (0 : Q') ≤ linearBound :=
    finiteChannelLinearBound_nonnegative
      coefficient amplitudeBound
      amplitudeBound_nonnegative states
  have rankCertificate :
      WeightedQuadraticGramLimitCertificate
        (rationalWeightedQuadraticPathSum
          channels channelWeight
          (rationalRankOnePathQuadratic
            (rationalCutoffChannelLinear
              states coefficient cutoffAmplitude)))
        (completedWeightedQuadraticPathSum
          channels channelWeight
          (completedRankOnePathQuadratic
            (completedChannelLinear
              states coefficient completedAmplitude))) :=
    weightedRankOneGramLimitCertificate
      channels channelWeight channelWeight_nonnegative
      (rationalCutoffChannelLinear
        states coefficient cutoffAmplitude)
      (completedChannelLinear
        states coefficient completedAmplitude)
      linearBound linearBound_nonnegative
      (fun channel hchannel cutoff =>
        rationalCutoffChannelLinear_abs_le
          coefficient cutoffAmplitude
          amplitudeBound amplitudeBound_nonnegative
          channel
          states
          (fun state hstate itemCutoff =>
            cutoffAmplitudeBound state
              hstate
              channel hchannel itemCutoff)
          cutoff)
      (fun channel hchannel approximation =>
        completedChannelLinear_abs_approx_le
          coefficient completedAmplitude
          amplitudeBound amplitudeBound_nonnegative
          channel
          states
          (fun state hstate itemApproximation =>
            completedAmplitudeBound state
              hstate
              channel hchannel itemApproximation)
          approximation)
      (fun channel hchannel =>
        rationalCutoffChannelLinear_converges
          states coefficient
          cutoffAmplitude completedAmplitude
          amplitudeBound amplitudeBound_nonnegative
          channel
          (fun state hstate approximation =>
            completedAmplitudeBound state
              hstate
              channel hchannel approximation)
          (fun state hstate =>
            amplitudeConverges state
              hstate
              channel hchannel))
  refine
    { cutoffNonnegative := ?_
      convergence := ?_
      completedNonnegative := ?_ }
  · intro cutoff
    exact weightedGramQuadratic_nonnegative
      states channels channelWeight
      (fun state channel =>
        cutoffAmplitude state channel cutoff)
      coefficient channelWeight_nonnegative
  · have hsos := rankCertificate.convergence
    apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
      (s :=
        fun cutoff =>
          CReal.ofQ'
            (rationalWeightedQuadraticPathSum
              channels channelWeight
              (rationalRankOnePathQuadratic
                (rationalCutoffChannelLinear
                  states coefficient cutoffAmplitude))
              cutoff))
    · intro cutoff
      apply SumOfSquares.Equiv_of_approx_eqv
      intro approximation
      have hsosEq :
          rationalWeightedQuadraticPathSum
              channels channelWeight
              (rationalRankOnePathQuadratic
                (rationalCutoffChannelLinear
                  states coefficient cutoffAmplitude))
              cutoff =
            weightedGramSOS
              states channels channelWeight
              (fun state channel =>
                cutoffAmplitude state channel cutoff)
              coefficient :=
        rationalWeightedChannelSquares_eq_weightedGramSOS
          states channels channelWeight
          coefficient cutoffAmplitude cutoff
      rw [hsosEq]
      exact Q'.eqv_symm
        (weightedGramQuadratic_eq_sos
          states channels channelWeight
          (fun state channel =>
            cutoffAmplitude state channel cutoff)
          coefficient)
    · exact hsos
  · exact rankCertificate.completedNonnegative

end YMGap.Continuum.BF4CompletedFiniteGramLimitBridge

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4CompletedFiniteGramLimitBridge.rationalCutoffChannelLinear_converges
#print axioms YMGap.Continuum.BF4CompletedFiniteGramLimitBridge.rationalWeightedChannelSquares_eq_weightedGramSOS
#print axioms YMGap.Continuum.BF4CompletedFiniteGramLimitBridge.finiteGramLimitCertificate
