/-
# Normalized projective Harnack control for the physical BF4 posteriors

An anchor is unnecessary once both positive rays are normalized probability
laws.  Summing a projective cross-ratio inequality over one coordinate gives
both pointwise windows

    p(x) <= C q(x),    q(x) <= C p(x).

At the existing squared-spread cap `C <= 65/64`, these windows imply

    ||p-q||_1 <= 2/64 <= 1/4.

This file proves that finite statement constructively.  The genuine BF4
boundary posteriors from `BF4PhysicalBoundaryPosterior` are its intended
physical inputs.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
import YMGap.Continuum.BF4PhysicalBoundaryPosterior

namespace YMGap.Continuum.BF4NormalizedProjectivePosteriorHarnack

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalBoundaryPosterior
open YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic normalized projective pairs -/

/-- Two nonnegative normalized finite profiles with a common projective
spread cap. -/
structure NormalizedProjectivePair
    {State : Type}
    (states : List State)
    (left right : State → Q') : Type where
  spread : Q'
  left_nonnegative :
    ∀ state, state ∈ states →
      (0 : Q') ≤ left state
  right_nonnegative :
    ∀ state, state ∈ states →
      (0 : Q') ≤ right state
  left_total_one :
    listQSum left states ≈ 1
  right_total_one :
    listQSum right states ≈ 1
  spreadSquare_le :
    spread * spread ≤ anchoredProjectiveCeiling
  projective :
    FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
      spread states left right

namespace NormalizedProjectivePair

/-- Normalization removes the projective scalar ambiguity and gives the
upper pointwise window for the left profile. -/
theorem left_upper
    {State : Type}
    {states : List State}
    {left right : State → Q'}
    (data : NormalizedProjectivePair states left right)
    (state : State) (state_mem : state ∈ states) :
    left state ≤ anchoredProjectiveCeiling * right state := by
  let square := data.spread * data.spread
  have hsum :
      listQSum
          (fun other => left state * right other)
          states ≤
        listQSum
          (fun other =>
            square * (left other * right state))
          states := by
    apply listQSum_mono
    intro other other_mem
    exact data.projective
      state state_mem other other_mem
  have hleft :
      listQSum
          (fun other => left state * right other)
          states ≈
        left state := by
    refine Q'.eqv_trans _
      (left state * listQSum right states) _ ?_ ?_
    · exact listQSum_mul_left
        (left state) right states
    refine Q'.eqv_trans _
      (left state * 1) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left
        (left state) _ _ data.right_total_one
    exact Q'.mul_one_eqv _
  have hright :
      listQSum
          (fun other =>
            square * (left other * right state))
          states ≈
        square * right state := by
    refine Q'.eqv_trans _
      (square *
        listQSum
          (fun other => left other * right state)
          states) _ ?_ ?_
    · exact listQSum_mul_left
        square
        (fun other => left other * right state)
        states
    refine Q'.eqv_trans _
      (square *
        (listQSum left states * right state)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left square _ _
        (listQSum_mul_right left (right state) states)
    refine Q'.eqv_trans _
      (square * (1 * right state)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left square _ _
        (Q'.mul_eqv_congr_right _ _
          (right state) data.left_total_one)
    exact Q'.mul_eqv_congr_left square _ _
      (Q'.one_mul_eqv _)
  have hsquare :
      left state ≤ square * right state :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hsum
        (Q'.le_of_eqv hright))
  exact Q'.le_trans' _ _ _ hsquare
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      data.spreadSquare_le
      (data.right_nonnegative state state_mem))

/-- The symmetric normalized pointwise window for the right profile. -/
theorem right_upper
    {State : Type}
    {states : List State}
    {left right : State → Q'}
    (data : NormalizedProjectivePair states left right)
    (state : State) (state_mem : state ∈ states) :
    right state ≤ anchoredProjectiveCeiling * left state := by
  let square := data.spread * data.spread
  have hsum :
      listQSum
          (fun other => left other * right state)
          states ≤
        listQSum
          (fun other =>
            square * (left state * right other))
          states := by
    apply listQSum_mono
    intro other other_mem
    exact data.projective
      other other_mem state state_mem
  have hleft :
      listQSum
          (fun other => left other * right state)
          states ≈
        right state := by
    refine Q'.eqv_trans _
      (listQSum left states * right state) _ ?_ ?_
    · exact listQSum_mul_right
        left (right state) states
    refine Q'.eqv_trans _
      (1 * right state) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _
        (right state) data.left_total_one
    exact Q'.one_mul_eqv _
  have hright :
      listQSum
          (fun other =>
            square * (left state * right other))
          states ≈
        square * left state := by
    refine Q'.eqv_trans _
      (square *
        listQSum
          (fun other => left state * right other)
          states) _ ?_ ?_
    · exact listQSum_mul_left
        square
        (fun other => left state * right other)
        states
    refine Q'.eqv_trans _
      (square *
        (left state * listQSum right states)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left square _ _
        (listQSum_mul_left
          (left state) right states)
    refine Q'.eqv_trans _
      (square * (left state * 1)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left square _ _
        (Q'.mul_eqv_congr_left
          (left state) _ _ data.right_total_one)
    exact Q'.mul_eqv_congr_left square _ _
      (Q'.mul_one_eqv _)
  have hsquare :
      right state ≤ square * left state :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hsum
        (Q'.le_of_eqv hright))
  exact Q'.le_trans' _ _ _ hsquare
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      data.spreadSquare_le
      (data.left_nonnegative state state_mem))

/-- The two normalized projective windows give a pointwise additive
deviation bound with the existing `1/64` tolerance. -/
theorem pointwise_deviation
    {State : Type}
    {states : List State}
    {left right : State → Q'}
    (data : NormalizedProjectivePair states left right)
    (state : State) (state_mem : state ∈ states) :
    Q'.abs (left state + (-right state)) ≤
      anchoredProjectiveTolerance *
        (left state + right state) := by
  let tolerance := anchoredProjectiveTolerance
  have htolerance : (0 : Q') ≤ tolerance := by
    decide
  have hleftNonnegative :=
    data.left_nonnegative state state_mem
  have hrightNonnegative :=
    data.right_nonnegative state state_mem
  have hrightLeSum :
      right state ≤ left state + right state := by
    have h :=
      Q'.add_le_self_of_nonneg
        (right state) (left state)
        hleftNonnegative
    exact Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv
        (Q'.add_comm_eqv
          (right state) (left state)))
  have hleftLeSum :
      left state ≤ left state + right state :=
    Q'.add_le_self_of_nonneg
      (left state) (right state)
      hrightNonnegative
  have htolRight :
      tolerance * right state ≤
        tolerance * (left state + right state) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      hrightLeSum htolerance
  have htolLeft :
      tolerance * left state ≤
        tolerance * (left state + right state) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      hleftLeSum htolerance
  have hfirst :
      left state ≤
        right state +
          tolerance * (left state + right state) := by
    refine Q'.le_trans' _ _ _
      (data.left_upper state state_mem)
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (anchoredProjectiveCeiling_mul_eqv_add
            (right state))) ?_)
    exact Q'.add_le_add
      (Q'.le_refl' (right state)) htolRight
  have hsecond :
      right state ≤
        left state +
          tolerance * (left state + right state) := by
    refine Q'.le_trans' _ _ _
      (data.right_upper state state_mem)
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (anchoredProjectiveCeiling_mul_eqv_add
            (left state))) ?_)
    exact Q'.add_le_add
      (Q'.le_refl' (left state)) htolLeft
  exact CReal.abs_sub_le_of_bounds hfirst hsecond

/-- **Normalized projective posterior theorem.**  Squared spread at most
`65/64` implies complete `L¹` distance at most `1/4`. -/
theorem l1_le_quarter
    {State : Type}
    {states : List State}
    {left right : State → Q'}
    (data : NormalizedProjectivePair states left right) :
    finiteL1Distance states left right ≤ quarter := by
  let tolerance := anchoredProjectiveTolerance
  refine Q'.le_trans' _ _ _
    (listQSum_mono
      (fun state =>
        Q'.abs (left state + (-right state)))
      (fun state =>
        tolerance * (left state + right state))
      states
      (fun state state_mem =>
        data.pointwise_deviation state state_mem)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_trans _
        (tolerance *
          listQSum
            (fun state => left state + right state)
            states) _
        (listQSum_mul_left
          tolerance
          (fun state => left state + right state)
          states)
        (Q'.eqv_trans _
          (tolerance *
            (listQSum left states +
              listQSum right states)) _
          (Q'.mul_eqv_congr_left tolerance _ _
            (listQSum_add left right states))
          (Q'.eqv_trans _
            (tolerance * (1 + 1)) _
            (Q'.mul_eqv_congr_left tolerance _ _
              (Q'.add_eqv_congr'
                data.left_total_one
                data.right_total_one))
            (Q'.eqv_refl _))))) ?_
  decide

end NormalizedProjectivePair

end YMGap.Continuum.BF4NormalizedProjectivePosteriorHarnack

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4NormalizedProjectivePosteriorHarnack.NormalizedProjectivePair.left_upper
#print axioms YMGap.Continuum.BF4NormalizedProjectivePosteriorHarnack.NormalizedProjectivePair.right_upper
#print axioms YMGap.Continuum.BF4NormalizedProjectivePosteriorHarnack.NormalizedProjectivePair.pointwise_deviation
#print axioms YMGap.Continuum.BF4NormalizedProjectivePosteriorHarnack.NormalizedProjectivePair.l1_le_quarter
