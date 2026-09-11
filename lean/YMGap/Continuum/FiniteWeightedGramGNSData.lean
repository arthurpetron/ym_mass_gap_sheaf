/-
# A constructive GNS datum from a finite weighted Gram transform

A finite channel transform

    L_f(k) = sum_x f(x) A(x,k)

with nonnegative channel weights defines the positive bilinear form

    B(f,g) = sum_k w(k) L_f(k) L_g(k).

This module packages that form as an actual `GNSData` on rational coefficient
functions.  It is the bridge from a concrete boundary-channel Gram
factorization to the generic positive-form trace theorem.
-/

import YMGap.Continuum.FinitePositiveFormTraceGluing
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.FiniteWeightedGramGNSData

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Linearity of the finite channel transform -/

theorem channelLinear_congr
    {State Channel : Type} (states : List State)
    (amplitude : State → Channel → Q')
    {left right : State → Q'}
    (hcoefficient : ∀ state, left state ≈ right state)
    (channel : Channel) :
    channelLinear states amplitude left channel ≈
      channelLinear states amplitude right channel := by
  unfold channelLinear
  apply listQSum_congr
  intro state
  exact Q'.mul_eqv_congr_right _ _ _ (hcoefficient state)

/-- The finite channel transform only inspects coefficients on its displayed
state list. -/
theorem channelLinear_congr_on
    {State Channel : Type} (states : List State)
    (amplitude : State → Channel → Q')
    {left right : State → Q'}
    (hcoefficient : ∀ state, state ∈ states → left state ≈ right state)
    (channel : Channel) :
    channelLinear states amplitude left channel ≈
      channelLinear states amplitude right channel := by
  unfold channelLinear
  apply listQSum_congr_on
  intro state hstate
  exact Q'.mul_eqv_congr_right _ _ _ (hcoefficient state hstate)

theorem channelLinear_add
    {State Channel : Type} (states : List State)
    (amplitude : State → Channel → Q')
    (left right : State → Q') (channel : Channel) :
    channelLinear states amplitude
        (fun state => left state + right state) channel ≈
      channelLinear states amplitude left channel +
        channelLinear states amplitude right channel := by
  unfold channelLinear
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        left state * amplitude state channel +
          right state * amplitude state channel)
      states) _ ?_ ?_
  · apply listQSum_congr
    intro state
    exact q_add_mul (left state) (right state) (amplitude state channel)
  · exact listQSum_add _ _ states

theorem channelLinear_scale
    {State Channel : Type} (states : List State)
    (amplitude : State → Channel → Q')
    (scalar : Q') (coefficient : State → Q') (channel : Channel) :
    channelLinear states amplitude
        (fun state => scalar * coefficient state) channel ≈
      scalar * channelLinear states amplitude coefficient channel := by
  unfold channelLinear
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        scalar * (coefficient state * amplitude state channel))
      states) _ ?_ ?_
  · apply listQSum_congr
    intro state
    exact Q'.mul_assoc_eqv scalar (coefficient state)
      (amplitude state channel)
  · exact listQSum_mul_left scalar _ states

/-! ## 2. The bilinear weighted Gram -/

/-- Bilinear form induced by the finite channel transform. -/
def weightedGramBilinear
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (channelWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (left right : State → Q') : Q' :=
  listQSum
    (fun channel =>
      channelWeight channel *
        (channelLinear states amplitude left channel *
          channelLinear states amplitude right channel))
    channels

/-- A finite weighted Gram only inspects both coefficient functions on its
displayed state list. -/
theorem weightedGramBilinear_congr_on
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (channelWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    {left left' right right' : State → Q'}
    (hleft : ∀ state, state ∈ states → left state ≈ left' state)
    (hright : ∀ state, state ∈ states → right state ≈ right' state) :
    weightedGramBilinear states channels channelWeight amplitude left right ≈
      weightedGramBilinear states channels channelWeight amplitude left' right' := by
  unfold weightedGramBilinear
  apply listQSum_congr_on
  intro channel _hchannel
  exact Q'.mul_eqv_congr_left (channelWeight channel) _ _
    (Q'.eqv_trans _
      (channelLinear states amplitude left' channel *
        channelLinear states amplitude right channel) _
      (Q'.mul_eqv_congr_right _ _ _
        (channelLinear_congr_on states amplitude hleft channel))
      (Q'.mul_eqv_congr_left _ _ _
        (channelLinear_congr_on states amplitude hright channel)))

theorem weightedGramBilinear_congr_left
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (channelWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    {left left' : State → Q'} (right : State → Q')
    (hleft : ∀ state, left state ≈ left' state) :
    weightedGramBilinear states channels channelWeight amplitude left right ≈
      weightedGramBilinear states channels channelWeight amplitude left' right := by
  unfold weightedGramBilinear
  apply listQSum_congr
  intro channel
  exact Q'.mul_eqv_congr_left (channelWeight channel) _ _
    (Q'.mul_eqv_congr_right _ _ _
      (channelLinear_congr states amplitude hleft channel))

theorem weightedGramBilinear_add_left
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (channelWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (left right test : State → Q') :
    weightedGramBilinear states channels channelWeight amplitude
        (fun state => left state + right state) test ≈
      weightedGramBilinear states channels channelWeight amplitude left test +
        weightedGramBilinear states channels channelWeight amplitude right test := by
  unfold weightedGramBilinear
  refine Q'.eqv_trans _
    (listQSum
      (fun channel =>
        channelWeight channel *
              (channelLinear states amplitude left channel *
                channelLinear states amplitude test channel) +
          channelWeight channel *
              (channelLinear states amplitude right channel *
                channelLinear states amplitude test channel))
      channels) _ ?_ ?_
  · apply listQSum_congr
    intro channel
    let leftValue := channelLinear states amplitude left channel
    let rightValue := channelLinear states amplitude right channel
    let testValue := channelLinear states amplitude test channel
    have hlinear := channelLinear_add
      states amplitude left right channel
    refine Q'.eqv_trans _
      (channelWeight channel * ((leftValue + rightValue) * testValue)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left (channelWeight channel) _ _
        (Q'.mul_eqv_congr_right _ _ testValue hlinear)
    refine Q'.eqv_trans _
      (channelWeight channel *
        (leftValue * testValue + rightValue * testValue)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left (channelWeight channel) _ _
        (q_add_mul leftValue rightValue testValue)
    exact Q'.mul_add_eqv (channelWeight channel)
      (leftValue * testValue) (rightValue * testValue)
  · exact listQSum_add _ _ channels

theorem weightedGramBilinear_scale_left
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (channelWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (scalar : Q') (left right : State → Q') :
    weightedGramBilinear states channels channelWeight amplitude
        (fun state => scalar * left state) right ≈
      scalar *
        weightedGramBilinear states channels channelWeight amplitude
          left right := by
  unfold weightedGramBilinear
  refine Q'.eqv_trans _
    (listQSum
      (fun channel =>
        scalar *
          (channelWeight channel *
            (channelLinear states amplitude left channel *
              channelLinear states amplitude right channel)))
      channels) _ ?_ ?_
  · apply listQSum_congr
    intro channel
    have hlinear := channelLinear_scale
      states amplitude scalar left channel
    refine Q'.eqv_trans _
      (channelWeight channel *
        ((scalar * channelLinear states amplitude left channel) *
          channelLinear states amplitude right channel)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left (channelWeight channel) _ _
        (Q'.mul_eqv_congr_right _ _ _ hlinear)
    refine Q'.eqv_trans _
      (channelWeight channel *
        (scalar *
          (channelLinear states amplitude left channel *
            channelLinear states amplitude right channel))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left (channelWeight channel) _ _
        (Q'.mul_assoc_eqv scalar
          (channelLinear states amplitude left channel)
          (channelLinear states amplitude right channel))
    refine Q'.eqv_trans _
      (scalar *
        (channelWeight channel *
          (channelLinear states amplitude left channel *
            channelLinear states amplitude right channel))) _ ?_ ?_
    · let value :=
        channelLinear states amplitude left channel *
          channelLinear states amplitude right channel
      refine Q'.eqv_trans _
        ((channelWeight channel * scalar) * value) _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv (channelWeight channel) scalar value)) ?_
      refine Q'.eqv_trans _
        ((scalar * channelWeight channel) * value) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ value
          (Q'.mul_comm_eqv (channelWeight channel) scalar)
      · exact Q'.mul_assoc_eqv scalar (channelWeight channel) value
    · exact Q'.eqv_refl _
  · exact listQSum_mul_left scalar _ channels

theorem weightedGramBilinear_symm
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (channelWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (left right : State → Q') :
    weightedGramBilinear states channels channelWeight amplitude left right ≈
      weightedGramBilinear states channels channelWeight amplitude right left := by
  unfold weightedGramBilinear
  apply listQSum_congr
  intro channel
  exact Q'.mul_eqv_congr_left (channelWeight channel) _ _
    (Q'.mul_comm_eqv
      (channelLinear states amplitude left channel)
      (channelLinear states amplitude right channel))

theorem weightedGramBilinear_self_eq_sos
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (channelWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (coefficient : State → Q') :
    weightedGramBilinear states channels channelWeight amplitude
        coefficient coefficient =
      weightedGramSOS states channels channelWeight amplitude coefficient :=
  rfl

/-! ## 3. The constructive GNS datum -/

/-- A finite nonnegatively weighted channel Gram as an actual constructive
GNS datum on coefficient functions. -/
def finiteWeightedGramGNSData
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (channelWeight : Channel → Q')
    (amplitude : State → Channel → Q')
    (hweight : ∀ channel, channel ∈ channels →
      (0 : Q') ≤ channelWeight channel) : GNSData where
  V := State → Q'
  veq := fun left right => ∀ state, left state ≈ right state
  veq_refl := fun coefficient state => Q'.eqv_refl (coefficient state)
  veq_symm := fun h state => Q'.eqv_symm (h state)
  veq_trans := fun hleft hright state =>
    Q'.eqv_trans _ _ _ (hleft state) (hright state)
  zero := fun _ => 0
  add := fun left right state => left state + right state
  neg := fun coefficient state => -coefficient state
  smul := fun scalar coefficient state => scalar * coefficient state
  add_congr := by
    intro left left' right right' hleft hright state
    exact QPoly.q_add_congr (hleft state) (hright state)
  neg_congr := by
    intro left right h state
    exact Q'.neg_eqv_congr _ _ (h state)
  smul_congr := by
    intro scalar left right h state
    exact Q'.mul_eqv_congr_left scalar _ _ (h state)
  add_assoc := fun left middle right state =>
    Q'.add_assoc_eqv (left state) (middle state) (right state)
  add_comm := fun left right state =>
    Q'.add_comm_eqv (left state) (right state)
  zero_add := fun coefficient state =>
    Q'.eqv_of_eq (Q'.zero_add' (coefficient state))
  neg_add := fun coefficient state =>
    Q'.neg_add_self_eqv (coefficient state)
  B := weightedGramBilinear states channels channelWeight amplitude
  B_congr_left := by
    intro left left' right hleft
    exact weightedGramBilinear_congr_left
      states channels channelWeight amplitude right hleft
  B_add_left := weightedGramBilinear_add_left
    states channels channelWeight amplitude
  B_smul_left := weightedGramBilinear_scale_left
    states channels channelWeight amplitude
  B_symm := weightedGramBilinear_symm
    states channels channelWeight amplitude
  self_nonneg := by
    intro coefficient
    rw [weightedGramBilinear_self_eq_sos]
    exact weightedGramSOS_nonnegative
      states channels channelWeight amplitude coefficient hweight

end YMGap.Continuum.FiniteWeightedGramGNSData

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.FiniteWeightedGramGNSData.channelLinear_add
#print axioms
  YMGap.Continuum.FiniteWeightedGramGNSData.weightedGramBilinear_congr_on
#print axioms
  YMGap.Continuum.FiniteWeightedGramGNSData.weightedGramBilinear_self_eq_sos
#print axioms
  YMGap.Continuum.FiniteWeightedGramGNSData.finiteWeightedGramGNSData
