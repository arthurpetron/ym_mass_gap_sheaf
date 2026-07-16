/-
# Constructive finite weighted Gram / sum-of-squares assembly

This module packages the algebra needed after a reflection-channel
convolution has been proved.  Given finitely many states, finitely many
channels, nonnegative channel weights, and exact rational half-amplitudes, the
matrix obtained by summing products of half-amplitudes is a literal Gram
matrix.  Its complete finite quadratic form is exactly a nonnegatively
weighted sum of rational squares.

The result is deliberately generic.  A physical reflection-positivity proof
must still identify the full reflected Yang--Mills summand with this Gram,
including all boundary and normalization factors.
-/

import YMGap.Continuum.FiniteDeterministicKernelPushforward
import YMGap.Continuum.SchurHadamardTransfer

namespace YMGap.Continuum.FiniteWeightedGramSOS

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SchurHadamardTransfer
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## Product algebra for exact list sums -/

theorem listQSum_mul_right {A : Type} (f : A -> Q') (a : Q') :
    forall xs : List A,
      listQSum (fun x => f x * a) xs ≈ listQSum f xs * a
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv a)
  | x :: xs => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl (f x * a))
          (listQSum_mul_right f a xs))
        (Q'.eqv_symm (Q'.add_mul_eqv (f x) (listQSum f xs) a))

/-- Cartesian product of two finite exact sums, kept in nested-list form. -/
theorem listQSum_product {A B : Type}
    (f : A -> Q') (g : B -> Q') : forall (xs : List A) (ys : List B),
    listQSum (fun x => listQSum (fun y => f x * g y) ys) xs ≈
      listQSum f xs * listQSum g ys
  | xs, ys => by
      refine Q'.eqv_trans _ _ _
        (listQSum_congr
          (fun x => listQSum_mul_left (f x) g ys) xs) ?_
      exact listQSum_mul_right f (listQSum g ys) xs

/-! ## Finite weighted channel Gram -/

/-- Entry of a finite channel Gram. -/
def weightedGram {State Channel : Type}
    (channels : List Channel) (channelWeight : Channel -> Q')
    (amplitude : State -> Channel -> Q') (left right : State) : Q' :=
  listQSum
    (fun channel => channelWeight channel *
      (amplitude left channel * amplitude right channel))
    channels

/-- Complete finite quadratic form of the channel Gram. -/
def weightedGramQuadratic {State Channel : Type}
    (states : List State) (channels : List Channel)
    (channelWeight : Channel -> Q')
    (amplitude : State -> Channel -> Q')
    (coefficient : State -> Q') : Q' :=
  listQSum
    (fun left => listQSum
      (fun right => (coefficient left * coefficient right) *
        weightedGram channels channelWeight amplitude left right)
      states)
    states

/-- Linear half-amplitude in a fixed channel. -/
def channelLinear {State Channel : Type}
    (states : List State) (amplitude : State -> Channel -> Q')
    (coefficient : State -> Q') (channel : Channel) : Q' :=
  listQSum
    (fun state => coefficient state * amplitude state channel)
    states

/-- Manifest sum-of-squares expression associated to the channel Gram. -/
def weightedGramSOS {State Channel : Type}
    (states : List State) (channels : List Channel)
    (channelWeight : Channel -> Q')
    (amplitude : State -> Channel -> Q')
    (coefficient : State -> Q') : Q' :=
  listQSum
    (fun channel => channelWeight channel *
      (channelLinear states amplitude coefficient channel *
        channelLinear states amplitude coefficient channel))
    channels

private def gramTerm {State Channel : Type}
    (channelWeight : Channel -> Q')
    (amplitude : State -> Channel -> Q')
    (coefficient : State -> Q')
    (left right : State) (channel : Channel) : Q' :=
  channelWeight channel *
    ((coefficient left * amplitude left channel) *
      (coefficient right * amplitude right channel))

/-- Exact finite Gram-to-SOS rearrangement. -/
theorem weightedGramQuadratic_eq_sos
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (channelWeight : Channel -> Q')
    (amplitude : State -> Channel -> Q')
    (coefficient : State -> Q') :
    weightedGramQuadratic states channels channelWeight amplitude coefficient ≈
      weightedGramSOS states channels channelWeight amplitude coefficient := by
  have hdistribute :
      weightedGramQuadratic states channels channelWeight amplitude coefficient ≈
        listQSum
          (fun left => listQSum
            (fun right => listQSum
              (gramTerm channelWeight amplitude coefficient left right)
              channels)
            states)
          states := by
    unfold weightedGramQuadratic weightedGram
    apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (listQSum_mul_left
          (coefficient left * coefficient right)
          (fun channel => channelWeight channel *
            (amplitude left channel * amplitude right channel))
          channels)) ?_
    apply listQSum_congr
    intro channel
    exact mul6_rearrange
      (coefficient left) (coefficient right)
      (channelWeight channel)
      (amplitude left channel) (amplitude right channel)
  have hswapRight :
      listQSum
          (fun left => listQSum
            (fun right => listQSum
              (gramTerm channelWeight amplitude coefficient left right)
              channels)
            states)
          states ≈
        listQSum
          (fun left => listQSum
            (fun channel => listQSum
              (fun right =>
                gramTerm channelWeight amplitude coefficient
                  left right channel)
              states)
            channels)
          states := by
    apply listQSum_congr
    intro left
    exact Q'.eqv_symm
      (listQSum_swap
        (fun right channel =>
          gramTerm channelWeight amplitude coefficient
            left right channel)
        states channels)
  have hswapLeft :
      listQSum
          (fun left => listQSum
            (fun channel => listQSum
              (fun right =>
                gramTerm channelWeight amplitude coefficient
                  left right channel)
              states)
            channels)
          states ≈
        listQSum
          (fun channel => listQSum
            (fun left => listQSum
              (fun right =>
                gramTerm channelWeight amplitude coefficient
                  left right channel)
              states)
            states)
          channels := by
    exact Q'.eqv_symm
      (listQSum_swap
        (fun left channel => listQSum
          (fun right =>
            gramTerm channelWeight amplitude coefficient
              left right channel)
          states)
        states channels)
  have hcollapse :
      listQSum
          (fun channel => listQSum
            (fun left => listQSum
              (fun right =>
                gramTerm channelWeight amplitude coefficient
                  left right channel)
              states)
            states)
          channels ≈
        weightedGramSOS states channels channelWeight amplitude coefficient := by
    unfold weightedGramSOS
    apply listQSum_congr
    intro channel
    let value : State -> Q' := fun state =>
      coefficient state * amplitude state channel
    refine Q'.eqv_trans _ _ _
      (listQSum_congr
        (fun left => listQSum_mul_left
          (channelWeight channel)
          (fun right => value left * value right)
          states)
        states) ?_
    refine Q'.eqv_trans _ _ _
      (listQSum_mul_left
        (channelWeight channel)
        (fun left => listQSum
          (fun right => value left * value right) states)
        states) ?_
    exact Q'.mul_eqv_congr_left (channelWeight channel) _ _
      (listQSum_product value value states states)
  exact Q'.eqv_trans _ _ _ hdistribute
    (Q'.eqv_trans _ _ _ hswapRight
      (Q'.eqv_trans _ _ _ hswapLeft hcollapse))

theorem weightedGramSOS_nonnegative
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (channelWeight : Channel -> Q')
    (amplitude : State -> Channel -> Q')
    (coefficient : State -> Q')
    (hweight : forall channel, channel ∈ channels ->
      (0 : Q') ≤ channelWeight channel) :
    (0 : Q') ≤
      weightedGramSOS states channels channelWeight amplitude coefficient := by
  unfold weightedGramSOS
  apply listQSum_nonnegative_on
  intro channel hchannel
  exact Q'.mul_nonneg _ _
    (hweight channel hchannel)
    (q_mul_self_nonneg
      (channelLinear states amplitude coefficient channel))

/-- Constructive finite reflection positivity once a physical summand has been
identified with the weighted channel Gram. -/
theorem weightedGramQuadratic_nonnegative
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (channelWeight : Channel -> Q')
    (amplitude : State -> Channel -> Q')
    (coefficient : State -> Q')
    (hweight : forall channel, channel ∈ channels ->
      (0 : Q') ≤ channelWeight channel) :
    (0 : Q') ≤
      weightedGramQuadratic states channels channelWeight amplitude coefficient := by
  have hsos := weightedGramSOS_nonnegative
    states channels channelWeight amplitude coefficient hweight
  exact Q'.le_trans' _ _ _ hsos
    (Q'.le_of_eqv (Q'.eqv_symm
      (weightedGramQuadratic_eq_sos
        states channels channelWeight amplitude coefficient)))

#print axioms listQSum_product
#print axioms weightedGramQuadratic_eq_sos
#print axioms weightedGramSOS_nonnegative
#print axioms weightedGramQuadratic_nonnegative

end YMGap.Continuum.FiniteWeightedGramSOS
