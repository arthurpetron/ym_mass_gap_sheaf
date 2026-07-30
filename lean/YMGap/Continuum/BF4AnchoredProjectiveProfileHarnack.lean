/-
# Anchored projective control implies the BF4 profile Harnack window

A Hilbert-projective estimate determines a positive ray only up to scalar.
This module supplies the missing normalization step.  If a candidate profile
`P` and a physical marginal `pi`

* obey a division-free projective spread bound on a finite carrier,
* agree at one strictly positive anchor, and
* have squared spread at most `65/64`,

then every retained coordinate satisfies

    |P(x) - pi(x)| <= (1/64) pi(x).

The proof is exact rational algebra.  In particular it does not divide by a
minimum marginal or pay for the carrier cardinality.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Constructive.CRealExp
import YMGap.Continuum.RationalCrossRatioDiameter

namespace YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Continuum.RationalCrossRatioDiameter

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

def anchoredProjectiveCeiling : Q' :=
  Q'.mkPos 65 64 (by decide)

def anchoredProjectiveFloor : Q' :=
  Q'.mkPos 63 64 (by decide)

def anchoredProjectiveTolerance : Q' :=
  Q'.mkPos 1 64 (by decide)

theorem anchoredProjectiveFloor_mul_ceiling_le_one :
    anchoredProjectiveFloor * anchoredProjectiveCeiling ≤
      (1 : Q') := by
  decide

theorem anchoredProjectiveCeiling_eq_one_add_sixtyFourth :
    anchoredProjectiveCeiling ≈
      1 + anchoredProjectiveTolerance := by
  decide

theorem anchoredProjectiveFloor_eq_one_sub_sixtyFourth :
    anchoredProjectiveFloor ≈
      1 + (-anchoredProjectiveTolerance) := by
  decide

theorem anchoredProjectiveCeiling_mul_eqv_add
    (marginal : Q') :
    anchoredProjectiveCeiling * marginal ≈
      marginal +
        anchoredProjectiveTolerance * marginal := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ marginal
      anchoredProjectiveCeiling_eq_one_add_sixtyFourth) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv
      1 anchoredProjectiveTolerance marginal) ?_
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.one_mul_eqv marginal)

theorem anchoredProjectiveFloor_mul_add_eqv
    (marginal : Q') :
    anchoredProjectiveFloor * marginal +
        anchoredProjectiveTolerance * marginal ≈
      marginal := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _
      (anchoredProjectiveTolerance * marginal)
      (Q'.mul_eqv_congr_right _ _ marginal
        anchoredProjectiveFloor_eq_one_sub_sixtyFourth)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _
      (anchoredProjectiveTolerance * marginal)
      (Q'.add_mul_eqv
        1 (-anchoredProjectiveTolerance) marginal)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _
      (anchoredProjectiveTolerance * marginal)
      (Q'.add_eqv_congr_right _ _
        ((-anchoredProjectiveTolerance) * marginal)
        (Q'.one_mul_eqv marginal))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv
      marginal
      ((-anchoredProjectiveTolerance) * marginal)
      (anchoredProjectiveTolerance * marginal)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left marginal _ _
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _
          (anchoredProjectiveTolerance * marginal)
          (Q'.neg_mul_eqv
            anchoredProjectiveTolerance marginal))
        (Q'.neg_add_self_eqv
          (anchoredProjectiveTolerance * marginal)))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' marginal)

private theorem divPos_mul_cancel_right
    (a c : Q') (hc : (0 : Q') < c) :
    Q'.divPos (a * c) c hc ≈ a := by
  unfold Q'.divPos
  refine Q'.eqv_trans _
    (a * (c * Q'.recipPos c hc)) _ ?_ ?_
  · exact Q'.mul_assoc_eqv a c (Q'.recipPos c hc)
  refine Q'.eqv_trans _ (a * 1) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left a _ _
      (Q'.mul_recipPos_eqv c hc)
  · exact Q'.mul_one_eqv a

/-- Constructive cancellation of a strictly positive common right factor. -/
theorem le_of_mul_le_mul_right_pos
    {a b c : Q'} (hc : (0 : Q') < c)
    (h : a * c ≤ b * c) :
    a ≤ b := by
  have hdiv :
      Q'.divPos (a * c) c hc ≤ b :=
    Q'.divPos_le_of_le_mul (a * c) c hc h
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (divPos_mul_cancel_right a c hc))
    hdiv

/-- An anchor-normalized projective comparison of a candidate profile with
a reference marginal.  `spreadSquare_le` is deliberately stated without a
square root. -/
structure AnchoredProjectiveProfile
    {State : Type}
    (states : List State)
    (profile marginal : State → Q') : Type where
  spread : Q'
  anchor : State
  anchor_mem : anchor ∈ states
  marginal_anchor_pos : (0 : Q') < marginal anchor
  anchor_match : profile anchor ≈ marginal anchor
  profile_nonnegative :
    ∀ state, state ∈ states →
      (0 : Q') ≤ profile state
  spreadSquare_le :
    spread * spread ≤ anchoredProjectiveCeiling
  projective :
    FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
      spread states profile marginal

namespace AnchoredProjectiveProfile

/-- A strictly positive finite kernel sends any two nonzero nonnegative
activities to anchored projectively comparable profiles.  This is the exact
positive-kernel constructor needed by the grouped Feynman--Kac route. -/
def ofKernelActions
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate
        kernel sources targets)
    (candidate physical : Source → Q')
    (candidateActivity :
      FiniteCrossRatioDiameterCertificate.NonzeroNonnegativeActivity
        sources candidate)
    (physicalActivity :
      FiniteCrossRatioDiameterCertificate.NonzeroNonnegativeActivity
        sources physical)
    (anchor : Target) (anchor_mem : anchor ∈ targets)
    (anchor_match :
      FiniteCrossRatioDiameterCertificate.finiteKernelAction
          kernel sources candidate anchor ≈
        FiniteCrossRatioDiameterCertificate.finiteKernelAction
          kernel sources physical anchor)
    (spreadSquare_le :
      certificate.spread * certificate.spread ≤
        anchoredProjectiveCeiling) :
    AnchoredProjectiveProfile
      targets
      (FiniteCrossRatioDiameterCertificate.finiteKernelAction
        kernel sources candidate)
      (FiniteCrossRatioDiameterCertificate.finiteKernelAction
        kernel sources physical) where
  spread := certificate.spread
  anchor := anchor
  anchor_mem := anchor_mem
  marginal_anchor_pos :=
    certificate.finiteKernelAction_pos
      physicalActivity anchor_mem
  anchor_match := anchor_match
  profile_nonnegative := by
    intro target htarget
    exact Q'.le_of_lt
      (certificate.finiteKernelAction_pos
        candidateActivity htarget)
  spreadSquare_le := spreadSquare_le
  projective :=
    certificate.finiteKernelAction_projectiveSpread
      candidate physical
      candidateActivity.nonnegative
      physicalActivity.nonnegative

/-- Transport an anchored projective certificate across pointwise semantic
equality of the candidate profile on the retained carrier. -/
def profileEqv
    {State : Type}
    {states : List State}
    {profile profile' marginal : State → Q'}
    (data :
      AnchoredProjectiveProfile states profile marginal)
    (hprofile :
      ∀ state, state ∈ states →
        profile' state ≈ profile state) :
    AnchoredProjectiveProfile states profile' marginal where
  spread := data.spread
  anchor := data.anchor
  anchor_mem := data.anchor_mem
  marginal_anchor_pos := data.marginal_anchor_pos
  anchor_match :=
    Q'.eqv_trans _ _ _
      (hprofile data.anchor data.anchor_mem)
      data.anchor_match
  profile_nonnegative := by
    intro state hstate
    exact Q'.le_trans' _ _ _
      (data.profile_nonnegative state hstate)
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (hprofile state hstate)))
  spreadSquare_le := data.spreadSquare_le
  projective := by
    intro left hleft right hright
    have hbound :=
      data.projective
        left hleft right hright
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_right _ _
          (marginal right)
          (hprofile left hleft)))
      (Q'.le_trans' _ _ _ hbound
        (Q'.le_of_eqv ?_))
    exact Q'.mul_eqv_congr_left
      (data.spread * data.spread) _ _
      (Q'.mul_eqv_congr_right _ _
        (marginal left)
        (Q'.eqv_symm
          (hprofile right hright)))

/-- Transport an anchored projective certificate across pointwise semantic
equality of the reference marginal on the retained carrier. -/
def marginalEqv
    {State : Type}
    {states : List State}
    {profile marginal marginal' : State → Q'}
    (data :
      AnchoredProjectiveProfile states profile marginal)
    (hmarginal :
      ∀ state, state ∈ states →
        marginal' state ≈ marginal state) :
    AnchoredProjectiveProfile states profile marginal' where
  spread := data.spread
  anchor := data.anchor
  anchor_mem := data.anchor_mem
  marginal_anchor_pos :=
    Q'.pos_of_lt_of_le
      data.marginal_anchor_pos
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (hmarginal data.anchor data.anchor_mem)))
  anchor_match :=
    Q'.eqv_trans _ _ _
      data.anchor_match
      (Q'.eqv_symm
        (hmarginal data.anchor data.anchor_mem))
  profile_nonnegative := data.profile_nonnegative
  spreadSquare_le := data.spreadSquare_le
  projective := by
    intro left hleft right hright
    have hbound :=
      data.projective
        left hleft right hright
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          (profile left) _ _
          (hmarginal right hright)))
      (Q'.le_trans' _ _ _ hbound
        (Q'.le_of_eqv ?_))
    exact Q'.mul_eqv_congr_left
      (data.spread * data.spread) _ _
      (Q'.mul_eqv_congr_left
        (profile right) _ _
        (Q'.eqv_symm
          (hmarginal left hleft)))

theorem upper_window
    {State : Type}
    {states : List State}
    {profile marginal : State → Q'}
    (data :
      AnchoredProjectiveProfile states profile marginal)
    (state : State) (hstate : state ∈ states)
    (hmarginal : (0 : Q') ≤ marginal state) :
    profile state ≤
      anchoredProjectiveCeiling * marginal state := by
  have hprojective :=
    data.projective
      state hstate data.anchor data.anchor_mem
  have hanchorRewrite :
      profile state * marginal data.anchor ≤
        (data.spread * data.spread * marginal state) *
          marginal data.anchor := by
    refine Q'.le_trans' _ _ _ hprojective
      (Q'.le_of_eqv ?_)
    calc
      (data.spread * data.spread) *
            (profile data.anchor * marginal state) ≈
          (data.spread * data.spread) *
            (marginal data.anchor * marginal state) :=
        Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_right _ _
            (marginal state) data.anchor_match)
      _ ≈
          (data.spread * data.spread * marginal state) *
            marginal data.anchor := by
        q_ring
  have hcancel :
      profile state ≤
        (data.spread * data.spread) * marginal state :=
    le_of_mul_le_mul_right_pos
      data.marginal_anchor_pos hanchorRewrite
  exact Q'.le_trans' _ _ _ hcancel
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      data.spreadSquare_le hmarginal)

theorem lower_projective_window
    {State : Type}
    {states : List State}
    {profile marginal : State → Q'}
    (data :
      AnchoredProjectiveProfile states profile marginal)
    (state : State) (hstate : state ∈ states) :
    marginal state ≤
      (data.spread * data.spread) * profile state := by
  have hprojective :=
    data.projective
      data.anchor data.anchor_mem state hstate
  have hanchorRewrite :
      marginal state * marginal data.anchor ≤
        ((data.spread * data.spread) * profile state) *
          marginal data.anchor := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv ?_)
      (Q'.le_trans' _ _ _ hprojective
        (Q'.le_of_eqv ?_))
    · exact Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv _ _)
        (Q'.mul_eqv_congr_right _ _
          (marginal state)
          (Q'.eqv_symm data.anchor_match))
    · q_ring
  exact le_of_mul_le_mul_right_pos
    data.marginal_anchor_pos hanchorRewrite

theorem lower_window
    {State : Type}
    {states : List State}
    {profile marginal : State → Q'}
    (data :
      AnchoredProjectiveProfile states profile marginal)
    (state : State) (hstate : state ∈ states) :
    anchoredProjectiveFloor * marginal state ≤
      profile state := by
  have hprojective :=
    data.lower_projective_window state hstate
  have hprofile : (0 : Q') ≤ profile state :=
    data.profile_nonnegative state hstate
  have hceiling :
      marginal state ≤
        anchoredProjectiveCeiling * profile state :=
    Q'.le_trans' _ _ _ hprojective
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        data.spreadSquare_le hprofile)
  have hfloorNonnegative :
      (0 : Q') ≤ anchoredProjectiveFloor := by
    decide
  have hscaled :
      anchoredProjectiveFloor * marginal state ≤
        anchoredProjectiveFloor *
          (anchoredProjectiveCeiling * profile state) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      hceiling hfloorNonnegative
  refine Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm (Q'.mul_assoc_eqv
          anchoredProjectiveFloor
          anchoredProjectiveCeiling
          (profile state)))) ?_)
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      anchoredProjectiveFloor_mul_ceiling_le_one
      hprofile)
    (Q'.le_of_eqv (Q'.one_mul_eqv (profile state)))

/-- **Anchored-projective-to-Harnack theorem.** -/
theorem relative_sixtyFourth
    {State : Type}
    {states : List State}
    {profile marginal : State → Q'}
    (data :
      AnchoredProjectiveProfile states profile marginal)
    (state : State) (hstate : state ∈ states)
    (hmarginal : (0 : Q') ≤ marginal state) :
    Q'.abs (profile state + (-marginal state)) ≤
      anchoredProjectiveTolerance * marginal state := by
  let epsilon :=
    anchoredProjectiveTolerance * marginal state
  have hupper :=
    data.upper_window state hstate hmarginal
  have hlower :=
    data.lower_window state hstate
  have hfirst :
      profile state ≤ marginal state + epsilon :=
    Q'.le_trans' _ _ _ hupper
      (Q'.le_of_eqv
        (anchoredProjectiveCeiling_mul_eqv_add
          (marginal state)))
  have hfloorAdd :
      anchoredProjectiveFloor * marginal state +
          epsilon ≤
        profile state + epsilon :=
    Q'.add_le_add_right _ _ _ hlower
  have hsecond :
      marginal state ≤ profile state + epsilon :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (anchoredProjectiveFloor_mul_add_eqv
          (marginal state)))
      hfloorAdd
  exact CReal.abs_sub_le_of_bounds hfirst hsecond

end AnchoredProjectiveProfile

end YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack.le_of_mul_le_mul_right_pos
#print axioms YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack.AnchoredProjectiveProfile.ofKernelActions
#print axioms YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack.AnchoredProjectiveProfile.marginalEqv
#print axioms YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack.AnchoredProjectiveProfile.relative_sixtyFourth
