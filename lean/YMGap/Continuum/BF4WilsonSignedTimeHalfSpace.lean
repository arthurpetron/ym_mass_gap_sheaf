/-
# Geometric half-space coverage of the original signed Wilson sources

The existing physical forward map decreases signed time. Its supported
half-space is therefore t <= 0. An expression in that half-space is recoded
as an actual intrinsic source at its computed radius, with a literal inverse
and the existing finite polynomial coordinate-support certificate.

Generators here are spatial loops at single time slices. Products may mix
slice times; arbitrary spacetime loops are not claimed. This fixed-spacing
source construction does not supply the canonical two-parameter support
field or change its rational scalar interface.
-/

import YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding

namespace YMGap.Continuum.BF4WilsonSignedTimeHalfSpace

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSignedTimeExpression
open YMGap.Continuum.BF4WilsonSignedTimeExpectation
  (fromIntrinsic mean mean_reflected_intrinsic)
open YMGap.Continuum.BF4WilsonSignedTimeBaseInclusion (inclusion)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
  (WindowExpression sourcePolynomial source_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression intrinsicForm_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
  (centeredExpression centered_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
  (SupportedQuaternionBlocks)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Physical forward support, with the existing signed-coordinate convention.
This is a predicate on literal syntax, not every representative of a quotient. -/
def LowerHalf {base : Nat} : Expression base → Prop
  | .one => True
  | .loop time _ _ => time ≤ 0
  | .add e f => LowerHalf e ∧ LowerHalf f
  | .mul e f => LowerHalf e ∧ LowerHalf f
  | .smul _ e => LowerHalf e

theorem lowerHalf_ofWindow_iff {base : Nat} (H : Nat) :
    ∀ e : WindowExpression base,
      LowerHalf (ofWindow H e) ↔ BF4ExactSlabFixedSpatialWilsonWindow.Within H e
  | .one => Iff.rfl
  | .loop offset _ _ => by
      change ((offset : Int)-(H : Int) ≤ 0) ↔ offset ≤ H
      constructor <;> intro h <;> omega
  | .add e f => and_congr (lowerHalf_ofWindow_iff H e) (lowerHalf_ofWindow_iff H f)
  | .mul e f => and_congr (lowerHalf_ofWindow_iff H e) (lowerHalf_ofWindow_iff H f)
  | .smul _ e => lowerHalf_ofWindow_iff H e

theorem fromIntrinsic_lowerHalf {base : Nat} (x : IntrinsicExpression base) :
    LowerHalf (fromIntrinsic x) :=
  (lowerHalf_ofWindow_iff x.radius x.expression).mpr x.within

theorem lowerHalf_inclusion_iff {base larger : Nat} (h : base ≤ larger) :
    ∀ e : Expression base, LowerHalf (inclusion h e) ↔ LowerHalf e
  | .one => Iff.rfl
  | .loop _ _ _ => Iff.rfl
  | .add e f => and_congr (lowerHalf_inclusion_iff h e) (lowerHalf_inclusion_iff h f)
  | .mul e f => and_congr (lowerHalf_inclusion_iff h e) (lowerHalf_inclusion_iff h f)
  | .smul _ e => lowerHalf_inclusion_iff h e

theorem lowerHalf_forward {base : Nat} (n : Nat) :
    ∀ e : Expression base, LowerHalf e → LowerHalf (forward n e)
  | .one, _ => True.intro
  | .loop time _ _, he => by
      change time ≤ 0 at he
      change time-(n : Int) ≤ 0
      omega
  | .add e f, he => ⟨lowerHalf_forward n e he.1, lowerHalf_forward n f he.2⟩
  | .mul e f, he => ⟨lowerHalf_forward n e he.1, lowerHalf_forward n f he.2⟩
  | .smul _ e, he => lowerHalf_forward n e he

/-- A witnessed finite delay puts every signed source into the supported half. -/
theorem forward_within_lowerHalf {base : Nat} (H : Nat) :
    ∀ e : Expression base, Within H e → LowerHalf (forward H e)
  | .one, _ => True.intro
  | .loop time _ _, he => by
      change -(H : Int) ≤ time ∧ time ≤ (H : Int) at he
      change time-(H : Int) ≤ 0
      omega
  | .add e f, he => ⟨forward_within_lowerHalf H e he.1, forward_within_lowerHalf H f he.2⟩
  | .mul e f, he => ⟨forward_within_lowerHalf H e he.1, forward_within_lowerHalf H f he.2⟩
  | .smul _ e, he => forward_within_lowerHalf H e he

/-- The window guard excludes Int.toNat truncation in the literal inverse. -/
theorem ofWindow_window {base : Nat} (H : Nat) :
    ∀ e : Expression base, Within H e → ofWindow H (window H e) = e
  | .one, _ => rfl
  | .loop time value spin, he => by
      change -(H : Int) ≤ time ∧ time ≤ (H : Int) at he
      change Expression.loop (((((H : Int)+time).toNat) : Int)-(H : Int)) value spin =
        .loop time value spin
      congr 1
      omega
  | .add e f, he => by
      change Expression.add (ofWindow H (window H e)) (ofWindow H (window H f)) = .add e f
      rw [ofWindow_window H e he.1, ofWindow_window H f he.2]
  | .mul e f, he => by
      change Expression.mul (ofWindow H (window H e)) (ofWindow H (window H f)) = .mul e f
      rw [ofWindow_window H e he.1, ofWindow_window H f he.2]
  | .smul c e, he => by
      change Expression.smul c (ofWindow H (window H e)) = .smul c e
      rw [ofWindow_window H e he]

theorem window_halfWithin {base : Nat} (H : Nat) :
    ∀ e : Expression base, Within H e → LowerHalf e →
      BF4ExactSlabFixedSpatialWilsonWindow.Within H (window H e)
  | .one, _, _ => True.intro
  | .loop time _ _, he, hp => by
      change -(H : Int) ≤ time ∧ time ≤ (H : Int) at he
      change time ≤ 0 at hp
      change ((H : Int)+time).toNat ≤ H
      omega
  | .add e f, he, hp =>
      ⟨window_halfWithin H e he.1 hp.1, window_halfWithin H f he.2 hp.2⟩
  | .mul e f, he, hp =>
      ⟨window_halfWithin H e he.1 hp.1, window_halfWithin H f he.2 hp.2⟩
  | .smul _ e, he, hp => window_halfWithin H e he hp

/-- Actual supported source; its radius and support witness remain data. -/
def toIntrinsic {base : Nat} (e : Expression base) (he : LowerHalf e) : IntrinsicExpression base :=
  ⟨radius e, window (radius e) e, window_halfWithin (radius e) e (within_radius e) he⟩

theorem fromIntrinsic_toIntrinsic {base : Nat} (e : Expression base) (he : LowerHalf e) :
    fromIntrinsic (toIntrinsic e he) = e :=
  ofWindow_window (radius e) e (within_radius e)

/-- Complete support of the polynomial, including all signed cross terms. -/
theorem window_source_supported {base : Nat} (H : Nat) (e : Expression base)
    (he : Within H e) (hp : LowerHalf e) :
    SupportedQuaternionBlocks ((H+1)*(baseLinks base).length)
      (sourcePolynomial (window H e)) :=
  source_supported H (window H e) (window_halfWithin H e he hp)

/-- The same half-window bound survives every actual spatial padding. Heat
cutoff does not enter this source polynomial's definition. -/
theorem centered_source_supported {base : Nat} (r H : Nat) (e : Expression base)
    (he : Within H e) (hp : LowerHalf e) :
    SupportedQuaternionBlocks ((H+1)*(baseLinks (paddedWidth base r)).length)
      (sourcePolynomial (centeredExpression r (window H e))) :=
  source_supported H (centeredExpression r (window H e))
    ((centered_within r H (window H e)).mpr (window_halfWithin H e he hp))

/-- Every finite signed source has an explicit supported time translate. -/
def shiftedSource {base : Nat} (e : Expression base) : IntrinsicExpression base :=
  toIntrinsic (forward (radius e) e) (forward_within_lowerHalf (radius e) e (within_radius e))

theorem fromIntrinsic_shiftedSource {base : Nat} (e : Expression base) :
    fromIntrinsic (shiftedSource e) = forward (radius e) e :=
  fromIntrinsic_toIntrinsic _ _

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) {base : Nat} (hb : 0 < base)

/-- Geometric half-space positivity for the original signed-time mean. -/
theorem mean_reflection_positive (e : Expression base) (he : LowerHalf e) :
    leEv (ofQ' 0) (mean hw0 hw1 hsmall hd hs hb (.mul (reflect e) e)) := by
  have h := mean_reflected_intrinsic hw0 hw1 hsmall hd hs hb (toIntrinsic e he) (toIntrinsic e he)
  rw [fromIntrinsic_toIntrinsic] at h
  exact leEv_trans (intrinsicForm_nonnegative hw0 hw1 hsmall hd hs hb (toIntrinsic e he))
    (leEv_of_equiv h.symm)

/-- This source is an element of the actual supported observable quotient. -/
def supportedObservable (e : Expression base) (he : LowerHalf e) :
    BF4WilsonSpatialUnionObservableQuotient.Observable hw0 hw1 hsmall hd hs :=
  BF4WilsonSpatialUnionObservableQuotient.ofStage hw0 hw1 hsmall hd hs
    ⟨base, hb, toIntrinsic e he⟩

theorem embedding_supportedObservable (e : Expression base) (he : LowerHalf e) :
    BF4WilsonSignedTimeUnionSupportedEmbedding.embedding hw0 hw1 hsmall hd hs
        (supportedObservable hw0 hw1 hsmall hd hs hb e he) =
      BF4WilsonSignedTimeUnionObservable.ofStage hw0 hw1 hsmall hd hs ⟨base, hb, e⟩ := by
  change BF4WilsonSignedTimeUnionObservable.ofStage hw0 hw1 hsmall hd hs
    ⟨base, hb, fromIntrinsic (toIntrinsic e he)⟩ = _
  rw [fromIntrinsic_toIntrinsic]

end YMGap.Continuum.BF4WilsonSignedTimeHalfSpace

#print axioms YMGap.Continuum.BF4WilsonSignedTimeHalfSpace.LowerHalf
#print axioms YMGap.Continuum.BF4WilsonSignedTimeHalfSpace.lowerHalf_ofWindow_iff
#print axioms YMGap.Continuum.BF4WilsonSignedTimeHalfSpace.fromIntrinsic_lowerHalf
#print axioms YMGap.Continuum.BF4WilsonSignedTimeHalfSpace.lowerHalf_inclusion_iff
#print axioms YMGap.Continuum.BF4WilsonSignedTimeHalfSpace.lowerHalf_forward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeHalfSpace.forward_within_lowerHalf
#print axioms YMGap.Continuum.BF4WilsonSignedTimeHalfSpace.ofWindow_window
#print axioms YMGap.Continuum.BF4WilsonSignedTimeHalfSpace.window_halfWithin
#print axioms YMGap.Continuum.BF4WilsonSignedTimeHalfSpace.toIntrinsic
#print axioms YMGap.Continuum.BF4WilsonSignedTimeHalfSpace.fromIntrinsic_toIntrinsic
#print axioms YMGap.Continuum.BF4WilsonSignedTimeHalfSpace.window_source_supported
#print axioms YMGap.Continuum.BF4WilsonSignedTimeHalfSpace.centered_source_supported
#print axioms YMGap.Continuum.BF4WilsonSignedTimeHalfSpace.shiftedSource
#print axioms YMGap.Continuum.BF4WilsonSignedTimeHalfSpace.fromIntrinsic_shiftedSource
#print axioms YMGap.Continuum.BF4WilsonSignedTimeHalfSpace.mean_reflection_positive
#print axioms YMGap.Continuum.BF4WilsonSignedTimeHalfSpace.supportedObservable
#print axioms YMGap.Continuum.BF4WilsonSignedTimeHalfSpace.embedding_supportedObservable
