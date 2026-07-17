/-
# Four-block recoding for an oriented heterogeneous doubled-time entry

For strict presentations `left` and `right`, the oriented mixed coefficient
uses the lower fingerprint of the transported `left` roots and the upper
fingerprint of the doubled-time translated `right` roots.  Putting those two
root lists into one ordinary strict-joint chart produces four blocks of
unequal possible lengths

  lower-left, lower-right, upper-left, upper-right.

The projection in this file retains the first and fourth blocks.  We prove
both the arbitrary-radius cylinder identity and the aligned fixed-stage
identity with the heterogeneous signed chart constructed in the oriented
spatial comparison.  This is finite syntax and canonical root geometry; no
law or limiting assumption is introduced.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointHeterogeneousBipushforward
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedSignedSpatialComparison
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointFixedStageRecoding

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeJointRecoding

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderPresentation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointFixedStageRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedSignedSpatialComparison
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionUpperSupportLocalQuery

/-! ## 1. Common-box vectors and the selected two-block cylinder -/

def orientedDoubledTimeSource
    {base : Nat} (shift : Nat)
    (left : StrictJointCylinderVector base) :
    StrictJointCylinderVector (base + (shift + shift)) :=
  boxTransportStrictJointCylinderVector
    (Nat.le_add_right base (shift + shift)) left

def orientedDoubledTimeTarget
    {base : Nat} (shift : Nat)
    (right : StrictJointCylinderVector base) :
    StrictJointCylinderVector (base + (shift + shift)) :=
  timeTranslateStrictJointCylinderVector (shift + shift) right

/-- The two common-box root lists regarded as one ordinary strict-joint root
list. -/
def orientedDoubledTimeJointRoots
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) : List (List Nat) :=
  (orientedDoubledTimeSource shift left).roots ++
    (orientedDoubledTimeTarget shift right).roots

@[simp] theorem orientedDoubledTimeJointRoots_length
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) :
    (orientedDoubledTimeJointRoots shift left right).length =
      left.roots.length + right.roots.length := by
  unfold orientedDoubledTimeJointRoots
    orientedDoubledTimeSource orientedDoubledTimeTarget
    boxTransportStrictJointCylinderVector transportedCylinderRoots
  simp only [List.length_append, List.length_map,
    timeTranslateStrictJointCylinderVector_roots]

theorem orientedDoubledTimeJointRoots_canonical
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) :
    ∀ root, root ∈ orientedDoubledTimeJointRoots shift left right →
      root ∈ canonicalSurfacePolymers (base + (shift + shift)) := by
  intro root hroot
  rcases List.mem_append.mp hroot with hleft | hright
  · exact (orientedDoubledTimeSource shift left).rootsCanonical root hleft
  · exact (orientedDoubledTimeTarget shift right).rootsCanonical root hright

/-- The actual selected lower-left and upper-right query roots at a common
reflection radius. -/
def orientedDoubledTimeCommonCylinderRoots
    {base : Nat} (radius shift : Nat)
    (left right : StrictJointCylinderVector base) : List (List Nat) :=
  let outer := base + (shift + shift)
  centralStrictLowerCylinderRoots radius outer
      (orientedDoubledTimeSource shift left).roots ++
    centralStrictUpperCylinderRoots radius outer
      (orientedDoubledTimeTarget shift right).roots

/-! ## 2. Unequal four-block projection -/

/-- Retain the first block of length `leftCount` and the fourth block, after
skipping the intervening blocks of lengths `rightCount` and `leftCount`. -/
def orientedDoubledTimeJointProjection
    (leftCount rightCount : Nat) (bits : List Bool) : List Bool :=
  bits.take leftCount ++
    bits.drop (leftCount + (rightCount + leftCount))

def orientedDoubledTimeJointPredicate
    (leftCount rightCount : Nat)
    (leftBits rightBits : List Bool) : List Bool → Bool :=
  fun bits => centralStrictJointPairPredicate
    leftCount leftBits rightBits
      (orientedDoubledTimeJointProjection leftCount rightCount bits)

private theorem oriented_four_block_projection
    (leftCount rightCount : Nat)
    (first second third fourth : List Bool)
    (hfirst : first.length = leftCount)
    (hsecond : second.length = rightCount)
    (hthird : third.length = leftCount) :
    orientedDoubledTimeJointProjection leftCount rightCount
        ((first ++ second) ++ (third ++ fourth)) =
      first ++ fourth := by
  unfold orientedDoubledTimeJointProjection
  rw [show (first ++ second) ++ (third ++ fourth) =
      first ++ (second ++ (third ++ fourth)) by
        simp only [List.append_assoc]]
  rw [← hfirst, List.take_append_length]
  rw [List.drop_length_add_append]
  have hskip : rightCount + first.length =
      second.length + third.length := by omega
  rw [hskip, List.drop_length_add_append, List.drop_append_length]

/-- Generic cylinder form of the four-block projection. -/
theorem orientedProjectedFourBlockCylinderEvent_eq
    (leftCount rightCount : Nat)
    (firstRoots secondRoots thirdRoots fourthRoots : List (List Nat))
    (hfirst : firstRoots.length = leftCount)
    (hsecond : secondRoots.length = rightCount)
    (hthird : thirdRoots.length = leftCount)
    (leftBits rightBits : List Bool) :
    sourceCylinderEvent
        ((firstRoots ++ secondRoots) ++ (thirdRoots ++ fourthRoots))
        (orientedDoubledTimeJointPredicate
          leftCount rightCount leftBits rightBits) =
      sourceCylinderEvent
        (firstRoots ++ fourthRoots)
        (centralStrictJointPairPredicate
          leftCount leftBits rightBits) := by
  funext family
  unfold sourceCylinderEvent cylinderEvent
    orientedDoubledTimeJointPredicate
  simp only [familyOccurrenceFingerprint_append]
  apply congrArg (centralStrictJointPairPredicate
    leftCount leftBits rightBits)
  apply oriented_four_block_projection
  · rw [familyOccurrenceFingerprint_length, hfirst]
  · rw [familyOccurrenceFingerprint_length, hsecond]
  · rw [familyOccurrenceFingerprint_length, hthird]

/-- At every radius, the projected ordinary joint cylinder is literally the
selected lower-left/upper-right common cylinder. -/
theorem orientedDoubledTimeJointEvent_eq_common
    {base : Nat} (shift radius : Nat)
    (left right : StrictJointCylinderVector base)
    (leftBits rightBits : List Bool) :
    sourceCylinderEvent
        (centralStrictJointCylinderRoots
          radius (base + (shift + shift))
          (orientedDoubledTimeJointRoots shift left right))
        (orientedDoubledTimeJointPredicate
          left.roots.length right.roots.length leftBits rightBits) =
      sourceCylinderEvent
        (orientedDoubledTimeCommonCylinderRoots
          radius shift left right)
        (centralStrictJointPairPredicate
          left.roots.length leftBits rightBits) := by
  unfold centralStrictJointCylinderRoots
    centralStrictLowerCylinderRoots centralStrictUpperCylinderRoots
    orientedDoubledTimeJointRoots
    orientedDoubledTimeCommonCylinderRoots
  simp only [List.map_append]
  apply orientedProjectedFourBlockCylinderEvent_eq
  · unfold orientedDoubledTimeSource
      boxTransportStrictJointCylinderVector transportedCylinderRoots
    simp only [List.length_map]
  · unfold orientedDoubledTimeTarget
    simp only [timeTranslateStrictJointCylinderVector_roots,
      List.length_map]
  · unfold orientedDoubledTimeSource
      boxTransportStrictJointCylinderVector transportedCylinderRoots
    simp only [List.length_map]

/-! ## 3. Aligned fixed-stage signed recoding -/

/-- The selected lower-left and upper-right roots of the aligned ordinary
joint chart are exactly the heterogeneous oriented mixed roots. -/
theorem orientedDoubledTimeSelectedCenteredRoots_eq
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (left right : StrictJointCylinderVector base) :
    (orientedDoubledTimeSource shift left).roots.map
          (centralStrictLowerCenteredStageRoot
            (base + (shift + shift))
            (fixedStage - (shift + shift))) ++
        (orientedDoubledTimeTarget shift right).roots.map
          (centralStrictUpperCenteredStageRoot
            (base + (shift + shift))
            (fixedStage - (shift + shift))) =
      orientedDoubledTimeMixedCenteredRoots
        base shift fixedStage left.roots right.roots := by
  unfold orientedDoubledTimeSource orientedDoubledTimeTarget
    boxTransportStrictJointCylinderVector transportedCylinderRoots
    orientedDoubledTimeMixedCenteredRoots
    strictJointDoubledTimeMixedCenteredUpperRoot
  simp only [timeTranslateStrictJointCylinderVector_roots,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro root hroot
  simp only [Function.comp_apply]
  exact strictJointDoubledTimeMixedJointLowerCenteredRoot_eq
    hstage (left.rootsCanonical root hroot)

/-- Exact fixed-stage recoding into the heterogeneous signed mixed chart. -/
theorem orientedDoubledTimeJointCenteredEvent_eq_signedMixed
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (left right : StrictJointCylinderVector base)
    (leftBits rightBits : List Bool) :
    sourceCylinderEvent
        (centralStrictJointCenteredStageRoots
          (base + (shift + shift))
          (fixedStage - (shift + shift))
          (orientedDoubledTimeJointRoots shift left right))
        (orientedDoubledTimeJointPredicate
          left.roots.length right.roots.length leftBits rightBits) =
      sourceCylinderEvent
        (orientedDoubledTimeMixedCenteredRoots
          base shift fixedStage left.roots right.roots)
        (centralStrictJointPairPredicate
          left.roots.length leftBits rightBits) := by
  rw [centralStrictJointCenteredStageRoots_split]
  unfold orientedDoubledTimeJointRoots
  simp only [List.map_append]
  rw [orientedProjectedFourBlockCylinderEvent_eq
    left.roots.length right.roots.length
    ((orientedDoubledTimeSource shift left).roots.map
      (centralStrictLowerCenteredStageRoot
        (base + (shift + shift))
        (fixedStage - (shift + shift))))
    ((orientedDoubledTimeTarget shift right).roots.map
      (centralStrictLowerCenteredStageRoot
        (base + (shift + shift))
        (fixedStage - (shift + shift))))
    ((orientedDoubledTimeSource shift left).roots.map
      (centralStrictUpperCenteredStageRoot
        (base + (shift + shift))
        (fixedStage - (shift + shift))))
    ((orientedDoubledTimeTarget shift right).roots.map
      (centralStrictUpperCenteredStageRoot
        (base + (shift + shift))
        (fixedStage - (shift + shift))))]
  · rw [orientedDoubledTimeSelectedCenteredRoots_eq
      hstage left right]
  · unfold orientedDoubledTimeSource
      boxTransportStrictJointCylinderVector transportedCylinderRoots
    simp only [List.length_map]
  · unfold orientedDoubledTimeTarget
    simp only [timeTranslateStrictJointCylinderVector_roots,
      List.length_map]
  · unfold orientedDoubledTimeSource
      boxTransportStrictJointCylinderVector transportedCylinderRoots
    simp only [List.length_map]

#print axioms orientedDoubledTimeJointRoots_canonical
#print axioms orientedProjectedFourBlockCylinderEvent_eq
#print axioms orientedDoubledTimeJointEvent_eq_common
#print axioms orientedDoubledTimeSelectedCenteredRoots_eq
#print axioms orientedDoubledTimeJointCenteredEvent_eq_signedMixed

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeJointRecoding
