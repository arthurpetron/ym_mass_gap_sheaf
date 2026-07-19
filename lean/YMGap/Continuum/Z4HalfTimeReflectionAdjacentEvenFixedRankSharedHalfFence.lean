/-
# Fence against fixed-original-rank shared-half gluing

The local fixed-face Gram is a sum of rank-one features.  It is tempting to
hold one original Gram rank fixed while composing adjacent faces, and then
to seek one common half-feature for that contribution.  This file records a
finite obstruction to that strategy before any Cartesian endpoint carrier is
enumerated.

Let `u0`, `u1`, and `u2` be the constant four-channel states with labels zero,
one, and two.  The symmetric-edge feature belonging to the ordered pair
`(u0,u1)` is the indicator of `{u0,u1}`; the feature belonging to `(u1,u2)`
is the indicator of `{u1,u2}`.  Compose those two rank-one face terms across
one shared channel, summing the literal production range `0,...,12`.  With
the six private channels fixed so that the first face sees `u0 -> u1` and the
second sees `u1 -> u2`, the forward entry is one and the reversed entry is
zero.  Hence this fixed-rank contribution is not symmetric.

Every sum of same-half outer products is symmetric, even if its rank weight
is signed and even if an arbitrary finite glue coordinate is retained.
Consequently the contribution below cannot have the fixed-original-rank
shared-half form used by a rank-aware Gram transport.

Production instantiation.  At `K = 2`, hence channel cutoff `12`, the packed
`(u0,u1)` and `(u1,u2)` coordinates of
`anchorJointFourEdgeFeatureGramRep` have exactly the two indicator features
used here.  Their derived edge weights are positive.  The two full patch
states below merely supply the private coordinates that realize those local
four-channel states; the only contracted coordinate is their shared channel.
Thus positive production weights rescale this nonsymmetric skeleton but do
not repair it.  We intentionally do not compute the packed positions in the
large four-channel Cartesian list: the support obstruction is independent of
that enumeration.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedInterfaceEndpointOperator

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedRankSharedHalfFence

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedInterfaceEndpointOperator
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceBlock

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Two production edge-feature supports -/

def fixedRankFenceU0 : FourChannels := ⟨0, 0, 0, 0⟩

def fixedRankFenceU1 : FourChannels := ⟨1, 1, 1, 1⟩

def fixedRankFenceU2 : FourChannels := ⟨2, 2, 2, 2⟩

/-- The feature of the symmetric-edge Gram rank joining `u0` to `u1`. -/
def fixedRankFenceE01 (state : FourChannels) : Q' :=
  if state = fixedRankFenceU0 ∨ state = fixedRankFenceU1 then 1 else 0

/-- The feature of the symmetric-edge Gram rank joining `u1` to `u2`. -/
def fixedRankFenceE12 (state : FourChannels) : Q' :=
  if state = fixedRankFenceU1 ∨ state = fixedRankFenceU2 then 1 else 0

/-! ## 2. The literal two-face, thirteen-middle-state contribution -/

/-- On the left, face A has private labels zero and face B has private labels
one.  Together with a shared label zero, face A therefore sees `u0`. -/
def fixedRankFencePatchLeft : TwoFacePatchChannels :=
  ⟨0, 0, 0, 0, 1, 1, 1⟩

/-- On the right, face A has private labels one and face B has private labels
two.  Together with a shared label two, face B therefore sees `u2`. -/
def fixedRankFencePatchRight : TwoFacePatchChannels :=
  ⟨2, 1, 1, 1, 2, 2, 2⟩

/-- The seven-channel endpoints and middle label one realize the local chain
`u0 -> u1 -> u2` literally.  This is the finite production embedding of the
three abstract supports; no Cartesian position lookup is involved. -/
theorem fixedRankFencePatch_realizes_support_chain :
    twoFacePatchAChannels fixedRankFencePatchLeft = fixedRankFenceU0 ∧
      (⟨1, fixedRankFencePatchRight.firstA,
          fixedRankFencePatchRight.secondA,
          fixedRankFencePatchRight.thirdA⟩ : FourChannels) =
        fixedRankFenceU1 ∧
      (⟨1, fixedRankFencePatchLeft.firstB,
          fixedRankFencePatchLeft.secondB,
          fixedRankFencePatchLeft.thirdB⟩ : FourChannels) =
        fixedRankFenceU1 ∧
      twoFacePatchBChannels fixedRankFencePatchRight = fixedRankFenceU2 := by
  decide

/-- Composition of the selected face-A rank `(u0,u1)` and face-B rank
`(u1,u2)`.  The shared middle channel runs over the exact `K = 2`
production window of length thirteen. -/
def fixedRankFenceTwoFaceContribution
    (left right : TwoFacePatchChannels) : Q' :=
  finSum (fun middle =>
    (fixedRankFenceE01 (twoFacePatchAChannels left) *
        fixedRankFenceE01
          ⟨middle, right.firstA, right.secondA, right.thirdA⟩) *
      (fixedRankFenceE12
          ⟨middle, left.firstB, left.secondB, left.thirdB⟩ *
        fixedRankFenceE12 (twoFacePatchBChannels right))) 13

/-- The unique common support point is the middle label one. -/
theorem fixedRankFenceTwoFaceContribution_forward :
    fixedRankFenceTwoFaceContribution
      fixedRankFencePatchLeft fixedRankFencePatchRight ≈ 1 := by
  decide

/-- Reversing the endpoints misses both oriented support chains. -/
theorem fixedRankFenceTwoFaceContribution_reverse :
    fixedRankFenceTwoFaceContribution
      fixedRankFencePatchRight fixedRankFencePatchLeft ≈ 0 := by
  decide

/-- The selected fixed-original-rank two-face contribution is genuinely
nonsymmetric. -/
theorem fixedRankFenceTwoFaceContribution_not_symmetric :
    ¬ (fixedRankFenceTwoFaceContribution
          fixedRankFencePatchLeft fixedRankFencePatchRight ≈
        fixedRankFenceTwoFaceContribution
          fixedRankFencePatchRight fixedRankFencePatchLeft) := by
  decide

/-! ## 3. Same-half sums are symmetric, so cannot represent the patch -/

/-- The most permissive fixed-original-rank same-half ansatz needed here.
The original rank weight is retained, while the half feature may depend on
an arbitrary finite glue coordinate. -/
def fixedOriginalRankSharedHalfContribution
    (rankWeight : Q')
    (halfFeature : Nat → TwoFacePatchChannels → Q')
    (glueCount : Nat) (left right : TwoFacePatchChannels) : Q' :=
  finSum (fun glue =>
    rankWeight * (halfFeature glue left * halfFeature glue right)) glueCount

theorem fixedOriginalRankSharedHalfContribution_symmetric
    (rankWeight : Q')
    (halfFeature : Nat → TwoFacePatchChannels → Q')
    (glueCount : Nat) (left right : TwoFacePatchChannels) :
    fixedOriginalRankSharedHalfContribution rankWeight halfFeature
        glueCount left right ≈
      fixedOriginalRankSharedHalfContribution rankWeight halfFeature
        glueCount right left := by
  unfold fixedOriginalRankSharedHalfContribution
  exact finSum_eqv_congr _ _ (fun glue =>
    Q'.mul_eqv_congr_left rankWeight _ _
      (Q'.mul_comm_eqv
        (halfFeature glue left) (halfFeature glue right))) glueCount

/-- Abstract reusable fence: a nonsymmetric kernel cannot be one fixed
original rank paired through any finite family of common half features. -/
theorem nonsymmetricKernel_not_fixedOriginalRankSharedHalf
    {kernel : TwoFacePatchChannels → TwoFacePatchChannels → Q'}
    {left right : TwoFacePatchChannels}
    (hnonsymmetric : ¬ (kernel left right ≈ kernel right left)) :
    ¬ ∃ (glueCount : Nat) (rankWeight : Q')
        (halfFeature : Nat → TwoFacePatchChannels → Q'),
      ∀ source target,
        kernel source target ≈
          fixedOriginalRankSharedHalfContribution rankWeight halfFeature
            glueCount source target := by
  rintro ⟨glueCount, rankWeight, halfFeature, hfactor⟩
  apply hnonsymmetric
  exact Q'.eqv_trans _ _ _ (hfactor left right)
    (Q'.eqv_trans _ _ _
      (fixedOriginalRankSharedHalfContribution_symmetric
        rankWeight halfFeature glueCount left right)
      (Q'.eqv_symm (hfactor right left)))

/-- No choice of finite glue carrier, retained rank weight, or common
half-feature can reproduce the audited two-face rank contribution. -/
theorem fixedRankFenceTwoFaceContribution_not_sharedHalf :
    ¬ ∃ (glueCount : Nat) (rankWeight : Q')
        (halfFeature : Nat → TwoFacePatchChannels → Q'),
      ∀ left right,
        fixedRankFenceTwoFaceContribution left right ≈
          fixedOriginalRankSharedHalfContribution rankWeight halfFeature
            glueCount left right :=
  nonsymmetricKernel_not_fixedOriginalRankSharedHalf
    fixedRankFenceTwoFaceContribution_not_symmetric

#print axioms fixedRankFenceTwoFaceContribution_forward
#print axioms fixedRankFenceTwoFaceContribution_reverse
#print axioms fixedRankFenceTwoFaceContribution_not_symmetric
#print axioms fixedRankFencePatch_realizes_support_chain
#print axioms fixedOriginalRankSharedHalfContribution_symmetric
#print axioms nonsymmetricKernel_not_fixedOriginalRankSharedHalf
#print axioms fixedRankFenceTwoFaceContribution_not_sharedHalf

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedRankSharedHalfFence
