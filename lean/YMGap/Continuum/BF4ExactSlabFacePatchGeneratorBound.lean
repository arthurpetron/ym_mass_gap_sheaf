/-
# Improved original conditional-generator margin from physical face patches

The actual small-nome pair estimate supplies a face coefficient 1-6e.
Exact physical incidence turns it into the global coefficient 1-36e,
improving the previous coarse 1-50e count. No patch-gap hypothesis remains.

At the exact nome 1/40 the new margin is positive and the old one negative.
This proves a strictly larger certified parameter region, not a continuum
scaling trajectory or an OS/physical Hamiltonian gap.
-/

import YMGap.Continuum.BF4ExactSlabFacePatchEnergy
import YMGap.Continuum.BF4ExactSlabFacePatchSmallNome

namespace YMGap.Continuum.BF4ExactSlabFacePatchGeneratorBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabSignedNeighborEnergy
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabTwoLinkResidualLowerBound
open YMGap.Continuum.BF4ExactSlabFacePatchEnergy
open YMGap.Continuum.BF4ExactSlabFacePatchSmallNome
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Original nome-dependent margin, with no extent or late-cutoff argument. -/
def margin {w : Q'} (hd : heatRemainderBound w < (1 : Q')) : Q' :=
  1 + -(36 * pairCoefficient hd)

theorem margin_pin {w : Q'} (hd : heatRemainderBound w < (1 : Q')) :
    Q'.eqv (faceMargin (faceCoefficient hd)) (margin hd) := by
  unfold faceMargin faceCoefficient margin
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.const 1) (.neg (.mul (.const 6)
      (.add (.const 1) (.neg (.add (.const 1)
        (.neg (.mul (.const 6) (.var 0)))))))))
    (.add (.const 1) (.neg (.mul (.const 36) (.var 0))))
    (by decide) (fun _ => pairCoefficient hd)

theorem old_margin_le {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < (1 : Q')) :
    BF4ExactSlabConditionalGeneratorMargin.margin hd ≤ margin hd := by
  have h := Q'.mul_le_mul_of_nonneg_right (36 : Q') 50 (pairCoefficient hd)
    (by decide : (36 : Q') ≤ 50) (pairCoefficient_nonnegative hw0 hd)
  exact Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg h)

/-- Strictly sharper collective bound on the SAME original completed
conditional generator, under the original proved small-nome comparison guards. -/
theorem generator_square_lower {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (x : GNSCompletionSpace
      (fullData hw0 hw1 K extent hK)) :
    RCle (RCscale (margin hd)
      ((projections hw0 hw1 K extent hK).finalEnergy (schedule extent) x))
      (normSq (conditionalGenerator hw0 hw1 K extent hK x)) := by
  have h := generator_square_lower_of_face_bounds hw0 hw1 K extent hK
    (faceCoefficient hd) (faceCoefficient_le_one hw0 hd) x
    (fun id _ => actual_face_lower hw0 hw1 hsmall hd K extent hK id x)
  rw [RCSignedPairBudget.scale_congr (margin_pin hd)] at h
  exact h

/-- A finite rational point outside the old positive-margin certificate. -/
def expandedNome : Q' := ⟨1, 39⟩

theorem expandedNome_guards :
    (0 : Q') < expandedNome ∧ expandedNome < (1 : Q') ∧
      heatRatio expandedNome ≤ HalfPow.half ∧
        heatRemainderBound expandedNome < (1 : Q') := by decide

/-- The old scalar certificate fails here, while the new SAME-operator
lower margin is positive. This does not upper-bound the true spectral gap. -/
theorem expandedNome_margin_separation :
    (0 : Q') < margin expandedNome_guards.2.2.2 ∧
      BF4ExactSlabConditionalGeneratorMargin.margin expandedNome_guards.2.2.2 < (0 : Q') := by
  decide

/-- An actual positive, extent/late-cutoff independent completed generator
estimate at nome 1/40, with no analytic input left to supply. -/
theorem expandedNome_generator_square_lower (K extent : Nat)
    (hK : headCutoff expandedNome ≤ K)
    (x : GNSCompletionSpace (fullData expandedNome_guards.1 expandedNome_guards.2.1
      K extent hK)) :
    (0 : Q') < margin expandedNome_guards.2.2.2 ∧
      RCle (RCscale (margin expandedNome_guards.2.2.2)
        ((projections expandedNome_guards.1 expandedNome_guards.2.1 K extent hK).finalEnergy
          (schedule extent) x))
        (normSq (conditionalGenerator expandedNome_guards.1 expandedNome_guards.2.1 K extent hK x)) :=
  ⟨expandedNome_margin_separation.1,
    generator_square_lower expandedNome_guards.1 expandedNome_guards.2.1
      expandedNome_guards.2.2.1 expandedNome_guards.2.2.2 K extent hK x⟩

#print axioms margin
#print axioms margin_pin
#print axioms old_margin_le
#print axioms generator_square_lower
#print axioms expandedNome_guards
#print axioms expandedNome_margin_separation
#print axioms expandedNome_generator_square_lower

end YMGap.Continuum.BF4ExactSlabFacePatchGeneratorBound
