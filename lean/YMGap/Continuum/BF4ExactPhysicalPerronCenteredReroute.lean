/-
# Centered exact-Haar / physical-Perron reroute

The all-observable same-action seam is false: the exact and physical vacuum
code-delta quadratics differ.  The contraction consumers, however, only act
on the physical stationary-mean-zero subspace.  This file installs the
strictly weaker and still honest seam that they actually need.

`ExactHaarPhysicalPerronCenteredSameActionAt` asks for equality only after an
explicit `CentralPhysicalMeanZero` witness is supplied.  The old full seam
maps to it, but not conversely.  Both the symmetric-reference quarter and the
local-gluing sixteenth transfer through the centered seam.  An AF-family
wrapper retains the genuine local row witnesses without asking for the
refuted equality on constants or vacuum point observables.

This module does not inhabit centered same action or local gluing.  In
particular, it does not claim that centering removes the signed/positive
fusion obstruction; it only states the minimal surviving producer consumed
by the proved contraction algebra.

## Axiom gate

Finite lists and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactPhysicalPerronReroute

namespace YMGap.Continuum.BF4ExactPhysicalPerronCenteredReroute

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4CommonRankOneRowTriangle
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4LocalContractionGluing
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SymmetricReferenceOperatorComparison
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Minimal centered same-action seam -/

/-- Equality of the literal signed Haar quadratic and normalized positive
physical quadratic only on the physical stationary-mean-zero subspace. -/
structure ExactHaarPhysicalPerronCenteredSameActionAt
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Type where
  centered_same_action :
    ∀ observable,
      CentralPhysicalMeanZero w hw K 0 observable →
      exactSlabAllCutoffQuadratic w K observable ≈
        centralNormalizedFullPhysicalReflectionQuadratic
          w hw K 0 observable

/-- The refuted all-observable seam is strictly stronger and therefore still
adapts to the viable centered consumer. -/
def ExactHaarPhysicalPerronSameActionAt.toCentered
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (identification :
      ExactHaarPhysicalPerronSameActionAt w hw K) :
    ExactHaarPhysicalPerronCenteredSameActionAt w hw K where
  centered_same_action := fun observable _ =>
    identification.same_action observable

namespace ExactHaarPhysicalPerronCenteredSameActionAt

/-- Centered same action lands on the filtered positive-row joint law. -/
theorem exact_eq_physicalJoint
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (identification :
      ExactHaarPhysicalPerronCenteredSameActionAt w hw K)
    (observable : EdgeLabelling → Q')
    (hmean : CentralPhysicalMeanZero w hw K 0 observable) :
    exactSlabAllCutoffQuadratic w K observable ≈
      centralPhysicalJointQuadratic w hw K 0 observable :=
  Q'.eqv_trans _ _ _
    (identification.centered_same_action observable hmean)
    (Q'.eqv_symm
      (centralPhysicalJointQuadratic_eq_normalizedFull
        w hw K 0 observable))

/-- The physical symmetric-reference comparison needs no equality on the
constant or vacuum point observables: centered same action is sufficient for
the exact quarter contraction. -/
theorem exact_quadratic_abs_le_quarter_of_physicalPerron
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (identification :
      ExactHaarPhysicalPerronCenteredSameActionAt w hw K)
    (comparison :
      CentralPhysicalSymmetricReferenceComparison w hw K 0)
    (hquarter :
      comparison.reference.rate + comparison.epsilon ≤
        Q'.mkPos 1 4 (by decide))
    (observable : EdgeLabelling → Q')
    (hmean : CentralPhysicalMeanZero w hw K 0 observable) :
    Q'.abs (exactSlabAllCutoffQuadratic w K observable) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          w hw K 0 observable observable := by
  have hphysical :=
    comparison.physical_markov_quadratic_abs_le_quarter
      hquarter observable hmean
  have hforms :
      exactSlabAllCutoffQuadratic w K observable ≈
        centralPhysicalWeightedInner w hw K 0
          observable
          (centralPhysicalMarkovApply w hw K 0 observable) :=
    Q'.eqv_trans _ _ _
      (identification.exact_eq_physicalJoint observable hmean)
      (Q'.eqv_symm
        (centralPhysicalWeightedMarkovQuadratic_eq_joint
          w hw K 0 observable))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hforms))
    hphysical

/-! ## 2. Direct local-gluing transfer on the centered subspace -/

/-- Exact all-word gluing and a local quarter rate give the exact signed-Haar
sixteenth using only centered same action. -/
theorem exact_quadratic_abs_le_sixteenth_of_local_gluing
    {w : Q'} {hw : (0 : Q') ≤ w} {K depth : Nat}
    {qS : Q'}
    (identification :
      ExactHaarPhysicalPerronCenteredSameActionAt w hw K)
    (qS_le_quarter :
      qS ≤ YMGap.Continuum.FiveHolonomyPerronCutoff.quarter)
    (localRow_exists :
      ∀ source,
        source ∈ centralPositiveHalfStates w hw K 0 →
          Nonempty
            (Σ oneStep : EdgeLabelling → EdgeLabelling → Q',
              PhysicalBF4LocalContractionGluingRow
                hw K 0 source depth oneStep qS))
    (observable : EdgeLabelling → Q')
    (hmean : CentralPhysicalMeanZero w hw K 0 observable) :
    Q'.abs (exactSlabAllCutoffQuadratic w K observable) ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalWeightedInner
          w hw K 0 observable observable := by
  let states := centralPositiveHalfStates w hw K 0
  let physical :=
    centralNormalizedPhysicalReflectedKernel w hw K 0
  let vacuum := centralPhysicalVacuumJoint w hw K 0
  let physicalQuadratic :=
    finiteJointQuadratic states observable physical
  let vacuumQuadratic :=
    finiteJointQuadratic states observable vacuum
  have hvacuum : vacuumQuadratic ≈ 0 :=
    centralPhysicalVacuumJoint_quadratic_meanZero observable hmean
  have hdifference :
      physicalQuadratic + (-vacuumQuadratic) ≈
        physicalQuadratic := by
    exact Q'.eqv_trans _
      (physicalQuadratic + 0) _
      (Q'.add_eqv_congr_left
        physicalQuadratic (-vacuumQuadratic) 0
        (Q'.eqv_trans _ (-0) _
          (Q'.neg_eqv_congr _ _ hvacuum)
          (Q'.eqv_refl 0)))
      (Q'.eqv_of_eq (Q'.add_zero' physicalQuadratic))
  have hrow :
      ∀ state,
        state ∈ states →
          finiteJointDifferenceAbsRowMass
              states physical vacuum state ≤
            Q'.mkPos 1 16 (by decide) *
              centralPhysicalRowMarginal w hw K 0 state := by
    intro state hstate
    obtain ⟨⟨oneStep, row⟩⟩ := localRow_exists state hstate
    change physicalCenteredPhysicalRowMass
        w hw K 0 state ≤ _
    exact row.physical_centered_row_le_sixteenth qS_le_quarter
  have hperturbation :
      Q'.abs (physicalQuadratic + (-vacuumQuadratic)) ≤
        Q'.mkPos 1 16 (by decide) *
          finiteWeightedSquare
            states
            (centralPhysicalRowMarginal w hw K 0)
            observable := by
    exact finiteJointQuadratic_abs_sub_le_weightedSquare
      states observable
      (centralPhysicalRowMarginal w hw K 0)
      physical vacuum
      (Q'.mkPos 1 16 (by decide))
      (fun left right hleft hright =>
        centralNormalizedPhysicalReflectedKernel_symm
          ((mem_centralPositiveHalfStates_iff).1 hleft).1
          ((mem_centralPositiveHalfStates_iff).1 hright).1)
      (fun left right _ _ =>
        centralPhysicalVacuumJoint_symmetric
          w hw K 0 left right)
      hrow
  have hphysical :
      Q'.abs physicalQuadratic ≤
        Q'.mkPos 1 16 (by decide) *
          centralPhysicalWeightedInner
            w hw K 0 observable observable := by
    refine Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.abs_eqv_congr hdifference))
      (Q'.le_trans' _ _ _ hperturbation ?_)
    exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_left
        (Q'.mkPos 1 16 (by decide))
        (finiteWeightedSquare
          states
          (centralPhysicalRowMarginal w hw K 0)
          observable)
        (centralPhysicalWeightedInner
          w hw K 0 observable observable)
        (finiteWeightedSquare_physical_eqv_inner
          w hw K 0 observable))
  have hforms :
      exactSlabAllCutoffQuadratic w K observable ≈
        physicalQuadratic := by
    exact identification.exact_eq_physicalJoint observable hmean
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hforms))
    hphysical

end ExactHaarPhysicalPerronCenteredSameActionAt

/-! ## 3. AF-family centered local-gluing route -/

/-- Minimal AF-uniform local-gluing certificate after removing the refuted
all-observable same-action premise. -/
structure ExactHaarPhysicalCenteredLocalGluingAFCertificate
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q') : Type where
  coupling_pos : ∀ scale, (0 : Q') < coupling scale
  coupling_le_window : ∀ scale, coupling scale ≤ law.g₁
  centeredSameAction :
    ∀ scale,
      ExactHaarPhysicalPerronCenteredSameActionAt
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
  depth : Nat → Nat
  localRate : Nat → Q'
  localRate_le_quarter :
    ∀ scale,
      localRate scale ≤
        YMGap.Continuum.FiveHolonomyPerronCutoff.quarter
  localRow_exists :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0 →
        Nonempty
          (Σ oneStep : EdgeLabelling → EdgeLabelling → Q',
            PhysicalBF4LocalContractionGluingRow
              (matchedAllSpinWeight_nonnegative
                family coupling scale)
              (matchedAllSpinCutoff family coupling scale) 0
              source (depth scale) oneStep
              (localRate scale))

namespace ExactHaarPhysicalCenteredLocalGluingAFCertificate

/-- The corrected AF route transfers the local physical sixteenth to the
literal exact quadratic at every matched scale on the stationary-mean-zero
subspace. -/
theorem exact_quadratic_abs_le_sixteenth_at
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      ExactHaarPhysicalCenteredLocalGluingAFCertificate
        family law spacing coupling)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
        observable) :
    Q'.abs
        (exactSlabAllCutoffQuadratic
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          observable) ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          observable observable :=
  (certificate.centeredSameAction scale)
    |>.exact_quadratic_abs_le_sixteenth_of_local_gluing
      (certificate.localRate_le_quarter scale)
      (certificate.localRow_exists scale)
      observable hmean

end ExactHaarPhysicalCenteredLocalGluingAFCertificate

end YMGap.Continuum.BF4ExactPhysicalPerronCenteredReroute

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4ExactPhysicalPerronCenteredReroute.ExactHaarPhysicalPerronSameActionAt.toCentered
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronCenteredReroute.ExactHaarPhysicalPerronCenteredSameActionAt.exact_eq_physicalJoint
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronCenteredReroute.ExactHaarPhysicalPerronCenteredSameActionAt.exact_quadratic_abs_le_quarter_of_physicalPerron
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronCenteredReroute.ExactHaarPhysicalPerronCenteredSameActionAt.exact_quadratic_abs_le_sixteenth_of_local_gluing
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronCenteredReroute.ExactHaarPhysicalCenteredLocalGluingAFCertificate.exact_quadratic_abs_le_sixteenth_at
