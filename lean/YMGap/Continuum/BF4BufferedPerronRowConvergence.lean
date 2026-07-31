/-
# Buffered Perron convergence implies a row-relative BF4 bound

This file proves the finite constructive ``buffer--middle--buffer'' estimate
which is implicit in the Faraut expression

    C^2 q^(m-2).

The centered density of a joint law is factored through a left endpoint
buffer, a contracted middle kernel, and a right endpoint buffer.  If the two
endpoint absolute masses are at most `C`, the middle absolute row mass is at
most `rho`, and the target weight has total mass one, then the centered joint
row is at most

    C * C * rho * sourceWeight.

There is no carrier-cardinality factor and no minimum-marginal denominator.
The proof is finite Tonelli/triangle algebra over `Q'`.

The second half specializes the generic theorem to the physical BF4 joint
and combines it with the already proved Faraut depth estimate.  Its only
remaining physical input is the literal buffered density factorization of
the conditionally integrated slab.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CommonRankOneRowTriangle
import YMGap.Continuum.BF4FarautJointCarrierAFBudget
import YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth

namespace YMGap.Continuum.BF4BufferedPerronRowConvergence

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4CalibratedNonemptyFeatureEnvelope
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4CommonRankOneRowTriangle
open YMGap.Continuum.BF4FarautJointCarrierAFBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SymmetricReferenceOperatorComparison
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact finite buffer--middle--buffer algebra -/

/-- A centered density factored through two finite endpoint carriers. -/
def finiteBufferedDensity
    {Source Target Left Middle : Type}
    (leftStates : List Left) (middleStates : List Middle)
    (leftBuffer : Source → Left → Q')
    (middleKernel : Left → Middle → Q')
    (rightBuffer : Middle → Target → Q')
    (source : Source) (target : Target) : Q' :=
  listQSum
    (fun left =>
      leftBuffer source left *
        listQSum
          (fun middle =>
            middleKernel left middle *
              rightBuffer middle target)
          middleStates)
    leftStates

/-- The cancellation-free absolute majorant of `finiteBufferedDensity`. -/
def finiteBufferedDensityMajorant
    {Source Target Left Middle : Type}
    (leftStates : List Left) (middleStates : List Middle)
    (leftBuffer : Source → Left → Q')
    (middleKernel : Left → Middle → Q')
    (rightBuffer : Middle → Target → Q')
    (source : Source) (target : Target) : Q' :=
  listQSum
    (fun left =>
      Q'.abs (leftBuffer source left) *
        listQSum
          (fun middle =>
            Q'.abs (middleKernel left middle) *
              Q'.abs (rightBuffer middle target))
          middleStates)
    leftStates

/-- The factored density is pointwise bounded by its Tonelli majorant. -/
theorem abs_finiteBufferedDensity_le_majorant
    {Source Target Left Middle : Type}
    (leftStates : List Left) (middleStates : List Middle)
    (leftBuffer : Source → Left → Q')
    (middleKernel : Left → Middle → Q')
    (rightBuffer : Middle → Target → Q')
    (source : Source) (target : Target) :
    Q'.abs
        (finiteBufferedDensity
          leftStates middleStates
          leftBuffer middleKernel rightBuffer
          source target) ≤
      finiteBufferedDensityMajorant
        leftStates middleStates
        leftBuffer middleKernel rightBuffer
        source target := by
  unfold finiteBufferedDensity finiteBufferedDensityMajorant
  refine Q'.le_trans' _ _ _
    (abs_listQSum_le_sum_abs
      (fun left =>
        leftBuffer source left *
          listQSum
            (fun middle =>
              middleKernel left middle *
                rightBuffer middle target)
            middleStates)
      leftStates) ?_
  apply listQSum_mono
  intro left _
  refine Q'.le_trans' _ _ _
    (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
      (leftBuffer source left)
      (listQSum
        (fun middle =>
          middleKernel left middle *
            rightBuffer middle target)
        middleStates)) ?_
  apply Q'.mul_le_mul_of_nonneg_left
  · refine Q'.le_trans' _ _ _
      (abs_listQSum_le_sum_abs
        (fun middle =>
          middleKernel left middle *
            rightBuffer middle target)
        middleStates) ?_
    apply listQSum_mono
    intro middle _
    exact
      YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
        (middleKernel left middle)
        (rightBuffer middle target)
  · exact Q'.abs_nonneg _

/-- A nonnegative source-target weight transports the density majorant to
one centered joint entry. -/
theorem abs_centered_entry_le_bufferedMajorant
    {Source Target Left Middle : Type}
    (leftStates : List Left) (middleStates : List Middle)
    (leftBuffer : Source → Left → Q')
    (middleKernel : Left → Middle → Q')
    (rightBuffer : Middle → Target → Q')
    (joint rankOne : Source → Target → Q')
    (sourceWeight : Source → Q')
    (targetWeight : Target → Q')
    (source : Source) (target : Target)
    (weight_nonnegative :
      (0 : Q') ≤
        sourceWeight source * targetWeight target)
    (centered_density :
      joint source target + (-rankOne source target) ≈
        (sourceWeight source * targetWeight target) *
          finiteBufferedDensity
            leftStates middleStates
            leftBuffer middleKernel rightBuffer
            source target) :
    Q'.abs
        (joint source target + (-rankOne source target)) ≤
      (sourceWeight source * targetWeight target) *
        finiteBufferedDensityMajorant
          leftStates middleStates
          leftBuffer middleKernel rightBuffer
          source target := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr centered_density)) ?_
  refine Q'.le_trans' _ _ _
    (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
      (sourceWeight source * targetWeight target)
      (finiteBufferedDensity
        leftStates middleStates
        leftBuffer middleKernel rightBuffer
        source target)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (abs_finiteBufferedDensity_le_majorant
        leftStates middleStates
        leftBuffer middleKernel rightBuffer
        source target)
      (Q'.abs_nonneg _)) ?_
  exact Q'.le_of_eqv
    (Q'.mul_eqv_congr_right
      (Q'.abs
        (sourceWeight source * targetWeight target))
      (sourceWeight source * targetWeight target)
      (finiteBufferedDensityMajorant
        leftStates middleStates
        leftBuffer middleKernel rightBuffer
        source target)
      (Q'.eqv_of_eq
        (YMGap.Constructive.ExpNeg.abs_of_nonneg
          weight_nonnegative)))

/-- Integrated Tonelli majorant. -/
def finiteBufferedIntegratedMajorant
    {Source Target Left Middle : Type}
    (targets : List Target) (targetWeight : Target → Q')
    (leftStates : List Left) (middleStates : List Middle)
    (leftBuffer : Source → Left → Q')
    (middleKernel : Left → Middle → Q')
    (rightBuffer : Middle → Target → Q')
    (source : Source) : Q' :=
  listQSum
    (fun target =>
      targetWeight target *
        finiteBufferedDensityMajorant
          leftStates middleStates
          leftBuffer middleKernel rightBuffer
          source target)
    targets

/-- Exact Fubini form of the integrated majorant. -/
theorem finiteBufferedIntegratedMajorant_eqv
    {Source Target Left Middle : Type}
    (targets : List Target) (targetWeight : Target → Q')
    (leftStates : List Left) (middleStates : List Middle)
    (leftBuffer : Source → Left → Q')
    (middleKernel : Left → Middle → Q')
    (rightBuffer : Middle → Target → Q')
    (source : Source) :
    finiteBufferedIntegratedMajorant
        targets targetWeight
        leftStates middleStates
        leftBuffer middleKernel rightBuffer source ≈
      listQSum
        (fun left =>
          Q'.abs (leftBuffer source left) *
            listQSum
              (fun middle =>
                Q'.abs (middleKernel left middle) *
                  listQSum
                    (fun target =>
                      targetWeight target *
                        Q'.abs
                          (rightBuffer middle target))
                    targets)
              middleStates)
        leftStates := by
  unfold finiteBufferedIntegratedMajorant
    finiteBufferedDensityMajorant
  refine Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun target =>
        Q'.eqv_symm
          (listQSum_mul_left
            (targetWeight target)
            (fun left =>
              Q'.abs (leftBuffer source left) *
                listQSum
                  (fun middle =>
                    Q'.abs (middleKernel left middle) *
                      Q'.abs (rightBuffer middle target))
                  middleStates)
            leftStates))
      targets) ?_
  refine Q'.eqv_trans _ _ _
    (listQSum_swap
      (fun left target =>
        targetWeight target *
          (Q'.abs (leftBuffer source left) *
            listQSum
              (fun middle =>
                Q'.abs (middleKernel left middle) *
                  Q'.abs (rightBuffer middle target))
              middleStates))
      leftStates targets) ?_
  apply listQSum_congr
  intro left
  refine Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun target =>
        Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv
              (targetWeight target)
              (Q'.abs (leftBuffer source left))
              (listQSum
                (fun middle =>
                  Q'.abs (middleKernel left middle) *
                  Q'.abs (rightBuffer middle target))
                middleStates)))
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.mul_comm_eqv
                (targetWeight target)
                (Q'.abs (leftBuffer source left))))
            (Q'.mul_assoc_eqv
              (Q'.abs (leftBuffer source left))
              (targetWeight target)
              (listQSum
                (fun middle =>
                  Q'.abs (middleKernel left middle) *
                    Q'.abs (rightBuffer middle target))
                middleStates))))
      targets) ?_
  refine Q'.eqv_trans _ _ _
    (listQSum_mul_left
      (Q'.abs (leftBuffer source left))
      (fun target =>
        targetWeight target *
          listQSum
            (fun middle =>
              Q'.abs (middleKernel left middle) *
                Q'.abs (rightBuffer middle target))
            middleStates)
      targets) ?_
  apply Q'.mul_eqv_congr_left
  refine Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun target =>
        Q'.eqv_symm
          (listQSum_mul_left
            (targetWeight target)
            (fun middle =>
              Q'.abs (middleKernel left middle) *
                Q'.abs (rightBuffer middle target))
            middleStates))
      targets) ?_
  refine Q'.eqv_trans _ _ _
    (listQSum_swap
      (fun middle target =>
        targetWeight target *
          (Q'.abs (middleKernel left middle) *
            Q'.abs (rightBuffer middle target)))
      middleStates targets) ?_
  apply listQSum_congr
  intro middle
  refine Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun target =>
        Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv
              (targetWeight target)
              (Q'.abs (middleKernel left middle))
              (Q'.abs (rightBuffer middle target))))
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.mul_comm_eqv
                (targetWeight target)
                (Q'.abs (middleKernel left middle))))
            (Q'.mul_assoc_eqv
              (Q'.abs (middleKernel left middle))
              (targetWeight target)
              (Q'.abs (rightBuffer middle target)))))
      targets) ?_
  refine Q'.eqv_trans _ _ _
    (listQSum_mul_left
      (Q'.abs (middleKernel left middle))
      (fun target =>
        targetWeight target *
          Q'.abs (rightBuffer middle target))
      targets) ?_
  exact Q'.eqv_refl _

/-- Two endpoint absolute budgets and one middle absolute-row budget multiply
without a carrier loss. -/
theorem finiteBufferedIntegratedMajorant_le
    {Source Target Left Middle : Type}
    (targets : List Target) (targetWeight : Target → Q')
    (leftStates : List Left) (middleStates : List Middle)
    (leftBuffer : Source → Left → Q')
    (middleKernel : Left → Middle → Q')
    (rightBuffer : Middle → Target → Q')
    (source : Source)
    (endpointBound middleBound : Q')
    (endpointBound_nonnegative : (0 : Q') ≤ endpointBound)
    (middleBound_nonnegative : (0 : Q') ≤ middleBound)
    (left_bound :
      listQSum
          (fun left => Q'.abs (leftBuffer source left))
          leftStates ≤
        endpointBound)
    (middle_bound :
      ∀ left, left ∈ leftStates →
        listQSum
            (fun middle =>
              Q'.abs (middleKernel left middle))
            middleStates ≤
          middleBound)
    (right_bound :
      ∀ middle, middle ∈ middleStates →
        listQSum
            (fun target =>
              targetWeight target *
                Q'.abs (rightBuffer middle target))
            targets ≤
          endpointBound) :
    finiteBufferedIntegratedMajorant
        targets targetWeight
        leftStates middleStates
        leftBuffer middleKernel rightBuffer source ≤
      (endpointBound * endpointBound) * middleBound := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (finiteBufferedIntegratedMajorant_eqv
        targets targetWeight
        leftStates middleStates
        leftBuffer middleKernel rightBuffer source)) ?_
  refine Q'.le_trans' _ _ _
    (listQSum_mono _ _ leftStates
      (fun left hleft =>
        Q'.mul_le_mul_of_nonneg_left _ _ _
          (listQSum_mono _ _ middleStates
            (fun middle hmiddle =>
              Q'.mul_le_mul_of_nonneg_left _ _ _
                (right_bound middle hmiddle)
                (Q'.abs_nonneg _)))
          (Q'.abs_nonneg _))) ?_
  have hmiddleScaled :
      ∀ left, left ∈ leftStates →
        listQSum
            (fun middle =>
              Q'.abs (middleKernel left middle) *
                endpointBound)
            middleStates ≤
          middleBound * endpointBound := by
    intro left hleft
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (listQSum_mul_right
          (fun middle =>
            Q'.abs (middleKernel left middle))
          endpointBound middleStates)) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (middle_bound left hleft)
      endpointBound_nonnegative
  refine Q'.le_trans' _ _ _
    (listQSum_mono _ _ leftStates
      (fun left hleft =>
        Q'.mul_le_mul_of_nonneg_left _ _ _
          (hmiddleScaled left hleft)
          (Q'.abs_nonneg _))) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (listQSum_mul_right
        (fun left => Q'.abs (leftBuffer source left))
        (middleBound * endpointBound)
        leftStates)) ?_
  have hproduct_nonnegative :
      (0 : Q') ≤ middleBound * endpointBound :=
    Q'.mul_nonneg _ _
      middleBound_nonnegative endpointBound_nonnegative
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      left_bound hproduct_nonnegative) ?_
  exact Q'.le_of_eqv
    (by
      calc
        endpointBound * (middleBound * endpointBound) ≈
            (endpointBound * endpointBound) *
              middleBound := by
          exact Q'.eqv_trans _ _ _
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv
                endpointBound middleBound endpointBound))
            (Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_right _ _ _
                (Q'.mul_comm_eqv
                  endpointBound middleBound))
              (Q'.eqv_trans _ _ _
                (Q'.mul_assoc_eqv
                  middleBound endpointBound endpointBound)
                (Q'.mul_comm_eqv
                  middleBound
                  (endpointBound * endpointBound)))))

/-! ## 2. Joint-law row convergence -/

/-- Exact data identifying a centered joint row with a buffered density. -/
structure BufferedCenteredJointRow
    {State Left Middle : Type}
    (targets : List State)
    (targetWeight : State → Q')
    (leftStates : List Left) (middleStates : List Middle)
    (leftBuffer : State → Left → Q')
    (middleKernel : Left → Middle → Q')
    (rightBuffer : Middle → State → Q')
    (joint rankOne : State → State → Q')
    (sourceWeight : State → Q')
    (source : State)
    (endpointBound middleBound : Q') : Type where
  sourceWeight_nonnegative : (0 : Q') ≤ sourceWeight source
  targetWeight_nonnegative :
    ∀ target, target ∈ targets →
      (0 : Q') ≤ targetWeight target
  endpointBound_nonnegative : (0 : Q') ≤ endpointBound
  middleBound_nonnegative : (0 : Q') ≤ middleBound
  centered_density :
    ∀ target, target ∈ targets →
      joint source target + (-rankOne source target) ≈
        (sourceWeight source * targetWeight target) *
          finiteBufferedDensity
            leftStates middleStates
            leftBuffer middleKernel rightBuffer
            source target
  left_bound :
    listQSum
        (fun left => Q'.abs (leftBuffer source left))
        leftStates ≤
      endpointBound
  middle_bound :
    ∀ left, left ∈ leftStates →
      listQSum
          (fun middle =>
            Q'.abs (middleKernel left middle))
          middleStates ≤
        middleBound
  right_bound :
    ∀ middle, middle ∈ middleStates →
      listQSum
          (fun target =>
            targetWeight target *
              Q'.abs (rightBuffer middle target))
          targets ≤
        endpointBound

namespace BufferedCenteredJointRow

/-- Summing the entry bound pulls out the source marginal exactly. -/
theorem row_abs_mass_le_integrated
    {State Left Middle : Type}
    {targets : List State}
    {targetWeight : State → Q'}
    {leftStates : List Left} {middleStates : List Middle}
    {leftBuffer : State → Left → Q'}
    {middleKernel : Left → Middle → Q'}
    {rightBuffer : Middle → State → Q'}
    {joint rankOne : State → State → Q'}
    {sourceWeight : State → Q'}
    {source : State}
    {endpointBound middleBound : Q'}
    (data :
      BufferedCenteredJointRow
        targets targetWeight leftStates middleStates
        leftBuffer middleKernel rightBuffer
        joint rankOne sourceWeight source
        endpointBound middleBound) :
    finiteJointDifferenceAbsRowMass
        targets joint rankOne source ≤
      sourceWeight source *
        finiteBufferedIntegratedMajorant
          targets targetWeight
          leftStates middleStates
          leftBuffer middleKernel rightBuffer source := by
  unfold finiteJointDifferenceAbsRowMass
  refine Q'.le_trans' _ _ _
    (listQSum_mono _ _ targets
      (fun target htarget =>
        abs_centered_entry_le_bufferedMajorant
          leftStates middleStates
          leftBuffer middleKernel rightBuffer
          joint rankOne sourceWeight targetWeight
          source target
          (Q'.mul_nonneg _ _
            data.sourceWeight_nonnegative
            (data.targetWeight_nonnegative
              target htarget))
          (data.centered_density target htarget))) ?_
  refine Q'.le_of_eqv
    (Q'.eqv_trans _ _ _
      (listQSum_congr
        (fun target =>
          Q'.mul_assoc_eqv
            (sourceWeight source)
            (targetWeight target)
            (finiteBufferedDensityMajorant
              leftStates middleStates
              leftBuffer middleKernel rightBuffer
              source target))
        targets)
      (listQSum_mul_left
        (sourceWeight source)
        (fun target =>
          targetWeight target *
            finiteBufferedDensityMajorant
              leftStates middleStates
              leftBuffer middleKernel rightBuffer
              source target)
        targets))

/-- The exact buffer--middle--buffer row estimate. -/
theorem row_abs_mass_le
    {State Left Middle : Type}
    {targets : List State}
    {targetWeight : State → Q'}
    {leftStates : List Left} {middleStates : List Middle}
    {leftBuffer : State → Left → Q'}
    {middleKernel : Left → Middle → Q'}
    {rightBuffer : Middle → State → Q'}
    {joint rankOne : State → State → Q'}
    {sourceWeight : State → Q'}
    {source : State}
    {endpointBound middleBound : Q'}
    (data :
      BufferedCenteredJointRow
        targets targetWeight leftStates middleStates
        leftBuffer middleKernel rightBuffer
        joint rankOne sourceWeight source
        endpointBound middleBound) :
    finiteJointDifferenceAbsRowMass
        targets joint rankOne source ≤
      ((endpointBound * endpointBound) * middleBound) *
        sourceWeight source := by
  refine Q'.le_trans' _ _ _
    data.row_abs_mass_le_integrated ?_
  have hmajorant :=
    finiteBufferedIntegratedMajorant_le
      targets targetWeight
      leftStates middleStates
      leftBuffer middleKernel rightBuffer source
      endpointBound middleBound
      data.endpointBound_nonnegative
      data.middleBound_nonnegative
      data.left_bound data.middle_bound data.right_bound
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      hmajorant data.sourceWeight_nonnegative) ?_
  exact
    (Q'.le_of_eqv
      (Q'.mul_comm_eqv
        (sourceWeight source)
        ((endpointBound * endpointBound) * middleBound)))

end BufferedCenteredJointRow

/-! ## 3. Physical BF4 specialization and the sharp Faraut payment -/

/-- A literal physical BF4 centered-row factorization through two retained
endpoint buffers.  This is the precise output required from conditional
integration/lumpability of the grouped slab. -/
structure PhysicalBF4BufferedCenteredRow
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {Left Middle : Type}
    (leftStates : List Left) (middleStates : List Middle)
    (leftBuffer : EdgeLabelling → Left → Q')
    (middleKernel : Left → Middle → Q')
    (rightBuffer : Middle → EdgeLabelling → Q')
    (source : EdgeLabelling)
    (endpointBound middleBound : Q') : Type where
  sourceWeight_nonnegative :
    (0 : Q') ≤
      centralPhysicalRowMarginal
        w hw K halfExtent source
  targetWeight_nonnegative :
    ∀ target,
      target ∈
          centralPositiveHalfStates
            w hw K halfExtent →
        (0 : Q') ≤
          centralPhysicalRowMarginal
            w hw K halfExtent target
  endpointBound_nonnegative :
    (0 : Q') ≤ endpointBound
  middleBound_nonnegative :
    (0 : Q') ≤ middleBound
  centered_density :
    ∀ target,
      target ∈
          centralPositiveHalfStates
            w hw K halfExtent →
        centralNormalizedPhysicalReflectedKernel
              w hw K halfExtent source target +
            (-centralPhysicalVacuumJoint
              w hw K halfExtent source target) ≈
          (centralPhysicalRowMarginal
              w hw K halfExtent source *
            centralPhysicalRowMarginal
              w hw K halfExtent target) *
            finiteBufferedDensity
              leftStates middleStates
              leftBuffer middleKernel rightBuffer
              source target
  left_bound :
    listQSum
        (fun left => Q'.abs (leftBuffer source left))
        leftStates ≤
      endpointBound
  middle_bound :
    ∀ left, left ∈ leftStates →
      listQSum
          (fun middle =>
            Q'.abs (middleKernel left middle))
          middleStates ≤
        middleBound
  right_bound :
    ∀ middle, middle ∈ middleStates →
      listQSum
          (fun target =>
            centralPhysicalRowMarginal
                w hw K halfExtent target *
              Q'.abs (rightBuffer middle target))
          (centralPositiveHalfStates
            w hw K halfExtent) ≤
        endpointBound

namespace PhysicalBF4BufferedCenteredRow

/-- Forgetting the physical names leaves the generic square-carrier
buffered certificate. -/
def toBufferedCenteredJointRow
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {Left Middle : Type}
    {leftStates : List Left} {middleStates : List Middle}
    {leftBuffer : EdgeLabelling → Left → Q'}
    {middleKernel : Left → Middle → Q'}
    {rightBuffer : Middle → EdgeLabelling → Q'}
    {source : EdgeLabelling}
    {endpointBound middleBound : Q'}
    (data :
      PhysicalBF4BufferedCenteredRow
        (w := w) (hw := hw)
        (K := K) (halfExtent := halfExtent)
        leftStates middleStates
        leftBuffer middleKernel rightBuffer
        source endpointBound middleBound) :
    BufferedCenteredJointRow
      (centralPositiveHalfStates w hw K halfExtent)
      (centralPhysicalRowMarginal w hw K halfExtent)
      leftStates middleStates
      leftBuffer middleKernel rightBuffer
      (centralNormalizedPhysicalReflectedKernel
        w hw K halfExtent)
      (centralPhysicalVacuumJoint
        w hw K halfExtent)
      (centralPhysicalRowMarginal
        w hw K halfExtent)
      source endpointBound middleBound where
  sourceWeight_nonnegative :=
    data.sourceWeight_nonnegative
  targetWeight_nonnegative :=
    data.targetWeight_nonnegative
  endpointBound_nonnegative :=
    data.endpointBound_nonnegative
  middleBound_nonnegative :=
    data.middleBound_nonnegative
  centered_density :=
    data.centered_density
  left_bound := data.left_bound
  middle_bound := data.middle_bound
  right_bound := data.right_bound

end PhysicalBF4BufferedCenteredRow

/-- The physical specialization of the buffer--middle--buffer theorem. -/
theorem physicalCenteredPhysicalRowMass_le_of_buffered
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {Left Middle : Type}
    {leftStates : List Left} {middleStates : List Middle}
    {leftBuffer : EdgeLabelling → Left → Q'}
    {middleKernel : Left → Middle → Q'}
    {rightBuffer : Middle → EdgeLabelling → Q'}
    {source : EdgeLabelling}
    {endpointBound middleBound : Q'}
    (data :
      PhysicalBF4BufferedCenteredRow
        (w := w) (hw := hw)
        (K := K) (halfExtent := halfExtent)
        leftStates middleStates
        leftBuffer middleKernel rightBuffer
        source endpointBound middleBound) :
    physicalCenteredPhysicalRowMass
        w hw K halfExtent source ≤
      ((endpointBound * endpointBound) * middleBound) *
        centralPhysicalRowMarginal
          w hw K halfExtent source :=
  data.toBufferedCenteredJointRow.row_abs_mass_le

/-- The sharpened Faraut depth pays the physical centered row down to
`1/16` (in fact to `1/64`). -/
theorem physicalCenteredPhysicalRowMass_le_sixteenth_of_faraut_buffered
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {Left Middle : Type}
    {leftStates : List Left} {middleStates : List Middle}
    {leftBuffer : EdgeLabelling → Left → Q'}
    {middleKernel : Left → Middle → Q'}
    {rightBuffer : Middle → EdgeLabelling → Q'}
    {source : EdgeLabelling}
    {bits m : Nat} {qS : Q'}
    (qS_nonnegative : (0 : Q') ≤ qS)
    (qS_le_quarter : qS ≤ quarter)
    (depth_available :
      farautHarnackRequiredDepth bits ≤ m)
    (data :
      PhysicalBF4BufferedCenteredRow
        (w := w) (hw := hw)
        (K := K) (halfExtent := halfExtent)
        leftStates middleStates
        leftBuffer middleKernel rightBuffer
        source
        (farautRetainedSpread bits)
        (qS ^ (m - 2))) :
    physicalCenteredPhysicalRowMass
        w hw K halfExtent source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          w hw K halfExtent source := by
  have hrow :=
    physicalCenteredPhysicalRowMass_le_of_buffered data
  have hfaraut :
      (farautRetainedSpread bits *
          farautRetainedSpread bits) *
          qS ^ (m - 2) ≤
        farautHarnackTolerance := by
    exact faraut_perron_harnack_of_available_depth
      bits qS m qS_nonnegative qS_le_quarter
      depth_available
  have htolerance :
      farautHarnackTolerance ≤
        Q'.mkPos 1 16 (by decide) := by
    unfold farautHarnackTolerance
    decide
  exact Q'.le_trans' _ _ _ hrow
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.le_trans' _ _ _ hfaraut htolerance)
      data.sourceWeight_nonnegative)

/-! ## 4. Both spacing-uniform eighth fields -/

/-- Witness-bearing physical buffer factorization at one scale and one
retained source.  The intermediate carrier types and all three kernels are
data, so no choice principle is needed when the trajectory requests one
certificate per row. -/
structure PhysicalBF4FarautBufferedRow
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat)
    (source : EdgeLabelling)
    (bits depth : Nat) (qS : Q') : Type 1 where
  Left : Type
  Middle : Type
  leftStates : List Left
  middleStates : List Middle
  leftBuffer : EdgeLabelling → Left → Q'
  middleKernel : Left → Middle → Q'
  rightBuffer : Middle → EdgeLabelling → Q'
  certificate :
    PhysicalBF4BufferedCenteredRow
      (w := w) (hw := hw)
      (K := K) (halfExtent := halfExtent)
      leftStates middleStates
      leftBuffer middleKernel rightBuffer
      source
      (farautRetainedSpread bits)
      (qS ^ (depth - 2))

namespace PhysicalBF4FarautBufferedRow

/-- One witness-bearing physical factorization pays the centered physical
row to `1/16` at the sharpened Faraut depth. -/
theorem centered_row_le_sixteenth
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {source : EdgeLabelling}
    {bits depth : Nat} {qS : Q'}
    (row :
      PhysicalBF4FarautBufferedRow
        w hw K halfExtent source bits depth qS)
    (qS_nonnegative : (0 : Q') ≤ qS)
    (qS_le_quarter : qS ≤ quarter)
    (depth_available :
      farautHarnackRequiredDepth bits ≤ depth) :
    physicalCenteredPhysicalRowMass
        w hw K halfExtent source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          w hw K halfExtent source :=
  physicalCenteredPhysicalRowMass_le_sixteenth_of_faraut_buffered
    qS_nonnegative qS_le_quarter depth_available
    row.certificate

end PhysicalBF4FarautBufferedRow

/-- The two scale-uniform analytic inputs immediately below the requested
rowwise eighths.  The first field is supplied by cross-zero Harnack.  The
second is supplied, row by row, by
`PhysicalBF4FarautBufferedRow.centered_row_le_sixteenth` once the physical
conditional-integration factorization is constructed. -/
structure MatchedCrossZeroPhysicalSixteenthRows
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  harnack :
    ∀ scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale) 0
  physical_centered_row_sixteenth :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        physicalCenteredPhysicalRowMass
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) source ≤
          Q'.mkPos 1 16 (by decide) *
            centralPhysicalRowMarginal
              (matchedAllSpinWeight family coupling scale)
              (matchedAllSpinWeight_nonnegative
                family coupling scale)
              (matchedAllSpinCutoff family coupling scale)
              (halfExtent scale) source

namespace MatchedCrossZeroPhysicalSixteenthRows

/-- The first requested spacing-uniform scalar inequality, with the sharper
constant `1/16`. -/
theorem calibrated_rate_le_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (rows :
      MatchedCrossZeroPhysicalSixteenthRows
        family law spacing coupling
        halfExtent diagonalOrder)
    (scale : Nat) :
    (matchedPhysicallyRecenteredMehlerGramRawEndpointAt
        family coupling halfExtent
        diagonalOrder (fun _ => 0) scale).rate ≤
      Q'.mkPos 1 16 (by decide) := by
  unfold matchedPhysicallyRecenteredMehlerGramRawEndpointAt
  exact physicallyRecenteredCrossZero_rate_le_sixteenth
    (rows.harnack scale)

/-- Cross-zero Harnack and the physical centered-row sixteenth inhabit both
literal spacing-uniform `1/8` fields of
`MatchedPhysicallyRecenteredRowwiseEighthEstimates`. -/
def toRowwiseEighthEstimates
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (rows :
      MatchedCrossZeroPhysicalSixteenthRows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) where
  coupling_pos := rows.coupling_pos
  coupling_le_window := rows.coupling_le_window
  spectral_centered_row_eighth := by
    intro scale source hsource
    have hsixteenth :=
      physicalCenteredEndpointRowMass_crossZero_le_sixteenth_of_profile
        ((rows.harnack scale).profile_sixteenth hsource)
    refine Q'.le_trans' _ _ _ hsixteenth ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (by decide)
      (centralPhysicalRowMarginal_nonnegative
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale) source)
  comparison_row_eighth := by
    intro scale source hsource
    exact
      physicalNormalizedJointRowError_crossZero_le_eighth
        (rows.harnack scale) hsource
        (rows.physical_centered_row_sixteenth
          scale source hsource)

end MatchedCrossZeroPhysicalSixteenthRows

end YMGap.Continuum.BF4BufferedPerronRowConvergence

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4BufferedPerronRowConvergence.abs_finiteBufferedDensity_le_majorant
#print axioms YMGap.Continuum.BF4BufferedPerronRowConvergence.finiteBufferedIntegratedMajorant_eqv
#print axioms YMGap.Continuum.BF4BufferedPerronRowConvergence.finiteBufferedIntegratedMajorant_le
#print axioms YMGap.Continuum.BF4BufferedPerronRowConvergence.BufferedCenteredJointRow.row_abs_mass_le
#print axioms YMGap.Continuum.BF4BufferedPerronRowConvergence.physicalCenteredPhysicalRowMass_le_sixteenth_of_faraut_buffered
#print axioms YMGap.Continuum.BF4BufferedPerronRowConvergence.MatchedCrossZeroPhysicalSixteenthRows.calibrated_rate_le_sixteenth
#print axioms YMGap.Continuum.BF4BufferedPerronRowConvergence.MatchedCrossZeroPhysicalSixteenthRows.toRowwiseEighthEstimates
