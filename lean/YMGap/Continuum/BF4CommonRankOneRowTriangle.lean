/-
# Common-rank-one triangle for the two BF4 row estimates

Let `V(x,y) = pi(x) pi(y)` be the physical stationary rank-one joint.
If both the physical joint and a calibrated Mehler endpoint lie within
`1/16 * pi(x)` of `V` in every retained source row, then their mutual row
distance is at most `1/8 * pi(x)`.

At cross feature order zero the Harnack profile theorem already gives the
endpoint half of this argument with the sharp `1/16` constant, because the
nonempty feature Gram vanishes exactly.  Consequently one further physical
positive-kernel rank-one estimate proves the literal physical-minus-Mehler
row eighth; an exact fixed-magnetic endpoint factorization is not required
on this alternative route.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CalibratedAnchoredProjectiveHarnack
import YMGap.Continuum.BF4CalibratedNonemptyFeatureEnvelope

namespace YMGap.Continuum.BF4CommonRankOneRowTriangle

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4AFUniformRowRelativeBudget
open YMGap.Continuum.BF4CalibratedAnchoredProjectiveHarnack
open YMGap.Continuum.BF4CalibratedFeatureGramCoreTail
open YMGap.Continuum.BF4CalibratedNonemptyFeatureEnvelope
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4PhysicalRecenteredEndpointRate
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

private theorem sub_add_rearrange
    (a a' b b' : Q') :
    ((a + a') + (-(b + b'))) ≈
      ((a + (-b)) + (a' + (-b'))) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left
      (a + a') _ _ (Q'.neg_add_eqv b b')) ?_
  exact Q'.add_swap_inner a a' (-b) (-b')

private theorem same_reference_sub_eqv
    (left right reference : Q') :
    ((left + (-reference)) +
        (-(right + (-reference)))) ≈
      left + (-right) := by
  refine Q'.eqv_trans _ _ _
    (sub_add_rearrange
      left (-reference)
      right (-reference)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left
      (left + (-right))
      ((-reference) + (-(-reference))) 0 ?_) ?_
  · exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left
        (-reference) _ _ (Q'.neg_neg_eqv reference))
      (Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv (-reference) reference)
        (Q'.add_neg_self_eqv reference))
  · exact Q'.eqv_of_eq
      (Q'.add_zero' (left + (-right)))

private theorem listQSum_mono_local
    {A : Type} (lower upper : A → Q') :
    ∀ xs : List A,
      (∀ x, x ∈ xs → lower x ≤ upper x) →
        listQSum lower xs ≤ listQSum upper xs
  | [], _ => Q'.le_refl' 0
  | head :: tail, hbound =>
      Q'.add_le_add
        (hbound head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem =>
            hbound item
              (List.mem_cons_of_mem head hitem)))

/-- Absolute row mass of the physical joint after subtraction of its own
stationary rank-one joint. -/
def physicalCenteredPhysicalRowMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat)
    (source : EdgeLabelling) : Q' :=
  finiteJointDifferenceAbsRowMass
    (centralPositiveHalfStates w hw K halfExtent)
    (centralNormalizedPhysicalReflectedKernel
      w hw K halfExtent)
    (centralPhysicalVacuumJoint
      w hw K halfExtent)
    source

/-- Row distance through an arbitrary common joint. -/
theorem finiteJointDifferenceAbsRowMass_le_via_common
    {State : Type}
    (states : List State)
    (left middle right : State → State → Q')
    (source : State) :
    finiteJointDifferenceAbsRowMass
        states left right source ≤
      finiteJointDifferenceAbsRowMass
          states left middle source +
        finiteJointDifferenceAbsRowMass
          states right middle source := by
  let leftDifference := fun target =>
    Q'.abs
      (left source target +
        (-middle source target))
  let rightDifference := fun target =>
    Q'.abs
      (right source target +
        (-middle source target))
  have hentry :
      ∀ target,
        Q'.abs
            (left source target +
              (-right source target)) ≤
          leftDifference target +
            rightDifference target := by
    intro target
    have hrearrange :
        left source target +
            (-right source target) ≈
          (left source target +
              (-middle source target)) +
            (-(right source target +
              (-middle source target))) :=
      Q'.eqv_symm
        (same_reference_sub_eqv
          (left source target)
          (right source target)
          (middle source target))
    have htriangle :=
      Q'.abs_add_le'
        (left source target +
          (-middle source target))
        (-(right source target +
          (-middle source target)))
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr hrearrange)) ?_
    refine Q'.le_trans' _ _ _ htriangle ?_
    exact Q'.add_le_add_left _ _ _
      (Q'.le_of_eqv
        (Q'.abs_neg'
          (right source target +
            (-middle source target))))
  unfold finiteJointDifferenceAbsRowMass
  refine Q'.le_trans' _ _ _
    (listQSum_mono_local
      (fun target =>
        Q'.abs
          (left source target +
            (-right source target)))
      (fun target =>
        leftDifference target +
          rightDifference target)
      states
      (fun target _ => hentry target)) ?_
  exact Q'.le_of_eqv
    (listQSum_add
      leftDifference rightDifference states)

/-- Two `1/16` centered-row estimates imply the physical-minus-endpoint
`1/8` estimate with no carrier-size or marginal-floor loss. -/
theorem physicalNormalizedJointRowError_le_eighth_of_common_rankOne
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K halfExtent)
    {source : EdgeLabelling}
    (hphysical :
      physicalCenteredPhysicalRowMass
          w hw K halfExtent source ≤
        Q'.mkPos 1 16 (by decide) *
          centralPhysicalRowMarginal
            w hw K halfExtent source)
    (hendpoint :
      physicalCenteredEndpointRowMass
          endpoint source ≤
        Q'.mkPos 1 16 (by decide) *
          centralPhysicalRowMarginal
            w hw K halfExtent source) :
    physicalNormalizedJointRowError
        endpoint source ≤
      Q'.mkPos 1 8 (by decide) *
        centralPhysicalRowMarginal
          w hw K halfExtent source := by
  have htriangle :=
    finiteJointDifferenceAbsRowMass_le_via_common
      (centralPositiveHalfStates
        w hw K halfExtent)
      (centralNormalizedPhysicalReflectedKernel
        w hw K halfExtent)
      (centralPhysicalVacuumJoint
        w hw K halfExtent)
      endpoint.joint source
  unfold physicalNormalizedJointRowError
  unfold physicalCenteredPhysicalRowMass at hphysical
  unfold physicalCenteredEndpointRowMass at hendpoint
  refine Q'.le_trans' _ _ _ htriangle
    (Q'.le_trans' _ _ _
      (Q'.add_le_add hphysical hendpoint) ?_)
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          (Q'.mkPos 1 16 (by decide))
          (Q'.mkPos 1 16 (by decide))
          (centralPhysicalRowMarginal
            w hw K halfExtent source)))
      (Q'.mul_eqv_congr_right _ _ _
        (by decide)))

/-- The cross-zero Harnack datum proves the calibrated spectral rate with
the sharper `1/16` constant.  In particular this inhabits the requested
calibrated `1/8` field. -/
theorem physicallyRecenteredCrossZero_rate_le_sixteenth
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder : Nat}
    (harnack :
      CalibratedEmptyProfileHarnackData
        w hw K halfExtent diagonalOrder 0) :
    (physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint
        w hw K halfExtent diagonalOrder 0).rate ≤
      Q'.mkPos 1 16 (by decide) := by
  change
    physicalCenteredEndpointRate
        (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
          w hw K halfExtent diagonalOrder 0) ≤
      Q'.mkPos 1 16 (by decide)
  apply physicalCenteredEndpointRate_le_of_rows
    (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
      w hw K halfExtent diagonalOrder 0)
    (Q'.mkPos 1 16 (by decide))
    (by decide)
  intro source hsource
  exact
    physicalCenteredEndpointRowMass_crossZero_le_sixteenth_of_profile
      (harnack.profile_sixteenth hsource)

/-- **One physical rank-one estimate closes the second cross-zero row.**

The Harnack datum supplies the calibrated endpoint `1/16`; the displayed
physical centered-row `1/16` then yields the requested
physical-minus-Mehler `1/8` estimate by the common-rank-one triangle. -/
theorem physicalNormalizedJointRowError_crossZero_le_eighth
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder : Nat}
    (harnack :
      CalibratedEmptyProfileHarnackData
        w hw K halfExtent diagonalOrder 0)
    {source : EdgeLabelling}
    (hsource :
      source ∈
        centralPositiveHalfStates
          w hw K halfExtent)
    (hphysical :
      physicalCenteredPhysicalRowMass
          w hw K halfExtent source ≤
        Q'.mkPos 1 16 (by decide) *
          centralPhysicalRowMarginal
            w hw K halfExtent source) :
    physicalNormalizedJointRowError
        (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
          w hw K halfExtent diagonalOrder 0)
        source ≤
      Q'.mkPos 1 8 (by decide) *
        centralPhysicalRowMarginal
          w hw K halfExtent source := by
  apply physicalNormalizedJointRowError_le_eighth_of_common_rankOne
    (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
      w hw K halfExtent diagonalOrder 0)
    hphysical
  exact
    physicalCenteredEndpointRowMass_crossZero_le_sixteenth_of_profile
      (harnack.profile_sixteenth hsource)

end YMGap.Continuum.BF4CommonRankOneRowTriangle

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4CommonRankOneRowTriangle.finiteJointDifferenceAbsRowMass_le_via_common
#print axioms YMGap.Continuum.BF4CommonRankOneRowTriangle.physicalNormalizedJointRowError_le_eighth_of_common_rankOne
#print axioms YMGap.Continuum.BF4CommonRankOneRowTriangle.physicallyRecenteredCrossZero_rate_le_sixteenth
#print axioms YMGap.Continuum.BF4CommonRankOneRowTriangle.physicalNormalizedJointRowError_crossZero_le_eighth
