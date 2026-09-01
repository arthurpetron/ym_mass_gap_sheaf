/-
# The guarded face adds no new cofinal rate obligation

The finite-prefix envelope aligns one literal guarded face with the existing
all-vector prefix gaps.  This module performs the corresponding conditional
cofinal alignment.  Given the already isolated cofinal strict ceiling on the
constructed prefix rates, its located maximum with the fixed guarded-face
factor is still below one.  That one rate controls both the face and every
centered coefficient vector on every base carrier after representation-cutoff
removal.

No cofinal ceiling is constructed here.  In particular, the all-base
conductance/resistance problem, completed full-sector gap, spacing and volume
uniformity, continuum measure, OS/GNS reconstruction, and Clay theorem remain
open.

Constructive contract: located rational maximum and Bishop-real eventual
order only.  No `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or enlarged heartbeat option.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCofinalPrefixRateBridge
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardFinitePrefixAllVectorEnvelope

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardCofinalAllVectorEnvelope

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedLimit
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCofinalPrefixRateBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixUniformGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledConstructedUniformCRealGap
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAggregateSameObjectContraction
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAggregateSameObjectCutoffLimit
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableRetainedContraction
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

private theorem max'_lt_one_local {left right : Q'}
    (hleft : left < (1 : Q')) (hright : right < (1 : Q')) :
    Q'.max' left right < (1 : Q') := by
  unfold Q'.max'
  by_cases h : left ≤ right
  · rw [if_pos h]
    exact hright
  · rw [if_neg h]
    exact hleft

/-! ## 1. Cofinal envelope rate -/

/-- Maximum of a proposed cofinal all-vector rate and the fixed guarded-face
factor. -/
def reflectedBentGuardCofinalEnvelopeRate (q : Q') : Q' :=
  Q'.max' q reflectedBentGuardAggregateSameObjectContractionFactor

theorem cofinalRate_le_reflectedBentGuardCofinalEnvelope (q : Q') :
    q ≤ reflectedBentGuardCofinalEnvelopeRate q :=
  Q'.le_max'_left _ _

theorem reflectedBentGuardFactor_le_cofinalEnvelope (q : Q') :
    reflectedBentGuardAggregateSameObjectContractionFactor ≤
      reflectedBentGuardCofinalEnvelopeRate q :=
  Q'.le_max'_right _ _

theorem reflectedBentGuardCofinalEnvelopeRate_nonnegative
    {q : Q'} (hq0 : (0 : Q') ≤ q) :
    (0 : Q') ≤ reflectedBentGuardCofinalEnvelopeRate q :=
  Q'.le_trans' _ _ _ hq0
    (cofinalRate_le_reflectedBentGuardCofinalEnvelope q)

theorem reflectedBentGuardCofinalEnvelopeRate_lt_one
    {q : Q'} (hq1 : q < (1 : Q')) :
    reflectedBentGuardCofinalEnvelopeRate q < (1 : Q') :=
  max'_lt_one_local hq1
    reflectedBentGuardAggregateSameObjectContractionFactor_lt_one

/-! ## 2. The old cofinal ceiling relaxes to the guarded envelope -/

namespace FixedNomeCofinalFinitePrefixRateCeiling

/-- A cofinal ceiling on the all-vector prefix rates remains a cofinal ceiling
after adjoining the guarded-face factor. -/
def toReflectedBentGuardCofinalEnvelopeCeiling
    {q : Q'}
    (family : FixedNomeCofinalFinitePrefixRateCeiling
      anchorCoupling (by decide) (by decide) 2 q) :
    FixedNomeCofinalFinitePrefixRateCeiling
      anchorCoupling (by decide) (by decide) 2
        (reflectedBentGuardCofinalEnvelopeRate q) where
  rate_nonnegative :=
    reflectedBentGuardCofinalEnvelopeRate_nonnegative
      family.rate_nonnegative
  rate_lt_one :=
    reflectedBentGuardCofinalEnvelopeRate_lt_one family.rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  prefixRate_le := by
    intro request
    exact Q'.le_trans' _ _ _ (family.prefixRate_le request)
      (cofinalRate_le_reflectedBentGuardCofinalEnvelope q)

/-- Hence the guarded envelope controls every centered coefficient vector on
every base carrier after representation-cutoff removal. -/
theorem allVectorCutoffLimit_gap_at_reflectedBentGuardEnvelope
    {q : Q'}
    (family : FixedNomeCofinalFinitePrefixRateCeiling
      anchorCoupling (by decide) (by decide) 2 q)
    (base : Nat) (coefficient : Nat → Q') :
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        (w := anchorCoupling) (by decide) (by decide)
        base 2 coefficient)
      (CReal.mul
        (CReal.ofQ' (reflectedBentGuardCofinalEnvelopeRate q))
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          (w := anchorCoupling) (by decide) (by decide)
          base 2 coefficient)) :=
  (toReflectedBentGuardCofinalEnvelopeCeiling family)
    |>.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
      (by decide) (by decide) 2 base coefficient

end FixedNomeCofinalFinitePrefixRateCeiling

/-! ## 3. The literal guarded face uses that same cofinal rate -/

@[simp] private theorem cRealMul_approx_local
    (left right : CReal) (cutoff : Nat) :
    (CReal.mul left right).approx cutoff =
      left.approx cutoff * right.approx cutoff := rfl

private theorem reflectedBentGuardFaceConnectedNormCutoffLimit_approx_nonnegative
    (cutoff : Nat) :
    (0 : Q') ≤ reflectedBentGuardFaceConnectedNormCutoffLimit.approx cutoff := by
  have hnorm :=
    centralPhysicalConnectedNormCutoffLimit_approx_eqv_centeredNorm
      (w := anchorCoupling) (by decide) (by decide) 2 cutoff
      (slabPhysicalFacePositiveUnitObservable reflectedBentRootFaceId)
  exact Q'.le_trans' _ _ _
    (centralPhysicalWeightedSquare_nonnegative
      anchorCoupling (by decide) cutoff 2
      (centralPhysicalCenteredObservable
        anchorCoupling (by decide) cutoff 2
        (slabPhysicalFacePositiveUnitObservable
          reflectedBentRootFaceId).value))
    (Q'.le_of_eqv (Q'.eqv_symm hnorm))

/-- The fixed guarded-face factor relaxes to the common cofinal envelope. -/
theorem reflectedBentGuardFaceCutoffLimit_leEv_cofinalEnvelope
    (q : Q') :
    CReal.leEv
      (anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit
        2 reflectedBentRootFaceId)
      (CReal.mul
        (CReal.ofQ' (reflectedBentGuardCofinalEnvelopeRate q))
        reflectedBentGuardFaceConnectedNormCutoffLimit) := by
  refine CReal.leEv_trans
    reflectedBentGuardFaceConnectedAutocorrelationCutoffLimit_leEv_factor_mul_norm
    ?_
  intro epsilon hepsilon
  refine ⟨0, ?_⟩
  intro cutoff _hcutoff
  rw [cRealMul_approx_local, cRealMul_approx_local,
    CReal.ofQ'_approx, CReal.ofQ'_approx]
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (reflectedBentGuardFactor_le_cofinalEnvelope q)
      (reflectedBentGuardFaceConnectedNormCutoffLimit_approx_nonnegative
        cutoff))
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))

/-! ## 4. One conditional cofinal package -/

/-- A single strict rate for the guarded face and every centered vector on
every finite base carrier.  The constructor below still requires the explicit
cofinal prefix ceiling; no inhabitant is hidden in this structure. -/
structure ReflectedBentGuardCofinalAllVectorEnvelopeData : Type 1 where
  rate : Q'
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  prefixCeiling : FixedNomeCofinalFinitePrefixRateCeiling
    anchorCoupling (by decide) (by decide) 2 rate
  face_gap : CReal.leEv
    (anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit
      2 reflectedBentRootFaceId)
    (CReal.mul (CReal.ofQ' rate)
      reflectedBentGuardFaceConnectedNormCutoffLimit)
  allVector_gap : ∀ base : Nat, ∀ coefficient : Nat → Q',
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        (w := anchorCoupling) (by decide) (by decide)
        base 2 coefficient)
      (CReal.mul (CReal.ofQ' rate)
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          (w := anchorCoupling) (by decide) (by decide)
          base 2 coefficient))

/-- The existing cofinal prefix-ceiling interface is sufficient for the
shared guarded face/all-vector envelope; the face imposes no new infinitary
input. -/
def reflectedBentGuardCofinalAllVectorEnvelopeData
    {q : Q'}
    (family : FixedNomeCofinalFinitePrefixRateCeiling
      anchorCoupling (by decide) (by decide) 2 q) :
    ReflectedBentGuardCofinalAllVectorEnvelopeData where
  rate := reflectedBentGuardCofinalEnvelopeRate q
  rate_nonnegative :=
    reflectedBentGuardCofinalEnvelopeRate_nonnegative
      family.rate_nonnegative
  rate_lt_one :=
    reflectedBentGuardCofinalEnvelopeRate_lt_one family.rate_lt_one
  prefixCeiling :=
    FixedNomeCofinalFinitePrefixRateCeiling.toReflectedBentGuardCofinalEnvelopeCeiling
      family
  face_gap := reflectedBentGuardFaceCutoffLimit_leEv_cofinalEnvelope q
  allVector_gap :=
    FixedNomeCofinalFinitePrefixRateCeiling.allVectorCutoffLimit_gap_at_reflectedBentGuardEnvelope
      family

#print axioms reflectedBentGuardCofinalEnvelopeRate_lt_one
#print axioms
  FixedNomeCofinalFinitePrefixRateCeiling.toReflectedBentGuardCofinalEnvelopeCeiling
#print axioms
  FixedNomeCofinalFinitePrefixRateCeiling.allVectorCutoffLimit_gap_at_reflectedBentGuardEnvelope
#print axioms reflectedBentGuardFaceCutoffLimit_leEv_cofinalEnvelope
#print axioms reflectedBentGuardCofinalAllVectorEnvelopeData

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardCofinalAllVectorEnvelope
