/-
# One strict envelope for the guarded face and every finite carrier prefix

The guarded opposite-cell argument gives one cutoff-independent strict factor
for a literal centered face.  Independently, the finite-vacuum-sector
Poincare construction gives one strict common rate on every fixed finite
prefix of representation-base carriers.  Their located rational maximum is
still strictly below one.

This module uses that maximum as one rate which controls both the literal
guarded face cutoff limit and every centered coefficient vector on every
vacuum carrier in the chosen finite prefix.  The prefix bound remains fixed:
no rate uniform in an unbounded/cofinal carrier family, completed full-sector
operator gap, thermodynamic or spacing limit, continuum QFT, or Clay theorem
is claimed.

Constructive contract: located rational maximum, finite Poincare estimates,
and Bishop-real eventual order only.  No `Classical`, choice,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or enlarged
heartbeat option.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixUniformGap
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAggregateSameObjectCutoffLimit

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardFinitePrefixAllVectorEnvelope

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixUniformGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedLimit
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledConstructedUniformCRealGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformCRealGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAggregateSameObjectContraction
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAggregateSameObjectCutoffLimit
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedRowPartition
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableRetainedContraction
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The shared finite-prefix rate -/

private theorem max'_lt_one_local {left right : Q'}
    (hleft : left < (1 : Q')) (hright : right < (1 : Q')) :
    Q'.max' left right < (1 : Q') := by
  unfold Q'.max'
  by_cases h : left ≤ right
  · rw [if_pos h]
    exact hright
  · rw [if_neg h]
    exact hleft

/-- Opaque certificate for the located maximum.  Keeping the recursive
finite-prefix rate behind this boundary prevents downstream cutoff-limit
expressions from normalizing the whole prefix construction. -/
structure ReflectedBentGuardFinitePrefixEnvelopeRateData
    (bound : Nat) : Type where
  rate : Q'
  rate_eq_max : rate =
    Q'.max'
      (constructedFinitePrefixRate
        (w := anchorCoupling) (by decide) (by decide) 2 bound)
      reflectedBentGuardAggregateSameObjectContractionFactor
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  prefix_le :
    constructedFinitePrefixRate
        (w := anchorCoupling) (by decide) (by decide) 2 bound ≤ rate
  face_le : reflectedBentGuardAggregateSameObjectContractionFactor ≤ rate

/-- Constructive maximum certificate, sealed after its finite comparison. -/
opaque reflectedBentGuardFinitePrefixEnvelopeRateData
    (bound : Nat) :
    ReflectedBentGuardFinitePrefixEnvelopeRateData bound := by
  let prefixRate := constructedFinitePrefixRate
    (w := anchorCoupling) (by decide) (by decide) 2 bound
  let face := reflectedBentGuardAggregateSameObjectContractionFactor
  let rate := Q'.max' prefixRate face
  have hprefix0 : (0 : Q') ≤ prefixRate :=
    constructedFinitePrefixRate_nonnegative
      (w := anchorCoupling) (by decide) (by decide) 2 bound
  have hprefix1 : prefixRate < (1 : Q') :=
    constructedFinitePrefixRate_lt_one
      (w := anchorCoupling) (by decide) (by decide) 2 bound
  have hface1 : face < (1 : Q') :=
    reflectedBentGuardAggregateSameObjectContractionFactor_lt_one
  have hrate1 : rate < (1 : Q') :=
    max'_lt_one_local hprefix1 hface1
  exact
    { rate := rate
      rate_eq_max := rfl
      rate_nonnegative :=
        Q'.le_trans' _ _ _ hprefix0 (Q'.le_max'_left _ _)
      rate_lt_one := hrate1
      prefix_le := Q'.le_max'_left _ _
      face_le := Q'.le_max'_right _ _ }

/-- Located maximum of the constructed all-vector finite-prefix rate and the
literal guarded face factor. -/
def reflectedBentGuardFinitePrefixEnvelopeRate (bound : Nat) : Q' :=
  (reflectedBentGuardFinitePrefixEnvelopeRateData bound).rate

theorem reflectedBentGuardFinitePrefixEnvelopeRate_eq_max
    (bound : Nat) :
    reflectedBentGuardFinitePrefixEnvelopeRate bound =
      Q'.max'
        (constructedFinitePrefixRate
          (w := anchorCoupling) (by decide) (by decide) 2 bound)
        reflectedBentGuardAggregateSameObjectContractionFactor :=
  (reflectedBentGuardFinitePrefixEnvelopeRateData bound).rate_eq_max

theorem reflectedBentGuardFinitePrefixEnvelopeRate_nonnegative
    (bound : Nat) :
    (0 : Q') ≤ reflectedBentGuardFinitePrefixEnvelopeRate bound :=
  (reflectedBentGuardFinitePrefixEnvelopeRateData bound).rate_nonnegative

theorem reflectedBentGuardFinitePrefixEnvelopeRate_lt_one
    (bound : Nat) :
    reflectedBentGuardFinitePrefixEnvelopeRate bound < (1 : Q') :=
  (reflectedBentGuardFinitePrefixEnvelopeRateData bound).rate_lt_one

theorem constructedFinitePrefixRate_le_reflectedBentGuardEnvelope
    (bound : Nat) :
    constructedFinitePrefixRate
        (w := anchorCoupling) (by decide) (by decide) 2 bound ≤
      reflectedBentGuardFinitePrefixEnvelopeRate bound :=
  (reflectedBentGuardFinitePrefixEnvelopeRateData bound).prefix_le

theorem reflectedBentGuardFactor_le_finitePrefixEnvelope
    (bound : Nat) :
    reflectedBentGuardAggregateSameObjectContractionFactor ≤
      reflectedBentGuardFinitePrefixEnvelopeRate bound :=
  (reflectedBentGuardFinitePrefixEnvelopeRateData bound).face_le

/-! ## 2. Every vector on the fixed carrier prefix obeys the envelope -/

/-- The finite-prefix all-vector estimate remains valid after relaxing its
rate to the common guarded envelope. -/
theorem reflectedBentGuardFinitePrefixMoving_abs_gap
    (bound base : Nat) (hbase : base ≤ bound)
    (later : Nat)
    (hlater :
      (fixedBaseConstructedUniformGapData
        (w := anchorCoupling) (by decide) (by decide) base 2).start ≤ later)
    (coefficient : Nat → Q') :
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        anchorCoupling (by decide) base later 2 coefficient
    Q'.abs
        (centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          anchorCoupling (by decide) base later 2 moving) ≤
      reflectedBentGuardFinitePrefixEnvelopeRate bound *
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          anchorCoupling (by decide) base later 2 moving := by
  let moving :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
      anchorCoupling (by decide) base later 2 coefficient
  have hprefix := constructedFinitePrefixMoving_abs_gap
    (w := anchorCoupling) (by decide) (by decide)
    2 bound base hbase later hlater coefficient
  have hbaseLater : base ≤ later :=
    Nat.le_trans
      (fixedBaseConstructedUniformGapData
        (w := anchorCoupling) (by decide) (by decide) base 2).start_ge_base
      hlater
  have hmatrixNonnegative := fixedBasePulledMovingMatrix_nonnegative
    (w := anchorCoupling) (hw := by decide)
    base later 2 hbaseLater coefficient
  have hmatrixDiagonal := fixedBasePulledMovingMatrix_le_diagonal
    (w := anchorCoupling) (hw := by decide)
    base later 2 hbaseLater coefficient
  have hdiagonal : (0 : Q') ≤
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        anchorCoupling (by decide) base later 2 moving :=
    Q'.le_trans' _ _ _ hmatrixNonnegative hmatrixDiagonal
  exact Q'.le_trans' _ _ _ hprefix
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (constructedFinitePrefixRate_le_reflectedBentGuardEnvelope bound)
      hdiagonal)

/-- The common envelope controls every centered coefficient vector on every
base carrier in the fixed prefix after representation-cutoff removal. -/
theorem reflectedBentGuardFinitePrefixCutoffLimit_gap
    (bound base : Nat) (hbase : base ≤ bound)
    (coefficient : Nat → Q') :
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        (w := anchorCoupling) (by decide) (by decide)
        base 2 coefficient)
      (CReal.mul
        (CReal.ofQ' (reflectedBentGuardFinitePrefixEnvelopeRate bound))
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          (w := anchorCoupling) (by decide) (by decide)
          base 2 coefficient)) := by
  let data := fixedBaseConstructedUniformGapData
    (w := anchorCoupling) (by decide) (by decide) base 2
  apply cReal_leEv_of_eventual_abs_gap
    (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
      (w := anchorCoupling) (by decide) (by decide) base 2 coefficient)
    (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
      (w := anchorCoupling) (by decide) (by decide) base 2 coefficient)
    (reflectedBentGuardFinitePrefixEnvelopeRate bound)
    (reflectedBentGuardFinitePrefixEnvelopeRate_nonnegative bound)
    (reflectedBentGuardFinitePrefixEnvelopeRate_lt_one bound)
    data.start
  intro later hlater
  rw [centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit_approx]
  rw [centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit_approx]
  exact reflectedBentGuardFinitePrefixMoving_abs_gap
    bound base hbase later hlater coefficient

/-! ## 3. The same envelope controls the literal guarded face -/

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

/-- The literal guarded face contraction can be relaxed to the same strict
rate that controls every vector on the chosen finite carrier prefix. -/
theorem reflectedBentGuardFaceCutoffLimit_leEv_finitePrefixEnvelope
    (bound : Nat) :
    CReal.leEv
      (anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit
        2 reflectedBentRootFaceId)
      (CReal.mul
        (CReal.ofQ' (reflectedBentGuardFinitePrefixEnvelopeRate bound))
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
      (reflectedBentGuardFactor_le_finitePrefixEnvelope bound)
      (reflectedBentGuardFaceConnectedNormCutoffLimit_approx_nonnegative
        cutoff))
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))

/-! ## 4. One package, with the cofinal boundary left explicit -/

/-- One strict shared rate controlling the guarded face and every centered
coefficient vector on every base carrier in a chosen finite prefix. -/
structure ReflectedBentGuardFinitePrefixAllVectorEnvelopeData
    (bound : Nat) : Type 1 where
  rate : Q'
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  face_gap : CReal.leEv
    (anchorSlabPhysicalFaceConnectedAutocorrelationCutoffLimit
      2 reflectedBentRootFaceId)
    (CReal.mul (CReal.ofQ' rate)
      reflectedBentGuardFaceConnectedNormCutoffLimit)
  allVector_gap : ∀ base : Nat, base ≤ bound →
    ∀ coefficient : Nat → Q',
      CReal.leEv
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
          (w := anchorCoupling) (by decide) (by decide)
          base 2 coefficient)
        (CReal.mul (CReal.ofQ' rate)
          (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
            (w := anchorCoupling) (by decide) (by decide)
            base 2 coefficient))

/-- Constructive inhabitant for every fixed finite prefix.  No passage to a
single rate uniform in `bound` is made. -/
def reflectedBentGuardFinitePrefixAllVectorEnvelopeData
    (bound : Nat) :
    ReflectedBentGuardFinitePrefixAllVectorEnvelopeData bound where
  rate := reflectedBentGuardFinitePrefixEnvelopeRate bound
  rate_nonnegative :=
    reflectedBentGuardFinitePrefixEnvelopeRate_nonnegative bound
  rate_lt_one := reflectedBentGuardFinitePrefixEnvelopeRate_lt_one bound
  face_gap :=
    reflectedBentGuardFaceCutoffLimit_leEv_finitePrefixEnvelope bound
  allVector_gap := reflectedBentGuardFinitePrefixCutoffLimit_gap bound

#print axioms reflectedBentGuardFinitePrefixEnvelopeRate_lt_one
#print axioms reflectedBentGuardFinitePrefixMoving_abs_gap
#print axioms reflectedBentGuardFinitePrefixCutoffLimit_gap
#print axioms reflectedBentGuardFaceCutoffLimit_leEv_finitePrefixEnvelope
#print axioms reflectedBentGuardFinitePrefixAllVectorEnvelopeData

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardFinitePrefixAllVectorEnvelope
