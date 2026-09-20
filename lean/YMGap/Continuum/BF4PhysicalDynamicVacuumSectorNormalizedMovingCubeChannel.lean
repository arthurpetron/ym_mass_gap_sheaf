/-
# Explicit normalization debt for the dynamic moving cube

The exact moving-centered cube has a positive rational norm floor at every
scale, but the dynamic-family interface does not keep that floor uniformly
away from zero.  This file records the honest alternative: rescale by the
reciprocal of the actual floor.  The rescaled completed vector has norm at
least one, while the reciprocal and its powers remain explicit normalization
debts which later cutoff-limit estimates must control.

No boundedness of those debts, cutoff convergence of the rescaled channel,
adaptive transition-product inhabitant, projective measure, OS
reconstruction, continuum Yang--Mills theory, or Clay conclusion is proved.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
import YMGap.Continuum.BoundedTransferCalculus

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerLaws
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero
open YMGap.Continuum.RCStrictPositivity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The moving coordinate floor is a subunit quantity -/

/-- The explicit moving-coordinate floor is at most one.  The proof compares
it with the vacuum row at the retained anchor and then uses normalization of
that actual row marginal. -/
theorem centralPhysicalVacuumSectorCoordinateFloor_le_one
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) :
    centralPhysicalVacuumSectorCoordinateFloor
        w (Q'.le_of_lt hw0) base half ≤ (1 : Q') := by
  let anchor := centralPhysicalVacuumSectorCoordinateAnchor w base half
  have hvacuum :
      zeroEdgeLabelling ∈ centralPositiveHalfStates
        w (Q'.le_of_lt hw0) anchor half :=
    zeroEdgeLabelling_mem_centralPositiveHalfStates
      (Q'.le_of_lt hw0) anchor half
  have hfloor :
      centralPhysicalMovingPositiveRowFloor
          w (Q'.le_of_lt hw0) anchor half ≤
        centralPhysicalRowMarginal
          w (Q'.le_of_lt hw0) anchor half zeroEdgeLabelling :=
    centralPhysicalMovingPositiveRowFloor_le
      hw0 hw1 half
      (Nat.le_max_left
        (centralPhysicalUniformRowFloorCutoff w half) base)
      (Nat.le_refl anchor) hvacuum
  have hrow :
      centralPhysicalRowMarginal
          w (Q'.le_of_lt hw0) anchor half zeroEdgeLabelling ≤ (1 : Q') :=
    centralPhysicalRowMarginal_le_one_on_carrier hvacuum
  change centralPhysicalMovingPositiveRowFloor
      w (Q'.le_of_lt hw0) anchor half ≤ (1 : Q')
  exact Q'.le_trans' _ _ _ hfloor hrow

/-! ## 2. Rational rescaling and its explicit debt -/

/-- Reciprocal rescaling of the concrete cube floor at one dynamic scale. -/
def movingCubeNormalizationScale
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) : Q' :=
  let floor := (centralPhysicalDynamicMovingCubeRCChannel family).normFloor scale
  Q'.divPos 1 floor
    ((centralPhysicalDynamicMovingCubeRCChannel family).normFloor_pos scale)

theorem movingCubeNormalizationScale_pos
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) :
    (0 : Q') < movingCubeNormalizationScale family scale := by
  unfold movingCubeNormalizationScale
  exact Q'.divPos_pos _ _ _ (by decide)

/-- Because the raw coordinate floor is at most one, reciprocal
normalization never shrinks the observable. -/
theorem one_le_movingCubeNormalizationScale
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) :
    (1 : Q') ≤ movingCubeNormalizationScale family scale := by
  let floor := (centralPhysicalDynamicMovingCubeRCChannel family).normFloor scale
  have hfloorPos : (0 : Q') < floor :=
    (centralPhysicalDynamicMovingCubeRCChannel family).normFloor_pos scale
  have hfloorOne : floor ≤ (1 : Q') := by
    exact centralPhysicalVacuumSectorCoordinateFloor_le_one
      (family.nome_pos scale) (family.nome_lt_one scale) 1 0
  unfold movingCubeNormalizationScale
  exact Q'.le_divPos_of_mul_le 1 floor hfloorPos
    (Q'.le_trans' _ floor _
      (Q'.le_of_eqv (Q'.one_mul_eqv floor)) hfloorOne)

/-- The normalization scale cancels the exact floor. -/
theorem movingCubeNormalizationScale_mul_floor_eqv_one
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) :
    (movingCubeNormalizationScale family scale *
      (centralPhysicalDynamicMovingCubeRCChannel family).normFloor scale) ≈
        (1 : Q') := by
  unfold movingCubeNormalizationScale
  exact Q'.divPos_mul_eqv _ _ _

/-- Norm scaling costs the square of the reciprocal floor. -/
def movingCubeNormalizationNormDebt
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) : Q' :=
  movingCubeNormalizationScale family scale *
    movingCubeNormalizationScale family scale

/-- Squared-correlation scaling costs the fourth power of the reciprocal
floor.  This debt must be controlled in any cutoff-limit theorem for the
renormalized observable. -/
def movingCubeNormalizationCorrelationSqDebt
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) : Q' :=
  movingCubeNormalizationNormDebt family scale *
    movingCubeNormalizationNormDebt family scale

theorem movingCubeNormalizationNormDebt_pos
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) :
    (0 : Q') < movingCubeNormalizationNormDebt family scale :=
  Q'.mul_pos
    (movingCubeNormalizationScale_pos family scale)
    (movingCubeNormalizationScale_pos family scale)

theorem movingCubeNormalizationCorrelationSqDebt_pos
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) :
    (0 : Q') < movingCubeNormalizationCorrelationSqDebt family scale :=
  Q'.mul_pos
    (movingCubeNormalizationNormDebt_pos family scale)
    (movingCubeNormalizationNormDebt_pos family scale)

/-! ## 3. The actual rescaled completed vector -/

/-- The unnormalized moving cube, embedded in the actual global completed
vacuum complement. -/
def movingCubeGlobalVectorAt
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) :
    CentralPhysicalCutoffCompletedVacuumComplement
      (family.nome_pos scale) (family.nome_lt_one scale) 0 :=
  centralPhysicalVacuumSectorCylinderCompletedVacuumComplementToGlobal
    ((centralPhysicalDynamicMovingCubeRCChannel family).vectorAt scale)

/-- The literal global completed vector obtained by reciprocal-floor
rescaling.  Vacuum orthogonality is preserved by the existing completed
rational-module operation. -/
def normalizedMovingCubeGlobalVectorAt
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) :
    CentralPhysicalCutoffCompletedVacuumComplement
      (family.nome_pos scale) (family.nome_lt_one scale) 0 :=
  centralPhysicalCutoffCompletedVacuumComplementSmul
    (family.nome_pos scale) (family.nome_lt_one scale) 0
    (movingCubeNormalizationScale family scale)
    (movingCubeGlobalVectorAt family scale)

/-- The literal completed norm square of the actual normalized global
vector. -/
def normalizedMovingCubeNormSq
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) : CReal.RC :=
  centralPhysicalCutoffCompletedInner
    (family.nome_pos scale) (family.nome_lt_one scale) 0
    (normalizedMovingCubeGlobalVectorAt family scale).1
    (normalizedMovingCubeGlobalVectorAt family scale).1

/-- The literal global same-object matrix coefficient of the actual
normalized vector. -/
def normalizedMovingCubeConnectedAutocorrelation
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale time : Nat) : CReal.RC :=
  centralPhysicalCutoffCompletedInner
    (family.nome_pos scale) (family.nome_lt_one scale) 0
    (centralPhysicalConcreteAdaptiveCompletedMarkovPower
      (family.nome_pos scale) (family.nome_lt_one scale) 0 time
      (normalizedMovingCubeGlobalVectorAt family scale).1)
    (normalizedMovingCubeGlobalVectorAt family scale).1

/-- Natural powers of the concrete completed transfer commute with rational
scaling. -/
theorem centralPhysicalConcreteAdaptiveCompletedMarkovPower_smul
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half time : Nat) (scalar : Q')
    (vector : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    centralPhysicalConcreteAdaptiveCompletedMarkovPower
        hw0 hw1 half time
        (completedPhysicalLinearSmul hw0 hw1 half scalar vector) =
      completedPhysicalLinearSmul hw0 hw1 half scalar
        (centralPhysicalConcreteAdaptiveCompletedMarkovPower
          hw0 hw1 half time vector) := by
  induction time with
  | zero => rfl
  | succ time ih =>
      change centralPhysicalConcreteAdaptiveCompletedMarkovTransfer
          hw0 hw1 half
          (centralPhysicalConcreteAdaptiveCompletedMarkovPower
            hw0 hw1 half time
            (completedPhysicalLinearSmul hw0 hw1 half scalar vector)) = _
      rw [ih]
      exact centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_smul
        hw0 hw1 half scalar
          (centralPhysicalConcreteAdaptiveCompletedMarkovPower
            hw0 hw1 half time vector)

/-- The norm of the actual normalized global vector is exactly the reciprocal
square debt times the literal norm of the original same-object channel. -/
theorem normalizedMovingCubeNormSq_eq_scaled
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) :
    normalizedMovingCubeNormSq family scale =
      CReal.RCscale
        (movingCubeNormalizationNormDebt family scale)
        ((centralPhysicalDynamicMovingCubeRCChannel family).normSq scale) := by
  unfold normalizedMovingCubeNormSq normalizedMovingCubeGlobalVectorAt
    movingCubeGlobalVectorAt movingCubeNormalizationNormDebt
    DynamicVacuumSectorSameObjectRCChannel.normSq
    centralPhysicalVacuumSectorCylinderCompletedInner
    centralPhysicalVacuumSectorCylinderCompletedVacuumComplementToGlobal
    centralPhysicalCutoffCompletedVacuumComplementSmul
  rw [centralPhysicalCutoffCompletedInner_smul_left,
    centralPhysicalCutoffCompletedInner_smul_right,
    CReal.RCscale_RCscale]

/-- The actual normalized matrix coefficient is the reciprocal-square debt
times the exact original sampled channel; no replacement observable enters. -/
theorem normalizedMovingCubeConnectedAutocorrelation_eq_scaled
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale time : Nat) :
    normalizedMovingCubeConnectedAutocorrelation family scale time =
      CReal.RCscale
        (movingCubeNormalizationNormDebt family scale)
        (DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation
          (centralPhysicalDynamicMovingCubeRCChannel family)
          scale time) := by
  rw [DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation_eq_global
    (centralPhysicalDynamicMovingCubeRCChannel family) scale time]
  unfold normalizedMovingCubeConnectedAutocorrelation
    normalizedMovingCubeGlobalVectorAt movingCubeGlobalVectorAt
    movingCubeNormalizationNormDebt
    centralPhysicalVacuumSectorCylinderCompletedVacuumComplementToGlobal
    centralPhysicalCutoffCompletedVacuumComplementSmul
  rw [centralPhysicalConcreteAdaptiveCompletedMarkovPower_smul,
    centralPhysicalCutoffCompletedInner_smul_left,
    centralPhysicalCutoffCompletedInner_smul_right,
    CReal.RCscale_RCscale]

private theorem RCmul_scale_both_local
    (scalar : Q') (left right : CReal.RC) :
    CReal.RCmul (CReal.RCscale scalar left) (CReal.RCscale scalar right) =
      CReal.RCscale (scalar * scalar) (CReal.RCmul left right) := by
  refine Quotient.inductionOn₂ left right ?_
  intro L R
  exact Quotient.sound
    (YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
      (fun n => by
        change ((scalar * L.approx n) * (scalar * R.approx n)).eqv
          ((scalar * scalar) * (L.approx n * R.approx n))
        ring_qeqv))

private theorem RCmul_rate_scale_both_local
    (rate scalar : Q') (value : CReal.RC) :
    CReal.RCmul
        (CReal.RCscale rate (CReal.RCscale scalar value))
        (CReal.RCscale scalar value) =
      CReal.RCscale (scalar * scalar)
        (CReal.RCmul (CReal.RCscale rate value) value) := by
  refine Quotient.inductionOn value ?_
  intro V
  exact Quotient.sound
    (YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
      (fun n => by
        change ((rate * (scalar * V.approx n)) *
            (scalar * V.approx n)).eqv
          ((scalar * scalar) * ((rate * V.approx n) * V.approx n))
        ring_qeqv))

/-- The actual normalized same-object correlation obeys the same completed
rate.  The reciprocal fourth-power appears only as the explicit scaling used
to transport the original squared estimate; after rewriting in terms of the
actual normalized norm it does not alter the rate. -/
theorem normalizedMovingCubeConnectedAutocorrelationSq_decay
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale time : Nat) :
    CReal.RCle
      (CReal.RCmul
        (normalizedMovingCubeConnectedAutocorrelation family scale time)
        (normalizedMovingCubeConnectedAutocorrelation family scale time))
      (CReal.RCmul
        (CReal.RCscale
          ((((family.completedGap scale).rate *
              (family.completedGap scale).rate)) ^ time)
          (normalizedMovingCubeNormSq family scale))
        (normalizedMovingCubeNormSq family scale)) := by
  let channel := centralPhysicalDynamicMovingCubeRCChannel family
  let debt := movingCubeNormalizationNormDebt family scale
  have hdecay := channel.connectedAutocorrelationSq_decay scale time
  unfold DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelationSq at hdecay
  have hscaled := CReal.RCscale_mono
    (Q'.le_of_lt
      (movingCubeNormalizationCorrelationSqDebt_pos family scale))
    hdecay
  rw [normalizedMovingCubeConnectedAutocorrelation_eq_scaled,
    normalizedMovingCubeNormSq_eq_scaled,
    RCmul_scale_both_local,
    RCmul_rate_scale_both_local]
  exact hscaled

private theorem RCscale_ofQ'_local (scalar value : Q') :
    CReal.RCscale scalar
        (Quotient.mk CReal.crealSetoid (CReal.ofQ' value)) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' (scalar * value)) := by
  rw [CReal.RCscale_mk]
  exact Quotient.sound
    (CReal.Equiv.symm (CRealAlg.ofQ'_mul scalar value))

/-- Reciprocal-floor normalization gives the actual completed vector the
uniform rational norm floor one at every scale. -/
theorem one_le_normalizedMovingCubeNormSq
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) :
    CReal.RCle
      (Quotient.mk CReal.crealSetoid (CReal.ofQ' 1))
      (normalizedMovingCubeNormSq family scale) := by
  let channel := centralPhysicalDynamicMovingCubeRCChannel family
  let floor := channel.normFloor scale
  let scalar := movingCubeNormalizationScale family scale
  let debt := movingCubeNormalizationNormDebt family scale
  have hscaled := CReal.RCscale_mono
    (Q'.le_of_lt (movingCubeNormalizationNormDebt_pos family scale))
    (channel.normFloor_le_normSq scale)
  have hcancel : scalar * floor ≈ (1 : Q') := by
    exact movingCubeNormalizationScale_mul_floor_eqv_one family scale
  have hdebtFloor : debt * floor ≈ scalar := by
    unfold debt movingCubeNormalizationNormDebt
    exact Q'.eqv_trans _ (scalar * (scalar * floor)) _
      (Q'.mul_assoc_eqv scalar scalar floor)
      (Q'.eqv_trans _ (scalar * 1) _
        (Q'.mul_eqv_congr_left scalar _ _ hcancel)
        (Q'.mul_one_eqv scalar))
  have honeDebtFloor : (1 : Q') ≤ debt * floor :=
    Q'.le_trans' _ scalar _
      (one_le_movingCubeNormalizationScale family scale)
      (Q'.ge_of_eqv hdebtFloor)
  have hconstant :
      CReal.RCle
        (Quotient.mk CReal.crealSetoid (CReal.ofQ' 1))
        (CReal.RCscale debt
          (Quotient.mk CReal.crealSetoid (CReal.ofQ' floor))) := by
    rw [RCscale_ofQ'_local]
    rw [CReal.RCle_mk]
    exact CReal.leEv_of_le (CReal.ofQ'_le_ofQ' honeDebtFloor)
  rw [normalizedMovingCubeNormSq_eq_scaled]
  exact CReal.RCle_trans hconstant hscaled

/-! ## 4. Physical-time sampling of the normalized observable -/

/-- The literal normalized connected autocorrelation sampled with the same
canonical floor schedule as the underlying dynamic family. -/
def normalizedMovingCubeSampledConnectedAutocorrelation
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale time : Nat) : CReal.RC :=
  normalizedMovingCubeConnectedAutocorrelation family scale
    (centralPhysicalDynamicRCLatticeSteps family scale time)

/-- The square of the literal sampled normalized autocorrelation. -/
def normalizedMovingCubeSampledConnectedAutocorrelationSq
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale time : Nat) : CReal.RC :=
  CReal.RCmul
    (normalizedMovingCubeSampledConnectedAutocorrelation family scale time)
    (normalizedMovingCubeSampledConnectedAutocorrelation family scale time)

/-- Canonical physical-time sampling preserves the exact normalized decay
estimate at the scheduled lattice power. -/
theorem normalizedMovingCubeSampledConnectedAutocorrelationSq_decay
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale time : Nat) :
    CReal.RCle
      (normalizedMovingCubeSampledConnectedAutocorrelationSq
        family scale time)
      (CReal.RCmul
        (CReal.RCscale
          ((((family.completedGap scale).rate *
              (family.completedGap scale).rate)) ^
            (centralPhysicalDynamicRCLatticeSteps family scale time))
          (normalizedMovingCubeNormSq family scale))
        (normalizedMovingCubeNormSq family scale)) := by
  exact normalizedMovingCubeConnectedAutocorrelationSq_decay
    family scale (centralPhysicalDynamicRCLatticeSteps family scale time)

/-- Zero transfer steps identify the normalized matrix coefficient with the
literal normalized norm square. -/
theorem normalizedMovingCubeConnectedAutocorrelation_zero_eq_normSq
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) :
    normalizedMovingCubeConnectedAutocorrelation family scale 0 =
      normalizedMovingCubeNormSq family scale := by
  rfl

/-- Floor sampling at physical time zero chooses zero transfer steps. -/
theorem normalizedMovingCubeSampledConnectedAutocorrelation_zero_eq_normSq
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) :
    normalizedMovingCubeSampledConnectedAutocorrelation family scale 0 =
      normalizedMovingCubeNormSq family scale := by
  simpa [normalizedMovingCubeSampledConnectedAutocorrelation,
    centralPhysicalDynamicRCLatticeSteps,
    centralPhysicalDynamicRCSampling,
    physicalSeparationSamplingOfSpacingToZero, floorLatticeSteps] using
      (normalizedMovingCubeConnectedAutocorrelation_zero_eq_normSq
        family scale)

/-- Every finite-cutoff zero-time value of the normalized observable has the
same rational lower witness one. -/
theorem one_le_normalizedMovingCubeSampledConnectedAutocorrelation_zero
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) :
    CReal.RCle
      (Quotient.mk CReal.crealSetoid (CReal.ofQ' 1))
      (normalizedMovingCubeSampledConnectedAutocorrelation family scale 0) := by
  rw [normalizedMovingCubeSampledConnectedAutocorrelation_zero_eq_normSq]
  exact one_le_normalizedMovingCubeNormSq family scale

/-! ## 5. Honest cutoff-limit interface for the normalized channel -/

/-- Explicit representative-level cutoff removal for the actual normalized
global same-object channel.  The convergence field is new analytic data: in
particular, this structure cannot be inhabited merely from pointwise
positivity, because its representatives include the reciprocal-floor debt. -/
structure NormalizedMovingCubeScheduledRCContinuumLimit
    (family : DynamicVacuumSectorCompletedFamily 0) : Type 1 where
  representative : Nat -> Nat -> CReal
  represents : forall time scale,
    Quotient.mk CReal.crealSetoid (representative time scale) =
      normalizedMovingCubeSampledConnectedAutocorrelation family scale time
  limitRepresentative : Nat -> CReal
  converges : forall time,
    CReal.ConvergesTo (fun scale => representative time scale)
      (limitRepresentative time)

namespace NormalizedMovingCubeScheduledRCContinuumLimit

/-- The continuum correlation selected by an explicit limit of the same
normalized finite-cutoff matrix coefficients. -/
def continuumConnectedAutocorrelation
    {family : DynamicVacuumSectorCompletedFamily 0}
    (limit : NormalizedMovingCubeScheduledRCContinuumLimit family)
    (time : Nat) : CReal.RC :=
  Quotient.mk CReal.crealSetoid (limit.limitRepresentative time)

/-- The explicit rational unit floor survives the same-observable cutoff
limit.  Unlike the weaker `RCIsPositive` projection below, this theorem
retains the actual floor witness needed by downstream clustering certificates.
It is obtained only from the finite unit-floor estimate and the supplied
representative convergence modulus. -/
theorem one_le_continuumConnectedAutocorrelation_zero
    {family : DynamicVacuumSectorCompletedFamily 0}
    (limit : NormalizedMovingCubeScheduledRCContinuumLimit family) :
    CReal.RCle
      (Quotient.mk CReal.crealSetoid (CReal.ofQ' 1))
      (limit.continuumConnectedAutocorrelation 0) := by
  have hterm : forall scale,
      CReal.leEv (CReal.ofQ' 1) (limit.representative 0 scale) := by
    intro scale
    have hrc : CReal.RCle
        (Quotient.mk CReal.crealSetoid (CReal.ofQ' 1))
        (Quotient.mk CReal.crealSetoid
          (limit.representative 0 scale)) := by
      rw [limit.represents 0 scale]
      exact one_le_normalizedMovingCubeSampledConnectedAutocorrelation_zero
        family scale
    exact hrc
  have hlimit : CReal.leEv
      (CReal.ofQ' 1) (limit.limitRepresentative 0) := by
    apply CReal.leEv_of_convergesTo_le
      (CReal.convergesTo_const (CReal.ofQ' 1))
      (limit.converges 0)
    exact hterm
  exact hlimit

/-- If the reciprocal-normalized same-observable channel converges, its
continuum zero-time value is automatically nonzero.  No separate uniform
norm-floor hypothesis is needed: the floor one was proved before taking the
limit.  Constructing this limit, and hence controlling the normalization
debt, remains open. -/
theorem continuumConnectedAutocorrelation_zero_isPositive
    {family : DynamicVacuumSectorCompletedFamily 0}
    (limit : NormalizedMovingCubeScheduledRCContinuumLimit family) :
    RCIsPositive (limit.continuumConnectedAutocorrelation 0) := by
  exact ⟨1, by decide, limit.one_le_continuumConnectedAutocorrelation_zero⟩

end NormalizedMovingCubeScheduledRCContinuumLimit

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.centralPhysicalVacuumSectorCoordinateFloor_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.one_le_movingCubeNormalizationScale
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.movingCubeNormalizationScale_mul_floor_eqv_one
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.movingCubeNormalizationNormDebt_pos
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.movingCubeNormalizationCorrelationSqDebt_pos
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.centralPhysicalConcreteAdaptiveCompletedMarkovPower_smul
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.normalizedMovingCubeNormSq_eq_scaled
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.normalizedMovingCubeConnectedAutocorrelation_eq_scaled
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.normalizedMovingCubeConnectedAutocorrelationSq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.one_le_normalizedMovingCubeNormSq
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.normalizedMovingCubeSampledConnectedAutocorrelationSq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.normalizedMovingCubeSampledConnectedAutocorrelation_zero_eq_normSq
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.one_le_normalizedMovingCubeSampledConnectedAutocorrelation_zero
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.NormalizedMovingCubeScheduledRCContinuumLimit.one_le_continuumConnectedAutocorrelation_zero
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation_zero_isPositive
