/-
# BF4/AF reduction of the open completed weak-to-strong RG bridge

`CompletedWeakToStrongRGBridge` deliberately records every datum needed to
transport the concrete completed strong-coupling gap to a weak-coupling
physical family.  Several of its fields are not independent once the existing
BF4/Faraut producer is placed on the proved two-loop AF trajectory:

* the weak coupling schedule and its modulus are the AF schedule;
* the physical spacing and its modulus come from the quadratic BF4 envelope;
* the block depth is the Faraut depth `46 * bits + 3`;
* its positive, uniformly bounded physical length is already proved;
* the BF4 same-object/rate-sharpness chain gives the honest macro rate `1/4`.

Section 1 packages those fields as the constructed `BF4AFCompletedRGGeometry`.
Section 2 isolates the genuinely operator-level residue: a completed physical
carrier and transfer, an isometric intertwining map to the proved strong
endpoint, vacuum-complement preservation, and the Cauchy--Schwarz link between
the same BF4 probe correlation and the norm of that blocked transfer.

From this smaller `CompletedBF4RGOperatorRealization`, Section 3 proves the
completed block norm gap and independently reconstructs the factor-four BF4
macro rate `1/4`.  Thus the earlier lossless `1/16` separator bridge is not
silently substituted for the available BF4 sharpness theorem.

No inhabitant of the BF4 producer or completed operator realization is
constructed here.  In particular, the genuine positive-physical BF4 local
gluing, same-object physical correlator, rate-sharpness probe, completed
weak-coupling carrier, and nonperturbative blocking map remain named analytic
obligations.  Nothing in this file constructs continuum Yang--Mills or proves
the Clay mass-gap theorem.
-/

import YMGap.Continuum.BF4AFPhysicalSpacingToZero
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedRGTransport

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedBF4RGReduction

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4FarautJointCarrierAFBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4FarautPhysicalSeparatorProducer
open YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.ContinuumGapModulus
open YMGap.Continuum.FixedDistancePhysicalSeparator
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepTransfer
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedVacuumComplement
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedRGTransport
open YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

variable {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}

/-! ## 1. Constructed AF/BF4 geometry -/

/-- The portion of completed weak-to-strong RG data already forced by an
existing BF4/Faraut producer on the proved AF trajectory.

This package has no carrier, transfer, or blocking-map fields.  It records only
the schedule, scale geometry, and the same-object factor-four rate that the
existing kernel-checked BF4/AF chain constructs. -/
structure BF4AFCompletedRGGeometry (P : PhysicalSeparator) : Type 1 where
  afTrajectory : AFTrajectoryCertificate
  physicalCoupling : Nat -> Q'
  physicalCoupling_eq_af : forall j,
    physicalCoupling j = afSchedule afTrajectory j
  physicalSpacing : PhysicalSpacing
  depth : Nat -> Nat
  depth_pos : forall j, 0 < depth j
  lengthCeiling : Q'
  lengthCeiling_pos : (0 : Q') < lengthCeiling
  physicalLengthBound : forall j,
    Q'.ofNat (depth j) * physicalSpacing.spacing j <= lengthCeiling
  spacingToZero : SpacingToZero physicalSpacing
  groupedQuarter : forall j,
    qpow (P.sep j) (depth j) <= quarter

namespace BF4AFCompletedRGGeometry

/-- The constructed geometry is genuinely weak-coupling. -/
theorem physicalCoupling_pos (G : BF4AFCompletedRGGeometry P) (j : Nat) :
    (0 : Q') < G.physicalCoupling j := by
  rw [G.physicalCoupling_eq_af j]
  exact afSchedule_pos G.afTrajectory j

/-- The exact proved AF modulus controls the geometry's coupling schedule. -/
theorem physicalCoupling_to_zero
    (G : BF4AFCompletedRGGeometry P)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (j : Nat) (hj : afScheduleCutoff G.afTrajectory epsilon <= j) :
    G.physicalCoupling j <= epsilon := by
  rw [G.physicalCoupling_eq_af j]
  exact afSchedule_to_zero G.afTrajectory epsilon hepsilon j hj

/-- The BF4-derived physical spacing tends to zero with explicit Type-level
modulus data. -/
theorem physicalSpacing_to_zero
    (G : BF4AFCompletedRGGeometry P)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (j : Nat) (hj : G.spacingToZero.modulus epsilon <= j) :
    G.physicalSpacing.spacing j <= epsilon :=
  G.spacingToZero.spacing_le epsilon hepsilon j hj

/-- The constructed BF4/AF geometry already gives the canonical
fixed-distance contraction at its honest factor-four macro rate `1/4`. -/
def fixedDistance (G : BF4AFCompletedRGGeometry P) :
    FixedDistanceContraction P G.physicalSpacing where
  depth := G.depth
  depth_pos := G.depth_pos
  macroRate := quarter
  macroRate_nonnegative := by decide
  macroRate_lt_one := by decide
  lengthCeiling := G.lengthCeiling
  lengthCeiling_pos := G.lengthCeiling_pos
  groupedBound := G.groupedQuarter
  physicalLengthBound := G.physicalLengthBound

end BF4AFCompletedRGGeometry

namespace BF4GeometryCompiler

/-- Compile all non-operator fields of the completed RG bridge from the
existing BF4/Faraut producer and its exact AF schedule identification. -/
def ofProducer
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF) :
    BF4AFCompletedRGGeometry P where
  afTrajectory := AF
  physicalCoupling := coupling
  physicalCoupling_eq_af := trajectory.coupling_eq
  physicalSpacing :=
    producer.toBF4QuarterPhysicalSeparatorProducer.physicalSpacing
  depth := fun scale => farautRequiredDepth (bits scale)
  depth_pos := by
    intro scale
    unfold farautRequiredDepth
    omega
  lengthCeiling := producer.lengthCeiling
  lengthCeiling_pos := producer.lengthCeiling_pos
  physicalLengthBound := producer.requiredDepth_physical_length_le
  spacingToZero :=
    producer.physicalSpacingToZeroOfAFTrajectory AF trajectory
  groupedQuarter := producer.groupedPhysicalSameObject

end BF4GeometryCompiler

/-! ## 2. The irreducible completed operator realization -/

/-- **The remaining completed operator-level weak-to-strong RG data.**

All coupling, spacing, depth, length, and BF4 rate data are parameters already
constructed by `BF4GeometryCompiler.ofProducer`.  The fields below are precisely the
operator realization still missing: a completed weak-coupling transfer, an
isometric intertwining block map to the concrete strong endpoint, preservation
of the vacuum complement, and realization of the selected BF4 probe.

`correlationSquare_le_blockedProbeNorm` is the constructive Cauchy--Schwarz
handoff for the *same* embedded BF4 probe.  It says that the squared connected
correlation at the selected macro depth is bounded by the squared norm of that
depth-fold transfer. -/
structure CompletedBF4RGOperatorRealization
    {endpointCoupling : Q'}
    (hendpoint : (0 : Q') <= endpointCoupling)
    (hle : endpointCoupling <= anchorCoupling)
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF) : Type 1 where
  PhysicalCompletion : Nat -> Type
  physicalInner :
    (scale : Nat) -> PhysicalCompletion scale -> PhysicalCompletion scale -> CReal.RC
  physicalTransfer :
    (scale : Nat) -> PhysicalCompletion scale -> PhysicalCompletion scale
  physicalVacuumOrthogonal :
    (scale : Nat) -> PhysicalCompletion scale -> Prop
  toStrong :
    (scale : Nat) -> PhysicalCompletion scale ->
      StrictJointCylinderOSCompletion hendpoint hle
  normIdentification : forall scale (vector : PhysicalCompletion scale),
    strictJointCylinderCompletedInner hendpoint hle
        (toStrong scale vector) (toStrong scale vector) =
      physicalInner scale vector vector
  transferIntertwining : forall scale (vector : PhysicalCompletion scale),
    toStrong scale
        (transferIterate (physicalTransfer scale)
          (farautRequiredDepth (bits scale)) vector) =
      strictJointCylinderCompletedTwoStepTransfer hendpoint hle
        (toStrong scale vector)
  mapsVacuumOrthogonal : forall scale (vector : PhysicalCompletion scale),
    physicalVacuumOrthogonal scale vector ->
      StrictJointCylinderCompletionVacuumOrthogonal
        hendpoint hle (toStrong scale vector)
  rateProbe : (scale : Nat) -> PhysicalCompletion scale
  rateProbe_orthogonal : forall scale,
    physicalVacuumOrthogonal scale (rateProbe scale)
  rateProbe_inner : forall scale,
    physicalInner scale (rateProbe scale) (rateProbe scale) =
      constantRC
        (centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          (producer.rateSharpness.probe scale)
          (producer.rateSharpness.probe scale))
  correlationSquare_le_blockedProbeNorm : forall scale,
    CReal.RCle
      (constantRC
        (P.corrIface.connectedCorr scale
            (producer.sameObject.embed scale
              (producer.rateSharpness.probe scale))
            (farautRequiredDepth (bits scale)) *
          P.corrIface.connectedCorr scale
            (producer.sameObject.embed scale
              (producer.rateSharpness.probe scale))
            (farautRequiredDepth (bits scale))))
      (physicalInner scale
        (transferIterate (physicalTransfer scale)
          (farautRequiredDepth (bits scale)) (rateProbe scale))
        (transferIterate (physicalTransfer scale)
          (farautRequiredDepth (bits scale)) (rateProbe scale)))

namespace CompletedBF4RGOperatorRealization

variable {endpointCoupling : Q'}
    {hendpoint : (0 : Q') <= endpointCoupling}
    {hle : endpointCoupling <= anchorCoupling}
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}

/-- Rational order introduces order between the corresponding completed-real
constants. -/
theorem constantRC_le_of_rat {left right : Q'} (h : left <= right) :
    CReal.RCle (constantRC left) (constantRC right) := by
  change CReal.leEv (CReal.ofQ' left) (CReal.ofQ' right)
  exact CReal.leEv_of_le (CReal.ofQ'_le_ofQ' h)

/-- Equivalent rationals define the same completed-real constant. -/
theorem constantRC_eq_of_eqv {left right : Q'} (h : left ≈ right) :
    constantRC left = constantRC right := by
  exact Quotient.sound (CReal.ofQ'_equiv_of_eqv h)

/-- Scaling a completed-real rational constant agrees with rational
multiplication. -/
theorem RCscale_constant (scalar value : Q') :
    CReal.RCscale scalar (constantRC value) =
      constantRC (scalar * value) := by
  show Quotient.mk CReal.crealSetoid
      (CReal.mul (CReal.ofQ' scalar) (CReal.ofQ' value)) =
    Quotient.mk CReal.crealSetoid (CReal.ofQ' (scalar * value))
  exact Quotient.sound
    (CReal.Equiv.symm
      (YMGap.Constructive.CRealAlg.ofQ'_mul scalar value))

/-- The selected macro-depth physical transfer. -/
def blockedTransfer
    (R : CompletedBF4RGOperatorRealization
      hendpoint hle producer AF trajectory)
    (scale : Nat) : R.PhysicalCompletion scale -> R.PhysicalCompletion scale :=
  transferIterate (R.physicalTransfer scale)
    (farautRequiredDepth (bits scale))

/-! ## 3. Operator and same-probe consequences -/

/-- Every physical RG block inherits the concrete completed strong-endpoint
operator-norm gap on the vacuum complement. -/
theorem blockedTransfer_norm_gap
    (R : CompletedBF4RGOperatorRealization
      hendpoint hle producer AF trajectory)
    (scale : Nat) (vector : R.PhysicalCompletion scale)
    (horthogonal : R.physicalVacuumOrthogonal scale vector) :
    CReal.RCle
      (R.physicalInner scale (R.blockedTransfer scale vector)
        (R.blockedTransfer scale vector))
      (CReal.RCscale
        (anchorDecoratedDoubledTimeRate * anchorDecoratedDoubledTimeRate)
        (R.physicalInner scale vector vector)) := by
  rw [blockedTransfer]
  rw [<- R.normIdentification scale
    (transferIterate (R.physicalTransfer scale)
      (farautRequiredDepth (bits scale)) vector)]
  rw [R.transferIntertwining scale vector]
  rw [<- R.normIdentification scale vector]
  exact anchorDecoratedDoubledTimeRate_completed_vacuum_operator_norm_gap
    hendpoint hle (R.toStrong scale vector)
      (R.mapsVacuumOrthogonal scale vector horthogonal)

/-- The realized BF4 rate probe has completed squared norm at most one; this
is derived from the existing finite weighted-inner normalization. -/
theorem rateProbe_norm_le_one
    (R : CompletedBF4RGOperatorRealization
      hendpoint hle producer AF trajectory)
    (scale : Nat) :
    CReal.RCle
      (R.physicalInner scale (R.rateProbe scale) (R.rateProbe scale))
      (constantRC 1) := by
  rw [R.rateProbe_inner scale]
  exact constantRC_le_of_rat
    (producer.rateSharpness.probe_inner_le_one scale)

/-- The factor-four BF4 sharpness pin, the same-probe Cauchy--Schwarz handoff,
and the concrete endpoint operator theorem imply the squared quarter bound. -/
theorem separatorPower_square_le_quarter_square
    (R : CompletedBF4RGOperatorRealization
      hendpoint hle producer AF trajectory)
    (scale : Nat) :
    qpow (P.sep scale) (farautRequiredDepth (bits scale)) *
        qpow (P.sep scale) (farautRequiredDepth (bits scale)) <=
      quarter * quarter := by
  let corr := P.corrIface.connectedCorr scale
    (producer.sameObject.embed scale
      (producer.rateSharpness.probe scale))
    (farautRequiredDepth (bits scale))
  have hdepth : producer.bf4.depth scale =
      farautRequiredDepth (bits scale) := producer.depth_matches scale
  have hsharp :
      qpow (P.sep scale) (farautRequiredDepth (bits scale)) <=
        Q'.ofNat 4 * corr := by
    dsimp [corr]
    rw [<- hdepth]
    exact producer.rateSharpness.separatorPower_le_four_correlation scale
  have hsep0 : (0 : Q') <=
      qpow (P.sep scale) (farautRequiredDepth (bits scale)) :=
    qpow_nonneg _ (Q'.le_of_lt (P.sep_pos scale)) _
  have hcorr0 : (0 : Q') <= corr :=
    P.corrIface.connectedCorr_nonneg _ _ _
  have hfourCorr0 : (0 : Q') <= Q'.ofNat 4 * corr :=
    Q'.mul_nonneg _ _ (by decide) hcorr0
  have hsharpSquare :
      qpow (P.sep scale) (farautRequiredDepth (bits scale)) *
          qpow (P.sep scale) (farautRequiredDepth (bits scale)) <=
        (Q'.ofNat 4 * corr) * (Q'.ofNat 4 * corr) :=
    Q'.mul_le_mul_of_nonneg hsharp hsharp hfourCorr0 hsep0
  have hfourSquare :
      (Q'.ofNat 4 * corr) * (Q'.ofNat 4 * corr) ≈
        Q'.ofNat 16 * (corr * corr) := by
    ring_qeqv
  have hseparatorToScaledCorrelation :
      CReal.RCle
        (constantRC
          (qpow (P.sep scale) (farautRequiredDepth (bits scale)) *
            qpow (P.sep scale) (farautRequiredDepth (bits scale))))
        (CReal.RCscale (Q'.ofNat 16) (constantRC (corr * corr))) := by
    have hconstant := constantRC_le_of_rat hsharpSquare
    rw [RCscale_constant]
    exact CReal.RCle_trans hconstant
      (CReal.leEv_of_equiv
        (show CReal.Equiv (CReal.ofQ' ((Q'.ofNat 4 * corr) *
            (Q'.ofNat 4 * corr)))
          (CReal.ofQ' (Q'.ofNat 16 * (corr * corr))) from
          CReal.ofQ'_equiv_of_eqv hfourSquare))
  have hcorrelationToBlocked := CReal.RCscale_mono
    (by decide : (0 : Q') <= Q'.ofNat 16)
    (R.correlationSquare_le_blockedProbeNorm scale)
  have hgap := R.blockedTransfer_norm_gap scale (R.rateProbe scale)
    (R.rateProbe_orthogonal scale)
  have hscaledGap := CReal.RCscale_mono
    (by decide : (0 : Q') <= Q'.ofNat 16) hgap
  have hprobe := CReal.RCscale_mono
    (Q'.mul_nonneg _ _ anchorDecoratedDoubledTimeRate_nonnegative
      anchorDecoratedDoubledTimeRate_nonnegative)
    (R.rateProbe_norm_le_one scale)
  rw [RCscale_constant_one] at hprobe
  have hscaledProbe := CReal.RCscale_mono
    (by decide : (0 : Q') <= Q'.ofNat 16) hprobe
  rw [CReal.RCscale_RCscale] at hscaledGap
  rw [CReal.RCscale_RCscale, RCscale_constant] at hscaledProbe
  have hquotient :
      CReal.RCle
        (constantRC
          (qpow (P.sep scale) (farautRequiredDepth (bits scale)) *
            qpow (P.sep scale) (farautRequiredDepth (bits scale))))
        (constantRC
          (Q'.ofNat 16 *
            (anchorDecoratedDoubledTimeRate *
              anchorDecoratedDoubledTimeRate))) :=
    CReal.RCle_trans hseparatorToScaledCorrelation
      (CReal.RCle_trans hcorrelationToBlocked
        (CReal.RCle_trans hscaledGap hscaledProbe))
  have hrational := constantRC_le_reflect hquotient
  have hcollapse :
      Q'.ofNat 16 *
          (anchorDecoratedDoubledTimeRate *
            anchorDecoratedDoubledTimeRate) ≈
        quarter * quarter := by
    let sixteenth : Q' := Q'.mkPos 1 16 (by decide)
    have hrSquare :
        anchorDecoratedDoubledTimeRate *
            anchorDecoratedDoubledTimeRate ≈
          sixteenth * sixteenth :=
      Q'.eqv_trans _
        (sixteenth * anchorDecoratedDoubledTimeRate) _
        (Q'.mul_eqv_congr_right _ _ _
          anchorDecoratedDoubledTimeRate_eqv_sixteenth)
        (Q'.mul_eqv_congr_left _ _ _
          anchorDecoratedDoubledTimeRate_eqv_sixteenth)
    exact Q'.eqv_trans _
      (Q'.ofNat 16 * (sixteenth * sixteenth)) _
      (Q'.mul_eqv_congr_left _ _ _ hrSquare)
      (by unfold sixteenth quarter; decide)
  exact Q'.le_trans' _ _ _ hrational (Q'.le_of_eqv hcollapse)

/-- Constructive square reflection recovers exactly the honest BF4 macro rate
`1/4`, not the lossless bridge's stronger `1/16`. -/
theorem separatorPower_le_quarter
    (R : CompletedBF4RGOperatorRealization
      hendpoint hle producer AF trajectory)
    (scale : Nat) :
    qpow (P.sep scale) (farautRequiredDepth (bits scale)) <= quarter := by
  have habs := Q'.abs_le_of_sq_le_sq
    (show (0 : Q') < quarter by unfold quarter; decide)
    (R.separatorPower_square_le_quarter_square scale)
  exact Q'.le_trans' _ _ _
    (Q'.le_abs_self
      (qpow (P.sep scale) (farautRequiredDepth (bits scale)))) habs

/-- The operator-derived rate and the already-constructed BF4/AF geometry
assemble into the canonical fixed-distance contraction. -/
def fixedDistance
    (R : CompletedBF4RGOperatorRealization
      hendpoint hle producer AF trajectory) :
    FixedDistanceContraction P
      (BF4GeometryCompiler.ofProducer producer AF trajectory).physicalSpacing where
  depth := fun scale => farautRequiredDepth (bits scale)
  depth_pos := (BF4GeometryCompiler.ofProducer producer AF trajectory).depth_pos
  macroRate := quarter
  macroRate_nonnegative := by decide
  macroRate_lt_one := by decide
  lengthCeiling := producer.lengthCeiling
  lengthCeiling_pos := producer.lengthCeiling_pos
  groupedBound := R.separatorPower_le_quarter
  physicalLengthBound := producer.requiredDepth_physical_length_le

/-- The completed operator realization therefore yields the same positive
dimensionful BF4 floor `(1 - 1/4) / L`. -/
def physicalFloorRate
    (R : CompletedBF4RGOperatorRealization
      hendpoint hle producer AF trajectory) : Q' :=
  R.fixedDistance.floorRate

/-- The operator-derived physical floor is definitionally the honest BF4
quarter margin divided by the constructed AF/Faraut length ceiling. -/
theorem physicalFloorRate_eq
    (R : CompletedBF4RGOperatorRealization
      hendpoint hle producer AF trajectory) :
    R.physicalFloorRate =
      Q'.divPos ((1 : Q') - quarter)
        producer.lengthCeiling producer.lengthCeiling_pos := rfl

theorem physicalFloorRate_pos
    (R : CompletedBF4RGOperatorRealization
      hendpoint hle producer AF trajectory) :
    (0 : Q') < R.physicalFloorRate :=
  R.fixedDistance.floorRate_pos

theorem physicalFloorRate_le_marginRate
    (R : CompletedBF4RGOperatorRealization
      hendpoint hle producer AF trajectory)
    (scale : Nat) :
    R.physicalFloorRate <=
      marginRate P
        (BF4GeometryCompiler.ofProducer producer AF trajectory).physicalSpacing scale :=
  R.fixedDistance.floorRate_le_marginRate scale

/-- The physical spacings used by the operator reduction retain the explicit
AF-derived modulus; it is not an extra operator-realization premise. -/
theorem physicalSpacing_to_zero
    (_R : CompletedBF4RGOperatorRealization
      hendpoint hle producer AF trajectory)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      (BF4GeometryCompiler.ofProducer producer AF trajectory).spacingToZero.modulus
          epsilon <= scale) :
    (BF4GeometryCompiler.ofProducer producer AF trajectory).physicalSpacing.spacing
        scale <= epsilon :=
  (BF4GeometryCompiler.ofProducer producer AF trajectory).physicalSpacing_to_zero
    epsilon hepsilon scale hscale

/-- Headline finite-scale conclusion of the reduced completed route: one
strictly positive rational bounds the physical margin rate at every point of
the explicit vanishing-spacing AF trajectory. -/
theorem spacingUniformPhysicalMarginFloor
    (R : CompletedBF4RGOperatorRealization
      hendpoint hle producer AF trajectory) :
    (0 : Q') < R.physicalFloorRate /\
      forall scale,
        R.physicalFloorRate <=
          marginRate P
            (BF4GeometryCompiler.ofProducer producer AF trajectory).physicalSpacing
            scale :=
  ⟨R.physicalFloorRate_pos, R.physicalFloorRate_le_marginRate⟩

end CompletedBF4RGOperatorRealization

#print axioms BF4AFCompletedRGGeometry.physicalCoupling_pos
#print axioms BF4AFCompletedRGGeometry.physicalCoupling_to_zero
#print axioms BF4AFCompletedRGGeometry.physicalSpacing_to_zero
#print axioms BF4AFCompletedRGGeometry.fixedDistance
#print axioms BF4GeometryCompiler.ofProducer
#print axioms CompletedBF4RGOperatorRealization.constantRC_le_of_rat
#print axioms CompletedBF4RGOperatorRealization.constantRC_eq_of_eqv
#print axioms CompletedBF4RGOperatorRealization.RCscale_constant
#print axioms CompletedBF4RGOperatorRealization.blockedTransfer_norm_gap
#print axioms CompletedBF4RGOperatorRealization.rateProbe_norm_le_one
#print axioms CompletedBF4RGOperatorRealization.separatorPower_square_le_quarter_square
#print axioms CompletedBF4RGOperatorRealization.separatorPower_le_quarter
#print axioms CompletedBF4RGOperatorRealization.fixedDistance
#print axioms CompletedBF4RGOperatorRealization.physicalFloorRate_eq
#print axioms CompletedBF4RGOperatorRealization.physicalFloorRate_pos
#print axioms CompletedBF4RGOperatorRealization.physicalFloorRate_le_marginRate
#print axioms CompletedBF4RGOperatorRealization.physicalSpacing_to_zero
#print axioms CompletedBF4RGOperatorRealization.spacingUniformPhysicalMarginFloor

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedBF4RGReduction
