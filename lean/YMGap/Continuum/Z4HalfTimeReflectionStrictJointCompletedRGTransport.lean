/-
# Completed weak-to-strong RG transport of the concrete operator gap

The strong-coupling campaign now proves an intrinsic completed estimate

  ||S x||^2 <= (1/16)^2 ||x||^2

for the concrete two-step transfer `S = T^2` on the completed vacuum
complement.  A continuum consequence cannot identify `1/16` with a
one-fine-lattice-step separator: at spacing `a_j -> 0` that would manufacture
an infinite physical mass.  The honest next object is a blocking map whose
depth grows while its physical length stays bounded.

This file isolates that exact object.  A `CompletedWeakToStrongRGBridge`
contains, at every fine scale,

* the physical completed carrier, inner form, and one-step transfer;
* a positive block depth and an isometric map into the proved strong-coupling
  completion;
* exact intertwining of the depth-fold transfer with the concrete endpoint
  `S` and preservation of the vacuum complement;
* a same-operator rate-sharpness probe tying the physical separator power to
  the norm of that very blocked transfer;
* a uniform physical-length ceiling and a Type-level modulus `a_j -> 0`.

The endpoint theorem then gives, without any further analytic assumption,

  ||S_j^(depth j) x||^2 <= (1/16)^2 ||x||^2,
  (sep_phys j)^(depth j) <= 1/16.

The second inequality constructs the existing canonical
`FixedDistanceContraction`.  Consequently `(1-1/16)/L` is a strictly positive
uniform lower bound for `(1-sep_phys j)/a_j`, and—on a supplied logarithm
window—for the exact physical rate `-log(sep_phys j)/a_j`.

No bridge inhabitant is constructed here.  Its isometric physical blocking,
same-operator sharpness, and weak-coupling carrier identification are precisely
the open nonperturbative RG input.  The theorem therefore contracts the new
completed endpoint into the canonical physical-floor pipeline without claiming
the continuum Yang--Mills theory or the Clay result.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap
import YMGap.Continuum.FixedDistancePhysicalSeparator
import YMGap.Continuum.PhysicalSeparatorLinearTail
import YMGap.Continuum.RCDistBridge
import YMGap.Continuum.ContinuumGapModulus

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedRGTransport

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.FixedDistancePhysicalSeparator
open YMGap.Continuum.ContinuumGapModulus
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.RGTransport
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepMoments
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepTransfer
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedVacuumComplement
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap
open YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Generic transfer iteration and constant completed reals -/

/-- Strict iteration of a carrier endomorphism. -/
def transferIterate {Carrier : Type} (transfer : Carrier -> Carrier) :
    Nat -> Carrier -> Carrier
  | 0, vector => vector
  | n + 1, vector => transfer (transferIterate transfer n vector)

/-- Addition of iteration counts is composition of strict iterates. -/
theorem transferIterate_add {Carrier : Type} (transfer : Carrier -> Carrier) :
    forall first second (vector : Carrier),
      transferIterate transfer (first + second) vector =
        transferIterate transfer first
          (transferIterate transfer second vector)
  | 0, second, vector => by
      simp only [Nat.zero_add, transferIterate]
  | first + 1, second, vector => by
      rw [Nat.succ_add, transferIterate, transferIterate,
        transferIterate_add transfer first second vector]

/-- A rational constant embedded in the completed-real quotient. -/
def constantRC (value : Q') : CReal.RC :=
  Quotient.mk CReal.crealSetoid (CReal.ofQ' value)

/-- Scaling the constant one in the completed-real quotient gives the
corresponding rational constant. -/
theorem RCscale_constant_one (scalar : Q') :
    CReal.RCscale scalar (constantRC 1) = constantRC scalar := by
  show Quotient.mk CReal.crealSetoid
      (CReal.mul (CReal.ofQ' scalar) (CReal.ofQ' 1)) =
    Quotient.mk CReal.crealSetoid (CReal.ofQ' scalar)
  exact Quotient.sound
    (YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
      (fun _ => Q'.mul_one_eqv scalar))

/-- Order between rational constants reflects from the completed-real quotient
back to exact rational order. -/
theorem constantRC_le_reflect {left right : Q'}
    (h : CReal.RCle (constantRC left) (constantRC right)) : left <= right := by
  change CReal.RCle
    (Quotient.mk CReal.crealSetoid (CReal.ofQ' left))
    (Quotient.mk CReal.crealSetoid (CReal.ofQ' right)) at h
  rw [CReal.RCle_mk] at h
  refine Q'.le_of_forall_pos_add ?_
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  exact hN N (Nat.le_refl N)

/-! ## 2. The explicit weak-to-strong completed blocking bridge -/

/-- **The open physical RG bridge to the proved completed endpoint.**

At scale `j`, `physicalTransfer (physicalCoupling j)` is one fine two-step
transfer.  Its strict
`depth j` iterate is mapped isometrically to the concrete strong-coupling
two-step transfer.  `separatorProbeLower` is the same-operator sharpness pin:
the square of the physical separator power is bounded by the squared norm of
the blocked transfer acting on one unit probe.  This prevents an unrelated or
artificially loose separator from being substituted into the physical floor.

The structure is deliberately uninhabited for 4D Yang--Mills. -/
structure CompletedWeakToStrongRGBridge
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (P : PhysicalSeparator) (A : PhysicalSpacing) : Type 1 where
  /-- The proved two-loop asymptotic-freedom trajectory indexing the fine
  physical theories. -/
  afTrajectory : AFTrajectoryCertificate
  /-- The physical weak-coupling schedule. -/
  physicalCoupling : Nat -> Q'
  /-- Exact identification with the shifted proved AF schedule. -/
  physicalCoupling_eq_af : forall j,
    physicalCoupling j = afSchedule afTrajectory j
  /-- The completed physical state carrier at a supplied coupling.  Scale `j`
  uses `PhysicalCompletion (physicalCoupling j)`. -/
  PhysicalCompletion : Q' -> Type
  /-- The completed physical inner form at each coupling. -/
  physicalInner :
    (g : Q') -> PhysicalCompletion g -> PhysicalCompletion g -> CReal.RC
  /-- One fine physical two-step transfer at each coupling. -/
  physicalTransfer : (g : Q') -> PhysicalCompletion g -> PhysicalCompletion g
  /-- The physical completed vacuum-complement predicate. -/
  physicalVacuumOrthogonal :
    (g : Q') -> PhysicalCompletion g -> Prop
  /-- Number of fine two-step transfers in one RG block. -/
  depth : Nat -> Nat
  /-- Every RG block contains at least one fine transfer. -/
  depth_pos : forall j : Nat, 0 < depth j
  /-- The completed blocking map into the proved strong-coupling endpoint. -/
  toStrong :
    (j : Nat) -> PhysicalCompletion (physicalCoupling j) ->
      StrictJointCylinderOSCompletion hcoupling hle
  /-- Blocking preserves squared norm exactly. -/
  normIdentification : forall j
      (vector : PhysicalCompletion (physicalCoupling j)),
    strictJointCylinderCompletedInner hcoupling hle
        (toStrong j vector) (toStrong j vector) =
      physicalInner (physicalCoupling j) vector vector
  /-- The depth-fold fine transfer intertwines with the concrete endpoint
  two-step transfer. -/
  transferIntertwining : forall j
      (vector : PhysicalCompletion (physicalCoupling j)),
    toStrong j
        (transferIterate (physicalTransfer (physicalCoupling j))
          (depth j) vector) =
      strictJointCylinderCompletedTwoStepTransfer hcoupling hle
        (toStrong j vector)
  /-- Blocking maps the physical vacuum complement into the proved endpoint
  vacuum complement. -/
  mapsVacuumOrthogonal : forall j
      (vector : PhysicalCompletion (physicalCoupling j)),
    physicalVacuumOrthogonal (physicalCoupling j) vector ->
      StrictJointCylinderCompletionVacuumOrthogonal
        hcoupling hle (toStrong j vector)
  /-- Same-operator rate-sharpness probe at every scale. -/
  separatorProbe : (j : Nat) -> PhysicalCompletion (physicalCoupling j)
  /-- The probe is vacuum-orthogonal. -/
  separatorProbe_orthogonal : forall j,
    physicalVacuumOrthogonal (physicalCoupling j) (separatorProbe j)
  /-- The probe has squared norm at most one. -/
  separatorProbe_norm_le_one : forall j,
    CReal.RCle
      (physicalInner (physicalCoupling j)
        (separatorProbe j) (separatorProbe j))
      (constantRC 1)
  /-- The selected physical separator is witnessed by this same blocked
  operator: `(sep_j^depth_j)^2 <= ||S_j^depth_j probe_j||^2`. -/
  separatorProbeLower : forall j,
    CReal.RCle
      (constantRC
        (qpow (P.sep j) (depth j) * qpow (P.sep j) (depth j)))
      (physicalInner (physicalCoupling j)
        (transferIterate (physicalTransfer (physicalCoupling j))
          (depth j) (separatorProbe j))
        (transferIterate (physicalTransfer (physicalCoupling j))
          (depth j) (separatorProbe j)))
  /-- Uniform upper bound on the physical length of one RG block. -/
  lengthCeiling : Q'
  /-- The physical-length ceiling is positive. -/
  lengthCeiling_pos : (0 : Q') < lengthCeiling
  /-- One block occupies at most the fixed physical length.  `physicalTransfer`
  is already the project's two-step physical transfer, so the spacing unit in
  this bridge is the matching two-step unit. -/
  physicalLengthBound : forall j,
    Q'.ofNat (depth j) * A.spacing j <= lengthCeiling
  /-- The fine spacings genuinely approach zero with an explicit modulus. -/
  spacingToZero : SpacingToZero A

namespace CompletedWeakToStrongRGBridge

variable {coupling : Q'} {hcoupling : (0 : Q') <= coupling}
    {hle : coupling <= anchorCoupling}
    {P : PhysicalSeparator} {A : PhysicalSpacing}

/-- The bridge's coupling at every fine scale is strictly positive. -/
theorem physicalCoupling_pos
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A) (j : Nat) :
    (0 : Q') < B.physicalCoupling j := by
  rw [B.physicalCoupling_eq_af j]
  exact afSchedule_pos B.afTrajectory j

/-- The bridge is genuinely weak-coupling: its exact AF-indexed coupling tends
to zero with the proved explicit cutoff. -/
theorem physicalCoupling_to_zero
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (j : Nat) (hj : afScheduleCutoff B.afTrajectory epsilon <= j) :
    B.physicalCoupling j <= epsilon := by
  rw [B.physicalCoupling_eq_af j]
  exact afSchedule_to_zero B.afTrajectory epsilon hepsilon j hj

/-- The bridge's physical lattice spacing tends to zero with its supplied
Type-level modulus. -/
theorem physicalSpacing_to_zero
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (j : Nat) (hj : B.spacingToZero.modulus epsilon <= j) :
    A.spacing j <= epsilon :=
  B.spacingToZero.spacing_le epsilon hepsilon j hj

/-- The depth-fold physical transfer constituting one RG block. -/
def blockedTransfer
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A)
    (j : Nat) : B.PhysicalCompletion (B.physicalCoupling j) ->
      B.PhysicalCompletion (B.physicalCoupling j) :=
  transferIterate (B.physicalTransfer (B.physicalCoupling j)) (B.depth j)

/-- Iteration by a number of whole RG blocks. -/
def blockedPower
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A)
    (j : Nat) : Nat ->
    B.PhysicalCompletion (B.physicalCoupling j) ->
      B.PhysicalCompletion (B.physicalCoupling j)
  | 0, vector => vector
  | n + 1, vector => B.blockedTransfer j (blockedPower B j n vector)

/-- Repeating `n` whole blocks is literally the fine physical transfer iterated
`n * depth j` times. -/
theorem blockedPower_eq_transferIterate_mul
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A)
    (j : Nat) : forall n
      (vector : B.PhysicalCompletion (B.physicalCoupling j)),
    B.blockedPower j n vector =
      transferIterate (B.physicalTransfer (B.physicalCoupling j))
        (n * B.depth j) vector
  | 0, _ => by
      simp only [blockedPower, Nat.zero_mul, transferIterate]
  | n + 1, vector => by
      rw [blockedPower, blockedTransfer,
        blockedPower_eq_transferIterate_mul B j n vector]
      rw [<- transferIterate_add]
      congr 2
      rw [Nat.succ_mul, Nat.add_comm]

/-! ## 3. Transport of the completed operator gap -/

/-- One fine RG block inherits the concrete endpoint operator-norm gap. -/
theorem blockedTransfer_norm_gap
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A)
    (j : Nat) (vector : B.PhysicalCompletion (B.physicalCoupling j))
    (horthogonal :
      B.physicalVacuumOrthogonal (B.physicalCoupling j) vector) :
    CReal.RCle
      (B.physicalInner (B.physicalCoupling j) (B.blockedTransfer j vector)
        (B.blockedTransfer j vector))
      (CReal.RCscale
        (anchorDecoratedDoubledTimeRate * anchorDecoratedDoubledTimeRate)
        (B.physicalInner (B.physicalCoupling j) vector vector)) := by
  rw [blockedTransfer]
  rw [<- B.normIdentification j
    (transferIterate (B.physicalTransfer (B.physicalCoupling j))
      (B.depth j) vector)]
  rw [B.transferIntertwining j vector]
  rw [<- B.normIdentification j vector]
  exact anchorDecoratedDoubledTimeRate_completed_vacuum_operator_norm_gap
    hcoupling hle (B.toStrong j vector)
      (B.mapsVacuumOrthogonal j vector horthogonal)

/-- Blocking intertwines every whole-block power with the corresponding power
of the concrete strong-coupling transfer. -/
theorem blockedPower_intertwining
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A)
    (j : Nat) : forall n
      (vector : B.PhysicalCompletion (B.physicalCoupling j)),
    B.toStrong j (B.blockedPower j n vector) =
      strictJointCylinderCompletedTwoStepPower hcoupling hle n
        (B.toStrong j vector)
  | 0, vector => by
      rw [blockedPower,
        strictJointCylinderCompletedTwoStepPower_zero]
  | n + 1, vector => by
      rw [blockedPower, blockedTransfer, B.transferIntertwining]
      rw [blockedPower_intertwining B j n vector]
      exact (strictJointCylinderCompletedTwoStepPower_succ
        hcoupling hle n (B.toStrong j vector)).symm

/-- The geometric endpoint decay transports through every whole-block power. -/
theorem blockedPower_norm_decay
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A)
    (j n : Nat) (vector : B.PhysicalCompletion (B.physicalCoupling j))
    (horthogonal :
      B.physicalVacuumOrthogonal (B.physicalCoupling j) vector) :
    CReal.RCle
      (B.physicalInner (B.physicalCoupling j) (B.blockedPower j n vector)
        (B.blockedPower j n vector))
      (CReal.RCscale
        ((anchorDecoratedDoubledTimeRate *
          anchorDecoratedDoubledTimeRate) ^ n)
        (B.physicalInner (B.physicalCoupling j) vector vector)) := by
  rw [<- B.normIdentification j (B.blockedPower j n vector)]
  rw [B.blockedPower_intertwining j n vector]
  rw [<- B.normIdentification j vector]
  exact anchorDecoratedDoubledTimeRate_completed_power_norm_decay
    hcoupling hle n (B.toStrong j vector)
      (B.mapsVacuumOrthogonal j vector horthogonal)

/-! ## 4. Same-operator separator bound -/

/-- The squared physical separator power is bounded by the squared endpoint
rate.  This is the exact contraction of sharpness, isometric intertwining, and
the concrete completed operator theorem. -/
theorem separatorPower_square_le_anchorRate_square
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A)
    (j : Nat) :
    qpow (P.sep j) (B.depth j) * qpow (P.sep j) (B.depth j) <=
      anchorDecoratedDoubledTimeRate * anchorDecoratedDoubledTimeRate := by
  have hgap := B.blockedTransfer_norm_gap j (B.separatorProbe j)
    (B.separatorProbe_orthogonal j)
  have hscaled := CReal.RCscale_mono
    (Q'.mul_nonneg _ _ anchorDecoratedDoubledTimeRate_nonnegative
      anchorDecoratedDoubledTimeRate_nonnegative)
    (B.separatorProbe_norm_le_one j)
  rw [RCscale_constant_one] at hscaled
  exact constantRC_le_reflect
    (CReal.RCle_trans (B.separatorProbeLower j)
      (CReal.RCle_trans hgap hscaled))

/-- The selected physical separator power is at most the concrete endpoint
rate `1/16`.  Square reflection is constructive and uses the strict positivity
of the endpoint rate. -/
theorem separatorPower_le_anchorRate
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A)
    (j : Nat) :
    qpow (P.sep j) (B.depth j) <= anchorDecoratedDoubledTimeRate := by
  have habs := Q'.abs_le_of_sq_le_sq anchorDecoratedDoubledTimeRate_pos
    (B.separatorPower_square_le_anchorRate_square j)
  exact Q'.le_trans' _ _ _
    (Q'.le_abs_self (qpow (P.sep j) (B.depth j))) habs

/-! ## 5. Canonical fixed-distance and physical-floor consequences -/

/-- Forgetting the completed carrier data yields the project's canonical
same-separator fixed-distance contraction, now with macro rate `1/16`. -/
def fixedDistance
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A) :
    FixedDistanceContraction P A where
  depth := B.depth
  depth_pos := B.depth_pos
  macroRate := anchorDecoratedDoubledTimeRate
  macroRate_nonnegative := anchorDecoratedDoubledTimeRate_nonnegative
  macroRate_lt_one := anchorDecoratedDoubledTimeRate_lt_one
  lengthCeiling := B.lengthCeiling
  lengthCeiling_pos := B.lengthCeiling_pos
  groupedBound := B.separatorPower_le_anchorRate
  physicalLengthBound := B.physicalLengthBound

/-- The uniform rational physical margin-rate floor extracted from the bridge. -/
def physicalFloorRate
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A) : Q' :=
  B.fixedDistance.floorRate

/-- The physical floor is definitionally the macro margin divided by the
uniform physical-length ceiling. -/
theorem physicalFloorRate_eq
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A) :
    B.physicalFloorRate =
      Q'.divPos ((1 : Q') - anchorDecoratedDoubledTimeRate)
        B.lengthCeiling B.lengthCeiling_pos := rfl

/-- The transported physical floor is strictly positive. -/
theorem physicalFloorRate_pos
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A) :
    (0 : Q') < B.physicalFloorRate :=
  B.fixedDistance.floorRate_pos

/-- The same positive rational lies below the physical margin rate at every
scale of the supplied spacing-to-zero trajectory. -/
theorem physicalFloorRate_le_marginRate
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A) (j : Nat) :
    B.physicalFloorRate <= marginRate P A j :=
  B.fixedDistance.floorRate_le_marginRate j

/-- Headline spacing-uniform lower conclusion: one strictly positive rational
is below the physical margin rate at every scale of the vanishing-spacing
trajectory. -/
theorem spacingUniformPhysicalMarginFloor
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A) :
    (0 : Q') < B.physicalFloorRate /\
      forall j, B.physicalFloorRate <= marginRate P A j :=
  ⟨B.physicalFloorRate_pos, B.physicalFloorRate_le_marginRate⟩

/-- On a supplied direct logarithm window, the bridge gives a uniform positive
floor for the exact rate `-log(sep_phys j)/a_j`. -/
def exactLogRateFloor
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A)
    (W : PhysicalLogWindow P) :
    UniformPhysicalLogRateFloor
      (exactRateFamilyOfPhysicalData P A.spacing A.spacing_pos W) :=
  B.fixedDistance.exactLogRateFloor W

/-- The exact-log floor constructed from the bridge is strictly positive. -/
theorem exactLogRateFloor_pos
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A)
    (W : PhysicalLogWindow P) :
    (0 : Q') < (B.exactLogRateFloor W).floor :=
  (B.exactLogRateFloor W).floor_pos

/-- The independent upper-rate datum still required for a finite two-sided
physical mass band.  It is not implied by a strict lower contraction. -/
abbrev MarginRateCeiling
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A) : Type :=
  FixedDistanceContraction.MarginRateCeiling B.fixedDistance

/-- Given the independent finiteness ceiling, package the two-sided rational
physical-gap band. -/
def physicalGapFloor
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A)
    (U : B.MarginRateCeiling) :
    PhysicalGapFloor P A.spacing A.spacing_pos :=
  B.fixedDistance.physicalGapFloor U

/-- Given a direct log window and the independent finiteness ceiling, package
the complete exact physical-separator certificate. -/
def exactPhysicalSeparatorCertificate
    (B : CompletedWeakToStrongRGBridge hcoupling hle P A)
    (W : PhysicalLogWindow P) (U : B.MarginRateCeiling) :
    PhysicalSeparatorLogRate.ExactPhysicalSeparatorCertificate :=
  B.fixedDistance.exactPhysicalSeparatorCertificate W U

end CompletedWeakToStrongRGBridge

#print axioms transferIterate
#print axioms transferIterate_add
#print axioms RCscale_constant_one
#print axioms constantRC_le_reflect
#print axioms CompletedWeakToStrongRGBridge.physicalCoupling_pos
#print axioms CompletedWeakToStrongRGBridge.physicalCoupling_to_zero
#print axioms CompletedWeakToStrongRGBridge.physicalSpacing_to_zero
#print axioms CompletedWeakToStrongRGBridge.blockedTransfer_norm_gap
#print axioms CompletedWeakToStrongRGBridge.blockedPower_eq_transferIterate_mul
#print axioms CompletedWeakToStrongRGBridge.blockedPower_intertwining
#print axioms CompletedWeakToStrongRGBridge.blockedPower_norm_decay
#print axioms CompletedWeakToStrongRGBridge.separatorPower_square_le_anchorRate_square
#print axioms CompletedWeakToStrongRGBridge.separatorPower_le_anchorRate
#print axioms CompletedWeakToStrongRGBridge.fixedDistance
#print axioms CompletedWeakToStrongRGBridge.physicalFloorRate_eq
#print axioms CompletedWeakToStrongRGBridge.physicalFloorRate_pos
#print axioms CompletedWeakToStrongRGBridge.physicalFloorRate_le_marginRate
#print axioms CompletedWeakToStrongRGBridge.spacingUniformPhysicalMarginFloor
#print axioms CompletedWeakToStrongRGBridge.exactLogRateFloor
#print axioms CompletedWeakToStrongRGBridge.exactLogRateFloor_pos
#print axioms CompletedWeakToStrongRGBridge.physicalGapFloor
#print axioms CompletedWeakToStrongRGBridge.exactPhysicalSeparatorCertificate

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedRGTransport
