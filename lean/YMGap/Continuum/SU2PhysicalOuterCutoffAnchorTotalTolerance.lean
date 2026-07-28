/-
# Total-tolerance rescaling for the fixed-anchor physical SU(2) outer tail

`SU2PhysicalOuterCutoffAnchorSchedule` makes the one-coordinate omitted-spin
mass at precision `r` at most `dyad r`.  Tensoring over a fixed finite face
carrier introduces a finite coefficient depending on the number of faces and
the fixed anchor one-coordinate ceiling.  This module extracts that
coefficient exactly and then pays it constructively.

For fixed dimension `d`,

  tensorEnvelope(r,d) ≈ dyad r * tensorCoefficient(d).

Given a positive rational tolerance `ε`, rescale it by

  ε * invSucc(tensorCoefficient(d).num.toNat).

`HalfPow.pow_half_le` supplies an executable dyadic precision whose half-power
is below the rescaled tolerance, while
`ExpNeg.mul_le_of_mul_invSucc_toNat` pays the coefficient.  The resulting
Type-level schedule bounds the complete tensor envelope, and hence the
fixed-box physical cutoff increment, by `ε`.

The construction is fixed at `anchorCoupling = 1/400` and at a fixed finite
tensor dimension or finite box.  It is not uniform in volume, does not vary
the nome or spacing, and constructs no continuum or infinite-volume limit.

## Axiom gate

Constructive `Nat`/`Q'` recursion only.  No `Classical.*`, `Real`,
`native_decide`, `sorry`, custom axiom, choice, functional extensionality, or
noncomputable declaration.
-/

import YMGap.Continuum.SU2PhysicalOuterCutoffAnchorSchedule

namespace YMGap.Continuum.SU2PhysicalOuterCutoffAnchorTotalTolerance

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.SU2PhysicalOuterCutoffAnchorSchedule
open YMGap.Continuum.SU2PhysicalOuterCutoffTensorTail
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact fixed-dimensional coefficient -/

/-- The fixed-anchor one-coordinate ceiling used by every tensor dimension. -/
def anchorPhysicalOneFaceCeiling : Q' :=
  su2PhysicalHeatCeiling
    anchorCoupling anchorPhysicalBaseCutoff

theorem anchorPhysicalOneFaceCeiling_nonnegative :
    (0 : Q') ≤ anchorPhysicalOneFaceCeiling := by
  unfold anchorPhysicalOneFaceCeiling
  exact su2PhysicalHeatCeiling_nonnegative
    (w := anchorCoupling) (by decide)
    anchorPhysicalBaseCutoff

/-- Fixed-dimensional coefficient multiplying the scheduled one-coordinate
dyadic tail. -/
def anchorPhysicalTensorTailCoefficient : Nat → Q'
  | 0 => 0
  | dimension + 1 =>
      anchorPhysicalOneFaceCeiling ^ dimension +
        anchorPhysicalOneFaceCeiling *
          anchorPhysicalTensorTailCoefficient dimension

theorem anchorPhysicalTensorTailCoefficient_nonnegative :
    ∀ dimension,
      (0 : Q') ≤
        anchorPhysicalTensorTailCoefficient dimension
  | 0 => Q'.le_refl' 0
  | dimension + 1 =>
      Q'.zero_le_add _ _
        (Q'.pow_nonneg _
          anchorPhysicalOneFaceCeiling_nonnegative
          dimension)
        (Q'.mul_nonneg _ _
          anchorPhysicalOneFaceCeiling_nonnegative
          (anchorPhysicalTensorTailCoefficient_nonnegative
            dimension))

/-- The physical tensor envelope is exactly the scheduled dyadic tail times
one fixed-dimensional nonnegative coefficient.  The retained cutoff `M` does
not enter the numerical coefficient; it enters through the separately proved
head schedule that certifies the one-coordinate dyadic tail. -/
theorem anchorPhysicalTensorTailEnvelope_eqv_coefficient
    (M precision : Nat) :
    ∀ dimension,
      su2PhysicalTensorTailEnvelope
          anchorCoupling
          anchorPhysicalBaseCutoff
          M precision dimension ≈
        dyad precision *
          anchorPhysicalTensorTailCoefficient dimension
  | 0 =>
      Q'.eqv_symm
        (Q'.mul_zero_eqv (dyad precision))
  | dimension + 1 => by
      have ih :=
        anchorPhysicalTensorTailEnvelope_eqv_coefficient
          M precision dimension
      change
        dyad precision *
              anchorPhysicalOneFaceCeiling ^ dimension +
            anchorPhysicalOneFaceCeiling *
              su2PhysicalTensorTailEnvelope
                anchorCoupling
                anchorPhysicalBaseCutoff
                M precision dimension ≈
          dyad precision *
            (anchorPhysicalOneFaceCeiling ^ dimension +
              anchorPhysicalOneFaceCeiling *
                anchorPhysicalTensorTailCoefficient dimension)
      have hsecond :
          anchorPhysicalOneFaceCeiling *
              su2PhysicalTensorTailEnvelope
                anchorCoupling
                anchorPhysicalBaseCutoff
                M precision dimension ≈
            dyad precision *
              (anchorPhysicalOneFaceCeiling *
                anchorPhysicalTensorTailCoefficient dimension) := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left
            anchorPhysicalOneFaceCeiling _ _ ih) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv
              anchorPhysicalOneFaceCeiling
              (dyad precision)
              (anchorPhysicalTensorTailCoefficient dimension))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            (anchorPhysicalOneFaceCeiling * dyad precision)
            (dyad precision * anchorPhysicalOneFaceCeiling)
            (anchorPhysicalTensorTailCoefficient dimension)
            (Q'.mul_comm_eqv
              anchorPhysicalOneFaceCeiling
              (dyad precision))) ?_
        exact Q'.mul_assoc_eqv
          (dyad precision)
          anchorPhysicalOneFaceCeiling
          (anchorPhysicalTensorTailCoefficient dimension)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          (dyad precision *
            anchorPhysicalOneFaceCeiling ^ dimension)
          _ _ hsecond) ?_
      exact Q'.eqv_symm
        (Q'.mul_add_eqv
          (dyad precision)
          (anchorPhysicalOneFaceCeiling ^ dimension)
          (anchorPhysicalOneFaceCeiling *
            anchorPhysicalTensorTailCoefficient dimension))

/-! ## 2. Arbitrary positive rational tolerance -/

/-- Tolerance after paying the fixed-dimensional tensor coefficient. -/
def anchorPhysicalTensorScaledTolerance
    (dimension : Nat) (ε : Q') : Q' :=
  ε * Q'.invSucc
    (anchorPhysicalTensorTailCoefficient dimension).num.toNat

theorem anchorPhysicalTensorScaledTolerance_pos
    (dimension : Nat) {ε : Q'}
    (hε : (0 : Q') < ε) :
    (0 : Q') <
      anchorPhysicalTensorScaledTolerance dimension ε := by
  unfold anchorPhysicalTensorScaledTolerance
  exact Q'.mul_pos hε (Q'.invSucc_pos _)

/-- Executable dyadic precision paying the complete tensor coefficient. -/
def anchorPhysicalTensorTolerancePrecision
    (dimension : Nat) (ε : Q') : Nat :=
  (anchorPhysicalTensorScaledTolerance dimension ε).den

/-- Executable retained-spin cutoff paired with the total-tolerance
precision. -/
def anchorPhysicalTensorToleranceRetainedCutoff
    (dimension : Nat) (ε : Q') : Nat :=
  anchorPhysicalRetainedCutoff
    (anchorPhysicalTensorTolerancePrecision dimension ε)

/-- The full fixed-dimensional physical tensor envelope is below every
requested positive rational tolerance at the executable precision and
retained cutoff. -/
theorem anchorPhysicalTensorTailEnvelope_le_tolerance
    (dimension : Nat) {ε : Q'}
    (hε : (0 : Q') < ε) :
    su2PhysicalTensorTailEnvelope
        anchorCoupling
        anchorPhysicalBaseCutoff
        (anchorPhysicalTensorToleranceRetainedCutoff
          dimension ε)
        (anchorPhysicalTensorTolerancePrecision
          dimension ε)
        dimension ≤
      ε := by
  let coefficient :=
    anchorPhysicalTensorTailCoefficient dimension
  let tolerance :=
    anchorPhysicalTensorScaledTolerance dimension ε
  let precision :=
    anchorPhysicalTensorTolerancePrecision dimension ε
  have hcoefficient : (0 : Q') ≤ coefficient :=
    anchorPhysicalTensorTailCoefficient_nonnegative dimension
  have htolerance : (0 : Q') < tolerance :=
    anchorPhysicalTensorScaledTolerance_pos dimension hε
  have hdyad :
      dyad precision ≤ tolerance := by
    change HalfPow.half ^ tolerance.den ≤ tolerance
    exact HalfPow.pow_half_le tolerance htolerance
  have hfactor :=
    anchorPhysicalTensorTailEnvelope_eqv_coefficient
      (anchorPhysicalTensorToleranceRetainedCutoff
        dimension ε)
      precision dimension
  have hscaled :
      dyad precision * coefficient ≤
        tolerance * coefficient :=
    Q'.mul_le_mul_of_nonneg_right
      _ _ _ hdyad hcoefficient
  have hpay :
      tolerance * coefficient ≤ ε := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv tolerance coefficient)) ?_
    dsimp only [coefficient, tolerance]
    exact
      YMGap.Constructive.ExpNeg.mul_le_of_mul_invSucc_toNat
        (anchorPhysicalTensorTailCoefficient dimension)
        ε
        (anchorPhysicalTensorTailCoefficient_nonnegative
          dimension)
        (Q'.le_of_lt hε)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hfactor)
    (Q'.le_trans' _ _ _ hscaled hpay)

/-- Type-level precision/cutoff certificate for the complete tensor envelope
at one fixed dimension and positive rational tolerance. -/
structure AnchorPhysicalTensorToleranceSchedule
    (dimension : Nat) (ε : Q') : Type where
  precision : Nat
  retainedCutoff : Nat
  retainedCutoff_eq :
    retainedCutoff =
      anchorPhysicalRetainedCutoff precision
  envelope_le :
    su2PhysicalTensorTailEnvelope
        anchorCoupling
        anchorPhysicalBaseCutoff
        retainedCutoff precision dimension ≤
      ε

/-- Canonical total-tolerance tensor schedule. -/
def canonicalAnchorPhysicalTensorToleranceSchedule
    (dimension : Nat) {ε : Q'} (hε : (0 : Q') < ε) :
    AnchorPhysicalTensorToleranceSchedule dimension ε where
  precision :=
    anchorPhysicalTensorTolerancePrecision dimension ε
  retainedCutoff :=
    anchorPhysicalTensorToleranceRetainedCutoff dimension ε
  retainedCutoff_eq := rfl
  envelope_le :=
    anchorPhysicalTensorTailEnvelope_le_tolerance
      dimension hε

@[simp] theorem
    canonicalAnchorPhysicalTensorToleranceSchedule_retainedCutoff
    (dimension : Nat) {ε : Q'} (hε : (0 : Q') < ε) :
    (canonicalAnchorPhysicalTensorToleranceSchedule
      dimension hε).retainedCutoff =
        anchorPhysicalTensorToleranceRetainedCutoff
          dimension ε :=
  rfl

/-! ## 3. Clean dyadic specialization -/

private theorem dyad_pos_local :
    ∀ precision : Nat, (0 : Q') < dyad precision
  | 0 => by
      change (0 : Q') < (1 : Q')
      decide
  | precision + 1 => by
      change
        (0 : Q') <
          HalfPow.half * HalfPow.half ^ precision
      exact Q'.mul_pos (by decide)
        (dyad_pos_local precision)

/-- Total precision specialized to a requested dyadic tolerance. -/
def anchorPhysicalTensorDyadicPrecision
    (dimension targetPrecision : Nat) : Nat :=
  anchorPhysicalTensorTolerancePrecision
    dimension (dyad targetPrecision)

/-- Retained-spin cutoff specialized to a requested dyadic tolerance. -/
def anchorPhysicalTensorDyadicRetainedCutoff
    (dimension targetPrecision : Nat) : Nat :=
  anchorPhysicalTensorToleranceRetainedCutoff
    dimension (dyad targetPrecision)

theorem anchorPhysicalTensorTailEnvelope_le_dyad
    (dimension targetPrecision : Nat) :
    su2PhysicalTensorTailEnvelope
        anchorCoupling
        anchorPhysicalBaseCutoff
        (anchorPhysicalTensorDyadicRetainedCutoff
          dimension targetPrecision)
        (anchorPhysicalTensorDyadicPrecision
          dimension targetPrecision)
        dimension ≤
      dyad targetPrecision := by
  exact anchorPhysicalTensorTailEnvelope_le_tolerance
    dimension (dyad_pos_local targetPrecision)

/-! ## 4. Physical fixed-box cutoff-increment schedule -/

/-- Precision that makes the complete fixed-box cutoff increment at most
`ε`, after paying the number of physical plaquette coordinates. -/
def anchorPhysicalCutoffIncrementTolerancePrecision
    (n : Nat) (ε : Q') : Nat :=
  anchorPhysicalTensorTolerancePrecision
    (plaquetteEdgeCount n) ε

/-- Retained physical spin cutoff paired with the fixed-box precision. -/
def anchorPhysicalCutoffIncrementToleranceRetainedCutoff
    (n : Nat) (ε : Q') : Nat :=
  anchorPhysicalRetainedCutoff
    (anchorPhysicalCutoffIncrementTolerancePrecision n ε)

/-- Every later physical cutoff extension of the fixed box has total omitted
mass below the requested positive rational tolerance. -/
theorem anchorPhysicalCutoffIncrement_le_tolerance
    {ε : Q'} (hε : (0 : Q') < ε)
    {K n : Nat}
    (hretained :
      anchorPhysicalCutoffIncrementToleranceRetainedCutoff
          n ε ≤ K) :
    parametricKCutoffIncrement anchorCoupling
        (anchorPhysicalCutoffIncrementToleranceRetainedCutoff
          n ε)
        K n ≤
      ε := by
  let precision :=
    anchorPhysicalCutoffIncrementTolerancePrecision n ε
  have hincrement :=
    anchorScheduledCutoffIncrement_le_tensorEnvelope
      precision (K := K) (n := n) hretained
  have henvelope :=
    anchorPhysicalTensorTailEnvelope_le_tolerance
      (plaquetteEdgeCount n) hε
  exact Q'.le_trans' _ _ _ hincrement henvelope

/-- Type-level precision/cutoff certificate for one fixed finite box and one
positive rational tolerance. -/
structure AnchorPhysicalCutoffIncrementToleranceSchedule
    (n : Nat) (ε : Q') : Type where
  precision : Nat
  retainedCutoff : Nat
  retainedCutoff_eq :
    retainedCutoff =
      anchorPhysicalRetainedCutoff precision
  increment_le :
    ∀ K : Nat,
      retainedCutoff ≤ K →
        parametricKCutoffIncrement anchorCoupling
            retainedCutoff K n ≤
          ε

/-- Canonical Type-level fixed-box schedule furnished by the total-tolerance
rescaling. -/
def canonicalAnchorPhysicalCutoffIncrementToleranceSchedule
    (n : Nat) {ε : Q'} (hε : (0 : Q') < ε) :
    AnchorPhysicalCutoffIncrementToleranceSchedule n ε where
  precision :=
    anchorPhysicalCutoffIncrementTolerancePrecision n ε
  retainedCutoff :=
    anchorPhysicalCutoffIncrementToleranceRetainedCutoff n ε
  retainedCutoff_eq := rfl
  increment_le := by
    intro K hK
    exact anchorPhysicalCutoffIncrement_le_tolerance
      hε hK

@[simp] theorem
    canonicalAnchorPhysicalCutoffIncrementToleranceSchedule_retainedCutoff
    (n : Nat) {ε : Q'} (hε : (0 : Q') < ε) :
    (canonicalAnchorPhysicalCutoffIncrementToleranceSchedule
      n hε).retainedCutoff =
        anchorPhysicalCutoffIncrementToleranceRetainedCutoff
          n ε :=
  rfl

#print axioms anchorPhysicalTensorTailCoefficient_nonnegative
#print axioms anchorPhysicalTensorTailEnvelope_eqv_coefficient
#print axioms anchorPhysicalTensorScaledTolerance_pos
#print axioms anchorPhysicalTensorTailEnvelope_le_tolerance
#print axioms canonicalAnchorPhysicalTensorToleranceSchedule
#print axioms canonicalAnchorPhysicalTensorToleranceSchedule_retainedCutoff
#print axioms anchorPhysicalTensorTailEnvelope_le_dyad
#print axioms anchorPhysicalCutoffIncrement_le_tolerance
#print axioms canonicalAnchorPhysicalCutoffIncrementToleranceSchedule
#print axioms canonicalAnchorPhysicalCutoffIncrementToleranceSchedule_retainedCutoff

end YMGap.Continuum.SU2PhysicalOuterCutoffAnchorTotalTolerance
