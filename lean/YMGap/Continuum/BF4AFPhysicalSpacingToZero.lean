/-
M2r -- the proved AF coupling modulus forces the BF4 quadratic physical
spacing envelope to vanish.

`ContinuumGapModulus.afSchedule_to_zero` now carries a genuine explicit
epsilon cutoff.  This file transports that modulus through the existing
physical envelope

    a(g) * Lambda <= C * g^2.

Thus a BF4 trajectory definitionally tied to the proved shifted AF schedule
does not need an independent `a_j -> 0` hypothesis.
-/

import YMGap.Continuum.BF4FarautPhysicalSeparatorProducer
import YMGap.Continuum.PhysicalSeparatorLinearTail
import YMGap.Continuum.ContinuumGapModulus

namespace YMGap.Continuum.BF4AFPhysicalSpacingToZero

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4FarautPhysicalSeparatorProducer
open YMGap.Continuum.ContinuumGapModulus
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.PhysicalSeparatorLinearTail

/-! ## 1. Coupling and spacing moduli -/

/-- A Type-level modulus for a positive rational coupling sequence tending to
zero. -/
structure CouplingToZero (coupling : Nat -> Q') : Type where
  modulus : Q' -> Nat
  coupling_le : forall epsilon : Q', (0 : Q') < epsilon ->
    forall j : Nat, modulus epsilon <= j -> coupling j <= epsilon

/-- Exact identification of a coupling sequence with the shifted schedule of
one two-loop AF trajectory certificate. -/
structure ShiftedAFTrajectoryIdentification
    (C : AFTrajectoryCertificate) (coupling : Nat -> Q') : Type where
  coupling_eq : forall j : Nat, coupling j = afSchedule C j

/-- The corrected explicit AF cutoff supplies a genuine coupling-to-zero
modulus for any definitionally identified sequence. -/
def couplingToZeroOfAFTrajectory
    (C : AFTrajectoryCertificate) (coupling : Nat -> Q')
    (H : ShiftedAFTrajectoryIdentification C coupling) :
    CouplingToZero coupling where
  modulus := afScheduleCutoff C
  coupling_le := fun epsilon hepsilon j hj => by
    rw [H.coupling_eq j]
    exact afSchedule_to_zero C epsilon hepsilon j hj

/-- The physical spacing obtained by evaluating an envelope on a coupling
sequence known to lie in its window. -/
def physicalSpacingOfEnvelope
    {g₁ : Q'} (E : PhysicalSpacingEnvelope g₁)
    (coupling : Nat -> Q')
    (coupling_pos : forall j, (0 : Q') < coupling j)
    (coupling_le_window : forall j, coupling j <= g₁) :
    PhysicalSpacing where
  spacing := fun j => E.a (coupling j)
  spacing_pos := fun j =>
    E.a_pos (coupling j) (coupling_pos j) (coupling_le_window j)

/-- Positive denominator used when transferring a coupling modulus through
the quadratic spacing envelope. -/
def envelopeThresholdDenominator {g₁ : Q'}
    (E : PhysicalSpacingEnvelope g₁) : Q' :=
  E.C + 1

theorem envelopeThresholdDenominator_pos {g₁ : Q'}
    (E : PhysicalSpacingEnvelope g₁) :
    (0 : Q') < envelopeThresholdDenominator E :=
  Q'.add_pos E.C_pos (by decide)

/-- A coupling threshold small enough that the quadratic envelope is below
the requested physical spacing. -/
def envelopeCouplingThreshold {g₁ : Q'}
    (E : PhysicalSpacingEnvelope g₁) (epsilon : Q') : Q' :=
  Q'.divPos (epsilon * E.Λ) (envelopeThresholdDenominator E)
    (envelopeThresholdDenominator_pos E)

theorem envelopeCouplingThreshold_pos {g₁ : Q'}
    (E : PhysicalSpacingEnvelope g₁) (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < envelopeCouplingThreshold E epsilon :=
  Q'.divPos_pos _ _ (envelopeThresholdDenominator_pos E)
    (Q'.mul_pos hepsilon E.Λ_pos)

/-- The computed spacing cutoff requests both `g <= 1` and the sharper
epsilon-dependent coupling threshold. -/
def envelopeSpacingModulus {g₁ : Q'}
    (E : PhysicalSpacingEnvelope g₁) {coupling : Nat -> Q'}
    (Z : CouplingToZero coupling) (epsilon : Q') : Nat :=
  max (Z.modulus 1) (Z.modulus (envelopeCouplingThreshold E epsilon))

/-- A coupling-to-zero modulus plus the existing quadratic physical envelope
constructs the exact spacing-to-zero modulus. -/
def spacingToZeroOfQuadraticEnvelope
    {g₁ : Q'} (E : PhysicalSpacingEnvelope g₁)
    (coupling : Nat -> Q')
    (coupling_pos : forall j, (0 : Q') < coupling j)
    (coupling_le_window : forall j, coupling j <= g₁)
    (Z : CouplingToZero coupling) :
    SpacingToZero
      (physicalSpacingOfEnvelope E coupling coupling_pos coupling_le_window) where
  modulus := envelopeSpacingModulus E Z
  spacing_le := fun epsilon hepsilon j hj => by
    have honeStart : Z.modulus 1 <= j :=
      Nat.le_trans (Nat.le_max_left _ _) hj
    have hthresholdStart :
        Z.modulus (envelopeCouplingThreshold E epsilon) <= j :=
      Nat.le_trans (Nat.le_max_right _ _) hj
    have hg1 : coupling j <= (1 : Q') :=
      Z.coupling_le 1 (by decide) j honeStart
    have hgt : coupling j <= envelopeCouplingThreshold E epsilon :=
      Z.coupling_le (envelopeCouplingThreshold E epsilon)
        (envelopeCouplingThreshold_pos E epsilon hepsilon) j hthresholdStart
    have hg0 : (0 : Q') <= coupling j := Q'.le_of_lt (coupling_pos j)
    have hsq : coupling j * coupling j <= coupling j := by
      have hmul := Q'.mul_le_mul_of_nonneg_left
        (coupling j) 1 (coupling j) hg1 hg0
      exact Q'.le_trans' _ _ _ hmul
        (Q'.le_of_eqv (Q'.mul_one_eqv (coupling j)))
    have hCnonnegative : (0 : Q') <= E.C := Q'.le_of_lt E.C_pos
    have hDnonnegative :
        (0 : Q') <= envelopeThresholdDenominator E :=
      Q'.le_of_lt (envelopeThresholdDenominator_pos E)
    have hCDen : E.C <= envelopeThresholdDenominator E := by
      unfold envelopeThresholdDenominator
      exact Q'.add_le_self_of_nonneg E.C 1 (by decide)
    have hquadLinear :
        E.C * (coupling j * coupling j) <= E.C * coupling j :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hsq hCnonnegative
    have hlinearDen :
        E.C * coupling j <= envelopeThresholdDenominator E * coupling j :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hCDen hg0
    have hdenThreshold :
        envelopeThresholdDenominator E * coupling j <=
          envelopeThresholdDenominator E *
            envelopeCouplingThreshold E epsilon :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hgt hDnonnegative
    have hthresholdCollapse :
        (envelopeThresholdDenominator E *
          envelopeCouplingThreshold E epsilon).eqv (epsilon * E.Λ) := by
      exact Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv (envelopeThresholdDenominator E)
          (envelopeCouplingThreshold E epsilon))
        (Q'.divPos_mul_eqv (epsilon * E.Λ)
          (envelopeThresholdDenominator E)
          (envelopeThresholdDenominator_pos E))
    have hquad :
        E.C * (coupling j * coupling j) <= epsilon * E.Λ :=
      Q'.le_trans' _ _ _ hquadLinear
        (Q'.le_trans' _ _ _ hlinearDen
          (Q'.le_trans' _ _ _ hdenThreshold
            (Q'.le_of_eqv hthresholdCollapse)))
    have hspacingMul :
        E.a (coupling j) * E.Λ <= epsilon * E.Λ :=
      Q'.le_trans' _ _ _
        (E.spacing_quad (coupling j) (coupling_pos j)
          (coupling_le_window j)) hquad
    have hquot :
        E.a (coupling j) <=
          Q'.divPos (epsilon * E.Λ) E.Λ E.Λ_pos :=
      Q'.le_divPos_of_mul_le (epsilon * E.Λ) E.Λ E.Λ_pos hspacingMul
    have hcollapse :
        (Q'.divPos (epsilon * E.Λ) E.Λ E.Λ_pos).eqv epsilon := by
      unfold Q'.divPos
      exact Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv epsilon E.Λ (Q'.recipPos E.Λ E.Λ_pos))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left epsilon
            (E.Λ * Q'.recipPos E.Λ E.Λ_pos) 1
            (Q'.mul_recipPos_eqv E.Λ E.Λ_pos))
          (Q'.mul_one_eqv epsilon))
    exact Q'.le_trans' _ _ _ hquot (Q'.le_of_eqv hcollapse)

end YMGap.Continuum.BF4AFPhysicalSpacingToZero

/-! ## 2. BF4/Faraut specialization -/

namespace YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.PhysicalSeparatorLinearTail

namespace BF4FarautQuarterPhysicalSeparatorProducer

variable {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator.PhysicalSeparator}

/-- The precise same-schedule AF datum required by the BF4 producer. -/
abbrev ShiftedAFCoupling
    (_producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (C : AFTrajectoryCertificate) : Type :=
  ShiftedAFTrajectoryIdentification C coupling

/-- No independent spacing modulus remains once the producer's coupling is
identified with a proved AF trajectory. -/
def physicalSpacingToZeroOfAFTrajectory
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (C : AFTrajectoryCertificate)
    (H : producer.ShiftedAFCoupling C) :
    SpacingToZero
      producer.toBF4QuarterPhysicalSeparatorProducer.physicalSpacing := by
  exact spacingToZeroOfQuadraticEnvelope spacing coupling
    producer.bf4.coupling_pos producer.bf4.coupling_le_window
    (couplingToZeroOfAFTrajectory C coupling H)

end BF4FarautQuarterPhysicalSeparatorProducer

end YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

#print axioms YMGap.Continuum.BF4AFPhysicalSpacingToZero.couplingToZeroOfAFTrajectory
#print axioms YMGap.Continuum.BF4AFPhysicalSpacingToZero.spacingToZeroOfQuadraticEnvelope
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.physicalSpacingToZeroOfAFTrajectory
