/-
# Reflection positivity of the BF4 U(1) exponent Gram

The orientation-correct U(1) all-label theorem applies to coefficients that
are even under global charge conjugation.  Heat-exponent profiles depend
only on squared charge magnitudes, hence are exactly even.

This module proves that fact for individual exponent indicators and arbitrary
finite rational linear combinations.  It then identifies the diagonal
entries already used by `BF4SU2U1ExponentGramDiscriminator` with the genuine
orientation-correct normalized all-label quadratic.  No auxiliary carrier or
surrogate law is introduced.

## Axiom gate

Finite lists, integers, and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, custom axiom, noncomputable declaration, or placeholder.
-/

import YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator
import YMGap.Continuum.BF4U1TwistedPhysicalReindex

namespace YMGap.Continuum.BF4U1ExponentGramPositivity

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExponentGramMatchedOneStep
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator
open YMGap.Continuum.BF4U1ReflectionCovariance
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.BF4U1TwistedPhysicalReindex
open YMGap.Continuum.BF4U1TwistedReflectionGram
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact charge-conjugation invariance -/

theorem u1HeatExponentOn_conjugate
    (state : ChargeLabelling) :
    ∀ ids : List Nat,
      u1HeatExponentOn ids
          (conjugateChargeLabelling state) =
        u1HeatExponentOn ids state
  | [] => rfl
  | id :: tail => by
      simp only [u1HeatExponentOn, conjugateChargeLabelling,
        chargeMagnitude_negateChargeLabel,
        u1HeatExponentOn_conjugate state tail]

theorem u1LowerHeatExponent_conjugate
    (half : Nat) (state : ChargeLabelling) :
    u1LowerHeatExponent half
        (conjugateChargeLabelling state) =
      u1LowerHeatExponent half state := by
  unfold u1LowerHeatExponent
  exact u1HeatExponentOn_conjugate state _

theorem u1ExponentCoefficient_conjugate
    (half exponent : Nat) (state : ChargeLabelling) :
    u1ExponentCoefficient half exponent
        (conjugateChargeLabelling state) =
      u1ExponentCoefficient half exponent state := by
  unfold u1ExponentCoefficient
  rw [u1LowerHeatExponent_conjugate]

theorem u1ExponentCoefficient_even
    (D : U1SlabData) (exponent : Nat) :
    ChargeConjugationEvenOn D
      (u1ExponentCoefficient D.half exponent) := by
  intro state _
  exact u1ExponentCoefficient_conjugate
    D.half exponent state

/-! ## 2. Finite exponent packets -/

def u1ExponentLinearCoefficient
    (half : Nat)
    (coefficients : List (Nat × Q'))
    (state : ChargeLabelling) : Q' :=
  listQSum
    (fun pair =>
      pair.2 * u1ExponentCoefficient half pair.1 state)
    coefficients

theorem u1ExponentLinearCoefficient_conjugate
    (half : Nat) (coefficients : List (Nat × Q'))
    (state : ChargeLabelling) :
    u1ExponentLinearCoefficient half coefficients
        (conjugateChargeLabelling state) =
      u1ExponentLinearCoefficient half coefficients state := by
  unfold u1ExponentLinearCoefficient
  induction coefficients with
  | nil => rfl
  | cons pair tail ih =>
      simp only [listQSum]
      rw [u1ExponentCoefficient_conjugate, ih]

theorem u1ExponentLinearCoefficient_even
    (D : U1SlabData)
    (coefficients : List (Nat × Q')) :
    ChargeConjugationEvenOn D
      (u1ExponentLinearCoefficient D.half coefficients) := by
  intro state _
  exact u1ExponentLinearCoefficient_conjugate
    D.half coefficients state

/-- The genuine normalized all-label quadratic for a finite linear
combination of U(1) heat-exponent groups. -/
def u1ExponentPacketQuadratic
    (D : U1SlabData)
    (coefficients : List (Nat × Q')) : Q' :=
  u1FullNormalizedMassReflectionQuadratic D
    (u1ExponentLinearCoefficient D.half coefficients)

theorem u1ExponentPacketQuadratic_nonnegative
    (D : U1SlabData)
    (coefficients : List (Nat × Q')) :
    (0 : Q') ≤
      u1ExponentPacketQuadratic D coefficients := by
  exact u1FullNormalizedMassReflectionQuadratic_nonnegative
    D (u1ExponentLinearCoefficient D.half coefficients)
    (u1ExponentLinearCoefficient_even D coefficients)

/-! ## 3. Orientation correction does not change magnitude exponents -/

private theorem u1HeatExponentOn_reflectedRestrictions
    (half : Nat) (physical : ChargeLabelling) :
    ∀ ids : List Nat,
      (∀ id, id ∈ ids → id ∈ centralLowerFaceIds half) →
      u1HeatExponentOn ids
          (u1ReflectedUpperRestriction half physical) =
        u1HeatExponentOn ids
          (centralReflectedUpperRestriction half physical)
  | [], _ => rfl
  | id :: tail, hids => by
      have hid : id ∈ centralLowerFaceIds half :=
        hids id List.mem_cons_self
      have htail : ∀ item, item ∈ tail →
          item ∈ centralLowerFaceIds half :=
        fun item hitem =>
          hids item (List.mem_cons_of_mem id hitem)
      simp only [u1HeatExponentOn]
      rw [u1HeatExponentOn_reflectedRestrictions
        half physical tail htail]
      simp only [u1ReflectedUpperRestriction,
        centralReflectedUpperRestriction, if_pos hid,
        chargeMagnitude_reflectChargeLabel]

theorem u1LowerHeatExponent_reflectedRestrictions
    (half : Nat) (physical : ChargeLabelling) :
    u1LowerHeatExponent half
        (u1ReflectedUpperRestriction half physical) =
      u1LowerHeatExponent half
        (centralReflectedUpperRestriction half physical) := by
  unfold u1LowerHeatExponent
  apply u1HeatExponentOn_reflectedRestrictions
  intro id hid
  exact hid

theorem u1ExponentCoefficient_reflectedRestrictions
    (half exponent : Nat) (physical : ChargeLabelling) :
    u1ExponentCoefficient half exponent
        (u1ReflectedUpperRestriction half physical) =
      u1ExponentCoefficient half exponent
        (centralReflectedUpperRestriction half physical) := by
  unfold u1ExponentCoefficient
  rw [u1LowerHeatExponent_reflectedRestrictions]

/-! ## 4. Identification with the existing discriminator entries -/

theorem u1ExponentGramEntry_diagonal_eq_fullNormalized
    (D : U1SlabData) (exponent : Nat) :
    u1ExponentGramEntry D.half D.states D.normalizedMass
        { leftExponent := exponent, rightExponent := exponent } ≈
      u1FullNormalizedMassReflectionQuadratic D
        (u1ExponentCoefficient D.half exponent) := by
  unfold u1ExponentGramEntry reflectedLawBilinear
    u1FullNormalizedMassReflectionQuadratic
  apply listQSum_congr_on
  intro physical _
  rw [u1ExponentCoefficient_reflectedRestrictions]
  exact Q'.eqv_refl _

theorem u1ExponentGramEntry_diagonal_nonnegative
    (D : U1SlabData) (exponent : Nat) :
    (0 : Q') ≤
      u1ExponentGramEntry D.half D.states D.normalizedMass
        { leftExponent := exponent, rightExponent := exponent } := by
  have hpositive :
      (0 : Q') ≤
        u1FullNormalizedMassReflectionQuadratic D
          (u1ExponentCoefficient D.half exponent) :=
    u1FullNormalizedMassReflectionQuadratic_nonnegative
      D (u1ExponentCoefficient D.half exponent)
      (u1ExponentCoefficient_even D exponent)
  exact Q'.le_trans' _ _ _ hpositive
    (Q'.ge_of_eqv
      (u1ExponentGramEntry_diagonal_eq_fullNormalized
        D exponent))

/-- The actual coarse diagonal coordinate used in the SU(2)/U(1)
discriminator is nonnegative. -/
theorem u1CoarseExponentGramEntry_diagonal_nonnegative
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff exponent : Nat) :
    (0 : Q') ≤
      u1CoarseExponentGramEntry G candidate hcandidate
        fineChargeCutoff
        { leftExponent := exponent,
          rightExponent := exponent } := by
  exact u1ExponentGramEntry_diagonal_nonnegative
    (coarseU1Data G candidate hcandidate fineChargeCutoff)
    exponent

end YMGap.Continuum.BF4U1ExponentGramPositivity

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4U1ExponentGramPositivity.u1HeatExponentOn_conjugate
#print axioms YMGap.Continuum.BF4U1ExponentGramPositivity.u1ExponentCoefficient_even
#print axioms YMGap.Continuum.BF4U1ExponentGramPositivity.u1ExponentLinearCoefficient_even
#print axioms YMGap.Continuum.BF4U1ExponentGramPositivity.u1ExponentPacketQuadratic_nonnegative
#print axioms YMGap.Continuum.BF4U1ExponentGramPositivity.u1ExponentCoefficient_reflectedRestrictions
#print axioms YMGap.Continuum.BF4U1ExponentGramPositivity.u1ExponentGramEntry_diagonal_eq_fullNormalized
#print axioms YMGap.Continuum.BF4U1ExponentGramPositivity.u1CoarseExponentGramEntry_diagonal_nonnegative
