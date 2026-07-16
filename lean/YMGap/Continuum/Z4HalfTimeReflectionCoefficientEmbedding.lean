/-
# Constructive coefficient embedding for the half-time support chart

The finite centered coefficient list is extended to the complete half-time
support space by deterministic fiber aggregation.  This definition is zero
off the represented supports and gives the exact quadratic identity required
by `CentralHalfTimeCoefficientEmbedding`; no injectivity or extra frontier
structure is needed.
-/

import YMGap.Continuum.FiniteCoefficientZeroExtension
import YMGap.Continuum.Z4HalfTimeReflectionCenteredCRealBridge

namespace YMGap.Continuum.Z4HalfTimeReflectionCoefficientEmbedding

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCoefficientZeroExtension
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionAmbientQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionCenteredCRealBridge
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal

local infix:50 " ≈ " => Q'.eqv

/-- Sum the centered coefficients over the finite fiber represented by one
half-time occupied support. -/
def centralHalfTimeZeroExtendedCoefficient
    {State : Type}
    (data : CenteredFiniteJointCylinderData State)
    (supportAt : Nat → State → List Nat)
    (stage : Nat) (support : List Nat) : Q' :=
  finiteCoefficientZeroExtension data.states data.coefficient
    (supportAt stage) support

theorem centralHalfTimeZeroExtendedCoefficient_eqv_zero_of_not_image
    {State : Type}
    (data : CenteredFiniteJointCylinderData State)
    (supportAt : Nat → State → List Nat)
    (stage : Nat) (support : List Nat)
    (houtside : ∀ state, state ∈ data.states →
      support ≠ supportAt stage state) :
    centralHalfTimeZeroExtendedCoefficient data supportAt stage support ≈
      0 := by
  exact finiteCoefficientZeroExtension_eqv_zero_of_not_image
    data.states data.coefficient (supportAt stage) support houtside

/-- The support-membership conjunct already present in the centered pair
chart is sufficient to derive the complete coefficient embedding. -/
theorem centralHalfTimeZeroExtendedCoefficient_embedding
    {State : Type}
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (data : CenteredFiniteJointCylinderData State)
    (halfSchedule : Nat → Nat)
    (supportAt : Nat → State → List Nat)
    (hlegal : ∀ stage state, state ∈ data.states →
      supportAt stage state ∈
        centralHalfSupportSpace (halfSchedule stage)) :
    CentralHalfTimeCoefficientEmbedding coupling hcoupling data
      halfSchedule supportAt
      (centralHalfTimeZeroExtendedCoefficient data supportAt) := by
  intro stage
  unfold centralAmbientSupportQuadratic
    centralHalfTimeZeroExtendedCoefficient
  exact finiteJointQuadratic_zeroExtension_eqv
    data.states data.coefficient (supportAt stage)
    (centralHalfSupportSpace (halfSchedule stage))
    (centralHalfSupportSpace_nodup (halfSchedule stage))
    (hlegal stage)
    (centralAmbientSupportPairLaw coupling hcoupling
      (centeredRecedingStageCutoff data.base stage)
      (halfSchedule stage))

theorem centralHalfTimeZeroExtendedCoefficient_embedding_of_chart
    {State : Type}
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (data : CenteredFiniteJointCylinderData State)
    (halfSchedule : Nat → Nat)
    (supportAt : Nat → State → List Nat)
    (chartEpsilon : Nat → Q')
    (hchart : CentralHalfTimeCenteredPairChart coupling hcoupling data
      halfSchedule supportAt chartEpsilon) :
    CentralHalfTimeCoefficientEmbedding coupling hcoupling data
      halfSchedule supportAt
      (centralHalfTimeZeroExtendedCoefficient data supportAt) := by
  apply centralHalfTimeZeroExtendedCoefficient_embedding
  exact hchart.2.1

/-- Reflection-positive closure with the coefficient-reindex argument removed
from the caller: the unique fiber-summed zero extension above supplies it. -/
theorem centeredFiniteJointCylinderQuadratic_geRat_zero_of_halfTime_zeroExtension
    {State : Type}
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤
      YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorCoupling)
    (data : CenteredFiniteJointCylinderData State)
    (halfSchedule floorSchedule : Nat → Nat)
    (supportAt : Nat → State → List Nat)
    (chartEpsilon : Nat → Q')
    (hchart : CentralHalfTimeCenteredPairChart coupling hcoupling data
      halfSchedule supportAt chartEpsilon)
    (hcarrier : CentralHalfTimeCarrierSchedule
      halfSchedule floorSchedule)
    (hvanishes : CentralHalfTimeCenteredTotalModulusVanishes data
      halfSchedule floorSchedule
      (centralHalfTimeZeroExtendedCoefficient data supportAt)
      chartEpsilon) :
    YMGap.Constructive.ExpPos.geRat
      (centeredFiniteJointCylinderQuadratic
        coupling hcoupling hle data) 0 := by
  exact centeredFiniteJointCylinderQuadratic_geRat_zero_of_halfTime
    hcoupling hle data halfSchedule floorSchedule supportAt
    (centralHalfTimeZeroExtendedCoefficient data supportAt)
    chartEpsilon hchart
    (centralHalfTimeZeroExtendedCoefficient_embedding_of_chart
      coupling hcoupling data halfSchedule supportAt chartEpsilon hchart)
    hcarrier hvanishes

#print axioms centralHalfTimeZeroExtendedCoefficient_eqv_zero_of_not_image
#print axioms centralHalfTimeZeroExtendedCoefficient_embedding
#print axioms centralHalfTimeZeroExtendedCoefficient_embedding_of_chart
#print axioms centeredFiniteJointCylinderQuadratic_geRat_zero_of_halfTime_zeroExtension

end YMGap.Continuum.Z4HalfTimeReflectionCoefficientEmbedding
