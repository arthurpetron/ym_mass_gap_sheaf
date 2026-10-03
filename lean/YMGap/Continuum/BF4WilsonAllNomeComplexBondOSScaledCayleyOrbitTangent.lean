/-
# Arbitrary-base tangents on the original signed Cayley orbit

The supplied two-sided tangent at an original graph point transports by the
actual signed isometry to every point of its graph orbit. Forward and backward
quotients use the same computed reciprocal as the zero-base quotients. Thus
the source-computed radius is independent of the arbitrary numerical base time.

This is numerical-time differentiation on the original maximal graph. It does
not calibrate physical spacing or assert a continuum/QFT conclusion.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRealTangentData
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedGraph
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedScalarCommutation
import YMGap.Continuum.SignedRealTimeData

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyOrbitTangent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (timeValue realValue)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Point ofPoint input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (imagScale cneg)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime (positiveAction)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins
  (positiveRealAction_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime
  (signedAction signedAction_addTime signedAction_positiveTime signedAction_distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedScalarCommutation
  (signedAction_realScalar signedAction_imagScale signedAction_cneg signedAction_diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyNegativeRealTangent
  (negativeClock)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyTangentData (slope)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRealTangentData
  (realRightQuotient realLeftQuotient RealTangent ofPointRealTangent slope_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveRealNormalizedTangent
  (realScalar)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedGraph
  (signedGraphMap signedGraphMap_input signedGraphMap_output)
open YMGap.Continuum.PositiveTimeReciprocalData (reciprocalReal reciprocalRealCauchy)
open YMGap.Continuum.SignedRealTimeData (SignedTimeValue)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "P" => Point hw0 hw1 (width := width)
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1
local notation "Dist" => distance hw0 hw1
local notation "G" => signedAction hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private def positiveClock (D : PositiveTime) : SignedTimeValue :=
  SignedRealTimeData.positiveTime (timeValue D)

/-- Forward signed-time quotient based at `s`; its denominator is the
constructed reciprocal of the same supplied positive time `D`. -/
def forwardQuotientAt (s : SignedTimeValue) (D : PositiveTime) (u : H) : H :=
  realScalar hw0 hw1 (reciprocalReal D) (reciprocalRealCauchy D)
    (diff hw0 hw1
      (G (SignedRealTimeData.addTime s (positiveClock D)) u) (G s u))

/-- Backward quotient based at `s`; the numerator order implements division
by the signed time `-D`, with no sign decision or new reciprocal. -/
def backwardQuotientAt (s : SignedTimeValue) (D : PositiveTime) (u : H) : H :=
  realScalar hw0 hw1 (reciprocalReal D) (reciprocalRealCauchy D)
    (diff hw0 hw1 (G s u)
      (G (SignedRealTimeData.addTime s (negativeClock D)) u))

theorem forwardQuotientAt_transport (s : SignedTimeValue) (D : PositiveTime) (u : H) :
    forwardQuotientAt hw0 hw1 s D u =
      G s (realRightQuotient hw0 hw1 D u) := by
  unfold forwardQuotientAt realRightQuotient
  rw [signedAction_addTime, ← signedAction_diff, ← signedAction_realScalar,
    positiveClock, signedAction_positiveTime, positiveRealAction_pin]

theorem backwardQuotientAt_transport (s : SignedTimeValue) (D : PositiveTime) (u : H) :
    backwardQuotientAt hw0 hw1 s D u =
      G s (realLeftQuotient hw0 hw1 D u) := by
  unfold backwardQuotientAt realLeftQuotient
  rw [signedAction_addTime, ← signedAction_diff, ← signedAction_realScalar]

private theorem orbitSlope_transport (p : P) (s : SignedTimeValue) :
    slope hw0 hw1 (Out (signedGraphMap hw0 hw1 s (ofPoint hw0 hw1 p))) =
      G s (slope hw0 hw1 (Out (ofPoint hw0 hw1 p))) := by
  calc
    slope hw0 hw1 (Out (signedGraphMap hw0 hw1 s (ofPoint hw0 hw1 p))) =
        cneg hw0 hw1 (imagScale hw0 hw1 2
          (Out (signedGraphMap hw0 hw1 s (ofPoint hw0 hw1 p)))) :=
      slope_pin hw0 hw1 _
    _ = cneg hw0 hw1 (imagScale hw0 hw1 2
          (G s (Out (ofPoint hw0 hw1 p)))) := by
      rw [signedGraphMap_output]
    _ = G s (cneg hw0 hw1 (imagScale hw0 hw1 2
          (Out (ofPoint hw0 hw1 p)))) := by
      rw [← signedAction_imagScale, ← signedAction_cneg]
    _ = G s (slope hw0 hw1 (Out (ofPoint hw0 hw1 p))) := by
      rw [slope_pin]

private theorem forwardOrbitError_eq (p : P) (s : SignedTimeValue) (D : PositiveTime) :
    Dist (forwardQuotientAt hw0 hw1 s D (In (ofPoint hw0 hw1 p)))
      (slope hw0 hw1 (Out (signedGraphMap hw0 hw1 s (ofPoint hw0 hw1 p)))) =
    Dist (realRightQuotient hw0 hw1 D (In (ofPoint hw0 hw1 p)))
      (slope hw0 hw1 (Out (ofPoint hw0 hw1 p))) := by
  rw [forwardQuotientAt_transport, orbitSlope_transport, signedAction_distance]

private theorem backwardOrbitError_eq (p : P) (s : SignedTimeValue) (D : PositiveTime) :
    Dist (backwardQuotientAt hw0 hw1 s D (In (ofPoint hw0 hw1 p)))
      (slope hw0 hw1 (Out (signedGraphMap hw0 hw1 s (ofPoint hw0 hw1 p)))) =
    Dist (realLeftQuotient hw0 hw1 D (In (ofPoint hw0 hw1 p)))
      (slope hw0 hw1 (Out (ofPoint hw0 hw1 p))) := by
  rw [backwardQuotientAt_transport, orbitSlope_transport, signedAction_distance]

/-- Whole-orbit tangent certificate on the ORIGINAL maximal graph. Its radius
is exactly the source-computed `ofPointRealTangent` radius and is independent
of base time. -/
structure PointOrbitTangent (p : P) : Type where
  radius : (e : Q') → (0 : Q') < e → Q'
  positive : ∀ e he, (0 : Q') < radius e he
  bound : ∀ e he (s : SignedTimeValue) (D : PositiveTime),
    RCle (realValue (timeValue D)) (rat (radius e he)) →
      (RCle (Dist (forwardQuotientAt hw0 hw1 s D
        (In (ofPoint hw0 hw1 p)))
        (slope hw0 hw1 (Out (signedGraphMap hw0 hw1 s (ofPoint hw0 hw1 p)))))
        (rat e)) ×'
      (RCle (Dist (backwardQuotientAt hw0 hw1 s D
        (In (ofPoint hw0 hw1 p)))
        (slope hw0 hw1 (Out (signedGraphMap hw0 hw1 s (ofPoint hw0 hw1 p)))))
        (rat e))

/-- Every supplied original Point has the same two-sided source-derived error
radius at every arbitrary signed numerical base time. -/
def ofPointOrbitTangent (p : P) : PointOrbitTangent hw0 hw1 p where
  radius := (ofPointRealTangent hw0 hw1 p).radius
  positive := (ofPointRealTangent hw0 hw1 p).positive
  bound := by
    intro e he s D htime
    have hb := (ofPointRealTangent hw0 hw1 p).bound e he D htime
    constructor
    · rw [forwardOrbitError_eq]
      exact hb.1
    · rw [backwardOrbitError_eq]
      exact hb.2

#print axioms forwardQuotientAt
#print axioms backwardQuotientAt
#print axioms forwardQuotientAt_transport
#print axioms backwardQuotientAt_transport
#print axioms PointOrbitTangent
#print axioms ofPointOrbitTangent

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyOrbitTangent
