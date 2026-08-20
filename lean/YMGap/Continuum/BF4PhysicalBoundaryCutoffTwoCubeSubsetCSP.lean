/-
# Local CSP model for the cutoff-two cube-subset sector

This module expresses the finite support-classification problem as 121 local
ternary constraints.  The first 48 constraints are the actual production
lower-link multiplicities for the fundamental-cube source.  The next 48 are
the same production multiplicities for an arbitrary lower/fixed labelling.
The final 25 constraints are a three-state automaton accepting precisely the
complement of

  * the all-one fundamental cube, and
  * all 0/2-labelled subsets of the six cube faces with zero labels off it.

Thus an unsatisfiability certificate for this CSP is a finite local support
classifier.  The certificate and its bridge to physical row closure are
separate modules.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoTwoFaceLeakage
import YMGap.Continuum.FiniteTernaryCSPUnsatCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetCSP

set_option maxRecDepth 300000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeBoundaryRow
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteTernaryCSPUnsatCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

/-! ## 1. Production link-support constraints -/

def cutoffTwoCubeSupportConstraint (link : Z4Link) : TernaryConstraint where
  scope := cutoffTwoCubeFixedIncidentFaceIds link
  accepts := fun word =>
    decide (0 < slabExplicitLinkMultiplicity 2 1
      (assembleReflectedSlabLabelling 0 centralLowerCubeState
        (wordToEdgeLabelling (cutoffTwoCubeFixedIncidentFaceIds link) word)
        zeroEdgeLabelling)
      link)

def cutoffTwoTargetSupportConstraint (link : Z4Link) : TernaryConstraint where
  scope := slabIncidentPlaqIds 1 link
  accepts := fun word =>
    decide (0 < slabExplicitLinkMultiplicity 2 1
      (wordToEdgeLabelling (slabIncidentPlaqIds 1 link) word) link)

def cutoffTwoCubeSupportConstraints : List TernaryConstraint :=
  (centralLowerLinks 0).map cutoffTwoCubeSupportConstraint

def cutoffTwoTargetSupportConstraints : List TernaryConstraint :=
  (centralLowerLinks 0).map cutoffTwoTargetSupportConstraint

/-! ## 2. Three-state language classifier -/

def cutoffTwoCubeSubsetClassifierNext
    (cubeCoordinate : Bool) (previous label : Nat) : Nat :=
  if previous = 2 then 2
  else if cubeCoordinate then
    if previous = 0 then (if label = 1 then 0 else 2)
    else if label = 0 ∨ label = 2 then 1 else 2
  else if label = 0 then previous else 2

def cutoffTwoCubeSubsetClassifierInitialAccepts : List Nat → Bool
  | [label, state] => decide (state = if label = 1 then 0 else 1)
  | _ => false

def cutoffTwoCubeSubsetClassifierStepAccepts
    (cubeCoordinate : Bool) : List Nat → Bool
  | [previous, label, following] =>
      decide (following =
        cutoffTwoCubeSubsetClassifierNext cubeCoordinate previous label)
  | _ => false

def cutoffTwoCubeSubsetClassifierInitial : TernaryConstraint where
  scope := [0, 1000]
  accepts := cutoffTwoCubeSubsetClassifierInitialAccepts

def cutoffTwoCubeSubsetClassifierStep
    (cubeCoordinate : Bool) (previous face following : Nat) :
    TernaryConstraint where
  scope := [previous, face, following]
  accepts := cutoffTwoCubeSubsetClassifierStepAccepts cubeCoordinate

def cutoffTwoCubeSubsetClassifierReject : TernaryConstraint where
  scope := [1023]
  accepts := fun word => decide (word = [2])

/-- The six cube coordinates are scanned first, followed by the remaining
18 production lower-face coordinates.  Auxiliary coordinates `1000..1023`
carry the deterministic classifier state. -/
def cutoffTwoCubeSubsetClassifierConstraints : List TernaryConstraint :=
  [cutoffTwoCubeSubsetClassifierInitial,
   cutoffTwoCubeSubsetClassifierStep true 1000 1 1001,
   cutoffTwoCubeSubsetClassifierStep true 1001 3 1002,
   cutoffTwoCubeSubsetClassifierStep true 1002 9 1003,
   cutoffTwoCubeSubsetClassifierStep true 1003 19 1004,
   cutoffTwoCubeSubsetClassifierStep true 1004 39 1005,
   cutoffTwoCubeSubsetClassifierStep false 1005 10 1006,
   cutoffTwoCubeSubsetClassifierStep false 1006 12 1007,
   cutoffTwoCubeSubsetClassifierStep false 1007 18 1008,
   cutoffTwoCubeSubsetClassifierStep false 1008 21 1009,
   cutoffTwoCubeSubsetClassifierStep false 1009 27 1010,
   cutoffTwoCubeSubsetClassifierStep false 1010 28 1011,
   cutoffTwoCubeSubsetClassifierStep false 1011 30 1012,
   cutoffTwoCubeSubsetClassifierStep false 1012 36 1013,
   cutoffTwoCubeSubsetClassifierStep false 1013 37 1014,
   cutoffTwoCubeSubsetClassifierStep false 1014 45 1015,
   cutoffTwoCubeSubsetClassifierStep false 1015 46 1016,
   cutoffTwoCubeSubsetClassifierStep false 1016 48 1017,
   cutoffTwoCubeSubsetClassifierStep false 1017 54 1018,
   cutoffTwoCubeSubsetClassifierStep false 1018 55 1019,
   cutoffTwoCubeSubsetClassifierStep false 1019 57 1020,
   cutoffTwoCubeSubsetClassifierStep false 1020 63 1021,
   cutoffTwoCubeSubsetClassifierStep false 1021 64 1022,
   cutoffTwoCubeSubsetClassifierStep false 1022 66 1023,
   cutoffTwoCubeSubsetClassifierReject]

def cutoffTwoCubeSubsetCSPConstraints : List TernaryConstraint :=
  cutoffTwoCubeSupportConstraints ++
    cutoffTwoTargetSupportConstraints ++
    cutoffTwoCubeSubsetClassifierConstraints

theorem cutoffTwoCubeSupportConstraints_count :
    cutoffTwoCubeSupportConstraints.length = 48 := by decide

theorem cutoffTwoTargetSupportConstraints_count :
    cutoffTwoTargetSupportConstraints.length = 48 := by decide

theorem cutoffTwoCubeSubsetClassifierConstraints_count :
    cutoffTwoCubeSubsetClassifierConstraints.length = 25 := by decide

theorem cutoffTwoCubeSubsetCSPConstraints_count :
    cutoffTwoCubeSubsetCSPConstraints.length = 121 := by decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetCSP

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetCSP.cutoffTwoCubeSubsetCSPConstraints_count
