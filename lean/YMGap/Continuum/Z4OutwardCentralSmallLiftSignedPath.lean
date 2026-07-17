/-
# Signed two-edge cancellation and the remaining cycle carrier

The two exact six-face transitions proved in the preceding module cancel at
their shared `000` cell.  Their endpoint mass does not disappear: it survives
with opposite signs at `111` and `100`.  A third equal-activity transition
from `100` to `111` is therefore the precise carrier needed to close this
minimal signed cycle.
-/

import YMGap.Continuum.Z4OutwardCentralSmallLiftActivityPair

namespace YMGap.Continuum.Z4OutwardCentralSmallLiftSignedPath

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4OutwardCentralSmallLiftActivityPair
open YMGap.Continuum.Z4OutwardChildQuerySmallLiftWitness
open YMGap.Continuum.Z4OutwardFineCoarseSupportGasCrossDifference
open YMGap.Continuum.Z4OutwardThreeCubeFineSubsupportPatterns
open YMGap.Continuum.Z4OutwardThreeCubeFullRootQueries
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand

local infix:50 " ≈ " => Q'.eqv

/-- Signed mass of one directed coarse-to-fine pattern transition. -/
def outwardSignedDirectedPatternEdge
    (activity : Q') (coarse fine pattern : ThreeBlockPattern) : Q' :=
  if pattern = coarse then activity
  else if pattern = fine then -activity
  else 0

def outwardCentralPathActivity (coupling : Q') : Q' :=
  couplingParametricKSupportFamilyActivity coupling 1 6
    [axisCoarseRoot zeroAxisOffset]

def outwardSmallLiftPathActivity (coupling : Q') : Q' :=
  couplingParametricKSupportFamilyActivity coupling 1 6
    [outwardXFineSmallLiftRoot]

/-- The signed profile of the exact path `111 → 000 → 100`. -/
def outwardCentralSmallLiftTwoEdgeProfile
    (coupling : Q') (pattern : ThreeBlockPattern) : Q' :=
  outwardSignedDirectedPatternEdge
      (outwardCentralPathActivity coupling)
      (true, true, true) (false, false, false) pattern +
    outwardSignedDirectedPatternEdge
      (outwardSmallLiftPathActivity coupling)
      (false, false, false) (true, false, false) pattern

private theorem neg_add_eqv_zero_of_eqv {left right : Q'}
    (h : left ≈ right) : -left + right ≈ 0 :=
  Q'.eqv_trans _ (-right + right) _
    (Q'.add_eqv_congr'
      (Q'.neg_eqv_congr left right h) (Q'.eqv_refl right))
    (Q'.neg_add_self_eqv right)

private theorem add_neg_eqv_zero_of_eqv {left right : Q'}
    (h : left ≈ right) : left + -right ≈ 0 :=
  Q'.eqv_trans _ (right + -right) _
    (Q'.add_eqv_congr' h (Q'.eqv_refl (-right)))
    (Q'.add_neg_self_eqv right)

/-- Exact cancellation at the shared intermediate cell. -/
theorem outwardCentralSmallLiftTwoEdgeProfile_000_eqv_zero
    (coupling : Q') :
    outwardCentralSmallLiftTwoEdgeProfile coupling
        (false, false, false) ≈ 0 := by
  unfold outwardCentralSmallLiftTwoEdgeProfile
    outwardSignedDirectedPatternEdge
  simp only [↓reduceIte]
  exact neg_add_eqv_zero_of_eqv
    (outwardCentral_smallLift_singletonFamilyActivities_eqv coupling)

/-- The positive endpoint debt remains in cell `111`. -/
theorem outwardCentralSmallLiftTwoEdgeProfile_111_eqv_activity
    (coupling : Q') :
    outwardCentralSmallLiftTwoEdgeProfile coupling
        (true, true, true) ≈ outwardCentralPathActivity coupling := by
  unfold outwardCentralSmallLiftTwoEdgeProfile
    outwardSignedDirectedPatternEdge
  simp only [↓reduceIte]
  exact Q'.eqv_of_eq (Q'.add_zero' _)

/-- The equal negative endpoint debt remains in cell `100`. -/
theorem outwardCentralSmallLiftTwoEdgeProfile_100_eqv_neg_activity
    (coupling : Q') :
    outwardCentralSmallLiftTwoEdgeProfile coupling
        (true, false, false) ≈
      -(outwardSmallLiftPathActivity coupling) := by
  unfold outwardCentralSmallLiftTwoEdgeProfile
    outwardSignedDirectedPatternEdge
  simp only [↓reduceIte]
  exact Q'.eqv_of_eq (Q'.zero_add' _)

/-- The two surviving endpoint coefficients are equal and opposite. -/
theorem outwardCentralSmallLift_endpointDebt_eqv_zero
    (coupling : Q') :
    outwardCentralSmallLiftTwoEdgeProfile coupling
          (true, true, true) +
        outwardCentralSmallLiftTwoEdgeProfile coupling
          (true, false, false) ≈ 0 := by
  refine Q'.eqv_trans _
    (outwardCentralPathActivity coupling +
      -(outwardSmallLiftPathActivity coupling)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (outwardCentralSmallLiftTwoEdgeProfile_111_eqv_activity coupling)
      (outwardCentralSmallLiftTwoEdgeProfile_100_eqv_neg_activity coupling)
  · exact add_neg_eqv_zero_of_eqv
      (outwardCentral_smallLift_singletonFamilyActivities_eqv coupling)

/-! ## The precise third-carrier residual -/

/-- A concrete compatible family closing the minimal cycle must move from
coarse cell `100` to fine cell `111` and have the same complete cutoff-one
activity as the central six-face carrier. -/
structure OutwardEqualActivity100To111Carrier (coupling : Q') where
  family : List (List Nat)
  compatible : family ∈ canonicalCompatibleAmbientFamilies 6
  coarse_pattern :
    outwardComponentSubsupportFamilyPattern outwardCoarseQueries family =
      (true, false, false)
  fine_pattern :
    outwardComponentSubsupportFamilyPattern outwardFineQueries family =
      (true, true, true)
  activity_eqv :
    couplingParametricKSupportFamilyActivity coupling 1 6 family ≈
      outwardCentralPathActivity coupling

/- The algebraic profile of the three-cycle after inserting an edge carrying
the already-derived common activity.  The structure above is the live search
interface whose inhabitant would realize this edge by an actual family. -/
def outwardEqualActivityThreeCycleProfile
    (coupling : Q') (pattern : ThreeBlockPattern) : Q' :=
  outwardCentralSmallLiftTwoEdgeProfile coupling pattern +
    outwardSignedDirectedPatternEdge
      (outwardCentralPathActivity coupling)
      (true, false, false) (true, true, true) pattern

theorem outwardEqualActivityThreeCycleProfile_000_eqv_zero
    (coupling : Q') :
    outwardEqualActivityThreeCycleProfile coupling
        (false, false, false) ≈ 0 := by
  unfold outwardEqualActivityThreeCycleProfile
  unfold outwardSignedDirectedPatternEdge
  rw [if_neg (by simp), if_neg (by simp)]
  exact Q'.eqv_trans _
    (outwardCentralSmallLiftTwoEdgeProfile coupling
      (false, false, false) + 0) _
    (Q'.eqv_refl _)
    (Q'.eqv_trans _
      (outwardCentralSmallLiftTwoEdgeProfile coupling
        (false, false, false)) _
      (Q'.eqv_of_eq (Q'.add_zero' _))
      (outwardCentralSmallLiftTwoEdgeProfile_000_eqv_zero coupling))

theorem outwardEqualActivityThreeCycleProfile_100_eqv_zero
    (coupling : Q') :
    outwardEqualActivityThreeCycleProfile coupling
        (true, false, false) ≈ 0 := by
  unfold outwardEqualActivityThreeCycleProfile
  unfold outwardSignedDirectedPatternEdge
  rw [if_pos rfl]
  refine Q'.eqv_trans _
    (-(outwardSmallLiftPathActivity coupling) +
      outwardCentralPathActivity coupling) _
    (Q'.add_eqv_congr'
      (outwardCentralSmallLiftTwoEdgeProfile_100_eqv_neg_activity coupling)
      (Q'.eqv_refl _)) ?_
  exact neg_add_eqv_zero_of_eqv
    (Q'.eqv_symm
      (outwardCentral_smallLift_singletonFamilyActivities_eqv coupling))

theorem outwardEqualActivityThreeCycleProfile_111_eqv_zero
    (coupling : Q') :
    outwardEqualActivityThreeCycleProfile coupling
        (true, true, true) ≈ 0 := by
  unfold outwardEqualActivityThreeCycleProfile
  unfold outwardSignedDirectedPatternEdge
  rw [if_neg (by simp), if_pos rfl]
  refine Q'.eqv_trans _
    (outwardCentralPathActivity coupling +
      -(outwardCentralPathActivity coupling)) _
    (Q'.add_eqv_congr'
      (outwardCentralSmallLiftTwoEdgeProfile_111_eqv_activity coupling)
      (Q'.eqv_refl _)) ?_
  exact Q'.add_neg_self_eqv _

#print axioms outwardCentralSmallLiftTwoEdgeProfile_000_eqv_zero
#print axioms outwardCentralSmallLiftTwoEdgeProfile_111_eqv_activity
#print axioms outwardCentralSmallLiftTwoEdgeProfile_100_eqv_neg_activity
#print axioms outwardCentralSmallLift_endpointDebt_eqv_zero
#print axioms outwardEqualActivityThreeCycleProfile_000_eqv_zero
#print axioms outwardEqualActivityThreeCycleProfile_100_eqv_zero
#print axioms outwardEqualActivityThreeCycleProfile_111_eqv_zero

end YMGap.Continuum.Z4OutwardCentralSmallLiftSignedPath
