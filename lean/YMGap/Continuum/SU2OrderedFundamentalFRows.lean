/-
# Fixed-output rows of the ordered fundamental associator

This successor extracts the four raw rational entries of the all-label
ordered associator for three fundamental external degrees and final degree
one.  The calculation uses only the certified Hahn synthesis and raw
transvectant analysis.
-/

import YMGap.Continuum.SU2OrderedAssociatorCoordinateBases
import YMGap.Continuum.SU2OrderedDirectRightIdentification
import YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
import YMGap.Continuum.SixJKernel

namespace YMGap.Continuum.SU2OrderedFundamentalFRows

open YMGap.Constructive
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.SU2OrderedAssociatorCoordinateBases
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2OrderedDirectRightIdentification
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SixJKernel

local infix:50 " ≈ " => Q'.eqv

/-- The fixed-final-degree-one singlet channel. -/
def fundamentalSingletChannel : LeftNestedCGChannel 1 1 1 where
  k := 1
  k_le := by decide
  outer :=
    { k := 0
      k_le := by decide
      s := 0
      s_le := by decide }

/-- The fixed-final-degree-one triplet channel. -/
def fundamentalTripletChannel : LeftNestedCGChannel 1 1 1 where
  k := 0
  k_le := by decide
  outer :=
    { k := 1
      k_le := by decide
      s := 0
      s_le := by decide }

/-- A literal one-hot all-label coordinate vector. -/
def channelDelta (center q : LeftNestedCGChannel 1 1 1) : Q' :=
  if q.k = center.k ∧ q.outer.k = center.outer.k ∧
      q.outer.s = center.outer.s then 1 else 0

def singletInput : LeftNestedCGChannel 1 1 1 → Q' :=
  channelDelta fundamentalSingletChannel

def tripletInput : LeftNestedCGChannel 1 1 1 → Q' :=
  channelDelta fundamentalTripletChannel

/-- The two fixed-final-degree-one left channels, in singlet/triplet order. -/
def fundamentalFixedLeftSinglet : FixedLeftCGChannel 1 1 1 1 where
  k := 1
  k_le := by decide
  r := 0
  r_le := by decide
  degree_eq := by decide

def fundamentalFixedLeftTriplet : FixedLeftCGChannel 1 1 1 1 where
  k := 0
  k_le := by decide
  r := 1
  r_le := by decide
  degree_eq := by decide

/-- The two fixed-final-degree-one right channels, in singlet/triplet order. -/
def fundamentalFixedRightSinglet : FixedRightCGChannel 1 1 1 1 where
  p := 1
  p_le := by decide
  r := 0
  r_le := by decide
  degree_eq := by decide

def fundamentalFixedRightTriplet : FixedRightCGChannel 1 1 1 1 where
  p := 0
  p_le := by decide
  r := 1
  r_le := by decide
  degree_eq := by decide

/-- The abstract all-label indices agree exactly with the fixed-output channel
enumeration at output coefficient zero. -/
theorem fundamentalFixedChannels_match :
    fixedLeftNestedChannel fundamentalFixedLeftSinglet 0 (by decide) =
        fundamentalSingletChannel ∧
    fixedLeftNestedChannel fundamentalFixedLeftTriplet 0 (by decide) =
        fundamentalTripletChannel ∧
    fixedRightOrderedChannel fundamentalFixedRightSinglet 0 (by decide) =
        fundamentalSingletChannel ∧
    fixedRightOrderedChannel fundamentalFixedRightTriplet 0 (by decide) =
        fundamentalTripletChannel := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def fundamentalHalf : Q' := Q'.mkPos 1 2 (by decide)
def fundamentalThreeHalves : Q' := Q'.mkPos 3 2 (by decide)

/-- **The four fixed-ordered fundamental F entries, computed from the actual
Hahn synthesis followed by raw ordered transvectant analysis.**

Rows are input channels and columns are output channels.  This is the
transpose convention to the vector-action matrix used elsewhere. -/
theorem orderedFundamentalF_entries :
    orderedAllLabelAssociator 1 1 1 singletInput
        fundamentalSingletChannel ≈ -fundamentalHalf ∧
    orderedAllLabelAssociator 1 1 1 singletInput
        fundamentalTripletChannel ≈ fundamentalThreeHalves ∧
    orderedAllLabelAssociator 1 1 1 tripletInput
        fundamentalSingletChannel ≈ fundamentalHalf ∧
    orderedAllLabelAssociator 1 1 1 tripletInput
        fundamentalTripletChannel ≈ fundamentalHalf := by
  decide

/-- The gauge-invariant diagonal triplet kernel extracted from the actual
fixed-ordered associator. -/
def orderedFundamentalTripletKernel : Q' :=
  let f := orderedAllLabelAssociator 1 1 1 tripletInput
    fundamentalTripletChannel
  f * f

/-- The ordered raw associator derives the fractional `1/4` kernel pin. -/
theorem orderedFundamentalTripletKernel_eq_oneQuarter :
    orderedFundamentalTripletKernel ≈ oneQuarter := by
  decide

/-- The derived ordered-associator pin agrees with the physical factorial
Racah kernel interface used by `PentagonNumericCore`. -/
theorem orderedFundamentalTripletKernel_eq_racahSmallest :
    orderedFundamentalTripletKernel ≈ racahKernelQ smallestTetra := by
  exact Q'.eqv_trans _ _ _ orderedFundamentalTripletKernel_eq_oneQuarter
    (Q'.eqv_symm racahKernelQ_smallest)

end YMGap.Continuum.SU2OrderedFundamentalFRows

#print axioms YMGap.Continuum.SU2OrderedFundamentalFRows.fundamentalFixedChannels_match
#print axioms YMGap.Continuum.SU2OrderedFundamentalFRows.orderedFundamentalF_entries
#print axioms YMGap.Continuum.SU2OrderedFundamentalFRows.orderedFundamentalTripletKernel_eq_oneQuarter
#print axioms YMGap.Continuum.SU2OrderedFundamentalFRows.orderedFundamentalTripletKernel_eq_racahSmallest
