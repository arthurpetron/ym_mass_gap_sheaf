/-
# Arbitrary fixed-output ordered F coefficients and the Racah bridge

For proof-carrying left and right channels with common final degree, the raw
ordered F coefficient is defined directly by the certified all-label
associator.  It is then exposed as one finite projected outer transvectant of
one finite Hahn reconstruction.  The comparison with the squared Racah
kernel is kept in its correct cross-multiplied normalization:

  dim(f) * P(a,b,c,d,e,f) = dim(e) * F_raw(e,f)^2.

No positivity, stochasticity, or Dougall summation is assumed.
-/

import YMGap.Continuum.SU2OrderedFundamentalFRows

namespace YMGap.Continuum.SU2OrderedFixedOutputFKernel

open YMGap.Constructive
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection
open YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases
open YMGap.Continuum.SU2GeneralHahnAssociatorCoordinateBases
open YMGap.Continuum.SU2OrderedAssociatorCoordinateBases
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2OrderedDirectRightIdentification
open YMGap.Continuum.SU2OrderedFundamentalFRows
open YMGap.Continuum.PentagonFromCoordinateBases
open YMGap.Continuum.SixJKernel

local infix:50 " ≈ " => Q'.eqv

/-- One-hot all-label data for a fixed-output left channel at output
coefficient zero. -/
def fixedLeftCoordinateDelta {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) :
    LeftNestedCGChannel a b c → Q' :=
  fun u => if u.k = q.k ∧ u.outer.k = q.r ∧ u.outer.s = 0 then 1 else 0

/-- The raw ordered F coefficient between arbitrary proof-carrying fixed-output
channels. -/
def fixedOrderedFCoefficient {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) : Q' :=
  orderedAllLabelAssociator a b c (fixedLeftCoordinateDelta qL)
    (fixedRightOrderedChannel qR 0 (Nat.zero_le d))

/-- The arbitrary fixed-output F coefficient is the corresponding direct-right
coordinate of the finite left Hahn reconstruction. -/
theorem fixedOrderedFCoefficient_eq_directCoordinate {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    fixedOrderedFCoefficient qL qR ≈
      directRightNestedCoordinates a b c
        (leftNestedReconstruct a b c (fixedLeftCoordinateDelta qL))
        (fixedRightNestedChannel qR 0 (Nat.zero_le d)) := by
  have h := orderedRightNestedCoordinates_eq_direct a b c
    (leftNestedReconstruct a b c (fixedLeftCoordinateDelta qL))
    (fixedRightOrderedChannel qR 0 (Nat.zero_le d))
  simpa only [fixedOrderedFCoefficient, orderedAllLabelAssociator,
    basisChange, orderedAssociatorCoordinateBases] using h

/-- **Finite exact transvectant/Hahn expression for every ordered F entry.**
The inner semantic vector is the explicit three-level Hahn reconstruction;
the output is one projected raw transvectant after the finite last-pair
transformation. -/
theorem fixedOrderedFCoefficient_eq_transvectantHahn {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    fixedOrderedFCoefficient qL qR ≈
      transvect a (b + c - 2 * qR.p) qR.r
        (rectProject a (b + c - 2 * qR.p)
          (lastPairOutput b c
            (leftNestedReconstruct a b c (fixedLeftCoordinateDelta qL))
            qR.p)) 0 := by
  exact Q'.eqv_trans _ _ _
    (fixedOrderedFCoefficient_eq_directCoordinate qL qR)
    (Q'.eqv_refl _)

/-- Every raw ordered F-entry square is nonnegative.  This is not a claim
that the unnormalized entry itself is a probability. -/
theorem fixedOrderedFCoefficient_square_nonneg {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    (0 : Q') ≤ fixedOrderedFCoefficient qL qR *
      fixedOrderedFCoefficient qL qR :=
  qMulSelf_nonneg (fixedOrderedFCoefficient qL qR)

/-- Correct dimension-weighted comparison between one raw ordered F entry
and the factorial squared Racah kernel.  It is division-free and therefore
constructive over `Q'`. -/
def FixedOrderedRacahBridgeAt {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) : Prop :=
  Q'.ofNat (dimRep qR.intermediate) *
      racahKernel6 a b c d qL.intermediate qR.intermediate ≈
    Q'.ofNat (dimRep qL.intermediate) *
      (fixedOrderedFCoefficient qL qR * fixedOrderedFCoefficient qL qR)

/-- The exact all-label normalization compatibility whose general proof would
identify the coordinate-basis F entries with the factorial Racah formula.
This definition is an interface, not an assumed hypothesis. -/
def FixedOrderedRacahCompatibility (a b c d : Nat) : Prop :=
  ∀ (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d),
    FixedOrderedRacahBridgeAt qL qR

/-- The general compatibility interface is already machine-verified on the
entire fundamental 2-by-2 block, with all Gram multiplicities included. -/
theorem fundamental_fixedOrderedRacahBridge :
    FixedOrderedRacahBridgeAt fundamentalFixedLeftSinglet
        fundamentalFixedRightSinglet ∧
    FixedOrderedRacahBridgeAt fundamentalFixedLeftSinglet
        fundamentalFixedRightTriplet ∧
    FixedOrderedRacahBridgeAt fundamentalFixedLeftTriplet
        fundamentalFixedRightSinglet ∧
    FixedOrderedRacahBridgeAt fundamentalFixedLeftTriplet
        fundamentalFixedRightTriplet := by
  unfold FixedOrderedRacahBridgeAt
  decide

/-- In particular, the physical smallest-tetrahedron triplet/triplet entry is
the derived ordered associator square `1/4`, with equal source/target Gram
multiplicities `3`. -/
theorem fundamental_triplet_bridge_explicit :
    Q'.ofNat 3 * racahKernel6 1 1 1 1 2 2 ≈
      Q'.ofNat 3 *
        (fixedOrderedFCoefficient fundamentalFixedLeftTriplet
          fundamentalFixedRightTriplet *
         fixedOrderedFCoefficient fundamentalFixedLeftTriplet
          fundamentalFixedRightTriplet) := by
  exact fundamental_fixedOrderedRacahBridge.2.2.2

end YMGap.Continuum.SU2OrderedFixedOutputFKernel

#print axioms YMGap.Continuum.SU2OrderedFixedOutputFKernel.fixedOrderedFCoefficient_eq_directCoordinate
#print axioms YMGap.Continuum.SU2OrderedFixedOutputFKernel.fixedOrderedFCoefficient_eq_transvectantHahn
#print axioms YMGap.Continuum.SU2OrderedFixedOutputFKernel.fixedOrderedFCoefficient_square_nonneg
#print axioms YMGap.Continuum.SU2OrderedFixedOutputFKernel.fundamental_fixedOrderedRacahBridge
#print axioms YMGap.Continuum.SU2OrderedFixedOutputFKernel.fundamental_triplet_bridge_explicit
