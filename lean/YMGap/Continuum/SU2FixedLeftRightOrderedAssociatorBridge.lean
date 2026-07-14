/-
# Bridge from concrete fixed-output Schur rows to the physical ordered associator

The concrete Schur coefficient is identified with a genuine matrix entry of
the fixed-ordered coordinate-basis associator.  This is deliberately kept in
the raw transvectant normalization: the separate Gram-weighted square is what
interfaces with the dimension-absorbed Racah probability kernel.
-/

import YMGap.Continuum.SU2FixedLeftRightAssociatorSchur
import YMGap.Continuum.SU2OrderedDirectRightIdentification
import YMGap.Continuum.SU2OrderedPentagonCoordinateBases
import YMGap.Continuum.SU2OrderedFixedOutputFKernel
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases
open YMGap.Continuum.SU2GeneralHahnAssociatorCoordinateBases
open YMGap.Continuum.SU2OrderedAssociatorCoordinateBases
open YMGap.Continuum.SU2DiagonalSchurUniqueness
open YMGap.Continuum.SU2ChannelSectionSchurReconstruction
open YMGap.Continuum.SU2ChannelAmbientSectionSchurReconstruction
open YMGap.Continuum.SU2OrderedDirectRightIdentification
open YMGap.Continuum.SU2OrderedPentagonCoordinateBases
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FixedLeftEvaluationLinearity
open YMGap.Continuum.SU2FixedLeftRightFinalDegreePropagation
open YMGap.Continuum.SU2FixedLeftRightAssociatorSchur
open YMGap.Continuum.SU2OrderedFundamentalFRows
open YMGap.Continuum.SU2OrderedFixedOutputFKernel
open YMGap.Continuum.SixJKernel
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.PentagonFromCoordinateBases

local infix:50 " ≈ " => Q'.eqv

/-- The ordered-right dependent coordinate vector selecting one fixed-output
channel and one output monomial. -/
def fixedRightOrderedBasisVector {a b c d : Nat}
    (qR : FixedRightCGChannel a b c d) (t : Nat) :
    LeftNestedCGChannel b c a → Q' :=
  fun q => fixedRightSectionData qR (mono t)
    ((orderedDirectChannelEquiv a b c).toFun q)

/-- Ordered synthesis of that basis vector is physically the direct fixed
right section used by the Schur construction. -/
theorem orderedRightBasisVector_synth_eq_fixedRightSection
    {a b c d : Nat} (qR : FixedRightCGChannel a b c d) (t : Nat) :
    PhysicalBoxEqv a b c
      (orderedRightNestedReconstruct a b c
        (fixedRightOrderedBasisVector qR t))
      (fixedRightSection qR (mono t)) := by
  apply directRightNestedCoordinates_ext
  intro u
  have hordered := directRightNestedCoordinates_eq_ordered a b c
    (orderedRightNestedReconstruct a b c
      (fixedRightOrderedBasisVector qR t)) u
  have hreconstruct := orderedRightNestedCoordinates_reconstruct a b c
    (fixedRightOrderedBasisVector qR t)
    ((orderedDirectChannelEquiv a b c).invFun u)
  have hroundtrip := (orderedDirectChannelEquiv a b c).right_inv u
  have hdata : fixedRightOrderedBasisVector qR t
        ((orderedDirectChannelEquiv a b c).invFun u) ≈
      fixedRightSectionData qR (mono t) u := by
    unfold fixedRightOrderedBasisVector
    rw [hroundtrip]
    exact Q'.eqv_refl _
  have hsection := directRightNestedCoordinates_reconstruct a b c
    (fixedRightSectionData qR (mono t)) u
  exact Q'.eqv_trans _ _ _ hordered
    (Q'.eqv_trans _ _ _ hreconstruct
      (Q'.eqv_trans _ _ _ hdata
        (Q'.eqv_symm (by
          simpa only [fixedRightSection] using hsection))))

/-- **The concrete diagonal Schur coefficient is an actual entry of the
inverse fixed-ordered all-label associator.** -/
theorem fixedLeftRightDiagonalCoeff_eq_orderedAssociatorInv
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) (s : Nat) (hs : s ≤ d) :
    fixedLeftRightDiagonalCoeff qL qR s ≈
      orderedAllLabelAssociatorInv a b c
        (fixedRightOrderedBasisVector qR s)
        (fixedLeftNestedChannel qL s hs) := by
  have hphysical := orderedRightBasisVector_synth_eq_fixedRightSection qR s
  have hcoordinate := leftNestedCoordinates_congr a b c
    (fixedRightSection qR (mono s))
    (orderedRightNestedReconstruct a b c
      (fixedRightOrderedBasisVector qR s))
    (fun i j l hi hj hl => Q'.eqv_symm (hphysical i j l hi hj hl))
    (fixedLeftNestedChannel qL s hs)
  unfold fixedLeftRightDiagonalCoeff fixedLeftAnalysis
  rw [dif_pos hs]
  simpa only [orderedAllLabelAssociatorInv, basisChange,
    orderedAssociatorCoordinateBases] using hcoordinate

/-- The raw ordered associator entry is independent of the output monomial
inside its irreducible final-degree window. -/
theorem fixedLeftRightDiagonalCoeff_constant
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) (s : Nat) (hs : s ≤ d) :
    fixedLeftRightDiagonalCoeff qL qR s ≈
      fixedLeftRightDiagonalCoeff qL qR 0 := by
  have hdiag := fixedLeft_fixedRightSection_hasDiagonalModel qL qR
  have hF := fixedLeft_fixedRightSection_loweringCovariant qL qR
  have hcov := diagonalModel_loweringCovariant d
    (ambientInduced (fixedLeftAnalysis qL) (fixedRightSection qR))
    (fixedLeftRightDiagonalCoeff qL qR) hdiag hF
  exact diagonal_coeff_constant d (fixedLeftRightDiagonalCoeff qL qR)
    hcov s (by omega)

/-- Every weight realization of the inverse ordered associator matrix entry
equals the exact Schur-row coefficient used by `rightChannelPrefix`. -/
theorem orderedAssociatorInv_entry_eq_schurCoeff
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) (s : Nat) (hs : s ≤ d) :
    orderedAllLabelAssociatorInv a b c
        (fixedRightOrderedBasisVector qR s)
        (fixedLeftNestedChannel qL s hs) ≈
      fixedLeftRightDiagonalCoeff qL qR 0 := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (fixedLeftRightDiagonalCoeff_eq_orderedAssociatorInv qL qR s hs))
    (fixedLeftRightDiagonalCoeff_constant qL qR s hs)

/-- The square of the physical raw associator entry is constructively
nonnegative.  No claim is made here that this raw square already has the
dimension/Gram normalization of `PentagonNumericCore.racahKernel`. -/
def fixedLeftRightRawKernel {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) : Q' :=
  fixedLeftRightDiagonalCoeff qL qR 0 *
    fixedLeftRightDiagonalCoeff qL qR 0

theorem fixedLeftRightRawKernel_nonneg
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    (0 : Q') ≤ fixedLeftRightRawKernel qL qR :=
  SumOfSquares.q_mul_self_nonneg (fixedLeftRightDiagonalCoeff qL qR 0)

/-! ## Normalization fence for the pinned squared kernel -/

/-- The four fundamental coefficients of the inverse ordered associator row
implemented by the Schur expansion.  The off-diagonal entries are transposed
relative to the forward `fixedOrderedFCoefficient` convention. -/
theorem fundamental_schurCoeff_entries :
    fixedLeftRightDiagonalCoeff fundamentalFixedLeftSinglet
        fundamentalFixedRightSinglet 0 ≈ -fundamentalHalf ∧
    fixedLeftRightDiagonalCoeff fundamentalFixedLeftSinglet
        fundamentalFixedRightTriplet 0 ≈ fundamentalHalf ∧
    fixedLeftRightDiagonalCoeff fundamentalFixedLeftTriplet
        fundamentalFixedRightSinglet 0 ≈ fundamentalThreeHalves ∧
    fixedLeftRightDiagonalCoeff fundamentalFixedLeftTriplet
        fundamentalFixedRightTriplet 0 ≈ fundamentalHalf := by
  decide

/-- **Machine-checked normalization obstruction.**  The raw Schur-row square
is not the dimension/Gram-normalized Racah probability at an off-diagonal
fundamental entry: `1/4 ≠ 3/4`.  Therefore the raw square must not be inserted
directly into `PentagonNumericCore.racahKernel`. -/
theorem fundamental_rawKernel_ne_racah_cross :
    ¬ (fixedLeftRightRawKernel fundamentalFixedLeftSinglet
          fundamentalFixedRightTriplet).eqv
        (racahKernel6 1 1 1 1 0 2) := by
  decide

/-- The same fence in the opposite off-diagonal direction is even sharper:
the inverse raw square is `9/4`, while the normalized kernel is `3/4`. -/
theorem fundamental_rawKernel_ne_racah_cross_transpose :
    ¬ (fixedLeftRightRawKernel fundamentalFixedLeftTriplet
          fundamentalFixedRightSinglet).eqv
        (racahKernel6 1 1 1 1 2 0) := by
  decide

/-- Correct division-free normalization for an inverse Schur row: left Gram
weight times the Racah probability equals right Gram weight times the inverse
raw entry square. -/
def InverseSchurGramRacahBridgeAt {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) : Prop :=
  triLeftChannelWeight a b c d qL.intermediate *
      racahKernel6 a b c d qL.intermediate qR.intermediate ≈
    triRightChannelWeight a b c d qR.intermediate *
      fixedLeftRightRawKernel qL qR

/-- The corrected inverse-row normalization is verified on the entire
fundamental block, including both off-diagonal fences above. -/
theorem fundamental_inverseSchur_gramRacahBridges :
    InverseSchurGramRacahBridgeAt fundamentalFixedLeftSinglet
        fundamentalFixedRightSinglet ∧
    InverseSchurGramRacahBridgeAt fundamentalFixedLeftSinglet
        fundamentalFixedRightTriplet ∧
    InverseSchurGramRacahBridgeAt fundamentalFixedLeftTriplet
        fundamentalFixedRightSinglet ∧
    InverseSchurGramRacahBridgeAt fundamentalFixedLeftTriplet
        fundamentalFixedRightTriplet := by
  unfold InverseSchurGramRacahBridgeAt
  decide

/-- At the pinned smallest tetrahedron the equal Gram weights cancel, so the
actual physical inverse-associator entry square itself is `1/4`. -/
theorem fundamental_triplet_rawKernel_eq_oneQuarter :
    fixedLeftRightRawKernel fundamentalFixedLeftTriplet
      fundamentalFixedRightTriplet ≈ oneQuarter := by
  decide

/-- Thus the actual ordered Schur/associator coefficient realizes the pinned
value of the faithful factorial `PentagonNumericCore` kernel at the smallest
tetrahedron, without identifying the raw square with that kernel elsewhere. -/
theorem fundamental_triplet_rawKernel_eq_racahSmallest :
    fixedLeftRightRawKernel fundamentalFixedLeftTriplet
      fundamentalFixedRightTriplet ≈ racahKernelQ smallestTetra := by
  exact Q'.eqv_trans _ _ _ fundamental_triplet_rawKernel_eq_oneQuarter
    (Q'.eqv_symm racahKernelQ_smallest)

end YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge

#print axioms YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge.orderedRightBasisVector_synth_eq_fixedRightSection
#print axioms YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge.fixedLeftRightDiagonalCoeff_eq_orderedAssociatorInv
#print axioms YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge.fixedLeftRightDiagonalCoeff_constant
#print axioms YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge.orderedAssociatorInv_entry_eq_schurCoeff
#print axioms YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge.fixedLeftRightRawKernel_nonneg
#print axioms YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge.fundamental_schurCoeff_entries
#print axioms YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge.fundamental_rawKernel_ne_racah_cross
#print axioms YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge.fundamental_rawKernel_ne_racah_cross_transpose
#print axioms YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge.fundamental_inverseSchur_gramRacahBridges
#print axioms YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge.fundamental_triplet_rawKernel_eq_racahSmallest
