/-
# Constructed six-face cost bound for the original local Ward score

There are at most six incident faces at a four-dimensional link. Their
actual value/derivative certificates yield explicit caps for A and D A,
independent of cutoff and extent at fixed strict nome. The score remains
S = A Dg + 2(D A)g, and its normalized square uses the FULL weight R*A.

These caps are deliberately conservative and nome-dependent. A useful
response floor, control as the nome approaches one, and the changing-spacing
energy/variance comparison remain open. No continuum claim is made.
-/

import YMGap.Continuum.QuaternionHaarAngularProductList
import YMGap.Continuum.BF4ExactSlabHeatAngularInterval
import YMGap.Continuum.BF4ExactSlabLocalWardVariance
import YMGap.Continuum.QuaternionHaarIntervalSecondMoment

namespace YMGap.Continuum.BF4ExactSlabLocalWardScoreBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabHeatAngularInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalHaarWard
open YMGap.Continuum.BF4ExactSlabLocalWardVariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarIntervalSecondMoment
open YMGap.Continuum.QuaternionHaarAngularProductBounds
open YMGap.Continuum.QuaternionHaarAngularProductList
open YMGap.Continuum.AngularProductBudget
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

/-- The added one makes the list budgets monotone, including empty stars. -/
def faceValueCap (w : Q') : Q' := prefixCap w + 1

theorem one_le_faceValueCap {w : Q'} (hw0 : (0 : Q') < w) : (1 : Q') ≤ faceValueCap w :=
  Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 (prefixCap w) (prefixCap_nonnegative hw0))
    (Q'.le_of_eqv (Q'.add_comm_eqv 1 (prefixCap w)))

theorem faceAngularCap_nonnegative {w : Q'} (hw0 : (0 : Q') < w) : (0 : Q') ≤ faceAngularCap w :=
  Q'.mul_nonneg _ _ (by decide) (SU2HeatQuarticPrefixBound.prefixBudget_nonnegative hw0)

/-- Six-factor value cap, with no lattice extent or cutoff parameter. -/
def incidentValueCap (w : Q') : Q' := valueBudget (faceValueCap w) 6

/-- Six-factor derivative cap, with its nome dependence exposed. -/
def incidentDerivativeCap (w : Q') : Q' := derivativeBudget (faceValueCap w) (faceAngularCap w) 6

/-- Actual incident product and its actual selected-link angular derivative. -/
def incidentAngularBound {i j : Nat} (hi : i < 4) (hj : j < 4)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent) :
    AngularBound (blocks extent) i j
      (reindexQuaternionPolynomial (linkHeadSwap extent link hl) (incidentHeat w K extent link))
      (incidentValueCap w) (incidentDerivativeCap w) := by
  have hb : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  let P := reindexedProductBound hb hi hj (linkHeadSwap extent link hl)
    (faceHeatPolynomial w K extent) (faceValueCap w) (faceAngularCap w) (incidentIds extent link)
    (fun id hid =>
      ⟨(intervalReindex (linkHeadSwap extent link hl)
          (facePrefixInterval hw0 hw1 K extent id (incidentIds_physical hid))).raise 1 Q'.zero_le_one,
        selectedFaceHeatAngularInterval hi hj hw0 hw1 K extent link hl id (incidentIds_physical hid)⟩)
  exact P.weaken (value_le (one_le_faceValueCap hw0) (incidentIds_length_le_six extent link))
    (derivative_le (one_le_faceValueCap hw0) (faceAngularCap_nonnegative hw0)
      (incidentIds_length_le_six extent link))

/-- Explicit cap for S=A Dg+2(D A)g from caps G and DG of the SAME test g. -/
def wardScoreCap (w G DG : Q') : Q' :=
  incidentValueCap w * DG + 2 * (incidentDerivativeCap w * G)

variable (w : Q') (K extent : Nat) (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "swap" => linkHeadSwap extent link hl
local notation "A" => reindexQuaternionPolynomial swap (incidentHeat w K extent link)
local notation "R" => reindexQuaternionPolynomial swap (complementHeat w K extent link)
local notation "W" => polyMul R A

/-- Constructed score interval; shared variables and the original action stay intact. -/
def localScoreInterval (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {i j : Nat} (hi : i < 4) (hj : j < 4) {g : RatPoly} {G DG : Q'}
    (P : AngularBound (blocks extent) i j g G DG) :
    Interval (blocks extent) (localScore w K extent link hl i j g) (wardScoreCap w G DG) := by
  let B := incidentAngularBound hi hj hw0 hw1 K extent link hl
  exact (B.value.mul P.derivative).add ((B.derivative.mul P.value).smul 2 (by decide))

/-- Normalized full-action score cost. Positivity and partition are constructed
at the stated late cutoff, not supplied as a substitute probability law. -/
theorem normalizedScoreSquare_le (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hK : headCutoff w ≤ K) {i j : Nat} (hi : i < 4) (hj : j < 4)
    {g : RatPoly} {G DG : Q'} (P : AngularBound (blocks extent) i j g G DG) :
    normalizedMoment (blocks extent) W
      (polyMul (localScore w K extent link hl i j g) (localScore w K extent link hl i j g))
      (framePartition_positive w K extent link hl hw0 hw1 hK) ≤
      wardScoreCap w G DG * wardScoreCap w G DG :=
  Interval.normalized_square_le
    (Interval.squareBound (localScoreInterval w K extent link hl hw0 hw1 hi hj P))
    (frameWeight_certificate w K extent link hl hw0 hw1 hK)
    (framePartition_positive w K extent link hl hw0 hw1 hK)

/-- The actual normalized response versus the actual signed-observable variance,
now with its score cost bounded explicitly. Independence of cutoff/extent
requires fixed test caps G,DG, as supplied by the coordinate test below. -/
theorem normalizedResponse_squared_le_variance_cap
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hK : headCutoff w ≤ K)
    {i j : Nat} (hi : i < 4) (hj : j < 4) {g : RatPoly} {G DG : Q'}
    (P : AngularBound (blocks extent) i j g G DG) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (blocks extent) f) :
    normalizedResponse w K extent link hl hw0 hw1 hK i j g f *
      normalizedResponse w K extent link hl hw0 hw1 hK i j g f ≤
    normalizedVariance (blocks extent) W f (framePartition_positive w K extent link hl hw0 hw1 hK) *
      (wardScoreCap w G DG * wardScoreCap w G DG) :=
  Q'.le_trans' _ _ _
    (normalizedResponse_squared_le_variance_cost w K extent link hl hw0 hw1 hK hi hj g f P.value.support hf)
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (normalizedScoreSquare_le w K extent link hl hw0 hw1 hK hi hj P)
      (normalizedVariance_nonnegative (frameWeight_certificate w K extent link hl hw0 hw1 hK)
        (framePartition_positive w K extent link hl hw0 hw1 hK) hf))

/-- Concrete coordinate tests supply their own caps (1,2); no test-bound assumption. -/
def coordinateLocalScoreInterval (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {i j coordinate : Nat} (hi : i < 4) (hj : j < 4) (hc : coordinate < 4*blocks extent) :
    Interval (blocks extent) (localScore w K extent link hl i j (polyVar coordinate)) (wardScoreCap w 1 2) :=
  localScoreInterval w K extent link hl hw0 hw1 hi hj (AngularBound.coordinate
    (Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)) hi hj hc)

end YMGap.Continuum.BF4ExactSlabLocalWardScoreBound

#print axioms YMGap.Continuum.BF4ExactSlabLocalWardScoreBound.one_le_faceValueCap
#print axioms YMGap.Continuum.BF4ExactSlabLocalWardScoreBound.faceAngularCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabLocalWardScoreBound.incidentAngularBound
#print axioms YMGap.Continuum.BF4ExactSlabLocalWardScoreBound.localScoreInterval
#print axioms YMGap.Continuum.BF4ExactSlabLocalWardScoreBound.normalizedScoreSquare_le
#print axioms YMGap.Continuum.BF4ExactSlabLocalWardScoreBound.normalizedResponse_squared_le_variance_cap
#print axioms YMGap.Continuum.BF4ExactSlabLocalWardScoreBound.coordinateLocalScoreInterval
