/-
# Retain the reciprocal-weighted source budget of the ACTUAL seed family

For nu the full original odd marginal, M_i=P_i(nu), J_i,k the actual
finite reciprocal polynomial, and tau_i the actual centered Haar piece,
retain B_I=sum_{i in I} H[M_i*J_i,k*tau_i^2]. Then

  sum_{i in I} ||q_i||_nu^2 <= B_I,
  ell*B_I <= sum_{i in I} H[tau_i^2].

Thus this is a refinement of the global lower-window estimate, not a new
assumed budget or a reciprocal limit. The original fringe cost and diagonal
cost are bounded by these actual finite quantities. Their regulator-uniform
comparison with the target norm remains open. All full-density, source,
seed-degree and physical-parameter dependence is retained.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedReciprocalNorm
import YMGap.Continuum.BF4ExactSlabFixedSpatialSeedNormBudget

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalSourceBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight marginalPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow (lower)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed (inverse)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedReciprocalNorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope (piece piece_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily (familyTests familyTests_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure (labels labels_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost (corrected diagonalRemainder)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeedNormBudget (corrected_norm_le diagonal_norm_sum_le)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headCutoff)
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound (headFloor_le_oneThirtySecond)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap majorant_prefix_bound)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential (qListSum)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project)
open YMGap.Continuum.QuaternionHaarFamilySquare (qListSum_scale)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks

private theorem sum_le {A : Type} (ids : List A) (f g : A → Q')
    (h : ∀ i, i ∈ ids → f i ≤ g i) : qListSum (ids.map f) ≤ qListSum (ids.map g) := by
  revert h
  induction ids with
  | nil => intro _; exact Q'.le_refl' _
  | cons i ids ih =>
      intro h
      exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ (h i List.mem_cons_self))
        (Q'.add_le_add_left _ _ _ (ih (fun j hj => h j (List.mem_cons_of_mem i hj))))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

/-- A computed finite rational budget, retaining the original reciprocal
polynomials instead of replacing the density by its global minimum. -/
def sourceCost (ids : List Nat) (k : Nat) (f : RatPoly) : Q' :=
  qListSum (ids.map (fun i => quaternionHaar (N width)
    (polyMul (polyMul (project i (marginalWeight w K width n))
      (inverse hw0 hw1 K width hK n i k))
      (polyMul (piece w K width n i f) (piece w K width n i f)))))

/-- Any supplied coordinate list, including the original fringe, has its
actual norm sum controlled without the global lower-window factor. -/
theorem family_norm_le_sourceCost (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < N width) (k : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    let qs := familyTests hw0 hw1 K width hK n k f
    qListSum (ids.map (fun i => marginalPair w K width n (qs i) (qs i))) ≤
      sourceCost hw0 hw1 K width hK n ids k f := by
  apply sum_le
  intro i hi
  exact test_norm_le_reciprocal_source hw0 hw1 K width hK n i (hids i hi) k
    (piece_supported w K width n i hf)

/-- The retained budget is provably no worse than the previous per-piece
global-window estimate; no reciprocal limit is taken. -/
theorem sourceCost_scaled_le_pieceSquares (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < N width) (k : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    lower w K width n * sourceCost hw0 hw1 K width hK n ids k f ≤
      qListSum (ids.map (fun i => quaternionHaar (N width)
        (polyMul (piece w K width n i f) (piece w K width n i f)))) := by
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qListSum_scale ids
    (fun i => quaternionHaar (N width)
      (polyMul (polyMul (project i (marginalWeight w K width n))
        (inverse hw0 hw1 K width hK n i k))
        (polyMul (piece w K width n i f) (piece w K width n i f))))
    (lower w K width n)))
    (sum_le _ _ _ (fun i hi => reciprocal_source_le_scaled_square
      hw0 hw1 K width hK n i (hids i hi) k (piece_supported w K width n i hf)))

/-- Arbitrary second-stage correction degrees preserve this sharper
original-marginal budget on the very same finite family. -/
theorem corrected_family_norm_le_sourceCost (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < N width) (k : Nat) (degrees : Nat → Nat)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    let qs := familyTests hw0 hw1 K width hK n k f
    let cs := corrected hw0 hw1 K width hK n qs degrees
    qListSum (ids.map (fun i => marginalPair w K width n (cs i) (cs i))) ≤
      sourceCost hw0 hw1 K width hK n ids k f := by
  exact Q'.le_trans' _ _ _
    (sum_le ids _ _ (fun i _ => corrected_norm_le hw0 hw1 K width hK n
      (familyTests hw0 hw1 K width hK n k f) degrees i
      (familyTests_supported hw0 hw1 K width hK n k i hf)))
    (family_norm_le_sourceCost hw0 hw1 K width hK n ids hids k hf)

/-- Upper control of the unavoidable fringe term identified by the joint
cost lower bound. This is not a uniform target-norm estimate. -/
theorem fringe_cost_le_sourceCost (k : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    let qs := familyTests hw0 hw1 K width hK n k f
    ((1 : Q') + -(headFloor w)) * qListSum ((fringeBlocks width).map
      (fun i => marginalPair w K width n (qs i) (qs i))) ≤
      ((1 : Q') + -(headFloor w)) * sourceCost hw0 hw1 K width hK n (fringeBlocks width) k f :=
  Q'.mul_le_mul_of_nonneg_left _ _ _
    (family_norm_le_sourceCost hw0 hw1 K width hK n (fringeBlocks width) (fringeBlocks_lt width) k hf)
    (Q'.sub_nonneg_of_le (Q'.le_trans' _ _ _ (headFloor_le_oneThirtySecond hw0 hw1) (by decide)))

/-- The existing diagonal-cost consumer now uses the retained reciprocal
source sum, with no premature replacement by u/ell. The signed active
determinant remainder still needs a joint upper estimate. -/
theorem diagonal_cost_le_sourceCost (k : Nat) (degrees : Nat → Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    diagonalRemainder hw0 hw1 K width hK n (familyTests hw0 hw1 K width hK n k f) degrees ≤
      (prefixCap w + -(headFloor w)) * sourceCost hw0 hw1 K width hK n (labels width) k f := by
  have hU := majorant_prefix_bound hw0 hw1 1
  change (1 : Q') ≤ prefixCap w at hU
  have hc : (0 : Q') ≤ prefixCap w + -(headFloor w) := Q'.sub_nonneg_of_le
    (Q'.le_trans' _ _ _ (headFloor_le_oneThirtySecond hw0 hw1)
      (Q'.le_trans' _ _ _ (by decide) hU))
  exact Q'.le_trans' _ _ _
    (diagonal_norm_sum_le hw0 hw1 K width hK n (familyTests hw0 hw1 K width hK n k f) degrees
      (fun i _ => familyTests_supported hw0 hw1 K width hK n k i hf))
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (corrected_family_norm_le_sourceCost hw0 hw1 K width hK n (labels width) (labels_lt width) k degrees hf) hc)

end YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalSourceBudget

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalSourceBudget.sourceCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalSourceBudget.family_norm_le_sourceCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalSourceBudget.sourceCost_scaled_le_pieceSquares
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalSourceBudget.corrected_family_norm_le_sourceCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalSourceBudget.fringe_cost_le_sourceCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalSourceBudget.diagonal_cost_le_sourceCost
