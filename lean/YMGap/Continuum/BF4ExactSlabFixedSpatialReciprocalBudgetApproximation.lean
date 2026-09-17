/-
# The retained source budget tracks the actual family norm at late degrees

For the original finite marginal and its existing source pieces, the
retained reciprocal-source budget differs from the ACTUAL norm sum by a
nonnegative error with an explicit geometric modulus. A constructed seed
degree satisfies both this cost tolerance and the original approximation
tolerance; the correction degree is then recomputed from those very seeds.

This enables a finite source-pinned test of the proposed uniform budget.
It asserts no regulator uniformity, width growth, monotonicity in degree,
signed active-cost estimate, or continuum/physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedBudgetError
import YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalSourceBudget
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFamilyApproximation

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalBudgetApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight marginalPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed (rate rate_nonnegative rate_lt_one)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedBudgetError
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope (piece piece_supported piece_centered)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily (familyTests)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalSourceBudget (sourceCost family_norm_le_sourceCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFamilyApproximation
  (error approximationDegreesAfter approximationDegreesAfter_seedFloor_le approximation_bound_after)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential (qListSum)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.QuaternionHaarFamilySquare (qListSum_add qListSum_scale)

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

private theorem sum_nonnegative {A : Type} (ids : List A) (f : A → Q')
    (h : ∀ i, i ∈ ids → (0 : Q') ≤ f i) : (0 : Q') ≤ qListSum (ids.map f) := by
  revert h
  induction ids with
  | nil => intro _; exact Q'.le_refl' _
  | cons i ids ih =>
      intro h
      exact Q'.zero_le_add _ _ (h i List.mem_cons_self)
        (ih (fun j hj => h j (List.mem_cons_of_mem i hj)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

/-- The original uncorrected test norms, on exactly the supplied indices. -/
def normSum (ids : List Nat) (k : Nat) (f : RatPoly) : Q' :=
  qListSum (ids.map (fun i => marginalPair w K width n
    (familyTests hw0 hw1 K width hK n k f i) (familyTests hw0 hw1 K width hK n k f i)))

/-- The finite error constant depends on the original source and regulators,
not on the approximation degree. It is not a physical decay constant. -/
def gapPrefactor (ids : List Nat) (f : RatPoly) : Q' :=
  qListSum (ids.map (fun i => errorPrefactor hw0 hw1 K width hK n (piece w K width n i f)))

theorem gapPrefactor_nonnegative (ids : List Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    (0 : Q') ≤ gapPrefactor hw0 hw1 K width hK n ids f :=
  sum_nonnegative _ _ (fun i _ => errorPrefactor_nonnegative hw0 hw1 K width hK n
    (piece_supported w K width n i hf))

/-- The old upper estimate is nonnegative above the actual norm sum. -/
theorem normSum_le_sourceCost (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < N width) (k : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    normSum hw0 hw1 K width hK n ids k f ≤ sourceCost hw0 hw1 K width hK n ids k f :=
  family_norm_le_sourceCost hw0 hw1 K width hK n ids hids k hf

/-- The ACTUAL finite family, not an ideal reciprocal limit, supplies the
reverse comparison up to a vanishing geometric error. -/
theorem sourceCost_le_normSum_add_geometric (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < N width) (k : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    sourceCost hw0 hw1 K width hK n ids k f ≤ normSum hw0 hw1 K width hK n ids k f +
      (rate hw0 hw1 K width hK n)^k * gapPrefactor hw0 hw1 K width hK n ids f := by
  let norms := fun i => marginalPair w K width n
    (familyTests hw0 hw1 K width hK n k f i) (familyTests hw0 hw1 K width hK n k f i)
  let caps := fun i => errorPrefactor hw0 hw1 K width hK n (piece w K width n i f)
  have h := sum_le ids _ (fun i => norms i + (rate hw0 hw1 K width hK n)^k*caps i)
    (fun i hi => budget_le_norm_add_geometric hw0 hw1 K width hK n i (hids i hi) k
      (piece_supported w K width n i hf) (piece_centered w K width n i f))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (qListSum_add ids norms (fun i => (rate hw0 hw1 K width hK n)^k*caps i))
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (qListSum_scale ids caps _))))

/-- Explicit zero-safe tolerance degree for the original cost/norm comparison. -/
def gapCutoff (ids : List Nat) (f : RatPoly) (epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff (rate hw0 hw1 K width hK n)
    (gapPrefactor hw0 hw1 K width hK n ids f) epsilon

theorem sourceCost_le_normSum_add (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < N width) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (k : Nat) (hk : gapCutoff hw0 hw1 K width hK n ids f epsilon ≤ k) :
    sourceCost hw0 hw1 K width hK n ids k f ≤ normSum hw0 hw1 K width hK n ids k f + epsilon :=
  Q'.le_trans' _ _ _ (sourceCost_le_normSum_add_geometric hw0 hw1 K width hK n ids hids k hf)
    (Q'.add_le_add_left _ _ _ (PositiveContractionResidual.geometric_bound
      (rate_nonnegative hw0 hw1 K width hK n) (rate_lt_one hw0 hw1 K width hK n)
      (gapPrefactor_nonnegative hw0 hw1 K width hK n ids hf) hepsilon k hk))

/-- Increase the seed degree for the actual cost diagnostic, then recompute
the correction degree from those enlarged seeds. Both tolerances are explicit. -/
def coupledDegrees (ids : List Nat) (f : RatPoly) (approxTolerance costTolerance : Q') : Nat × Nat :=
  approximationDegreesAfter hw0 hw1 K width hK n
    (gapCutoff hw0 hw1 K width hK n ids f costTolerance) f approxTolerance

/-- One finite pair of degrees witnesses BOTH original-norm approximation
and sharpness of the retained budget. No regulator-uniform estimate is assumed. -/
def coupledCertificate (ids : List Nat) (hids : ∀ i, i ∈ ids → i < N width)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f)
    (approxTolerance costTolerance : Q')
    (ha : (0 : Q') < approxTolerance) (hc : (0 : Q') < costTolerance) :
    { d : Nat × Nat //
      quaternionHaar (N width) (polyMul (marginalWeight w K width n)
        (polyMul (error hw0 hw1 K width hK n d.1 d.2 f) (error hw0 hw1 K width hK n d.1 d.2 f))) ≤
        approxTolerance ∧
      sourceCost hw0 hw1 K width hK n ids d.1 f ≤
        normSum hw0 hw1 K width hK n ids d.1 f + costTolerance } :=
  ⟨coupledDegrees hw0 hw1 K width hK n ids f approxTolerance costTolerance,
    approximation_bound_after hw0 hw1 K width hK n _ hf approxTolerance ha,
    sourceCost_le_normSum_add hw0 hw1 K width hK n ids hids hf costTolerance hc _
      (approximationDegreesAfter_seedFloor_le hw0 hw1 K width hK n _ f approxTolerance)⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalBudgetApproximation

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalBudgetApproximation.normSum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalBudgetApproximation.gapPrefactor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalBudgetApproximation.gapPrefactor_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalBudgetApproximation.normSum_le_sourceCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalBudgetApproximation.sourceCost_le_normSum_add_geometric
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalBudgetApproximation.gapCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalBudgetApproximation.sourceCost_le_normSum_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalBudgetApproximation.coupledDegrees
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReciprocalBudgetApproximation.coupledCertificate
