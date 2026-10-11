/-
# ORIGINAL selected-Haar defect payment by the actual computed logarithm

Construct the OWN selected partition's positive unit window from the actual
normalized original-action floor, then consume the finite selected-Haar
coercivity theorem and the SAME scalar binary-log identification. The resulting
sound eventual order retains an explicit nome/count/tolerance cutoff as data.

Every original factor and retained assignment stays unchanged. Identity
normalization is not division by the conditional partition. This is an
absolute unnormalized conditional defect estimate at finite heat cutoff;
OLD-centered source-relative payment, scaling, survival and gap remain open.
-/

import YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarEntropyCoercivity
import YMGap.Continuum.BF4SelectedEntropyLogBound

namespace YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarLogCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (evalRatPoly polyMul)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds
  (normalizedFloor normalizedFloor_positive normalizedHeatProduct normalizedHeatProduct_bounds)
open YMGap.Continuum.SU2PointwiseHeatStrictFloor (finiteCutoff)
open YMGap.Continuum.SU2HeatJacobiOriginalCoercivity (coercivityCutoff)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject)
open YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder (familyProject_pointwise_lower_bound)
open YMGap.Continuum.QuaternionHaarFamilyFiniteEntropy (familyProject_upper_bound)
open YMGap.Continuum.RegularizedLogFiniteProductCoercivity (selectedCount)
open YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarEntropyCoercivity

private theorem finiteCutoff_le {q : Q'} {K : Nat} (hK : coercivityCutoff q ≤ K+1) :
    finiteCutoff q ≤ K+1 :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hK

/-- The OWN selected partition retains the actual original pointwise floor. -/
theorem originalSelectedPartition_floor {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (K extent : Nat) (ids slots : List Nat) (qs : Nat → UnitNorm)
    (hK : finiteCutoff q ≤ K+1) :
    normalizedFloor q hq0 K ids ≤ originalSelectedPartition q hq0 K extent ids slots qs :=
  familyProject_pointwise_lower_bound slots (normalizedHeatProduct q hq0 K extent ids)
    (normalizedFloor q hq0 K ids)
    (fun heads => (normalizedHeatProduct_bounds hq0 hq1 K extent ids hK heads).1) qs

/-- Strict positivity is produced, not supplied as a new entropy/log premise. -/
theorem originalSelectedPartition_positive {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (K extent : Nat) (ids slots : List Nat) (qs : Nat → UnitNorm)
    (hK : finiteCutoff q ≤ K+1) :
    (0 : Q') < originalSelectedPartition q hq0 K extent ids slots qs :=
  Q'.pos_of_lt_of_le (normalizedFloor_positive hq0 hq1 K ids)
    (originalSelectedPartition_floor hq0 hq1 K extent ids slots qs hK)

theorem originalSelectedPartition_le_one {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (K extent : Nat) (ids slots : List Nat) (qs : Nat → UnitNorm)
    (hK : finiteCutoff q ≤ K+1) :
    originalSelectedPartition q hq0 K extent ids slots qs ≤ (1 : Q') :=
  familyProject_upper_bound slots (normalizedHeatProduct q hq0 K extent ids) 1
    (fun heads => (normalizedHeatProduct_bounds hq0 hq1 K extent ids hK heads).2) qs

/-- Literal unnormalized selected-Haar defect moment for the complete action. -/
def originalSelectedDefectHaar (q : Q') (hq0 : (0 : Q') < q)
    (K extent : Nat) (ids slots : List Nat) (selected : Nat → Bool)
    (qs : Nat → UnitNorm) : Q' :=
  evalRatPoly (environment qs) (familyProject slots
    (polyMul (normalizedHeatProduct q hq0 K extent ids)
      (selectedFaceDefectPolynomial extent selected ids)))

/-- Actual computed-log upper value at OWN selected Z and its produced window. -/
def originalLogCoercivityValue {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (K extent : Nat) (ids slots : List Nat) (selected : Nat → Bool)
    (qs : Nat → UnitNorm) (hK : coercivityCutoff q ≤ K+1) : CReal :=
  BF4SelectedEntropyLogBound.logBound q (originalSelectedPartition q hq0 K extent ids slots qs)
    (originalSelectedPartition_positive hq0 hq1 K extent ids slots qs (finiteCutoff_le hK))
    (originalSelectedPartition_le_one hq0 hq1 K extent ids slots qs (finiteCutoff_le hK))
    (selectedCount selected ids)

/-- SAME approximation index, explicit nome/count/tolerance cutoff, and no
partition division. This removes the actual finite-series remainder. -/
theorem original_selected_log_approx {q : Q'}
    (hq0 : (0 : Q') < q) (hq : Q'.mkPos 16 17 (by decide) ≤ q)
    (hq1 : q < (1 : Q')) (K extent : Nat) (ids slots : List Nat)
    (selected : Nat → Bool) (qs : Nat → UnitNorm)
    (hK : coercivityCutoff q ≤ K+1) (epsilon : Q') (he : (0 : Q') < epsilon)
    (N : Nat)
    (hN : BF4SelectedEntropyLogBound.logRate q ids.length (selectedCount selected ids) epsilon ≤ N) :
    originalSelectedDefectHaar q hq0 K extent ids slots selected qs ≤
      (originalLogCoercivityValue hq0 hq1 K extent ids slots selected qs hK).approx N+epsilon :=
  BF4SelectedEntropyLogBound.log_approx hq0 hq1
    (originalSelectedPartition q hq0 K extent ids slots qs)
    (originalSelectedPartition_positive hq0 hq1 K extent ids slots qs (finiteCutoff_le hK))
    (originalSelectedPartition_le_one hq0 hq1 K extent ids slots qs (finiteCutoff_le hK))
    ids.length (selectedCount selected ids)
    (originalSelectedDefectHaar q hq0 K extent ids slots selected qs)
    (fun n hn => original_selected_haar_coercivity_finite hq0 hq hq1
      K extent ids slots selected qs hK n hn) epsilon he N hN

/-- Sound cutoff-free eventual order with its explicit modulus retained in
Type. No ordinary one-slack CReal order transitivity is used. -/
def original_selected_log_bound {q : Q'}
    (hq0 : (0 : Q') < q) (hq : Q'.mkPos 16 17 (by decide) ≤ q)
    (hq1 : q < (1 : Q')) (K extent : Nat) (ids slots : List Nat)
    (selected : Nat → Bool) (qs : Nat → UnitNorm)
    (hK : coercivityCutoff q ≤ K+1) :
    CReal.ExplicitLeEv (CReal.ofQ' (originalSelectedDefectHaar q hq0 K extent ids slots selected qs))
      (originalLogCoercivityValue hq0 hq1 K extent ids slots selected qs hK) where
  modulus := BF4SelectedEntropyLogBound.logRate q ids.length (selectedCount selected ids)
  bound := original_selected_log_approx hq0 hq hq1 K extent ids slots selected qs hK

end YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarLogCoercivity

#print axioms YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarLogCoercivity.originalSelectedPartition_floor
#print axioms YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarLogCoercivity.originalSelectedPartition_positive
#print axioms YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarLogCoercivity.originalSelectedPartition_le_one
#print axioms YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarLogCoercivity.originalSelectedDefectHaar
#print axioms YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarLogCoercivity.originalLogCoercivityValue
#print axioms YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarLogCoercivity.original_selected_log_approx
#print axioms YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarLogCoercivity.original_selected_log_bound
