/-
# The factorized all-spin Haar integral reaches the ORIGINAL normalized packet

Both observables retain the complete original bulk action. The crossing
integrand is the selected weighted square times the full spectator action,
on the original shared link variables. Its diagonal has the existing
original channel packet as bulk limit, with a computed cutoff.

Multiplication by the SAME original partition-reciprocal sample gives an
explicit approximation to the existing normalized retained packet. The
error budget names the finite-volume reciprocal ceiling: it is NOT a
volume-uniform estimate. No new limiting object, analytic hypothesis,
surviving lower bound, thermodynamic separation or Clay result is supplied.
-/

import YMGap.Continuum.BF4ExactSlabAllSpinSpectatorFactorization
import YMGap.Continuum.BF4ExactSlabNormalizedChannelReconstruction

namespace YMGap.Continuum.BF4ExactSlabAllSpinSpectatorIntegralLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention
open YMGap.Continuum.BF4ExactSlabAllSpinSpectatorHaarForm
open YMGap.Continuum.BF4ExactSlabAllSpinSpectatorFactorization
open YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm (squareFactor)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity
open YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.BF4ExactSlabNormalizedChannelReconstruction (normalizedTolerance normalizedTolerance_positive normalizedTolerance_budget)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {K half : Nat}
    (choice : (id : Nat) → Choice half K id)

def integral (B : Nat) (e f : PlaquetteExpression half) : Q' :=
  quaternionHaar (blocks half)
    (polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) (dressedLower w B e)) (dressedLower w B f))
      (polyMul (squareFactor half (selectedWeight choice w) (selectedPolynomial choice)) (spectatorPolynomial choice w)))

include hw0 in
theorem integral_pairing (B : Nat) (e f : PlaquetteExpression half) :
    integral w choice B e f ≈ bulkPairing (Q'.le_of_lt hw0) K choice B e f :=
  factorized_mixed_haar choice (Q'.le_of_lt hw0) _ _
    (dressedLower_supported w B e) (dressedLower_supported w B f)
    (dressedLower_local w B e) (dressedLower_local w B f)

include hw0 in
theorem integral_energy (B : Nat) (e : PlaquetteExpression half) :
    integral w choice B e e ≈ energySequence w B half (lower e) (retainedInterface (Q'.le_of_lt hw0) K half choice) :=
  Q'.eqv_trans _ _ _ (integral_pairing w hw0 choice B e e) (bulkPairing_diagonal (Q'.le_of_lt hw0) K choice B e)

include hw0 in
theorem integral_nonnegative (B : Nat) (e : PlaquetteExpression half) : (0 : Q') ≤ integral w choice B e e :=
  Q'.le_trans' _ _ _ (bulkPairing_nonnegative (Q'.le_of_lt hw0) K choice B e)
    (Q'.ge_of_eqv (integral_pairing w hw0 choice B e e))

include hw0 in
theorem integral_original_bound (B : Nat) (hB : K ≤ B) (e : PlaquetteExpression half) :
    integral w choice B e e ≤ originalQuadratic w B e :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (integral_pairing w hw0 choice B e e))
    (bulkPairing_original_bound (Q'.le_of_lt hw0) K choice hw0 B hB e)

def bulkCutoff (e : PlaquetteExpression half) (epsilon : Q') : Nat :=
  max K (energyApproxCutoff w hw0 half (lower e) (retainedInterface (Q'.le_of_lt hw0) K half choice) epsilon)

theorem integral_approx_close (e : PlaquetteExpression half) (epsilon : Q') (he : (0 : Q') < epsilon)
    (B n : Nat) (hB : bulkCutoff w hw0 choice e epsilon ≤ B) (hn : bulkCutoff w hw0 choice e epsilon ≤ n) :
    integral w choice B e e ≤ (retainedPacket K w hw0 hw1 choice e).approx n + epsilon ∧
    (retainedPacket K w hw0 hw1 choice e).approx n ≤ integral w choice B e e + epsilon := by
  have h := energy_approx_close w hw0 hw1 half (lower e) _
    (retainedInterface_nonnegative (Q'.le_of_lt hw0) K half choice) epsilon he B n
    (Nat.le_trans (Nat.le_max_right _ _) hB) (Nat.le_trans (Nat.le_max_right _ _) hn)
  have hp := integral_energy w hw0 choice B e
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) h.1,
    Q'.le_trans' _ _ _ h.2 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv hp))⟩

/-- The limit is the existing original packet, not a new factored measure. -/
theorem integral_converges (e : PlaquetteExpression half) :
    ConvergesTo (fun B => ofQ' (integral w choice B e e)) (retainedPacket K w hw0 hw1 choice e) :=
  fun epsilon he => ⟨bulkCutoff w hw0 choice e epsilon, fun B hB =>
    ⟨bulkCutoff w hw0 choice e epsilon, fun n hn => integral_approx_close w hw0 hw1 choice e epsilon he B n hB hn⟩⟩

/-- The reciprocal is sampled from the ORIGINAL full-action limit. -/
def normalizedSample (B n : Nat) (e : PlaquetteExpression half) : Q' :=
  (actionReciprocal w hw0 hw1 half).approx n * integral w choice B e e

/-- Explicitly depends on the original finite-volume reciprocal ceiling. -/
def normalizedBulkCutoff (e : PlaquetteExpression half) (epsilon : Q') : Nat :=
  bulkCutoff w hw0 choice e (normalizedTolerance w hw0 hw1 (half := half) epsilon)

private theorem normalize_close (a b lambda ceiling delta epsilon : Q')
    (hl : (0 : Q') ≤ lambda) (hcap : lambda ≤ ceiling) (hd : (0 : Q') ≤ delta)
    (hb : ceiling*delta ≈ epsilon) (h : a ≤ b+delta) : lambda*a ≤ lambda*b+epsilon :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ h hl)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _))
      (Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hcap hd) (Q'.le_of_eqv hb))))

theorem normalizedSample_approx_close (e : PlaquetteExpression half) (epsilon : Q') (he : (0 : Q') < epsilon)
    (B n : Nat) (hB : normalizedBulkCutoff w hw0 hw1 choice e epsilon ≤ B)
    (hn : normalizedBulkCutoff w hw0 hw1 choice e epsilon ≤ n) :
    normalizedSample w hw0 hw1 choice B n e ≤ (normalizedRetainedPacket K w hw0 hw1 choice e).approx n + epsilon ∧
    (normalizedRetainedPacket K w hw0 hw1 choice e).approx n ≤ normalizedSample w hw0 hw1 choice B n e + epsilon := by
  have hd := normalizedTolerance_positive w hw0 hw1 (half := half) he
  have h := integral_approx_close w hw0 hw1 choice e _ hd B n hB hn
  have hf := normalize_close _ _ _ _ _ epsilon
    (Q'.le_of_lt (actionReciprocal_approx_pos w hw0 hw1 half n))
    (actionReciprocal_approx_le w hw0 hw1 half n) (Q'.le_of_lt hd)
    (normalizedTolerance_budget w hw0 hw1 (half := half) epsilon) h.1
  have hb := normalize_close _ _ _ _ _ epsilon
    (Q'.le_of_lt (actionReciprocal_approx_pos w hw0 hw1 half n))
    (actionReciprocal_approx_le w hw0 hw1 half n) (Q'.le_of_lt hd)
    (normalizedTolerance_budget w hw0 hw1 (half := half) epsilon) h.2
  exact ⟨hf, hb⟩

/-- Simultaneous bulk cutoff and representative index, returned as data. -/
def computedSample (e : PlaquetteExpression half) (epsilon : Q') : Q' :=
  let n := normalizedBulkCutoff w hw0 hw1 choice e epsilon
  normalizedSample w hw0 hw1 choice n n e

theorem computedSample_spec (e : PlaquetteExpression half) (epsilon : Q') (he : (0 : Q') < epsilon) :
    let n := normalizedBulkCutoff w hw0 hw1 choice e epsilon
    computedSample w hw0 hw1 choice e epsilon ≤ (normalizedRetainedPacket K w hw0 hw1 choice e).approx n + epsilon ∧
    (normalizedRetainedPacket K w hw0 hw1 choice e).approx n ≤ computedSample w hw0 hw1 choice e epsilon + epsilon :=
  normalizedSample_approx_close w hw0 hw1 choice e epsilon he _ _ (Nat.le_refl _) (Nat.le_refl _)

end YMGap.Continuum.BF4ExactSlabAllSpinSpectatorIntegralLimit

#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorIntegralLimit.integral
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorIntegralLimit.integral_pairing
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorIntegralLimit.integral_energy
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorIntegralLimit.integral_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorIntegralLimit.integral_original_bound
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorIntegralLimit.bulkCutoff
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorIntegralLimit.integral_approx_close
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorIntegralLimit.integral_converges
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorIntegralLimit.normalizedSample
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorIntegralLimit.normalizedBulkCutoff
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorIntegralLimit.normalizedSample_approx_close
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorIntegralLimit.computedSample
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorIntegralLimit.computedSample_spec
