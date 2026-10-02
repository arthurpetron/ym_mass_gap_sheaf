/-
# Actual diagonal cutoff debt controlled by the Haar square

Full-cycle path positivity removes the absolute values from the diagonal
omitted budget. Coefficient monotonicity and exact path reassembly then give
0 <= O_K(p,p) <= w^((K+1)*(K+3)) H[p^2], with no source-degree guard.

The same cap bounds the existing diagonal budget and feeds the original
second-order source energy. The mixed omitted budget remains unchanged.
This norm cap need not be numerically smaller than the exact diagonal debt;
its benefit is explicit cutoff dependence without an absolute leaf norm.
It is not a bound relative to interacting variance or a scaling theorem.
-/

import YMGap.Continuum.SU2QuaternionDiagonalRemainderMoment
import YMGap.Continuum.SU2QuaternionCyclicPathReassembly
import YMGap.Continuum.SU2QuaternionCyclicSecondOrder

namespace YMGap.Continuum.SU2QuaternionCyclicOmittedNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
open YMGap.Continuum.SU2QuaternionDiagonalRemainderMoment
open YMGap.Continuum.SU2QuaternionCyclicPathReassembly
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder
open YMGap.Continuum.SU2HeatProductCutoffDebt
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- Explicit coupling/cutoff coefficient, not an opaque uniform constant. -/
def omittedRate (w : Q') (K : Nat) : Q' :=
  RGTransport.qpow w ((K+1)*(K+3))

private theorem leafAbsSum_eq_of_paths (tail : Nat) :
    ∀ (m : Nat) (p test : RatPoly) (weight : List Nat → Q'),
      (∀ ds, ds.length = m → ValidPath tail p ds →
        (0 : Q') ≤ H (tail+1) (polyMul test (pathPiece tail p ds))) →
      leafAbsSum tail m p test weight = leafSum tail m p test weight
  | 0, p, test, weight, h => by
      change weight [] * Q'.abs (H (tail+1) (polyMul test p)) =
        weight [] * H (tail+1) (polyMul test p)
      have hpos : (0 : Q') ≤ H (tail+1) (polyMul test p) := h [] rfl True.intro
      rw [ExpNeg.abs_of_nonneg hpos]
  | m+1, p, test, weight, h => by
      apply congrArg qListSum
      apply List.map_congr_left
      intro d hd
      exact leafAbsSum_eq_of_paths tail m (nextPiece tail p d) test
        (fun ds => weight (d::ds)) (fun ds hlen hpath =>
          h (d::ds) (by simp only [List.length_cons, hlen]) ⟨hd, hpath⟩)

/-- Every full diagonal leaf is nonnegative, so its absolute budget is
literally the same rational as its signed pairing. -/
theorem full_leafAbsSum_diagonal_eq (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (weight : List Nat → Q') :
    leafAbsSum tail (tail+1) p p weight = leafSum tail (tail+1) p p weight :=
  leafAbsSum_eq_of_paths tail (tail+1) p p weight
    (fun ds hlen hpath => full_path_pairing_nonnegative tail p hp ds hlen hpath)

theorem pairOmittedBudget_diagonal_eq (tail : Nat) (w : Q') (K : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    pairOmittedBudget tail w K p p = pairOmitted tail w K p p :=
  full_leafAbsSum_diagonal_eq tail p hp (omittedDebt w K)

theorem pairOmitted_diagonal_nonnegative (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    (0 : Q') ≤ pairOmitted tail w K p p :=
  full_leafSum_diagonal_nonnegative tail p hp (omittedDebt w K)
    (fun ds _ => omittedDebt_nonnegative hw0 K ds)

/-- No source-degree cutoff, source positivity, or joint orthogonality
hypothesis is needed. Width/depth enter only through the actual Haar square. -/
theorem pairOmitted_diagonal_le_haar (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    pairOmitted tail w K p p ≤ omittedRate w K * H (tail+1) (polyMul p p) := by
  have h := full_leafSum_diagonal_mono tail p hp (omittedDebt w K)
    (fun _ => omittedRate w K * (1 : Q')) (fun ds _ =>
      Q'.le_trans' _ _ _ (omittedDebt_le_tail hw0 hw1 K ds)
        (Q'.ge_of_eqv (Q'.mul_one_eqv (omittedRate w K))))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (leafSum_smul tail (tail+1) p p (omittedRate w K) (fun _ => (1 : Q')))
    (Q'.mul_eqv_congr_left _ _ _ (full_leafSum_one tail p p hp))))

theorem pairOmittedBudget_diagonal_le_haar (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    pairOmittedBudget tail w K p p ≤ omittedRate w K * H (tail+1) (polyMul p p) := by
  rw [pairOmittedBudget_diagonal_eq tail w K p hp]
  exact pairOmitted_diagonal_le_haar tail hw0 hw1 K p hp

/-- Same mixed/cubic costs, with the diagonal omitted budget replaced by its
proved norm cap. This does not assume that any error is small. -/
def sourceNormErrorBudget (tail : Nat) (w : Q') (K : Nat) (a f : RatPoly) : Q' :=
  ((((1 : Q')-w)*((1 : Q')-w))*((1 : Q')-w)) *
    (pairCubicBudget tail a (polyMul a (polyMul f f)) +
      pairCubicBudget tail (polyMul a f) (polyMul a f)) +
    (pairOmittedBudget tail w K a (polyMul a (polyMul f f)) +
      omittedRate w K * H (tail+1) (polyMul (polyMul a f) (polyMul a f)))

theorem sourceErrorBudget_le_norm (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceErrorBudget tail w K a f ≤ sourceNormErrorBudget tail w K a f :=
  Q'.add_le_add_left _ _ _ (Q'.add_le_add_left _ _ _
    (pairOmittedBudget_diagonal_le_haar tail hw0 hw1 K (polyMul a f)
      (supported_polyMul ha hf)))

/-- Actual complete signed cubic-minus-cutoff error consumer. -/
theorem sourceError_le_norm (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceCubic tail w a f-sourceOmitted tail w K a f ≤
      sourceNormErrorBudget tail w K a f :=
  Q'.le_trans' _ _ _ (sourceError_bound tail hw0 hw1 K a f)
    (sourceErrorBudget_le_norm tail hw0 hw1 K a f ha hf)

end YMGap.Continuum.SU2QuaternionCyclicOmittedNorm

#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedNorm.omittedRate
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedNorm.full_leafAbsSum_diagonal_eq
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedNorm.pairOmittedBudget_diagonal_eq
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedNorm.pairOmitted_diagonal_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedNorm.pairOmitted_diagonal_le_haar
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedNorm.pairOmittedBudget_diagonal_le_haar
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedNorm.sourceNormErrorBudget
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedNorm.sourceErrorBudget_le_norm
#print axioms YMGap.Continuum.SU2QuaternionCyclicOmittedNorm.sourceError_le_norm
