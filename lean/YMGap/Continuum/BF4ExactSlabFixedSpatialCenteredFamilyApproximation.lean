/-
# Constructed corrected tests approximate the original centered observable

For each finite actual odd marginal and supported f, compute first a seed
degree and then a correction degree. The resulting SAME corrected family
sum approximates Phi=Z*f-H[nu*f] in H[nu*error^2], with a requested rational
tolerance. Both degrees are returned as data, and the existing temporal
Dirichlet energy inequality is instantiated on these actual tests.

This supplies the approximation side of the stable-decomposition problem.
It does NOT bound the signed diagonal/determinant cost uniformly, identify
an approximation degree with time, or establish a continuum spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamilyApproximation
import YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionFamilyApproximation
import YMGap.Continuum.QuaternionHaarWeightedSquareTriangle

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFamilyApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalPair marginalCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope (centeredObservable)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily
  (familySeeds familySeeds_supported familyTests familyTests_supported rawSum rawError rawError_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCorrectionFamilyApproximation
  (correctionError correctionError_supported correctionError_weighted_square_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost
  (correctedSum diagonalRemainder determinantRemainder actualResidual_corrected_energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (sumBound)
open YMGap.Continuum.QuaternionHaarWeightedSquareTriangle (weighted_square_add_bound)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks

private def quarter (epsilon : Q') : Q' := HalfPow.half * (HalfPow.half * epsilon)

private theorem quarter_positive {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < quarter epsilon :=
  Q'.mul_pos (by decide : (0 : Q') < HalfPow.half)
    (Q'.mul_pos (by decide : (0 : Q') < HalfPow.half) he)

private theorem quarter_budget (epsilon : Q') : sumBound (quarter epsilon) (quarter epsilon) ≈ epsilon :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (ExpNeg.two_halves (HalfPow.half * epsilon))
    (ExpNeg.two_halves (HalfPow.half * epsilon))) (ExpNeg.two_halves epsilon)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

def approximant (k l : Nat) (f : RatPoly) : RatPoly :=
  correctedSum hw0 hw1 K width hK n (familyTests hw0 hw1 K width hK n k f) (fun _ => l)

def error (k l : Nat) (f : RatPoly) : RatPoly :=
  polyAdd (approximant hw0 hw1 K width hK n k l f) (polyNeg (centeredObservable w K width n f))

theorem error_split (k l : Nat) (f : RatPoly) :
    RatPolyCoeffEqv (error hw0 hw1 K width hK n k l f)
      (polyAdd
        (correctionError hw0 hw1 K width hK n (familyTests hw0 hw1 K width hK n k f) l)
        (rawError hw0 hw1 K width hK n k f)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.var 0) (.neg (.var 2)))
    (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
    (by decide) (fun
      | 0 => approximant hw0 hw1 K width hK n k l f
      | 1 => rawSum hw0 hw1 K width hK n k f
      | _ => centeredObservable w K width n f)

/-- The correction cutoff is computed AFTER the seed degree, from those
actual polynomials. No diagonal-rate or degree-independence premise is used. -/
def approximationDegrees (f : RatPoly) (epsilon : Q') : Nat × Nat :=
  let k := BF4ExactSlabFixedSpatialSeedFamilyApproximation.approximationCutoff
    hw0 hw1 K width hK n f (quarter epsilon)
  let l := BF4ExactSlabFixedSpatialCorrectionFamilyApproximation.approximationCutoff
    hw0 hw1 K width hK n (familyTests hw0 hw1 K width hK n k f) (quarter epsilon)
  (k, l)

set_option maxHeartbeats 800000 in
theorem approximation_bound {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    let d := approximationDegrees hw0 hw1 K width hK n f epsilon
    quaternionHaar (N width) (polyMul (marginalWeight w K width n)
      (polyMul (error hw0 hw1 K width hK n d.1 d.2 f)
        (error hw0 hw1 K width hK n d.1 d.2 f))) ≤ epsilon := by
  let k := (approximationDegrees hw0 hw1 K width hK n f epsilon).1
  let l := (approximationDegrees hw0 hw1 K width hK n f epsilon).2
  let qs := familyTests hw0 hw1 K width hK n k f
  have hq := fun i (_ : i ∈ BF4ExactSlabFixedSpatialFamilyErasure.labels width) =>
    familyTests_supported hw0 hw1 K width hK n k i hf
  have hc := correctionError_weighted_square_le hw0 hw1 K width hK n qs hq
    (quarter epsilon) (quarter_positive hepsilon) l (Nat.le_refl _)
  have hr := BF4ExactSlabFixedSpatialSeedFamilyApproximation.rawError_weighted_square_le
    hw0 hw1 K width hK n hf (quarter epsilon) (quarter_positive hepsilon) k (Nat.le_refl _)
  have hb := weighted_square_add_bound (marginalCertificate hw0 hw1 K width hK n)
    (correctionError_supported hw0 hw1 K width hK n qs l hq)
    (rawError_supported hw0 hw1 K width hK n k hf) hc hr
  have he := error_split hw0 hw1 K width hK n k l f
  have hs := haar_of_coeff (blocks := N width) ((he.mul he).mul_left (marginalWeight w K width n))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hs)
    (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (quarter_budget epsilon)))

/-- Explicit finite degrees, not a propositional existence assertion. -/
def approximationCertificate {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    { d : Nat × Nat //
      quaternionHaar (N width) (polyMul (marginalWeight w K width n)
        (polyMul (error hw0 hw1 K width hK n d.1 d.2 f)
          (error hw0 hw1 K width hK n d.1 d.2 f))) ≤ epsilon } :=
  ⟨approximationDegrees hw0 hw1 K width hK n f epsilon,
    approximation_bound hw0 hw1 K width hK n hf epsilon hepsilon⟩

/-- The constructed approximants are precisely the tests consumed by the
actual temporal energy bound, with the signed remainder still displayed. -/
theorem approximant_energy (k l : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    let qs := familyTests hw0 hw1 K width hK n k f
    let s := approximant hw0 hw1 K width hK n k l f
    headFloor w*(marginalPair w K width n f s * marginalPair w K width n f s) ≤
      energy w K width (terminalMessage w K width n) f *
        (headFloor w*marginalPair w K width n s s +
          diagonalRemainder hw0 hw1 K width hK n qs (fun _ => l) +
          ((2 : Q')*headFloor w)*determinantRemainder hw0 hw1 K width hK n qs (fun _ => l)) :=
  actualResidual_corrected_energy hw0 hw1 K width hK n
    (familySeeds hw0 hw1 K width hK n k f) (fun _ => l)
    (fun i _ => familySeeds_supported hw0 hw1 K width hK n k i hf) hf

end YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFamilyApproximation

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFamilyApproximation.approximant
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFamilyApproximation.error
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFamilyApproximation.error_split
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFamilyApproximation.approximationDegrees
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFamilyApproximation.approximation_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFamilyApproximation.approximationCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredFamilyApproximation.approximant_energy
