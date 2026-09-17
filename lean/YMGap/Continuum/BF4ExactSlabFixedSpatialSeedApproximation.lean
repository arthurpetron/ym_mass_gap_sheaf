/-
# Quantitative finite approximation by the actual centered seeds

For the original marginal nu, q is the constructed finite weighted residual
and D=nu*q-tau. The checked cleared interval bounds (P_i nu)*D.
Cancel its certified positive floor to obtain
  H[D^2] <= rho^(2*k) * 4*u^2*B^2/ell^2.
All constants and a tolerance cutoff are computed from the actual finite
weight and source cap. The same construction is instantiated on every
conditional-Haar piece of the original partition-centered source.

The approximation degree k is not physical time. No signed family-cost
bound, uniform spectral gap, regulator limit or continuum conclusion is
asserted by these finite-error estimates.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope
import YMGap.Continuum.QuaternionHaarPositiveFloorCancellation

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSeedApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow
  (lower upper lower_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedWindow (conditionalLowerCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed
  (rate rate_nonnegative rate_lt_one defect defect_supported clearedDefectInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope
  (piece piece_supported piece_centered)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.QuaternionHaarPositiveFloorCancellation (cancelSquareBound)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks

private def intervalSquare {blocks : Nat} {p : RatPoly} {c : Q'}
    (P : Interval blocks p c) : SquareBound blocks p (c*c) where
  support := P.support
  nonnegative := Q'.mul_nonneg _ _ P.nonnegative P.nonnegative
  certificate := (P.mul P).upper

private theorem squareHaar {blocks : Nat} {p : RatPoly} {c : Q'}
    (P : SquareBound blocks p c) : quaternionHaar blocks (polyMul p p) ≤ c := by
  let I : Interval blocks (polyMul p p) c :=
    ⟨supported_polyMul P.support P.support, P.nonnegative, P.certificate,
      (Certificate.constant blocks c P.nonnegative).add (Certificate.square p P.support)⟩
  exact Q'.le_trans' _ _ _ (Q'.le_abs_self _) I.haar_bound

private theorem cap_identity (a u r B : Q') :
    a*((u*(r*B)+(u*r)*B)*(u*(r*B)+(u*r)*B)) ≈
      (r*r)*(a*((4*(u*u))*(B*B))) :=
  poly_identity_of_normal_eq
    (.mul (.var 0) (.mul
      (.add (.mul (.var 1) (.mul (.var 2) (.var 3))) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.add (.mul (.var 1) (.mul (.var 2) (.var 3))) (.mul (.mul (.var 1) (.var 2)) (.var 3)))))
    (.mul (.mul (.var 2) (.var 2))
      (.mul (.var 0) (.mul (.mul (.const 4) (.mul (.var 1) (.var 1))) (.mul (.var 3) (.var 3)))))
    (by decide) (fun | 0 => a | 1 => u | 2 => r | _ => B)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

/-- Computed finite prefactor 4*u^2*B^2/ell^2. No uniformity in any
regulator is asserted; B is the cap of the actual source polynomial. -/
def prefactor (B : Q') : Q' :=
  Q'.recipPos (lower w K width n * lower w K width n)
    (Q'.mul_pos (lower_positive hw0 hw1 K width hK n) (lower_positive hw0 hw1 K width hK n)) *
      ((4 * (upper w K width n * upper w K width n)) * (B*B))

theorem prefactor_nonnegative (B : Q') : (0 : Q') ≤ prefactor hw0 hw1 K width hK n B :=
  Q'.mul_nonneg _ _ (Q'.le_of_lt (Q'.recipPos_pos _ _))
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 4) (SumOfSquares.q_mul_self_nonneg _))
      (SumOfSquares.q_mul_self_nonneg B))

/-- The original, uncleared defect has a vanishing certified square cap. -/
def defectSquareBound (i : Nat) (hi : i < N width) (k : Nat)
    {tau : RatPoly} {B : Q'} (P : Interval (N width) tau B)
    (hc : RatPolyCoeffEqv (project i tau) polyZero) :
    SquareBound (N width) (defect hw0 hw1 K width hK n i k tau)
      (((rate hw0 hw1 K width hK n)^k * (rate hw0 hw1 K width hK n)^k) *
        prefactor hw0 hw1 K width hK n B) :=
  SquareBound.changeCap (cap_identity _ _ _ _)
    (cancelSquareBound (defect_supported hw0 hw1 K width hK n i k P.support)
      (lower_positive hw0 hw1 K width hK n)
      (conditionalLowerCertificate hw0 hw1 K width hK n i hi)
      (intervalSquare (clearedDefectInterval hw0 hw1 K width hK n i hi k P hc)))

theorem defect_haar_square_bound (i : Nat) (hi : i < N width) (k : Nat)
    {tau : RatPoly} {B : Q'} (P : Interval (N width) tau B)
    (hc : RatPolyCoeffEqv (project i tau) polyZero) :
    quaternionHaar (N width) (polyMul (defect hw0 hw1 K width hK n i k tau)
      (defect hw0 hw1 K width hK n i k tau)) ≤
        (((rate hw0 hw1 K width hK n)^k * (rate hw0 hw1 K width hK n)^k) *
          prefactor hw0 hw1 K width hK n B) :=
  squareHaar (defectSquareBound hw0 hw1 K width hK n i hi k P hc)

/-- A slightly weaker single-power envelope uses the existing zero-safe
geometric tolerance compiler without any square-root tolerance. -/
theorem defect_haar_square_le_geometric (i : Nat) (hi : i < N width) (k : Nat)
    {tau : RatPoly} {B : Q'} (P : Interval (N width) tau B)
    (hc : RatPolyCoeffEqv (project i tau) polyZero) :
    quaternionHaar (N width) (polyMul (defect hw0 hw1 K width hK n i k tau)
      (defect hw0 hw1 K width hK n i k tau)) ≤
        (rate hw0 hw1 K width hK n)^k * prefactor hw0 hw1 K width hK n B := by
  have h0 := Q'.pow_nonneg _ (rate_nonnegative hw0 hw1 K width hK n) k
  have h1 := HKPos.pow_le_one (rate_nonnegative hw0 hw1 K width hK n)
    (Q'.le_of_lt (rate_lt_one hw0 hw1 K width hK n)) k
  have hs : (rate hw0 hw1 K width hK n)^k * (rate hw0 hw1 K width hK n)^k ≤
      (rate hw0 hw1 K width hK n)^k :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ h1 h0)
      (Q'.le_of_eqv (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ (defect_haar_square_bound hw0 hw1 K width hK n i hi k P hc)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hs (prefactor_nonnegative hw0 hw1 K width hK n B))

def approximationCutoff (B epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff (rate hw0 hw1 K width hK n)
    (prefactor hw0 hw1 K width hK n B) epsilon

theorem defect_haar_square_le (i : Nat) (hi : i < N width)
    {tau : RatPoly} {B : Q'} (P : Interval (N width) tau B)
    (hc : RatPolyCoeffEqv (project i tau) polyZero)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (k : Nat)
    (hk : approximationCutoff hw0 hw1 K width hK n B epsilon ≤ k) :
    quaternionHaar (N width) (polyMul (defect hw0 hw1 K width hK n i k tau)
      (defect hw0 hw1 K width hK n i k tau)) ≤ epsilon :=
  Q'.le_trans' _ _ _ (defect_haar_square_le_geometric hw0 hw1 K width hK n i hi k P hc)
    (PositiveContractionResidual.geometric_bound (rate_nonnegative hw0 hw1 K width hK n)
      (rate_lt_one hw0 hw1 K width hK n) (prefactor_nonnegative hw0 hw1 K width hK n B)
      hepsilon k hk)

/-- Concrete specialization: the source piece and its conditional zero are
both produced by the actual original-marginal telescope. -/
def pieceDefectSquareBound (i : Nat) (hi : i < N width) (k : Nat)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    SquareBound (N width) (defect hw0 hw1 K width hK n i k (piece w K width n i f))
      (((rate hw0 hw1 K width hK n)^k * (rate hw0 hw1 K width hK n)^k) *
        prefactor hw0 hw1 K width hK n (polynomialCap (piece w K width n i f))) :=
  defectSquareBound hw0 hw1 K width hK n i hi k
    (polynomialInterval (N width) (piece w K width n i f) (piece_supported w K width n i hf))
    (piece_centered w K width n i f)

def pieceApproximationCutoff (i : Nat) (f : RatPoly) (epsilon : Q') : Nat :=
  approximationCutoff hw0 hw1 K width hK n (polynomialCap (piece w K width n i f)) epsilon

theorem piece_defect_haar_square_le (i : Nat) (hi : i < N width)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (k : Nat)
    (hk : pieceApproximationCutoff hw0 hw1 K width hK n i f epsilon ≤ k) :
    quaternionHaar (N width) (polyMul
      (defect hw0 hw1 K width hK n i k (piece w K width n i f))
      (defect hw0 hw1 K width hK n i k (piece w K width n i f))) ≤ epsilon :=
  defect_haar_square_le hw0 hw1 K width hK n i hi
    (polynomialInterval (N width) (piece w K width n i f) (piece_supported w K width n i hf))
    (piece_centered w K width n i f) epsilon hepsilon k hk

end YMGap.Continuum.BF4ExactSlabFixedSpatialSeedApproximation

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedApproximation.prefactor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedApproximation.prefactor_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedApproximation.defectSquareBound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedApproximation.defect_haar_square_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedApproximation.defect_haar_square_le_geometric
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedApproximation.approximationCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedApproximation.defect_haar_square_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedApproximation.pieceDefectSquareBound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedApproximation.pieceApproximationCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeedApproximation.piece_defect_haar_square_le
