/-
# Finite polynomial duals for the original plaquette boundary star

The dual is the literal fundamental face character times a finite geometric
reciprocal of ONLY the selected action factors touching its four boundary
links. All remaining action factors survive in the norm estimate. The local
positive window and exact retained-background square moment give
  lower(w) * H[fullAction * dualTest_k^2] <= H[restHeat].
The bound holds at every finite degree; no limiting inverse is constructed.

The coefficient cancellation retains its finite residual polynomial, with a
computed geometric interval and tolerance cutoff. The constants depend on
nome, not extent, placement, selected volume, late cutoff or reciprocal degree.
No summed-frame estimate, OS inverse, global norm gap or continuum claim follows.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow
import YMGap.Continuum.QuaternionHaarLocalDualNorm

namespace YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance (faceCharacter faceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
  (reciprocal reciprocal_supported remainder remainderInterval reciprocal_cancellation)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- A finite original-coordinate polynomial; no configuration-valued inverse. -/
def dualTest {w : Q'} (hw0 : (0 : Q') < w)
    (K extent : Nat) (ids : List Nat) (face : Z4Plaq) (k : Nat) : RatPoly :=
  polyMul (faceCharacter extent face)
    (reciprocal (starHeat w K extent ids face) (upper w) (upper_positive hw0) k)

theorem dualTest_supported {w : Q'} (hw0 : (0 : Q') < w)
    (K extent : Nat) (ids : List Nat) (face : Z4Plaq) (k : Nat) :
    SupportedQuaternionBlocks (B extent) (dualTest hw0 K extent ids face k) :=
  supported_polyMul (faceCharacter_supported extent face)
    (reciprocal_supported (starHeat_supported w K extent ids face)
      (upper w) (upper_positive hw0) k)

/-- The exact finite residual of the SAME local inverse algorithm. -/
def residualPolynomial {w : Q'} (hw0 : (0 : Q') < w)
    (K extent : Nat) (ids : List Nat) (face : Z4Plaq) (k : Nat) : RatPoly :=
  QuaternionHaarPolynomialGeometricInverse.residual
    (remainder (starHeat w K extent ids face) (upper w) (upper_positive hw0)) k

/-- Cancellation is coefficientwise and keeps the unremoved residual. -/
theorem cancellation_pin {w : Q'} (hw0 : (0 : Q') < w)
    (K extent : Nat) (ids : List Nat) (face : Z4Plaq) (k : Nat) :
    RatPolyCoeffEqv
      (polyAdd
        (polyMul (starHeat w K extent ids face) (dualTest hw0 K extent ids face k))
        (polyMul (faceCharacter extent face) (residualPolynomial hw0 K extent ids face k)))
      (faceCharacter extent face) := by
  let S := starHeat w K extent ids face
  let C := faceCharacter extent face
  let G := reciprocal S (upper w) (upper_positive hw0) k
  let R := residualPolynomial hw0 K extent ids face k
  have he : RatPolyCoeffEqv (polyAdd (polyMul S (polyMul C G)) (polyMul C R))
      (polyMul C (polyAdd (polyMul S G) R)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.var 3)))
      (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.var 3)))
      (by decide) (fun | 0 => S | 1 => C | 2 => G | _ => R)
  exact he.trans (((reciprocal_cancellation S (upper w) (upper_positive hw0) k).mul_left C).trans
    (RatPolyCoeffEqv.mul_one C))

/-- The full original selected action, not just the erased-star reference,
controls this finite dual. The remaining partition is kept explicitly. -/
theorem fullAction_norm_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (k : Nat) :
    lower w * quaternionHaar (B extent)
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
        (polyMul (dualTest hw0 K extent ids face k) (dualTest hw0 K extent ids face k))) ≤
      quaternionHaar (B extent) (restHeat w K extent ids face) := by
  let S := starHeat w K extent ids face
  let R := restHeat w K extent ids face
  let C := faceCharacter extent face
  let G := reciprocal S (upper w) (upper_positive hw0) k
  have Spos : Certificate (B extent) S :=
    headProduct_certificate hw0 hw1 K extent hK _
      (fun id hi => hids id (boundaryStar_mem hi).1)
  have Rpos : Certificate (B extent) R :=
    headProduct_certificate hw0 hw1 K extent hK _
      (fun id hi => hids id (boundaryRest_mem hi).1)
  have hn := QuaternionHaarLocalDualNorm.local_dual_norm_le
    (starHeat_supported w K extent ids face) (lower_positive hw0 hw1)
    (upper_positive hw0) (lower_le_upper hw0 hw1) Spos
    (starLowerCertificate hw0 hw1 K extent hK ids hids hnodup face)
    (starUpperCertificate hw0 hw1 K extent ids hids hnodup face) k Rpos
    (faceCharacter_supported extent face)
  have he : RatPolyCoeffEqv
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
        (polyMul (dualTest hw0 K extent ids face k) (dualTest hw0 K extent ids face k)))
      (polyMul (polyMul R (polyMul C C)) (polyMul S (polyMul G G))) :=
    ((selected_heat_partition w K extent ids face).mul_right _).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1))
          (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))))
        (.mul (.mul (.var 1) (.mul (.var 2) (.var 2)))
          (.mul (.var 0) (.mul (.var 3) (.var 3))))
        (by decide) (fun | 0 => S | 1 => R | 2 => C | _ => G))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff he)))
    (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (rest_square_moment w K extent ids hf)))

/-- The explicit approximation rate uses only the local twenty-four-face window. -/
def rate {w : Q'} (hw0 : (0 : Q') < w) : Q' :=
  QuaternionHaarPositiveWindowInverse.radius (lower w) (upper w) (upper_positive hw0)

theorem rate_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') ≤ rate hw0 :=
  QuaternionHaarPositiveWindowInverse.radius_nonnegative
    (upper_positive hw0) (lower_le_upper hw0 hw1)

theorem rate_lt_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    rate hw0 < (1 : Q') :=
  QuaternionHaarPositiveWindowInverse.radius_lt_one (lower_positive hw0 hw1) (upper_positive hw0)

/-- Actual finite residual interval, not an assumed approximation budget. -/
def residualInterval {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) (face : Z4Plaq) (k : Nat) :
    Interval (B extent) (residualPolynomial hw0 K extent ids face k) ((rate hw0)^k) :=
  QuaternionHaarPolynomialGeometricInverse.residualInterval
    (remainderInterval (starHeat_supported w K extent ids face)
      (upper_positive hw0) (lower_le_upper hw0 hw1)
      (starLowerCertificate hw0 hw1 K extent hK ids hids hnodup face)
      (starUpperCertificate hw0 hw1 K extent ids hids hnodup face)) k

/-- Explicit degree, independent of ambient geometry and the late heat cutoff. -/
def approximationCutoff {w : Q'} (hw0 : (0 : Q') < w) (epsilon : Q') : Nat :=
  QuaternionHaarPositiveWindowInverse.approximationCutoff
    (lower w) (upper w) (upper_positive hw0) epsilon

def residualApproximationInterval {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) (face : Z4Plaq)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (k : Nat)
    (hk : approximationCutoff hw0 epsilon ≤ k) :
    Interval (B extent) (residualPolynomial hw0 K extent ids face k) epsilon :=
  (residualInterval hw0 hw1 K extent hK ids hids hnodup face k).weaken
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
      (PositiveContractionResidual.geometric_bound (rate_nonnegative hw0 hw1)
        (rate_lt_one hw0 hw1) Q'.zero_le_one hepsilon k hk))

/-- Compare the retained mass with the ORIGINAL selected partition using only
the local star floor. Neither mass is replaced by a vacuum reference. -/
theorem lower_rest_mass_le_full_mass {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) (face : Z4Plaq) :
    lower w * quaternionHaar (B extent) (restHeat w K extent ids face) ≤
      quaternionHaar (B extent) (polynomialProduct (faceHeatPolynomial w K extent) ids) := by
  have Rpos := headProduct_certificate hw0 hw1 K extent hK (boundaryRest extent ids face)
    (fun id hi => hids id (boundaryRest_mem hi).1)
  have h := QuaternionHaarPositiveFloorCancellation.floor_insertion Rpos
    (starLowerCertificate hw0 hw1 K extent hK ids hids hnodup face)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (haar_of_coeff
    ((RatPolyCoeffEqv.mul_comm _ _).trans (selected_heat_partition w K extent ids face).symm)))

/-- The reverse partition comparison also pays only for the local star. -/
theorem full_mass_le_upper_rest_mass {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) (face : Z4Plaq) :
    quaternionHaar (B extent) (polynomialProduct (faceHeatPolynomial w K extent) ids) ≤
      upper w * quaternionHaar (B extent) (restHeat w K extent ids face) := by
  have Rpos := headProduct_certificate hw0 hw1 K extent hK (boundaryRest extent ids face)
    (fun id hi => hids id (boundaryRest_mem hi).1)
  have Spos := headProduct_certificate hw0 hw1 K extent hK (boundaryStar extent ids face)
    (fun id hi => hids id (boundaryStar_mem hi).1)
  have I : Interval (B extent) (starHeat w K extent ids face) (upper w) :=
    ⟨starHeat_supported w K extent ids face, Q'.le_of_lt (upper_positive hw0),
      starUpperCertificate hw0 hw1 K extent ids hids hnodup face,
      (Certificate.constant _ _ (Q'.le_of_lt (upper_positive hw0))).add Spos⟩
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff
    ((selected_heat_partition w K extent ids face).trans (RatPolyCoeffEqv.mul_comm _ _))))
    (Q'.le_trans' _ _ _ (Q'.le_abs_self _) (I.weighted_haar_bound Rpos))

/-- A norm estimate relative to the same full selected partition; the stronger
retained-mass estimate remains available for weighted family summation. -/
theorem fullAction_norm_partition_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (k : Nat) :
    (lower w * lower w) * quaternionHaar (B extent)
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
        (polyMul (dualTest hw0 K extent ids face k) (dualTest hw0 K extent ids face k))) ≤
      quaternionHaar (B extent) (polynomialProduct (faceHeatPolynomial w K extent) ids) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
      (fullAction_norm_bound hw0 hw1 K extent hK ids hids hnodup hf k)
      (Q'.le_of_lt (lower_positive hw0 hw1)))
      (lower_rest_mass_le_full_mass hw0 hw1 K extent hK ids hids hnodup face))

#print axioms dualTest
#print axioms dualTest_supported
#print axioms residualPolynomial
#print axioms cancellation_pin
#print axioms fullAction_norm_bound
#print axioms rate
#print axioms rate_nonnegative
#print axioms rate_lt_one
#print axioms residualInterval
#print axioms approximationCutoff
#print axioms residualApproximationInterval
#print axioms lower_rest_mass_le_full_mass
#print axioms full_mass_le_upper_rest_mass
#print axioms fullAction_norm_partition_bound

end YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDual
