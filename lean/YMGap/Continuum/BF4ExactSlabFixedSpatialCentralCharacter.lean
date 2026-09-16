/-
# One actual central spatial character

The fundamental character of the original p01 face at the spatial origin
has bare source-slice Haar mean zero and square moment one whenever the
spatial width is positive. The proof transports the existing original-face
Haar cancellation through the actual slice embedding; no auxiliary
character model or expanded coordinate computation replaces the word.

Its radius-zero physical presentation is pinned to the SAME finite-chain
middle ratios for the first and second moments. In particular the central
spatial potential and the original partition are retained. These are bare
Haar moments and exact finite pins, not yet a strictly positive interacting
variance or a nonconstant vector in the limiting reflected quotient.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
import YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm (original_character_support)
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail (faceScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks embedding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette plaquette_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe (sourceProbe)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe (windowProbe)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (sourceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding (windowRatio_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm (Physical mixedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
  (DistanceSpan radius encodeChart)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit (unitSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator
  (chartScalar chartScalar_pin)
open YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction (face_character_haar_zero)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

/-- An explicit spatial face, not a chosen nonempty-list witness. -/
def face : Z4Plaq := ((0, 0, 0, 0), Z4Plane.p01)

theorem face_mem {width : Nat} (hwidth : 0 < width) : face ∈ spatialFaces width :=
  (spatialFaces_mem_iff width face).mpr
    ⟨hwidth, hwidth, hwidth, rfl, by decide⟩

/-- The actual source plaquette's unnormalized fundamental SU(2) character. -/
def character (width : Nat) : RatPoly :=
  characterPolynomial (plaquette width face).scalar 1

theorem character_supported (width : Nat) :
    SupportedQuaternionBlocks (N width) (character width) :=
  SU2QuaternionRelativeHeatPairGeometry.character_supported
    (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1

private theorem positive_spin_mean_zero {width : Nat} (hwidth : 0 < width)
    (spin : Nat) (hspin : 0 < spin) :
    quaternionHaar (N width) (characterPolynomial (plaquette width face).scalar spin) ≈ 0 := by
  let E := embedding (Nat.le_succ width) (Nat.zero_le (width+1))
  have hface : timeShiftPlaquette 0 face ∈ boundaryCompleteSlabPlaquettes (width+1) :=
    spatialFaces_shift_physical (by omega) (Nat.zero_le (width+1)) (face_mem hwidth)
  let id := listIndexOf (timeShiftPlaquette 0 face) (boundaryCompleteSlabPlaquettes (width+1))
  have hi : id ∈ slabPhysicalFaceEdges (width+1) :=
    List.mem_range.mpr (listIndexOf_lt_of_mem _ _ hface)
  have he : slabPlaquetteAt (width+1) id = timeShiftPlaquette 0 face :=
    getD_listIndexOf_of_mem _ _ _ hface
  have hs : SupportedQuaternionBlocks (N width)
      (characterPolynomial (plaquette width face).scalar spin) :=
    SU2QuaternionRelativeHeatPairGeometry.character_supported
      (plaquette_supported width (N width) (Nat.le_refl _) face).scalar spin
  have hp := E.character_of_quaternion
    (plaquette_pin (Nat.le_succ width) (Nat.zero_le (width+1)) (face_mem hwidth)) spin
  have hpin := quaternionHaar_prefixPolynomialEqv (B (width+1)) hp
    (E.polynomial_supported _) (original_character_support (width+1) (timeShiftPlaquette 0 face) spin)
  have hz := face_character_haar_zero hi spin hspin
  simp only [faceScalar, he] at hz
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (E.haar _ hs)) (Q'.eqv_trans _ _ _ hpin hz)

theorem character_mean_zero {width : Nat} (hwidth : 0 < width) :
    quaternionHaar (N width) (character width) ≈ 0 :=
  positive_spin_mean_zero hwidth 1 (by decide)

private theorem first_character_mul_succ (p : RatPoly) (n : Nat) :
    RatPolyCoeffEqv (polyMul (characterPolynomial p 1) (characterPolynomial p (n+1)))
      (polyAdd (characterPolynomial p (n+2)) (characterPolynomial p n)) := by
  let a := polyMul (characterPolynomial p 1) (characterPolynomial p (n+1))
  let b := characterPolynomial p n
  exact (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.mul (.const (-1)) (.var 1))) (.var 1)) (by decide)
    (fun i => if i = 0 then a else b)).trans
    (((RatPolyCoeffEqv.refl a).add (cap_mul_left (-1) b)).add (RatPolyCoeffEqv.refl b))

private theorem haar_one (blocks : Nat) : quaternionHaar blocks polyOne ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one _)) (Q'.eqv_refl _))
    (Q'.eqv_of_eq (Q'.add_zero' 1))

/-- The source face is genuinely nonconstant under bare compact product Haar. -/
theorem character_square_one {width : Nat} (hwidth : 0 < width) :
    quaternionHaar (N width) (polyMul (character width) (character width)) ≈ 1 :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (first_character_mul_succ (plaquette width face).scalar 0))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (positive_spin_mean_zero hwidth 2 (by decide)) (haar_one _))
        (by decide)))

/-- One original signed-character factor at distance zero from reflection. -/
def presentation : DistanceSpan := [(1, [(0, [(face, [(1, 1)])])])]

theorem presentation_physical {width : Nat} (hwidth : 0 < width) :
    Physical width presentation := by
  intro x hx e he f hf
  have hx' := List.mem_singleton.mp hx
  subst x
  have he' := List.mem_singleton.mp he
  subst e
  have hf' := List.mem_singleton.mp hf
  subst f
  exact face_mem hwidth

def span (width : Nat) (hwidth : 0 < width) : PhysicalSpan width :=
  ⟨presentation, presentation_physical hwidth⟩

theorem span_radius (width : Nat) (hwidth : 0 < width) :
    radius (span width hwidth).val = 0 := rfl

private theorem singleton_sum (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polySmul 1 p) polyZero) p :=
  ((RatPolyCoeffEqv.one_smul p).add (RatPolyCoeffEqv.refl polyZero)).trans
    (RatPolyCoeffEqv.add_zero p)

private theorem singleton_ledger (p : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polySmul 1
        (polyMul (polyMul (polyAdd (polySmul 1 p) polyZero) polyOne) polyOne)) polyZero) p := by
  have hf : RatPolyCoeffEqv
      (polyMul (polyAdd (polySmul 1 p) polyZero) polyOne) p :=
    ((singleton_sum p).mul (RatPolyCoeffEqv.refl polyOne)).trans
      (RatPolyCoeffEqv.mul_one _)
  have hw := (hf.mul (RatPolyCoeffEqv.refl polyOne)).trans (RatPolyCoeffEqv.mul_one _)
  exact ((hw.smul 1).add (RatPolyCoeffEqv.refl polyZero)).trans (singleton_sum _)

-- The scalar coefficient proof above is independent of the plaquette's
-- coordinate ledger. Only the enclosing singleton syntax is reduced below.
attribute [local irreducible] plaquette

/-- Remove only the literal singleton/empty-product bookkeeping. -/
theorem sourceSpan_character (width : Nat) :
    RatPolyCoeffEqv (sourceSpan width presentation) (character width) := by
  simpa only [sourceSpan, presentation, windowProbe, sourceProbe,
    BF4ExactSlabTemporalSweep.product, BF4ExactSlabTemporalSweep.factor,
    polynomialProduct, finitePolySum, List.foldr_cons, List.foldr_nil,
    Nat.zero_mul, SU2QuaternionPartialFactorizedHaar.liftBoundary, character]
    using singleton_ledger (character width)

private theorem mixed_mean (width : Nat) :
    RatPolyCoeffEqv (mixedProduct width 0 (encodeChart 0 presentation) (encodeChart 0 unitSpan))
      (character width) :=
  ((sourceSpan_character width).mul (RatPolyCoeffEqv.refl polyOne)).trans
    (RatPolyCoeffEqv.mul_one _)

private theorem mixed_square (width : Nat) :
    RatPolyCoeffEqv (mixedProduct width 0 (encodeChart 0 presentation) (encodeChart 0 presentation))
      (polyMul (character width) (character width)) :=
  (sourceSpan_character width).mul (sourceSpan_character width)

/-- The finite first moment uses the same original chain and its partition. -/
theorem chartScalar_mean_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (hwidth : 0 < width) (stage t : Nat) :
    chartScalar hw0 hw1 width stage 0 (span width hwidth) (unit width) t ≈
      middleRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) t t (character width) :=
  Q'.eqv_trans _ _ _
    (chartScalar_pin hw0 hw1 width stage 0 (span width hwidth) (unit width)
      (Nat.le_refl 0) (Nat.le_refl 0) t)
    (Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) t 0 t (mixed_mean width))
      (windowRatio_zero hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) t t
        (character_supported width)))

/-- Reflection fixes this central face, so the diagonal is its ordinary
second moment in the same central density, not a new normalization. -/
theorem chartScalar_square_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (hwidth : 0 < width) (stage t : Nat) :
    chartScalar hw0 hw1 width stage 0 (span width hwidth) (span width hwidth) t ≈
      middleRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) t t
        (polyMul (character width) (character width)) :=
  Q'.eqv_trans _ _ _
    (chartScalar_pin hw0 hw1 width stage 0 (span width hwidth) (span width hwidth)
      (Nat.le_refl 0) (Nat.le_refl 0) t)
    (Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) t 0 t (mixed_square width))
      (windowRatio_zero hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) t t
        (supported_polyMul (character_supported width) (character_supported width))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter.face
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter.face_mem
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter.character
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter.character_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter.character_mean_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter.character_square_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter.presentation
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter.presentation_physical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter.span
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter.span_radius
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter.sourceSpan_character
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter.chartScalar_mean_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter.chartScalar_square_pin
