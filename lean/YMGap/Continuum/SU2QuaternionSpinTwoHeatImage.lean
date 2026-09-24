/-
# Retained image of the selected spin-two plaquette solid

Put the selected lower link in block zero, its heat-kernel partner in block
one, and the other three plaquette links in blocks two, three and four.  The
computed retained substitution replaces the selected link by its partner and
deletes the empty head.  For spin two, this is exactly the canonical exposed
solid on the four retained blocks.  This is the algebraic image needed by the
selected harmonic heat transmission theorem; no heat eigenaction is assumed.
-/

import YMGap.Continuum.SU2QuaternionHarmonicHeatInsertion
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonic
import YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
import YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
import YMGap.Continuum.SU2QuaternionAngularSupport
import YMGap.Continuum.SU2QuaternionRatPolyDifferential
import YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
import YMGap.Continuum.QuaternionHaarAngularCarrier
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

namespace YMGap.Continuum.SU2QuaternionSpinTwoHeatImage

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution
open YMGap.Continuum.SU2QuaternionHarmonicHeatInsertion
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.RGTransport (qpow)

local infix:50 " ≈ " => Q'.eqv

/-- The plaquette word in the selected heat chart.  Block one is deliberately
reserved for the retained heat-kernel partner. -/
def selectedWord (r0 r1 r2 r3 : Bool) : PolyQuaternion :=
  PolyQuaternion.mul
    (PolyQuaternion.mul
      (PolyQuaternion.mul
        (orientedCoordinateQuaternion 0 r0)
        (orientedCoordinateQuaternion 2 r1))
      (orientedCoordinateQuaternion 3 r2))
    (orientedCoordinateQuaternion 4 r3)

/-- The homogeneous radius term on exactly the four plaquette blocks. -/
def selectedRadius : RatPoly :=
  fourQuaternionRadiusProductAt 0 2 3 4

/-- The degree-two homogeneous representative before the selected heat step. -/
def selectedSolidTwo (r0 r1 r2 r3 : Bool) : RatPoly :=
  solidZonalCharacterPolynomial (selectedWord r0 r1 r2 r3).scalar
    selectedRadius 2

/-- The selected solid is genuinely supported on the five-block heat chart. -/
theorem selectedSolidTwo_supported (r0 r1 r2 r3 : Bool) :
    SupportedQuaternionBlocks 5 (selectedSolidTwo r0 r1 r2 r3) := by
  have oriented (block : Nat) (hb : block < 5) (r : Bool) :
      QuaternionSupported 5 (orientedCoordinateQuaternion block r) := by
    cases r
    · exact QuaternionSupported.coordinate hb
    · exact (QuaternionSupported.coordinate hb).conj
  have hs : SupportedQuaternionBlocks 5 (selectedWord r0 r1 r2 r3).scalar :=
    ((((oriented 0 (by omega) r0).mul (oriented 2 (by omega) r1)).mul
      (oriented 3 (by omega) r2)).mul (oriented 4 (by omega) r3)).scalar
  have hr : SupportedQuaternionBlocks 5 selectedRadius := by
    exact supported_polyMul (quaternionRadiusPolynomial_supported 5 0 (by omega))
      (supported_polyMul (quaternionRadiusPolynomial_supported 5 2 (by omega))
        (supported_polyMul (quaternionRadiusPolynomial_supported 5 3 (by omega))
          (quaternionRadiusPolynomial_supported 5 4 (by omega))))
  unfold selectedSolidTwo solidZonalCharacterPolynomial
  exact polyAdd_supported
    (supported_polyMul (polySmul_supported hs 2) (polySmul_supported hs 2))
    (polySmul_supported (supported_polyMul hr (supported_one 5)) (-1))

/-- Exact homogeneous degree in the selected lower block. -/
theorem selectedSolidTwo_degree (r0 r1 r2 r3 : Bool) :
    HasQuaternionBlockDegree 0 2 (selectedSolidTwo r0 r1 r2 r3) := by
  have hs : HasQuaternionBlockDegree 0 1 (selectedWord r0 r1 r2 r3).scalar := by
    have h := (((orientedCoordinateQuaternion_blockDegree 0 0 r0).mul
      (orientedCoordinateQuaternion_blockDegree 2 0 r1)).mul
      (orientedCoordinateQuaternion_blockDegree 3 0 r2)).mul
      (orientedCoordinateQuaternion_blockDegree 4 0 r3)
    simpa only [selectedWord, if_pos, if_neg (by omega : ¬ 0 = 2),
      if_neg (by omega : ¬ 0 = 3), if_neg (by omega : ¬ 0 = 4),
      Nat.add_zero] using h.scalar
  have hr : HasQuaternionBlockDegree 0 2 selectedRadius := by
    have h := (hasQuaternionBlockDegree_radius 0 0).mul
      ((hasQuaternionBlockDegree_radius 2 0).mul
        ((hasQuaternionBlockDegree_radius 3 0).mul
          (hasQuaternionBlockDegree_radius 4 0)))
    exact HasQuaternionBlockDegree.relabel (by decide) h
  exact solidZonalCharacterPolynomial_blockDegree hs hr 2

private def substituteQuaternion (q : PolyQuaternion) : PolyQuaternion where
  scalar := substituteRetained q.scalar
  iPart := substituteRetained q.iPart
  jPart := substituteRetained q.jPart
  kPart := substituteRetained q.kPart

private theorem substituteRetained_neg (p : RatPoly) :
    RatPolyCoeffEqv (substituteRetained (polyNeg p))
      (polyNeg (substituteRetained p)) :=
  (substituteRetained_congr
      (QuaternionHaarAngularCarrier.neg_smul p)).trans
    ((substituteRetained_smul (-1) p).trans
      (QuaternionHaarAngularCarrier.neg_smul _).symm)

private theorem substituteQuaternion_conj (q : PolyQuaternion) :
    PolyQuaternionCoeffEqv (substituteQuaternion (PolyQuaternion.conj q))
      (PolyQuaternion.conj (substituteQuaternion q)) :=
  ⟨RatPolyCoeffEqv.refl _, substituteRetained_neg _,
    substituteRetained_neg _, substituteRetained_neg _⟩

private theorem substituteQuaternion_mul (q r : PolyQuaternion) :
    PolyQuaternionCoeffEqv (substituteQuaternion (PolyQuaternion.mul q r))
      (PolyQuaternion.mul (substituteQuaternion q) (substituteQuaternion r)) := by
  let hm : ∀ a b : RatPoly,
      RatPolyCoeffEqv (substituteRetained (polyMul a b))
        (polyMul (substituteRetained a) (substituteRetained b)) :=
    fun a b => substituteRetained_mul a b
  let ha : ∀ a b : RatPoly,
      RatPolyCoeffEqv (substituteRetained (polyAdd a b))
        (polyAdd (substituteRetained a) (substituteRetained b)) :=
    fun a b => substituteRetained_add a b
  let hn : ∀ a : RatPoly,
      RatPolyCoeffEqv (substituteRetained (polyNeg a))
        (polyNeg (substituteRetained a)) :=
    fun a => substituteRetained_neg a
  constructor
  · exact (ha _ _).trans ((hm _ _).add
      ((hn _).trans ((RatPolyCoeffEqv.neg (ha _ _)).trans
        (RatPolyCoeffEqv.neg
          ((hm _ _).add ((ha _ _).trans ((hm _ _).add (hm _ _))))))))
  · exact (ha _ _).trans ((hm _ _).add ((ha _ _).trans
      ((hm _ _).add ((ha _ _).trans
        ((hm _ _).add ((hn _).trans (RatPolyCoeffEqv.neg (hm _ _))))))))
  · exact (ha _ _).trans ((hm _ _).add ((ha _ _).trans
      ((hm _ _).add ((ha _ _).trans
        ((hm _ _).add ((hn _).trans (RatPolyCoeffEqv.neg (hm _ _))))))))
  · exact (ha _ _).trans ((hm _ _).add ((ha _ _).trans
      ((hm _ _).add ((ha _ _).trans
        ((hm _ _).add ((hn _).trans (RatPolyCoeffEqv.neg (hm _ _))))))))

private theorem substituteQuaternion_coordinate_zero :
    PolyQuaternionCoeffEqv
      (substituteQuaternion (PolyQuaternion.coordinateVariable 0))
      (PolyQuaternion.coordinateVariable 0) :=
  ⟨substituteRetained_head_coordinate 0, substituteRetained_head_coordinate 1,
    substituteRetained_head_coordinate 2, substituteRetained_head_coordinate 3⟩

private theorem substituteQuaternion_coordinate_two :
    PolyQuaternionCoeffEqv
      (substituteQuaternion (PolyQuaternion.coordinateVariable 2))
      (PolyQuaternion.coordinateVariable 1) := by
  constructor <;> apply RatPolyCoeffEqv.of_canon_termwise <;> decide +kernel

private theorem substituteQuaternion_coordinate_three :
    PolyQuaternionCoeffEqv
      (substituteQuaternion (PolyQuaternion.coordinateVariable 3))
      (PolyQuaternion.coordinateVariable 2) := by
  constructor <;> apply RatPolyCoeffEqv.of_canon_termwise <;> decide +kernel

private theorem substituteQuaternion_coordinate_four :
    PolyQuaternionCoeffEqv
      (substituteQuaternion (PolyQuaternion.coordinateVariable 4))
      (PolyQuaternion.coordinateVariable 3) := by
  constructor <;> apply RatPolyCoeffEqv.of_canon_termwise <;> decide +kernel

private theorem substituteQuaternion_oriented_zero (r : Bool) :
    PolyQuaternionCoeffEqv
      (substituteQuaternion (orientedCoordinateQuaternion 0 r))
      (orientedCoordinateQuaternion 0 r) := by
  cases r
  · exact substituteQuaternion_coordinate_zero
  · exact substituteQuaternion_conj _ |>.trans
      substituteQuaternion_coordinate_zero.conj

private theorem substituteQuaternion_oriented_two (r : Bool) :
    PolyQuaternionCoeffEqv
      (substituteQuaternion (orientedCoordinateQuaternion 2 r))
      (orientedCoordinateQuaternion 1 r) := by
  cases r
  · exact substituteQuaternion_coordinate_two
  · exact substituteQuaternion_conj _ |>.trans
      substituteQuaternion_coordinate_two.conj

private theorem substituteQuaternion_oriented_three (r : Bool) :
    PolyQuaternionCoeffEqv
      (substituteQuaternion (orientedCoordinateQuaternion 3 r))
      (orientedCoordinateQuaternion 2 r) := by
  cases r
  · exact substituteQuaternion_coordinate_three
  · exact substituteQuaternion_conj _ |>.trans
      substituteQuaternion_coordinate_three.conj

private theorem substituteQuaternion_oriented_four (r : Bool) :
    PolyQuaternionCoeffEqv
      (substituteQuaternion (orientedCoordinateQuaternion 4 r))
      (orientedCoordinateQuaternion 3 r) := by
  cases r
  · exact substituteQuaternion_coordinate_four
  · exact substituteQuaternion_conj _ |>.trans
      substituteQuaternion_coordinate_four.conj

private theorem substituteRetained_selectedScalar
    (r0 r1 r2 r3 : Bool) :
    RatPolyCoeffEqv
      (substituteRetained (selectedWord r0 r1 r2 r3).scalar)
      (exposedFourWord r0 r1 r2 r3).scalar :=
  (substituteQuaternion_mul _ _).trans
    (((substituteQuaternion_mul _ _).trans
      (((substituteQuaternion_mul _ _).trans
        ((substituteQuaternion_oriented_zero r0).mul
          (substituteQuaternion_oriented_two r1))).mul
        (substituteQuaternion_oriented_three r2))).mul
      (substituteQuaternion_oriented_four r3)) |>.scalar

private theorem substituteRetained_radius_zero :
    RatPolyCoeffEqv (substituteRetained (quaternionRadiusPolynomial 0))
      (quaternionRadiusPolynomial 0) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

private theorem substituteRetained_radius_two :
    RatPolyCoeffEqv (substituteRetained (quaternionRadiusPolynomial 2))
      (quaternionRadiusPolynomial 1) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

private theorem substituteRetained_radius_three :
    RatPolyCoeffEqv (substituteRetained (quaternionRadiusPolynomial 3))
      (quaternionRadiusPolynomial 2) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

private theorem substituteRetained_radius_four :
    RatPolyCoeffEqv (substituteRetained (quaternionRadiusPolynomial 4))
      (quaternionRadiusPolynomial 3) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

private theorem substituteRetained_selectedRadius :
    RatPolyCoeffEqv (substituteRetained selectedRadius)
      fourQuaternionRadiusProduct := by
  unfold selectedRadius fourQuaternionRadiusProductAt fourQuaternionRadiusProduct
  exact (substituteRetained_mul _ _).trans
    (substituteRetained_radius_zero.mul
      ((substituteRetained_mul _ _).trans
        (substituteRetained_radius_two.mul
          ((substituteRetained_mul _ _).trans
            (substituteRetained_radius_three.mul substituteRetained_radius_four)))))

private theorem substituteRetained_one :
    RatPolyCoeffEqv (substituteRetained polyOne) polyOne := by
  exact (substituteRetained_degree_zero (hasQuaternionBlockDegree_one 0)).trans
    (RatPolyCoeffEqv.refl polyOne)

/-- Exact dropped-head substitution.  Both the old head block zero and its
retained partner block one become new block zero; the three remaining
plaquette blocks shift from `2,3,4` to `1,2,3`. -/
theorem substituteRetained_selectedSolidTwo
    (r0 r1 r2 r3 : Bool) :
    RatPolyCoeffEqv
      (substituteRetained (selectedSolidTwo r0 r1 r2 r3))
      (exposedSolidZonalCharacter r0 r1 r2 r3 2) := by
  let s := (selectedWord r0 r1 r2 r3).scalar
  let t := (exposedFourWord r0 r1 r2 r3).scalar
  have hs : RatPolyCoeffEqv (substituteRetained (polySmul 2 s)) (polySmul 2 t) :=
    (substituteRetained_smul 2 s).trans
      ((substituteRetained_selectedScalar r0 r1 r2 r3).smul 2)
  have hfirst : RatPolyCoeffEqv
      (substituteRetained (polyMul (polySmul 2 s) (polySmul 2 s)))
      (polyMul (polySmul 2 t) (polySmul 2 t)) :=
    (substituteRetained_mul _ _).trans (hs.mul hs)
  have hproduct : RatPolyCoeffEqv
      (substituteRetained (polyMul selectedRadius polyOne))
      (polyMul fourQuaternionRadiusProduct polyOne) :=
    (substituteRetained_mul _ _).trans
      (substituteRetained_selectedRadius.mul substituteRetained_one)
  have hsecond : RatPolyCoeffEqv
      (substituteRetained (polySmul (-1) (polyMul selectedRadius polyOne)))
      (polySmul (-1) (polyMul fourQuaternionRadiusProduct polyOne)) :=
    (substituteRetained_smul (-1) _).trans (hproduct.smul (-1))
  unfold selectedSolidTwo exposedSolidZonalCharacter solidZonalCharacterPolynomial
  exact (substituteRetained_add _ _).trans (hfirst.add hsecond)

/-- The full retained image follows functorially from the preceding computed
substitution; no second polynomial normalization is performed.  This is the
form used by
`harmonic_transmission_same_carrier`. -/
theorem retainedImage_selectedSolidTwo
    (r0 r1 r2 r3 : Bool) :
    RatPolyCoeffEqv
      (retainedImage (selectedSolidTwo r0 r1 r2 r3))
      (liftHead (exposedSolidZonalCharacter r0 r1 r2 r3 2)) := by
  unfold retainedImage
  simpa only [liftBoundary] using
    (lift_coeff 1 (substituteRetained_selectedSolidTwo r0 r1 r2 r3))

end YMGap.Continuum.SU2QuaternionSpinTwoHeatImage

#print axioms YMGap.Continuum.SU2QuaternionSpinTwoHeatImage.substituteRetained_selectedSolidTwo
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoHeatImage.retainedImage_selectedSolidTwo
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoHeatImage.selectedSolidTwo_supported
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoHeatImage.selectedSolidTwo_degree
