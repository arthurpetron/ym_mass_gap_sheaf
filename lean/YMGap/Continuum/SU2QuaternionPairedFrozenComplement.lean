/-
# Frozen-direction complement for the actual paired quaternion frame

For arbitrary supported polynomial coefficients u, the three frozen first
jets have the exact Lagrange complement
|u|^2 (1-X^2) - (sum u_i D_i X)^2. The norm and first-jet carrier pins are
used before the finite coefficient identity, yielding a literal sum of
three supported squares on the original Haar carrier. No coefficient is
differentiated and no radius is inverted.
-/

import YMGap.Continuum.SU2QuaternionPairedScalarSquare
import YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame

namespace YMGap.Continuum.SU2QuaternionPairedFrozenComplement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection (relativeScalar)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (pairedDerivative threeSum frozenSecondJet)
open YMGap.Continuum.SU2QuaternionPairedScalarSquare
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarSquareCertificate.Certificate

local infix:50 " ≈ " => Q'.eqv

private theorem direction_cases (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

/-- Actual frozen contraction of the three paired first derivatives.
The coefficient polynomials are multiplied after differentiation. -/
def frozenFirstJet (u : Fin 3 → RatPoly) (p : RatPoly) : RatPoly :=
  threeSum (fun i => polyMul (u i) (pairedDerivative i p))

/-- Cleared first-jet complement for the same actual relative scalar. -/
def frozenComplement (u : Fin 3 → RatPoly) : RatPoly :=
  polyAdd
    (polyMul (threeSquare u)
      (polyAdd polyOne (polyNeg (polyMul relativeScalar relativeScalar))))
    (polyNeg (polyMul (frozenFirstJet u relativeScalar)
      (frozenFirstJet u relativeScalar)))

/-- The three components of the ordinary cross product u × Z, where Z is
the actual vector part of the relative quaternion word. -/
def crossProduct (u : Fin 3 → RatPoly) (i : Fin 3) : RatPoly :=
  match i.val with
  | 0 => polyAdd (polyMul (u 1) (relativeVector 2))
      (polyNeg (polyMul (u 2) (relativeVector 1)))
  | 1 => polyAdd (polyMul (u 2) (relativeVector 0))
      (polyNeg (polyMul (u 0) (relativeVector 2)))
  | _ => polyAdd (polyMul (u 0) (relativeVector 1))
      (polyNeg (polyMul (u 1) (relativeVector 0)))

/-- Literal sum of the three cross-product squares. -/
def crossSquares (u : Fin 3 → RatPoly) : RatPoly :=
  threeSum (fun i => polyMul (crossProduct u i) (crossProduct u i))

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem vector_supported {blocks : Nat} (hb : 1 < blocks) (i : Fin 3) :
    SupportedQuaternionBlocks blocks (relativeVector i) := by
  have hp := relativeWord_supported hb
  rcases direction_cases i with rfl | rfl | rfl
  · exact hp.iPart
  · exact hp.jPart
  · exact hp.kPart

private theorem threeSum_congr {f g : Fin 3 → RatPoly}
    (h : ∀ i, RatPolyCoeffEqv (f i) (g i)) :
    RatPolyCoeffEqv (threeSum f) (threeSum g) :=
  (h 0).add ((h 1).add (h 2))

private theorem neg_product (p q : RatPoly) :
    RatPolyCoeffEqv (polyMul p (polyNeg q)) (polyNeg (polyMul p q)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.neg (.var 1)))
    (.neg (.mul (.var 0) (.var 1))) (by decide) (fun | 0 => p | _ => q)

private theorem frozen_first_pin {blocks : Nat} (u : Fin 3 → RatPoly) :
    HaarCarrierEqv blocks (frozenFirstJet u relativeScalar)
      (polyNeg (threeSum (fun i => polyMul (u i) (relativeVector i)))) := by
  have hterm (i : Fin 3) : HaarCarrierEqv blocks
      (polyMul (u i) (pairedDerivative i relativeScalar))
      (polyNeg (polyMul (u i) (relativeVector i))) := by
    exact (paired_first_jet blocks i).mul_left (u i) |>.trans
      (RatPolyCoeffEqv.haarCarrier (neg_product (u i) (relativeVector i)))
  exact (HaarCarrierEqv.add (hterm 0) (HaarCarrierEqv.add (hterm 1) (hterm 2))).trans
    (RatPolyCoeffEqv.haarCarrier
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.neg (.mul (.var 0) (.var 1)))
          (.add (.neg (.mul (.var 2) (.var 3))) (.neg (.mul (.var 4) (.var 5)))))
        (.neg (.add (.mul (.var 0) (.var 1))
          (.add (.mul (.var 2) (.var 3)) (.mul (.var 4) (.var 5)))))
        (by decide) (fun
          | 0 => u 0 | 1 => relativeVector 0
          | 2 => u 1 | 3 => relativeVector 1
          | 4 => u 2 | _ => relativeVector 2)))

private theorem unit_complement_pin {blocks : Nat} (hb : 1 < blocks) :
    HaarCarrierEqv blocks
      (polyAdd polyOne (polyNeg (polyMul relativeScalar relativeScalar)))
      (threeSquare (relativeVector)) := by
  have hnorm : RatPolyCoeffEqv (polyQuaternionNorm relativeWord)
      (polyAdd (polyMul relativeScalar relativeScalar)
        (threeSquare (relativeVector))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 0))
        (.add (.mul (.var 1) (.var 1))
          (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))))
      (.add (.mul (.var 0) (.var 0))
        (.add (.mul (.var 1) (.var 1))
          (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))))
      (by decide) (fun
        | 0 => relativeScalar | 1 => relativeVector 0
        | 2 => relativeVector 1 | _ => relativeVector 2)
  have hunit := HaarCarrierEqv.add (relativeWord_unit hb).symm
    (HaarCarrierEqv.refl blocks (polyNeg (polyMul relativeScalar relativeScalar)))
  exact hunit.trans (RatPolyCoeffEqv.haarCarrier
    (hnorm.add (RatPolyCoeffEqv.refl (polyNeg (polyMul relativeScalar relativeScalar))) |>.trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
        (by decide) (fun
          | 0 => polyMul relativeScalar relativeScalar
          | _ => threeSquare relativeVector))))

private def polyExprSq (e : PolyExpr) : PolyExpr := .mul e e
private def polyExprAdd3 (a b c : PolyExpr) : PolyExpr := .add a (.add b c)
private def polyExprThreeSq (a b c : PolyExpr) : PolyExpr :=
  polyExprAdd3 (polyExprSq a) (polyExprSq b) (polyExprSq c)
private def polyExprDot (a b c x y z : PolyExpr) : PolyExpr :=
  polyExprAdd3 (.mul a x) (.mul b y) (.mul c z)
private def polyExprCross0 (b c y z : PolyExpr) : PolyExpr :=
  .add (.mul b z) (.neg (.mul c y))
private def polyExprCross1 (a c x z : PolyExpr) : PolyExpr :=
  .add (.mul c x) (.neg (.mul a z))
private def polyExprCross2 (a b x y : PolyExpr) : PolyExpr :=
  .add (.mul a y) (.neg (.mul b x))
private def polyExprCrossSq (a b c x y z : PolyExpr) : PolyExpr :=
  polyExprAdd3 (polyExprSq (polyExprCross0 b c y z))
    (polyExprSq (polyExprCross1 a c x z))
    (polyExprSq (polyExprCross2 a b x y))

private theorem lagrange_pin (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyMul (threeSquare u) (threeSquare relativeVector))
        (polyNeg (polyMul (threeSum (fun i => polyMul (u i) (relativeVector i)))
          (threeSum (fun i => polyMul (u i) (relativeVector i))))))
      (crossSquares u) := by
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add
      (.mul (polyExprThreeSq (.var 0) (.var 1) (.var 2))
        (polyExprThreeSq (.var 3) (.var 4) (.var 5)))
      (.neg (.mul (polyExprDot (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5))
        (polyExprDot (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5)))))
    (polyExprCrossSq (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5))
    (by decide) (fun
      | 0 => u 0 | 1 => u 1 | 2 => u 2
      | 3 => relativeVector 0 | 4 => relativeVector 1 | _ => relativeVector 2)

/-- Actual carrier equality of the frozen complement with the literal
Lagrange sum. The quaternion norm and all three paired first jets are used
before the coefficientwise Lagrange identity. -/
theorem frozen_complement_pin {blocks : Nat} (hb : 1 < blocks)
    (u : Fin 3 → RatPoly) :
    HaarCarrierEqv blocks (frozenComplement u) (crossSquares u) := by
  let R := threeSquare u
  let Z2 := threeSquare relativeVector
  let V := threeSum (fun i => polyMul (u i) (relativeVector i))
  have hunit := unit_complement_pin hb
  have hfirst := frozen_first_pin (blocks := blocks) u
  have hfirstSq : HaarCarrierEqv blocks
      (polyMul (frozenFirstJet u relativeScalar) (frozenFirstJet u relativeScalar))
      (polyMul V V) := by
    exact (HaarCarrierEqv.mul hfirst hfirst).trans
      (RatPolyCoeffEqv.haarCarrier
        (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.neg (.var 0)) (.neg (.var 0))) (.mul (.var 0) (.var 0))
          (by decide) (fun _ => V)))
  have hradial : HaarCarrierEqv blocks
      (polyMul R (polyAdd polyOne (polyNeg (polyMul relativeScalar relativeScalar))))
      (polyMul R Z2) := hunit.mul_left R
  exact (HaarCarrierEqv.add hradial (HaarCarrierEqv.neg hfirstSq)).trans
    (RatPolyCoeffEqv.haarCarrier (lagrange_pin u))

private theorem cross_supported {blocks : Nat} (hb : 1 < blocks)
    (u : Fin 3 → RatPoly) (hu : ∀ i, SupportedQuaternionBlocks blocks (u i))
    (i : Fin 3) : SupportedQuaternionBlocks blocks (crossProduct u i) := by
  have hv := vector_supported hb
  rcases direction_cases i with rfl | rfl | rfl
  · exact supported_add (supported_polyMul (hu 1) (hv 2))
      (support_neg (supported_polyMul (hu 2) (hv 1)))
  · exact supported_add (supported_polyMul (hu 2) (hv 0))
      (support_neg (supported_polyMul (hu 0) (hv 2)))
  · exact supported_add (supported_polyMul (hu 0) (hv 1))
      (support_neg (supported_polyMul (hu 1) (hv 0)))

/-- Constructive certificate for the frozen coefficient complement. The
only cone input is explicit finite support of the three coefficient
polynomials; no radius division or pointwise positivity premise occurs. -/
def frozen_complement_certificate {blocks : Nat} (hb : 1 < blocks)
    (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks blocks (u i)) :
    Certificate blocks (frozenComplement u) := by
  have h0 := cross_supported hb u hu 0
  have h1 := cross_supported hb u hu 1
  have h2 := cross_supported hb u hu 2
  have Q : Certificate blocks (crossSquares u) := by
    unfold crossSquares threeSum
    exact (Certificate.square (crossProduct u 0) h0).add
      ((Certificate.square (crossProduct u 1) h1).add
        (Certificate.square (crossProduct u 2) h2))
  exact Certificate.transport (frozen_complement_pin hb u) Q

end YMGap.Continuum.SU2QuaternionPairedFrozenComplement

#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenComplement.frozenFirstJet
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenComplement.frozenComplement
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenComplement.crossSquares
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenComplement.frozen_complement_pin
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenComplement.frozen_complement_certificate
