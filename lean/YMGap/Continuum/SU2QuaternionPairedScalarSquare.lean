/-
# Actual paired relative-scalar derivative complements

On the SAME rational quaternion Haar carrier the three paired first jets
of coordinateVariable(0)*conj(coordinateVariable(1)) are the negatives of
its three vector components. Actual norm multiplicativity then identifies
1-X^2-(J_i X)^2 with the OTHER TWO component squares. The resulting
Type-valued Certificate is constructed, not supplied as a coordinate cone.

The pins retain arbitrary original insertions. They do not identify a group
flow, transport to arbitrary blocks, or claim a heat/conditional/OS bound.
-/

import YMGap.Continuum.SU2QuaternionPairedFrameScalarJets
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.SU2QuaternionPairedScalarSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection (relativeScalar)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (pairedDerivative)
open YMGap.Continuum.SU2QuaternionHaarSparseEquality (carrier_of_canon_check)
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound

/-- The literal quaternion word whose scalar is relativeScalar. -/
def relativeWord : PolyQuaternion :=
  PolyQuaternion.mul (PolyQuaternion.coordinateVariable 0)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 1))

/-- Actual vector components, in the same order as the plus-paired jets. -/
def relativeVector (i : Fin 3) : RatPoly :=
  match i.val with
  | 0 => relativeWord.iPart
  | 1 => relativeWord.jPart
  | _ => relativeWord.kPart

private theorem direction_cases (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

/-- Sparse polynomial checks produce the ACTUAL first-jet carrier pins.
The private scalar-jet theorem in the earlier leaf is not assumed here. -/
theorem paired_first_jet (blocks : Nat) (i : Fin 3) :
    HaarCarrierEqv blocks (pairedDerivative i relativeScalar)
      (polyNeg (relativeVector i)) := by
  rcases direction_cases i with rfl | rfl | rfl
  all_goals (apply carrier_of_canon_check; decide +kernel)

theorem relativeWord_supported {blocks : Nat} (hb : 1 < blocks) :
    Supported blocks relativeWord :=
  (Supported.coordinate (by omega : 0 < blocks)).mul (Supported.coordinate hb).conj

/-- Actual unit norm under every Haar insertion; no disjointness or
pointwise unit-norm premise is added. -/
theorem relativeWord_unit {blocks : Nat} (hb : 1 < blocks) :
    HaarCarrierEqv blocks (polyQuaternionNorm relativeWord) polyOne :=
  haarNorm_mul (haarNorm_coordinate (by omega : 0 < blocks))
    ((RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)).trans
      (haarNorm_coordinate hb))

/-- Existing scalar-square API specialized to this SAME actual word. -/
def relativeScalarSquare {blocks : Nat} (hb : 1 < blocks) :
    SquareBound blocks relativeScalar 1 :=
  SquareBound.scalar (relativeWord_supported hb) (relativeWord_unit hb)

/-- The desired original paired derivative complement. -/
def complementPolynomial (i : Fin 3) : RatPoly :=
  polyAdd (polyAdd polyOne (polyNeg (polyMul relativeScalar relativeScalar)))
    (polyNeg (polyMul (pairedDerivative i relativeScalar) (pairedDerivative i relativeScalar)))

/-- Literal sum of the other two component squares. -/
def complementSquares (i : Fin 3) : RatPoly :=
  match i.val with
  | 0 => polyAdd (polyMul relativeWord.jPart relativeWord.jPart)
      (polyMul relativeWord.kPart relativeWord.kPart)
  | 1 => polyAdd (polyMul relativeWord.iPart relativeWord.iPart)
      (polyMul relativeWord.kPart relativeWord.kPart)
  | _ => polyAdd (polyMul relativeWord.iPart relativeWord.iPart)
      (polyMul relativeWord.jPart relativeWord.jPart)

private def sqExpr (e : PolyExpr) : PolyExpr := .mul e e
private def normExpr : PolyExpr :=
  .add (sqExpr (.var 0)) (.add (sqExpr (.var 1))
    (.add (sqExpr (.var 2)) (sqExpr (.var 3))))
private def complementExpr (i : Fin 3) : PolyExpr :=
  .add (.add normExpr (.neg (sqExpr (.var 0)))) (.neg (sqExpr (.var (i.val+1))))
private def remainingExpr (i : Fin 3) : PolyExpr :=
  match i.val with
  | 0 => .add (sqExpr (.var 2)) (sqExpr (.var 3))
  | 1 => .add (sqExpr (.var 1)) (sqExpr (.var 3))
  | _ => .add (sqExpr (.var 1)) (sqExpr (.var 2))

private theorem complement_coeff (i : Fin 3) :
    RatPolyCoeffEqv
      (polyAdd
        (polyAdd (polyQuaternionNorm relativeWord) (polyNeg (polyMul relativeScalar relativeScalar)))
        (polyNeg (polyMul (relativeVector i) (relativeVector i))))
      (complementSquares i) := by
  rcases direction_cases i with rfl | rfl | rfl
  · exact coeffEvalExpr_eqv_of_normalize_eq
      (complementExpr 0) (remainingExpr 0) (by decide) (fun
        | 0 => relativeWord.scalar
        | 1 => relativeWord.iPart
        | 2 => relativeWord.jPart
        | _ => relativeWord.kPart)
  · exact coeffEvalExpr_eqv_of_normalize_eq
      (complementExpr 1) (remainingExpr 1) (by decide) (fun
        | 0 => relativeWord.scalar
        | 1 => relativeWord.iPart
        | 2 => relativeWord.jPart
        | _ => relativeWord.kPart)
  · exact coeffEvalExpr_eqv_of_normalize_eq
      (complementExpr 2) (remainingExpr 2) (by decide) (fun
        | 0 => relativeWord.scalar
        | 1 => relativeWord.iPart
        | 2 => relativeWord.jPart
        | _ => relativeWord.kPart)

/-- Exact two-square identity on the original carrier, with padding and
unit norm retained as actual arbitrary-insertion Haar relations. -/
theorem complementSquare_pin {blocks : Nat} (hb : 1 < blocks) (i : Fin 3) :
    HaarCarrierEqv blocks (complementPolynomial i) (complementSquares i) := by
  have hj := paired_first_jet blocks i
  have hs : HaarCarrierEqv blocks
      (polyMul (pairedDerivative i relativeScalar) (pairedDerivative i relativeScalar))
      (polyMul (relativeVector i) (relativeVector i)) :=
    (HaarCarrierEqv.mul hj hj).trans
      (RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
        (sqExpr (.neg (.var 0))) (sqExpr (.var 0)) (by decide) (fun _ => relativeVector i)))
  exact (HaarCarrierEqv.add
    (HaarCarrierEqv.add (relativeWord_unit hb).symm (HaarCarrierEqv.refl blocks _))
    (HaarCarrierEqv.neg hs)).trans (RatPolyCoeffEqv.haarCarrier (complement_coeff i))

/-- Constructed complement certificate for every original paired direction,
not a supplied cone inequality. No division or strict heat floor is used. -/
def complementSquare {blocks : Nat} (hb : 1 < blocks) (i : Fin 3) :
    Certificate blocks (complementPolynomial i) := by
  have hp := relativeWord_supported hb
  apply Certificate.transport (complementSquare_pin hb i)
  unfold complementSquares
  split
  · exact (Certificate.square relativeWord.jPart hp.jPart).add (.square relativeWord.kPart hp.kPart)
  · exact (Certificate.square relativeWord.iPart hp.iPart).add (.square relativeWord.kPart hp.kPart)
  · exact (Certificate.square relativeWord.iPart hp.iPart).add (.square relativeWord.jPart hp.jPart)

end YMGap.Continuum.SU2QuaternionPairedScalarSquare

#print axioms YMGap.Continuum.SU2QuaternionPairedScalarSquare.relativeWord
#print axioms YMGap.Continuum.SU2QuaternionPairedScalarSquare.relativeVector
#print axioms YMGap.Continuum.SU2QuaternionPairedScalarSquare.paired_first_jet
#print axioms YMGap.Continuum.SU2QuaternionPairedScalarSquare.relativeWord_supported
#print axioms YMGap.Continuum.SU2QuaternionPairedScalarSquare.relativeWord_unit
#print axioms YMGap.Continuum.SU2QuaternionPairedScalarSquare.relativeScalarSquare
#print axioms YMGap.Continuum.SU2QuaternionPairedScalarSquare.complementPolynomial
#print axioms YMGap.Continuum.SU2QuaternionPairedScalarSquare.complementSquares
#print axioms YMGap.Continuum.SU2QuaternionPairedScalarSquare.complementSquare_pin
#print axioms YMGap.Continuum.SU2QuaternionPairedScalarSquare.complementSquare
