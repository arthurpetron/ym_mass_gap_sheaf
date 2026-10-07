/-
# Exact paired scalar jets on the ORIGINAL two-block Haar carrier

The actual relativeScalar=scalarAt 0 1 has second jet -relativeScalar in
each of the three plus-paired angular directions. Distinct directions have
zero symmetrized mixed jet. Padding is handled by proved arbitrary-insertion
Haar equality, never by a false raw coefficient equality.

The resulting polynomial-coefficient second jet is FROZEN: no derivative
acts on a coefficient u. This removes the scalar acceleration correction
from this exact paired jet. It does not identify a group flow, prove a
geodesic/Harnack theorem, or supply useful original-action curvature, score,
survival or OS bounds. Arbitrary-block recoding remains separate.
-/

import YMGap.Continuum.SU2QuaternionAngularCoordinate
import YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
import YMGap.Continuum.SU2QuaternionHaarSparseEquality
import YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame

namespace YMGap.Continuum.SU2QuaternionPairedFrameScalarJets

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection (relativeScalar)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (scalar_supported)
open YMGap.Continuum.SU2QuaternionHaarSparseEquality (carrier_of_canon_check)
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare pairedScorePlus)

/-- The three literal plus-paired derivations on block zero. -/
def pairedDerivative (i : Fin 3) (p : RatPoly) : RatPoly :=
  match i.val with
  | 0 => polyAdd (angularDerivative 0 1 p) (angularDerivative 2 3 p)
  | 1 => polyAdd (angularDerivative 0 2 p) (polyNeg (angularDerivative 1 3 p))
  | _ => polyAdd (angularDerivative 0 3 p) (angularDerivative 1 2 p)

private theorem direction_cases (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

/-- The existing actual paired score uses exactly THESE paired derivations.
Arbitrary original A and b are retained, before any reciprocal or norm bound. -/
theorem pairedScorePlus_zero_derivative_pin (i : Fin 3) (A b : RatPoly) :
    RatPolyCoeffEqv (pairedScorePlus 0 A b i)
      (polyAdd (polyMul A (pairedDerivative i b))
        (polyNeg (polyMul b (pairedDerivative i A)))) := by
  have hp (db da eb ea : RatPoly) : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyMul A db) (polyNeg (polyMul b da)))
        (polyAdd (polyMul A eb) (polyNeg (polyMul b ea))))
      (polyAdd (polyMul A (polyAdd db eb))
        (polyNeg (polyMul b (polyAdd da ea)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 3))))
        (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 5)))))
      (.add (.mul (.var 0) (.add (.var 2) (.var 4)))
        (.neg (.mul (.var 1) (.add (.var 3) (.var 5)))))
      (by decide) (fun | 0 => A | 1 => b | 2 => db | 3 => da | 4 => eb | _ => ea)
  have hm (db da eb ea : RatPoly) : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyMul A db) (polyNeg (polyMul b da)))
        (polyNeg (polyAdd (polyMul A eb) (polyNeg (polyMul b ea)))))
      (polyAdd (polyMul A (polyAdd db (polyNeg eb)))
        (polyNeg (polyMul b (polyAdd da (polyNeg ea))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 3))))
        (.neg (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 5))))))
      (.add (.mul (.var 0) (.add (.var 2) (.neg (.var 4))))
        (.neg (.mul (.var 1) (.add (.var 3) (.neg (.var 5))))))
      (by decide) (fun | 0 => A | 1 => b | 2 => db | 3 => da | 4 => eb | _ => ea)
  rcases direction_cases i with rfl | rfl | rfl
  · exact hp (angularDerivative 0 1 b) (angularDerivative 0 1 A)
      (angularDerivative 2 3 b) (angularDerivative 2 3 A)
  · exact hm (angularDerivative 0 2 b) (angularDerivative 0 2 A)
      (angularDerivative 1 3 b) (angularDerivative 1 3 A)
  · exact hp (angularDerivative 0 3 b) (angularDerivative 0 3 A)
      (angularDerivative 1 2 b) (angularDerivative 1 2 A)

/-- Each paired derivation respects the SAME arbitrary-insertion Haar
carrier. No derivative of a variable direction coefficient is introduced. -/
theorem pairedDerivative_carrier {blocks : Nat} (hb : 0 < blocks)
    (i : Fin 3) {p q : RatPoly} (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks (pairedDerivative i p) (pairedDerivative i q) := by
  rcases direction_cases i with rfl | rfl | rfl
  · exact HaarCarrierEqv.add
      (angularDerivative_carrier hb (by decide) (by decide) h)
      (angularDerivative_carrier hb (by decide) (by decide) h)
  · exact HaarCarrierEqv.add
      (angularDerivative_carrier hb (by decide) (by decide) h)
      (HaarCarrierEqv.neg (angularDerivative_carrier hb (by decide) (by decide) h))
  · exact HaarCarrierEqv.add
      (angularDerivative_carrier hb (by decide) (by decide) h)
      (angularDerivative_carrier hb (by decide) (by decide) h)

/-- Explicit support for BOTH original relative-scalar blocks. -/
theorem relativeScalar_supported {blocks : Nat} (hb : 1 < blocks) :
    SupportedQuaternionBlocks blocks relativeScalar :=
  scalar_supported (by omega : 0 < blocks) hb

private def scalarFirstJet (i : Fin 3) : RatPoly :=
  match i.val with
  | 0 => polyAdd
      (polyAdd (polyMul (polyVar 0) (polyVar 5)) (polyNeg (polyMul (polyVar 1) (polyVar 4))))
      (polyAdd (polyMul (polyVar 2) (polyVar 7)) (polyNeg (polyMul (polyVar 3) (polyVar 6))))
  | 1 => polyAdd
      (polyAdd (polyMul (polyVar 0) (polyVar 6)) (polyNeg (polyMul (polyVar 2) (polyVar 4))))
      (polyNeg (polyAdd (polyMul (polyVar 1) (polyVar 7))
        (polyNeg (polyMul (polyVar 3) (polyVar 5)))))
  | _ => polyAdd
      (polyAdd (polyMul (polyVar 0) (polyVar 7)) (polyNeg (polyMul (polyVar 3) (polyVar 4))))
      (polyAdd (polyMul (polyVar 1) (polyVar 6)) (polyNeg (polyMul (polyVar 2) (polyVar 5))))

private theorem scalar_first_jet (blocks : Nat) (i : Fin 3) :
    HaarCarrierEqv blocks (pairedDerivative i relativeScalar) (scalarFirstJet i) := by
  rcases direction_cases i with rfl | rfl | rfl
  all_goals (apply carrier_of_canon_check; decide +kernel)

/-- The literal repeated paired derivative of the actual relative scalar.
There is no sphere-radius or heat-cutoff hypothesis. -/
theorem relativeScalar_second_jet {blocks : Nat} (hb : 1 < blocks) (i : Fin 3) :
    HaarCarrierEqv blocks (pairedDerivative i (pairedDerivative i relativeScalar))
      (polyNeg relativeScalar) := by
  refine (pairedDerivative_carrier (by omega : 0 < blocks) i
    (scalar_first_jet blocks i)).trans ?_
  rcases direction_cases i with rfl | rfl | rfl
  all_goals (apply carrier_of_canon_check; decide +kernel)

/-- The actual symmetrized mixed jet vanishes for distinct paired directions.
Neither order is silently omitted or replaced by a commuting-jet premise. -/
theorem relativeScalar_mixed_jet {blocks : Nat} (hb : 1 < blocks)
    (i j : Fin 3) (hij : i ≠ j) :
    HaarCarrierEqv blocks
      (polyAdd (pairedDerivative i (pairedDerivative j relativeScalar))
        (pairedDerivative j (pairedDerivative i relativeScalar))) polyZero := by
  refine (HaarCarrierEqv.add
    (pairedDerivative_carrier (by omega : 0 < blocks) i (scalar_first_jet blocks j))
    (pairedDerivative_carrier (by omega : 0 < blocks) j (scalar_first_jet blocks i))).trans ?_
  rcases direction_cases i with rfl | rfl | rfl
  all_goals rcases direction_cases j with rfl | rfl | rfl
  all_goals first
    | exact False.elim (hij rfl)
    | apply carrier_of_canon_check; decide +kernel

/-- A literal three-column sum, with no ambient dimension factor. -/
def threeSum (f : Fin 3 → RatPoly) : RatPoly :=
  polyAdd (f 0) (polyAdd (f 1) (f 2))

/-- Frozen coefficient contraction of ALL NINE ordered actual second jets.
This is not the square of a variable-coefficient differential operator. -/
def frozenSecondJet (u : Fin 3 → RatPoly) (p : RatPoly) : RatPoly :=
  threeSum (fun i => threeSum (fun j =>
    polyMul (polyMul (u i) (u j)) (pairedDerivative i (pairedDerivative j p))))

private theorem frozenSecondJet_grouped (u : Fin 3 → RatPoly) (p : RatPoly) :
    RatPolyCoeffEqv (frozenSecondJet u p)
      (polyAdd
        (threeSum (fun i => polyMul (polyMul (u i) (u i))
          (pairedDerivative i (pairedDerivative i p))))
        (polyAdd
          (polyMul (polyMul (u 0) (u 1)) (polyAdd
            (pairedDerivative 0 (pairedDerivative 1 p))
            (pairedDerivative 1 (pairedDerivative 0 p))))
          (polyAdd
            (polyMul (polyMul (u 0) (u 2)) (polyAdd
              (pairedDerivative 0 (pairedDerivative 2 p))
              (pairedDerivative 2 (pairedDerivative 0 p))))
            (polyMul (polyMul (u 1) (u 2)) (polyAdd
              (pairedDerivative 1 (pairedDerivative 2 p))
              (pairedDerivative 2 (pairedDerivative 1 p))))))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add
      (.add (.mul (.mul (.var 0) (.var 0)) (.var 3))
        (.add (.mul (.mul (.var 0) (.var 1)) (.var 4))
          (.mul (.mul (.var 0) (.var 2)) (.var 5))))
      (.add
        (.add (.mul (.mul (.var 1) (.var 0)) (.var 6))
          (.add (.mul (.mul (.var 1) (.var 1)) (.var 7))
            (.mul (.mul (.var 1) (.var 2)) (.var 8))))
        (.add (.mul (.mul (.var 2) (.var 0)) (.var 9))
          (.add (.mul (.mul (.var 2) (.var 1)) (.var 10))
            (.mul (.mul (.var 2) (.var 2)) (.var 11))))))
    (.add
      (.add (.mul (.mul (.var 0) (.var 0)) (.var 3))
        (.add (.mul (.mul (.var 1) (.var 1)) (.var 7))
          (.mul (.mul (.var 2) (.var 2)) (.var 11))))
      (.add (.mul (.mul (.var 0) (.var 1)) (.add (.var 4) (.var 6)))
        (.add (.mul (.mul (.var 0) (.var 2)) (.add (.var 5) (.var 9)))
          (.mul (.mul (.var 1) (.var 2)) (.add (.var 8) (.var 10))))))
    (by decide) (fun
      | 0 => u 0 | 1 => u 1 | 2 => u 2
      | 3 => pairedDerivative 0 (pairedDerivative 0 p)
      | 4 => pairedDerivative 0 (pairedDerivative 1 p)
      | 5 => pairedDerivative 0 (pairedDerivative 2 p)
      | 6 => pairedDerivative 1 (pairedDerivative 0 p)
      | 7 => pairedDerivative 1 (pairedDerivative 1 p)
      | 8 => pairedDerivative 1 (pairedDerivative 2 p)
      | 9 => pairedDerivative 2 (pairedDerivative 0 p)
      | 10 => pairedDerivative 2 (pairedDerivative 1 p)
      | _ => pairedDerivative 2 (pairedDerivative 2 p))

/-- Exact frozen scalar Hessian, for arbitrary polynomial coefficients.
The coefficients are only multiplied AFTER the actual second jets. -/
theorem frozenScalarSecondJet_pin {blocks : Nat} (hb : 1 < blocks)
    (u : Fin 3 → RatPoly) :
    HaarCarrierEqv blocks (frozenSecondJet u relativeScalar)
      (polyNeg (polyMul (threeSquare u) relativeScalar)) := by
  have hd := HaarCarrierEqv.add
    ((relativeScalar_second_jet hb 0).mul_left (polyMul (u 0) (u 0)))
    (HaarCarrierEqv.add
      ((relativeScalar_second_jet hb 1).mul_left (polyMul (u 1) (u 1)))
      ((relativeScalar_second_jet hb 2).mul_left (polyMul (u 2) (u 2))))
  have hz (i j : Fin 3) (hij : i ≠ j) : HaarCarrierEqv blocks
      (polyMul (polyMul (u i) (u j)) (polyAdd
        (pairedDerivative i (pairedDerivative j relativeScalar))
        (pairedDerivative j (pairedDerivative i relativeScalar)))) polyZero :=
    ((relativeScalar_mixed_jet hb i j hij).mul_left (polyMul (u i) (u j))).trans
      (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_zero_right _))
  refine (RatPolyCoeffEqv.haarCarrier (frozenSecondJet_grouped u relativeScalar)).trans
    ((HaarCarrierEqv.add hd (HaarCarrierEqv.add (hz 0 1 (by decide))
      (HaarCarrierEqv.add (hz 0 2 (by decide)) (hz 1 2 (by decide))))).trans ?_)
  refine (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.add_zero _)).trans ?_
  exact RatPolyCoeffEqv.haarCarrier
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.mul (.var 0) (.var 0)) (.neg (.var 3)))
        (.add (.mul (.mul (.var 1) (.var 1)) (.neg (.var 3)))
          (.mul (.mul (.var 2) (.var 2)) (.neg (.var 3)))))
      (.neg (.mul
        (.add (.mul (.var 0) (.var 0))
          (.add (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2)))) (.var 3)))
      (by decide) (fun | 0 => u 0 | 1 => u 1 | 2 => u 2 | _ => relativeScalar))

/-- Any actual output/action multiplier is retained under the SAME Haar
carrier. No positivity or support premise on that multiplier is added. -/
theorem frozenScalarSecondJet_weighted_pin {blocks : Nat} (hb : 1 < blocks)
    (u : Fin 3 → RatPoly) (W : RatPoly) :
    HaarCarrierEqv blocks (polyMul W (frozenSecondJet u relativeScalar))
      (polyMul W (polyNeg (polyMul (threeSquare u) relativeScalar))) :=
  (frozenScalarSecondJet_pin hb u).mul_left W

end YMGap.Continuum.SU2QuaternionPairedFrameScalarJets

#print axioms YMGap.Continuum.SU2QuaternionPairedFrameScalarJets.pairedDerivative_carrier
#print axioms YMGap.Continuum.SU2QuaternionPairedFrameScalarJets.pairedScorePlus_zero_derivative_pin
#print axioms YMGap.Continuum.SU2QuaternionPairedFrameScalarJets.relativeScalar_supported
#print axioms YMGap.Continuum.SU2QuaternionPairedFrameScalarJets.relativeScalar_second_jet
#print axioms YMGap.Continuum.SU2QuaternionPairedFrameScalarJets.relativeScalar_mixed_jet
#print axioms YMGap.Continuum.SU2QuaternionPairedFrameScalarJets.frozenScalarSecondJet_pin
#print axioms YMGap.Continuum.SU2QuaternionPairedFrameScalarJets.frozenScalarSecondJet_weighted_pin
