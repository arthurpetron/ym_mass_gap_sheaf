/-
# Cleared three-row signed Gram identity

The score column need not be a polynomial ratio d/P. Three actual cleared
curvature witnesses supply a square identity AFTER multiplication by the
three positive kernel factors. Their later cancellation is integrated order
reflection, not certificate-level division. Every cross term is signed.

Consumer: the shared-tail three-head conditional determinant. This leaf is
finite polynomial algebra only, not an interacting/scaling/OS gap estimate.
-/

import YMGap.Continuum.QuaternionHaarCurvatureDualBound
import YMGap.Continuum.QPolyHaarFrozenChain

namespace YMGap.Continuum.QuaternionHaarClearedThreeGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)

def kernelProduct (P : Fin 3 → RatPoly) : RatPoly := polyMul (polyMul (P 0) (P 1)) (P 2)

def complementProduct (P : Fin 3 → RatPoly) (i : Fin 3) : RatPoly :=
  match i.val with
  | 0 => polyMul (P 1) (P 2)
  | 1 => polyMul (P 0) (P 2)
  | _ => polyMul (P 0) (P 1)

def cyclicDifference (f : Fin 3 → RatPoly) (i : Fin 3) : RatPoly :=
  match i.val with
  | 0 => polyAdd (f 1) (polyNeg (f 2))
  | 1 => polyAdd (f 2) (polyNeg (f 0))
  | _ => polyAdd (f 0) (polyNeg (f 1))

def rowCurvature (P d dd : Fin 3 → RatPoly) (i : Fin 3) : RatPoly :=
  polyAdd (polyMul (P i) (dd i)) (polyNeg (polyMul (d i) (d i)))

def clearedWedge (P d f : Fin 3 → RatPoly) : RatPoly :=
  threeSum (fun i => polyMul (polyMul (complementProduct P i) (d i)) (cyclicDifference f i))

/-- All three diagonal and all three signed off-diagonal terms. -/
def replicaPolynomial (P d dd f : Fin 3 → RatPoly) : RatPoly :=
  let h := cyclicDifference f
  polyAdd
    (threeSum (fun i => polyMul (polyMul (complementProduct P i) (dd i)) (polyMul (h i) (h i))))
    (polyMul (cap 2)
      (polyAdd (polyMul (polyMul (P 2) (polyMul (d 0) (d 1))) (polyMul (h 0) (h 1)))
        (polyAdd (polyMul (polyMul (P 1) (polyMul (d 0) (d 2))) (polyMul (h 0) (h 2)))
          (polyMul (polyMul (P 0) (polyMul (d 1) (d 2))) (polyMul (h 1) (h 2))))))

private def exprThree (f : Fin 3 → PolyExpr) : PolyExpr := .add (f 0) (.add (f 1) (f 2))
private def minus (p q : PolyExpr) : PolyExpr := .add p (.neg q)
private def pExpr (i : Fin 3) : PolyExpr := .var i.val
private def dExpr (i : Fin 3) : PolyExpr := .var (3+i.val)
private def ddExpr (i : Fin 3) : PolyExpr := .var (6+i.val)
private def hExpr (i : Fin 3) : PolyExpr :=
  match i.val with
  | 0 => minus (.var 10) (.var 11)
  | 1 => minus (.var 11) (.var 9)
  | _ => minus (.var 9) (.var 10)
private def bExpr (i : Fin 3) : PolyExpr :=
  match i.val with
  | 0 => .mul (.var 1) (.var 2)
  | 1 => .mul (.var 0) (.var 2)
  | _ => .mul (.var 0) (.var 1)
private def replicaExpr : PolyExpr :=
  .add (exprThree (fun i => .mul (.mul (bExpr i) (ddExpr i)) (.mul (hExpr i) (hExpr i))))
    (.mul (.const 2)
      (.add (.mul (.mul (.var 2) (.mul (.var 3) (.var 4))) (.mul (hExpr 0) (hExpr 1)))
        (.add (.mul (.mul (.var 1) (.mul (.var 3) (.var 5))) (.mul (hExpr 0) (hExpr 2)))
          (.mul (.mul (.var 0) (.mul (.var 4) (.var 5))) (.mul (hExpr 1) (hExpr 2))))))
private def env (P d dd f : Fin 3 → RatPoly) : Nat → RatPoly
  | 0 => P 0 | 1 => P 1 | 2 => P 2
  | 3 => d 0 | 4 => d 1 | 5 => d 2
  | 6 => dd 0 | 7 => dd 1 | 8 => dd 2
  | 9 => f 0 | 10 => f 1 | _ => f 2

/-- Exact cleared square identity; no division and no sign of dd is assumed. -/
theorem cleared_replica_pin (P d dd f : Fin 3 → RatPoly) :
    RatPolyCoeffEqv (polyMul (kernelProduct P) (replicaPolynomial P d dd f))
      (polyAdd (polyMul (clearedWedge P d f) (clearedWedge P d f))
        (threeSum (fun i =>
          let v := polyMul (complementProduct P i) (cyclicDifference f i)
          polyMul (polyMul v v) (rowCurvature P d dd i)))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) replicaExpr)
    (.add
      (.mul (exprThree (fun i => .mul (.mul (bExpr i) (dExpr i)) (hExpr i)))
        (exprThree (fun i => .mul (.mul (bExpr i) (dExpr i)) (hExpr i))))
      (exprThree (fun i =>
        .mul (.mul (.mul (bExpr i) (hExpr i)) (.mul (bExpr i) (hExpr i)))
          (minus (.mul (pExpr i) (ddExpr i)) (.mul (dExpr i) (dExpr i))))))
    (by decide) (env P d dd f)

private theorem supported_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem three_supported {blocks : Nat} {f : Fin 3 → RatPoly}
    (hf : ∀ i, SupportedQuaternionBlocks blocks (f i)) :
    SupportedQuaternionBlocks blocks (threeSum f) :=
  supported_add (hf 0) (supported_add (hf 1) (hf 2))

/-- Actual square witnesses for the cleared replica, retaining all variables. -/
def cleared_replica_certificate {blocks : Nat} (P d dd f : Fin 3 → RatPoly)
    (hP : ∀ i, SupportedQuaternionBlocks blocks (P i))
    (hd : ∀ i, SupportedQuaternionBlocks blocks (d i))
    (hf : ∀ i, SupportedQuaternionBlocks blocks (f i))
    (C : ∀ i, Certificate blocks (rowCurvature P d dd i)) :
    Certificate blocks (polyMul (kernelProduct P) (replicaPolynomial P d dd f)) := by
  have hb (i : Fin 3) : SupportedQuaternionBlocks blocks (complementProduct P i) := by
    unfold complementProduct
    split
    · exact supported_polyMul (hP 1) (hP 2)
    · exact supported_polyMul (hP 0) (hP 2)
    · exact supported_polyMul (hP 0) (hP 1)
  have hh (i : Fin 3) : SupportedQuaternionBlocks blocks (cyclicDifference f i) := by
    unfold cyclicDifference
    split
    · exact supported_add (hf 1) (supported_neg (hf 2))
    · exact supported_add (hf 2) (supported_neg (hf 0))
    · exact supported_add (hf 0) (supported_neg (hf 1))
  let W := Certificate.square (clearedWedge P d f)
    (three_supported (fun i => supported_polyMul (supported_polyMul (hb i) (hd i)) (hh i)))
  let row := fun i => Certificate.multiplySquare
    (polyMul (complementProduct P i) (cyclicDifference f i)) (supported_polyMul (hb i) (hh i)) (C i)
  exact Certificate.ofCoeff (cleared_replica_pin P d dd f) (W.add ((row 0).add ((row 1).add (row 2))))

/-- Literal three-by-three determinant of the retained moments. -/
def momentDeterminant (A b D v e G : RatPoly) : RatPoly :=
  polyAdd
    (polyAdd (polyMul (polyMul A v) G) (polyMul (cap 2) (polyMul (polyMul b D) e)))
    (polyNeg (polyAdd (polyAdd (polyMul (polyMul b b) G) (polyMul A (polyMul e e)))
      (polyMul v (polyMul D D))))

def centeredNoise (A b v : RatPoly) : RatPoly := polyAdd (polyMul A v) (polyNeg (polyMul b b))
def centeredScore (A b D e : RatPoly) : RatPoly := polyAdd (polyMul A e) (polyNeg (polyMul b D))
def centeredFisher (A D G : RatPoly) : RatPoly := polyAdd (polyMul A G) (polyNeg (polyMul D D))

/-- Multiplication by the actual marginal, not an inverse, joins the centered bound. -/
theorem centered_difference_pin (A b D v e G : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyMul (centeredNoise A b v) (centeredFisher A D G))
        (polyNeg (polyMul (centeredScore A b D e) (centeredScore A b D e))))
      (polyMul A (momentDeterminant A b D v e G)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (minus
      (.mul (minus (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 1)))
        (minus (.mul (.var 0) (.var 5)) (.mul (.var 2) (.var 2))))
      (.mul (minus (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 2)))
        (minus (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 2)))))
    (.mul (.var 0)
      (minus
        (.add (.mul (.mul (.var 0) (.var 3)) (.var 5))
          (.mul (.const 2) (.mul (.mul (.var 1) (.var 2)) (.var 4))))
        (.add (.add (.mul (.mul (.var 1) (.var 1)) (.var 5))
          (.mul (.var 0) (.mul (.var 4) (.var 4)))) (.mul (.var 3) (.mul (.var 2) (.var 2))))))
    (by decide) (fun
      | 0 => A | 1 => b | 2 => D | 3 => v | 4 => e | _ => G)

end YMGap.Continuum.QuaternionHaarClearedThreeGram

#print axioms YMGap.Continuum.QuaternionHaarClearedThreeGram.cleared_replica_pin
#print axioms YMGap.Continuum.QuaternionHaarClearedThreeGram.cleared_replica_certificate
#print axioms YMGap.Continuum.QuaternionHaarClearedThreeGram.centered_difference_pin
