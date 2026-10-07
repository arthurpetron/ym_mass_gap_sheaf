/-
# Additive frozen-jet curvature on the literal product heat

Each factor uses its six actual upper rotations with supported polynomial
coefficients. Exact square expansion identifies the local matrix envelope
with its first/second frozen jets. Polynomial-cost tensorization then retains
all mixed product jets and adds local costs without an active-count penalty.

The product jets here are DEFINED by frozen Leibniz recursion. Their equality
to a direct whole-kernel angular differential sum, conditional integration,
the weighted coupled-score inequality and useful scaling remain unproved.
No derivative acts on any coefficient and no conditional Hessian sign is used.
-/

import YMGap.Continuum.QuaternionHaarPolynomialJetCurvature
import YMGap.Continuum.SU2QuaternionFrozenSixHeatCurvature
import YMGap.Continuum.SU2QuaternionProductHeatMarginals

namespace YMGap.Continuum.SU2QuaternionProductHeatFrozenJetCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionHeatLogCurvature
open YMGap.Continuum.SU2QuaternionFrozenSixHeatCurvature
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound (relativeCutoff)
open YMGap.Continuum.QuaternionHaarSixPolynomialMatrixEnvelope
open YMGap.Continuum.QuaternionHaarPolynomialJetCurvature

private def slot (k : Nat) : Fin 6 := ⟨k % 6, Nat.mod_lt _ (by decide)⟩

private def exprSix (f : Fin 6 → PolyExpr) : PolyExpr :=
  .add (f (slot 0)) (.add (f (slot 1)) (.add (f (slot 2))
    (.add (f (slot 3)) (.add (f (slot 4)) (f (slot 5))))))

private def uExpr (i : Fin 6) : PolyExpr := .var (2+i.val)
private def dExpr (i : Fin 6) : PolyExpr := .var (8+i.val)
private def eExpr (i j : Fin 6) : PolyExpr := .var (14+6*i.val+j.val)
private def squaresExpr : PolyExpr := exprSix (fun i => .mul (uExpr i) (uExpr i))
private def firstExpr : PolyExpr := exprSix (fun i => .mul (uExpr i) (dExpr i))
private def secondExpr : PolyExpr := exprSix (fun i => exprSix (fun j =>
  .mul (.mul (uExpr i) (uExpr j)) (eExpr i j)))

private theorem six_matrix_jet_pin (h C : RatPoly) (u d : Fin 6 → RatPoly)
    (e : Fin 6 → Fin 6 → RatPoly) :
    RatPolyCoeffEqv
      (matrixEnvelope (polyMul C (polyMul h h)) u (fun i j =>
        polyAdd (polyMul h (e i j)) (polyNeg (polyMul (d i) (d j)))))
      (jetCurvature (polyMul (polyMul (cap 6) C) (squareSum u)) h
        (sixSum (fun i => polyMul (u i) (d i)))
        (sixSum (fun i => sixSum (fun j => polyMul (polyMul (u i) (u j)) (e i j))))) := by
  let environment : Nat → RatPoly := fun k =>
    if k = 0 then h else if k = 1 then C else if k < 8 then u (slot (k-2))
    else if k < 14 then d (slot (k-8)) else e (slot ((k-14)/6)) (slot (k-14))
  have H := coeffEvalExpr_eqv_of_normalize_eq
    (.add
      (.mul (.mul (.const 6) (.mul (.var 1) (.mul (.var 0) (.var 0)))) squaresExpr)
      (exprSix (fun i => exprSix (fun j => .mul (.mul (uExpr i) (uExpr j))
        (.add (.mul (.var 0) (eExpr i j)) (.neg (.mul (dExpr i) (dExpr j))))))))
    (.add (.mul (.mul (.mul (.const 6) (.var 1)) squaresExpr) (.mul (.var 0) (.var 0)))
      (.add (.mul (.var 0) secondExpr) (.neg (.mul firstExpr firstExpr))))
    (by decide) environment
  simpa only [exprSix, uExpr, dExpr, eExpr, squaresExpr, firstExpr, secondExpr,
    coeffEvalExpr, environment, matrixEnvelope, squareSum, quadraticForm,
    sixSum, jetCurvature, slot] using H

/-- First jet: only the actual heat-factor derivatives are taken. -/
def frozenSixFirst (s : Nat) (h : RatPoly) (u : Fin 6 → RatPoly) : RatPoly :=
  sixSum (fun i => polyMul (u i)
    (angularDerivative (4*s+(sixPlane i).1.val) (4*s+(sixPlane i).2.val) h))

/-- Frozen second jet with all 36 ORDERED local mixed derivatives. -/
def frozenSixSecond (s : Nat) (h : RatPoly) (u : Fin 6 → RatPoly) : RatPoly :=
  sixSum (fun i => sixSum (fun j => polyMul (polyMul (u i) (u j))
    (angularDerivative (4*s+(sixPlane i).1.val) (4*s+(sixPlane i).2.val)
      (angularDerivative (4*s+(sixPlane j).1.val) (4*s+(sixPlane j).2.val) h))))

/-- Local adaptive POLYNOMIAL cost; the nome cap remains explicit. -/
def frozenSixCost (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (u : Fin 6 → RatPoly) : RatPoly :=
  polyMul (polyMul (cap 6) (cap (logCurvatureCap w hw0 hw1))) (squareSum u)

/-- Exact original local envelope-to-jet pin, with no coefficient derivative. -/
theorem frozenSixHeatEnvelope_jet_pin
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K a b s : Nat) (u : Fin 6 → RatPoly) :
    RatPolyCoeffEqv (frozenSixHeatEnvelope w hw0 hw1 K a b s u)
      (jetCurvature (frozenSixCost w hw0 hw1 u) (heatAt a b w K)
        (frozenSixFirst s (heatAt a b w K) u)
        (frozenSixSecond s (heatAt a b w K) u)) :=
  six_matrix_jet_pin (heatAt a b w K) (cap (logCurvatureCap w hw0 hw1)) u
    (fun i => angularDerivative (4*s+(sixPlane i).1.val) (4*s+(sixPlane i).2.val)
      (heatAt a b w K))
    (fun i j => angularDerivative (4*s+(sixPlane i).1.val) (4*s+(sixPlane i).2.val)
      (angularDerivative (4*s+(sixPlane j).1.val) (4*s+(sixPlane j).2.val)
        (heatAt a b w K)))

def heat_frozen_six_jet_certificate
    {blocks a b s : Nat} (ha : a < blocks) (hb : b < blocks) (hs : s < blocks)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K)
    (u : Fin 6 → RatPoly) (hu : ∀ i, SupportedQuaternionBlocks blocks (u i)) :
    Certificate blocks (jetCurvature (frozenSixCost w hw0 hw1 u) (heatAt a b w K)
      (frozenSixFirst s (heatAt a b w K) u) (frozenSixSecond s (heatAt a b w K) u)) :=
  Certificate.ofCoeff (frozenSixHeatEnvelope_jet_pin w hw0 hw1 K a b s u).symm
    (heat_frozen_six_curvature_certificate ha hb hs hw0 hw1 K hK u hu)

/-- First product jet defined by the literal frozen Leibniz recursion. -/
def productFrozenFirst (n : Nat) (w : Q') (K : Nat) (u : Nat → Fin 6 → RatPoly) :
    List Nat → RatPoly
  | [] => polyZero
  | s::ids => jetFirstProduct (heatAt s (n+s) w K)
      (frozenSixFirst (n+s) (heatAt s (n+s) w K) (u s))
      (productHeat n w K ids) (productFrozenFirst n w K u ids)

/-- Second product jet, RETAINING both cross-factor terms via `cap 2`. -/
def productFrozenSecond (n : Nat) (w : Q') (K : Nat) (u : Nat → Fin 6 → RatPoly) :
    List Nat → RatPoly
  | [] => polyZero
  | s::ids => jetSecondProduct (heatAt s (n+s) w K)
      (frozenSixFirst (n+s) (heatAt s (n+s) w K) (u s))
      (frozenSixSecond (n+s) (heatAt s (n+s) w K) (u s))
      (productHeat n w K ids) (productFrozenFirst n w K u ids)
      (productFrozenSecond n w K u ids)

/-- Costs ADD over literal factors. Duplicates retain their multiplicity. -/
def productFrozenCost (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (u : Nat → Fin 6 → RatPoly) : List Nat → RatPoly
  | [] => polyZero
  | s::ids => polyAdd (frozenSixCost w hw0 hw1 (u s))
      (productFrozenCost w hw0 hw1 u ids)

private def unitJetCertificate (blocks : Nat) :
    Certificate blocks (jetCurvature polyZero polyOne polyZero polyZero) :=
  Certificate.ofCoeff
    (RatPolyCoeffEqv.zero_smul polyOne).symm
    (Certificate.constant blocks 0 (Q'.le_refl' _))

/-- Constructed frozen-JET bound on the SAME literal product heat.
The cost is a sum of local coefficient squares, not count times a global loss.
The direct whole-kernel angular differential pin is not claimed here. -/
def productHeat_frozenJet_curvature_certificate
    (n : Nat) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K) (u : Nat → Fin 6 → RatPoly) :
    (ids : List Nat) → (∀ s, s ∈ ids → s < n) →
    (∀ s, s ∈ ids → ∀ i, SupportedQuaternionBlocks (n+n) (u s i)) →
    Certificate (n+n) (jetCurvature (productFrozenCost w hw0 hw1 u ids)
      (productHeat n w K ids) (productFrozenFirst n w K u ids)
      (productFrozenSecond n w K u ids))
  | [], _, _ => unitJetCertificate (n+n)
  | s::ids, hs, hu => by
    have hsN : s < n := hs s List.mem_cons_self
    have hids : ∀ j, j ∈ ids → j < n := fun j hj => hs j (List.mem_cons_of_mem s hj)
    exact polynomialJet_product_curvature_certificate
      (heatAt s (n+s) w K)
      (frozenSixFirst (n+s) (heatAt s (n+s) w K) (u s))
      (frozenSixSecond (n+s) (heatAt s (n+s) w K) (u s))
      (productHeat n w K ids) (productFrozenFirst n w K u ids)
      (productFrozenSecond n w K u ids)
      (frozenSixCost w hw0 hw1 (u s)) (productFrozenCost w hw0 hw1 u ids)
      (heat_supported (by omega) (by omega) w K)
      (productHeat_supported n w K ids hids)
      (heat_frozen_six_jet_certificate (by omega) (by omega) (by omega)
        hw0 hw1 K hK (u s) (hu s List.mem_cons_self))
      (productHeat_frozenJet_curvature_certificate n hw0 hw1 K hK u ids hids
        (fun j hj => hu j (List.mem_cons_of_mem s hj)))

end YMGap.Continuum.SU2QuaternionProductHeatFrozenJetCurvature

#print axioms YMGap.Continuum.SU2QuaternionProductHeatFrozenJetCurvature.frozenSixHeatEnvelope_jet_pin
#print axioms YMGap.Continuum.SU2QuaternionProductHeatFrozenJetCurvature.heat_frozen_six_jet_certificate
#print axioms YMGap.Continuum.SU2QuaternionProductHeatFrozenJetCurvature.productHeat_frozenJet_curvature_certificate
