/-
# Exact weighted THREE-head signed Gram moments

All three replicas use the existing original-head copy/lift placements
and ONE shared tail. The weighted replica integrates to SIX times the
literal signed moment determinant. No positivity, source factorization,
density inverse, independence of tail coordinates or Hessian sign is
assumed. The second jet may later contain an actual homogeneous cost.
This leaf is the exact finite moment join, not normalized conditional
order, an original-action estimate or a physical/OS gap.
-/

import YMGap.Continuum.SU2QuaternionTripleHeadReplica
import YMGap.Continuum.QuaternionHaarClearedThreeGram

namespace YMGap.Continuum.SU2QuaternionConditionalSignedGramReplica

set_option autoImplicit false

open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (partialHaarHeads_congr)
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
  (partialHaarHeads_add partialHaarHeads_neg partialHaarHeads_smul)
open YMGap.Continuum.SU2QuaternionTripleHeadReplica
open YMGap.Continuum.QuaternionHaarClearedThreeGram

private def sixAdd (a b c d e f : RatPoly) : RatPoly :=
  polyAdd a (polyAdd b (polyAdd c (polyAdd d (polyAdd e f))))

private def tensor (heads : Nat) (p q r : RatPoly) : RatPoly :=
  polyMul (polyMul (tripleCopy heads 0 p) (tripleCopy heads 1 q)) (tripleCopy heads 2 r)

/-- SIX permutations, including their multiplicities when arguments coincide. -/
def symTensor (heads : Nat) (p q r : RatPoly) : RatPoly :=
  sixAdd (tensor heads p q r) (tensor heads p r q)
    (tensor heads q p r) (tensor heads q r p)
    (tensor heads r p q) (tensor heads r q p)

/-- The exact weighted replica; input density and all ordered terms remain. -/
def weightedReplica (heads : Nat) (q P d dd phi : RatPoly) : RatPoly :=
  polyMul (kernelProduct (fun i => tripleCopy heads i q))
    (replicaPolynomial (fun i => tripleCopy heads i P) (fun i => tripleCopy heads i d)
      (fun i => tripleCopy heads i dd) (fun i => tripleCopy heads i phi))

def momentA (heads : Nat) (q P : RatPoly) : RatPoly :=
  partialHaarHeads heads (polyMul q P)
def momentB (heads : Nat) (q P phi : RatPoly) : RatPoly :=
  partialHaarHeads heads (polyMul (polyMul q P) phi)
def momentD (heads : Nat) (q d : RatPoly) : RatPoly :=
  partialHaarHeads heads (polyMul q d)
def momentV (heads : Nat) (q P phi : RatPoly) : RatPoly :=
  partialHaarHeads heads (polyMul (polyMul q P) (polyMul phi phi))
def momentE (heads : Nat) (q d phi : RatPoly) : RatPoly :=
  partialHaarHeads heads (polyMul (polyMul q d) phi)
def momentG (heads : Nat) (q dd : RatPoly) : RatPoly :=
  partialHaarHeads heads (polyMul q dd)

private def integrand (q P d dd phi : RatPoly) : Nat → RatPoly
  | 0 => polyMul q P
  | 1 => polyMul (polyMul q P) phi
  | 2 => polyMul q d
  | 3 => polyMul (polyMul q P) (polyMul phi phi)
  | 4 => polyMul (polyMul q d) phi
  | _ => polyMul q dd

private def expandedReplica (heads : Nat) (m : Nat → RatPoly) : RatPoly :=
  polyAdd
    (polyAdd (symTensor heads (m 0) (m 3) (m 5))
      (polyMul (cap 2) (symTensor heads (m 1) (m 2) (m 4))))
    (polyNeg (polyAdd
      (polyAdd (symTensor heads (m 1) (m 1) (m 5)) (symTensor heads (m 0) (m 4) (m 4)))
      (symTensor heads (m 3) (m 2) (m 2))))

private def exprSix (a b c d e f : PolyExpr) : PolyExpr :=
  .add a (.add b (.add c (.add d (.add e f))))
private def exprThree (f : Fin 3 → PolyExpr) : PolyExpr := .add (f 0) (.add (f 1) (f 2))
private def qExpr (i : Fin 3) : PolyExpr := .var i.val
private def pExpr (i : Fin 3) : PolyExpr := .var (3+i.val)
private def dExpr (i : Fin 3) : PolyExpr := .var (6+i.val)
private def ddExpr (i : Fin 3) : PolyExpr := .var (9+i.val)
private def fExpr (i : Fin 3) : PolyExpr := .var (12+i.val)
private def hExpr (i : Fin 3) : PolyExpr :=
  match i.val with
  | 0 => .add (fExpr 1) (.neg (fExpr 2))
  | 1 => .add (fExpr 2) (.neg (fExpr 0))
  | _ => .add (fExpr 0) (.neg (fExpr 1))
private def complementExpr (i : Fin 3) : PolyExpr :=
  match i.val with
  | 0 => .mul (pExpr 1) (pExpr 2)
  | 1 => .mul (pExpr 0) (pExpr 2)
  | _ => .mul (pExpr 0) (pExpr 1)
private def replicaExpr : PolyExpr :=
  .add (exprThree (fun i => .mul (.mul (complementExpr i) (ddExpr i))
      (.mul (hExpr i) (hExpr i))))
    (.mul (.const 2)
      (.add (.mul (.mul (pExpr 2) (.mul (dExpr 0) (dExpr 1))) (.mul (hExpr 0) (hExpr 1)))
        (.add (.mul (.mul (pExpr 1) (.mul (dExpr 0) (dExpr 2))) (.mul (hExpr 0) (hExpr 2)))
          (.mul (.mul (pExpr 0) (.mul (dExpr 1) (dExpr 2))) (.mul (hExpr 1) (hExpr 2))))))
private def integrandExpr (n : Nat) (i : Fin 3) : PolyExpr :=
  match n with
  | 0 => .mul (qExpr i) (pExpr i)
  | 1 => .mul (.mul (qExpr i) (pExpr i)) (fExpr i)
  | 2 => .mul (qExpr i) (dExpr i)
  | 3 => .mul (.mul (qExpr i) (pExpr i)) (.mul (fExpr i) (fExpr i))
  | 4 => .mul (.mul (qExpr i) (dExpr i)) (fExpr i)
  | _ => .mul (qExpr i) (ddExpr i)
private def tensorExpr (a b c : Nat) : PolyExpr :=
  .mul (.mul (integrandExpr a 0) (integrandExpr b 1)) (integrandExpr c 2)
private def symExpr (a b c : Nat) : PolyExpr :=
  exprSix (tensorExpr a b c) (tensorExpr a c b) (tensorExpr b a c)
    (tensorExpr b c a) (tensorExpr c a b) (tensorExpr c b a)
private def expandedExpr : PolyExpr :=
  .add (.add (symExpr 0 3 5) (.mul (.const 2) (symExpr 1 2 4)))
    (.neg (.add (.add (symExpr 1 1 5) (symExpr 0 4 4)) (symExpr 3 2 2)))
private def replicaEnv (heads : Nat) (q P d dd phi : RatPoly) : Nat → RatPoly
  | 0 => tripleCopy heads 0 q | 1 => tripleCopy heads 1 q | 2 => tripleCopy heads 2 q
  | 3 => tripleCopy heads 0 P | 4 => tripleCopy heads 1 P | 5 => tripleCopy heads 2 P
  | 6 => tripleCopy heads 0 d | 7 => tripleCopy heads 1 d | 8 => tripleCopy heads 2 d
  | 9 => tripleCopy heads 0 dd | 10 => tripleCopy heads 1 dd | 11 => tripleCopy heads 2 dd
  | 12 => tripleCopy heads 0 phi | 13 => tripleCopy heads 1 phi | _ => tripleCopy heads 2 phi

private theorem weighted_expansion_pin (heads : Nat) (q P d dd phi : RatPoly) :
    RatPolyCoeffEqv (weightedReplica heads q P d dd phi)
      (expandedReplica heads (integrand q P d dd phi)) := by
  have h := coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (qExpr 0) (qExpr 1)) (qExpr 2)) replicaExpr)
    expandedExpr (by decide) (replicaEnv heads q P d dd phi)
  simpa only [qExpr, pExpr, dExpr, ddExpr, fExpr, hExpr, complementExpr,
    replicaExpr, exprThree, expandedExpr, symExpr, exprSix, tensorExpr, integrandExpr,
    replicaEnv, coeffEvalExpr, weightedReplica, kernelProduct, replicaPolynomial,
    complementProduct, cyclicDifference, threeSum, expandedReplica, symTensor,
    sixAdd, tensor, integrand, tripleCopy_mul] using h

/-- Exact six-permutation moment pin, retaining the shared tail. -/
theorem symTensor_integral_pin (heads : Nat) (p q r : RatPoly) :
    RatPolyCoeffEqv (partialHaarHeads (heads+(heads+heads)) (symTensor heads p q r))
      (polyMul (cap 6) (polyMul (polyMul (partialHaarHeads heads p)
        (partialHaarHeads heads q)) (partialHaarHeads heads r))) := by
  unfold symTensor sixAdd
  rw [partialHaarHeads_add, partialHaarHeads_add, partialHaarHeads_add,
    partialHaarHeads_add, partialHaarHeads_add]
  refine ((replica_product_three heads p q r).add
    ((replica_product_three heads p r q).add
      ((replica_product_three heads q p r).add
        ((replica_product_three heads q r p).add
          ((replica_product_three heads r p q).add (replica_product_three heads r q p)))))).trans ?_
  exact coeffEvalExpr_eqv_of_normalize_eq
    (exprSix (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (.mul (.mul (.var 1) (.var 0)) (.var 2))
      (.mul (.mul (.var 1) (.var 2)) (.var 0))
      (.mul (.mul (.var 2) (.var 0)) (.var 1))
      (.mul (.mul (.var 2) (.var 1)) (.var 0)))
    (.mul (.const 6) (.mul (.mul (.var 0) (.var 1)) (.var 2)))
    (by decide) (fun
      | 0 => partialHaarHeads heads p
      | 1 => partialHaarHeads heads q
      | _ => partialHaarHeads heads r)

private theorem integral_cap (heads : Nat) (c : YMGap.Constructive.Q') (p : RatPoly) :
    RatPolyCoeffEqv (partialHaarHeads heads (polyMul (cap c) p))
      (polyMul (cap c) (partialHaarHeads heads p)) :=
  (partialHaarHeads_congr heads (cap_mul_left c p)).trans
    ((partialHaarHeads_smul heads c p).trans (cap_mul_left c _).symm)

private def expandedMoments (A b D v e G : RatPoly) : RatPoly :=
  polyAdd
    (polyAdd (polyMul (cap 6) (polyMul (polyMul A v) G))
      (polyMul (cap 2) (polyMul (cap 6) (polyMul (polyMul b D) e))))
    (polyNeg (polyAdd
      (polyAdd (polyMul (cap 6) (polyMul (polyMul b b) G))
        (polyMul (cap 6) (polyMul (polyMul A e) e)))
      (polyMul (cap 6) (polyMul (polyMul v D) D))))

private theorem expanded_integral_pin (heads : Nat) (m : Nat → RatPoly) :
    RatPolyCoeffEqv (partialHaarHeads (heads+(heads+heads)) (expandedReplica heads m))
      (expandedMoments (partialHaarHeads heads (m 0)) (partialHaarHeads heads (m 1))
        (partialHaarHeads heads (m 2)) (partialHaarHeads heads (m 3))
        (partialHaarHeads heads (m 4)) (partialHaarHeads heads (m 5))) := by
  have hnegative : RatPolyCoeffEqv
      (partialHaarHeads (heads+(heads+heads))
        (polyAdd (polyAdd (symTensor heads (m 1) (m 1) (m 5))
          (symTensor heads (m 0) (m 4) (m 4))) (symTensor heads (m 3) (m 2) (m 2))))
      (polyAdd
        (polyAdd (polyMul (cap 6) (polyMul (polyMul (partialHaarHeads heads (m 1))
          (partialHaarHeads heads (m 1))) (partialHaarHeads heads (m 5))))
          (polyMul (cap 6) (polyMul (polyMul (partialHaarHeads heads (m 0))
            (partialHaarHeads heads (m 4))) (partialHaarHeads heads (m 4)))))
        (polyMul (cap 6) (polyMul (polyMul (partialHaarHeads heads (m 3))
          (partialHaarHeads heads (m 2))) (partialHaarHeads heads (m 2))))) := by
    rw [partialHaarHeads_add, partialHaarHeads_add]
    exact ((symTensor_integral_pin heads (m 1) (m 1) (m 5)).add
      (symTensor_integral_pin heads (m 0) (m 4) (m 4))).add
        (symTensor_integral_pin heads (m 3) (m 2) (m 2))
  unfold expandedReplica
  rw [partialHaarHeads_add, partialHaarHeads_add]
  exact ((symTensor_integral_pin heads (m 0) (m 3) (m 5)).add
    ((integral_cap (heads+(heads+heads)) 2 _).trans
      ((symTensor_integral_pin heads (m 1) (m 2) (m 4)).mul_left (cap 2)))).add
    ((partialHaarHeads_neg (heads+(heads+heads)) _).trans (RatPolyCoeffEqv.neg hnegative))

private theorem expanded_determinant_pin (A b D v e G : RatPoly) :
    RatPolyCoeffEqv (expandedMoments A b D v e G)
      (polyMul (cap 6) (momentDeterminant A b D v e G)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add
      (.add (.mul (.const 6) (.mul (.mul (.var 0) (.var 3)) (.var 5)))
        (.mul (.const 2) (.mul (.const 6) (.mul (.mul (.var 1) (.var 2)) (.var 4)))))
      (.neg (.add
        (.add (.mul (.const 6) (.mul (.mul (.var 1) (.var 1)) (.var 5)))
          (.mul (.const 6) (.mul (.mul (.var 0) (.var 4)) (.var 4))))
        (.mul (.const 6) (.mul (.mul (.var 3) (.var 2)) (.var 2))))))
    (.mul (.const 6)
      (.add
        (.add (.mul (.mul (.var 0) (.var 3)) (.var 5))
          (.mul (.const 2) (.mul (.mul (.var 1) (.var 2)) (.var 4))))
        (.neg (.add
          (.add (.mul (.mul (.var 1) (.var 1)) (.var 5))
            (.mul (.var 0) (.mul (.var 4) (.var 4))))
          (.mul (.var 3) (.mul (.var 2) (.var 2)))))))
    (by decide) (fun
      | 0 => A | 1 => b | 2 => D | 3 => v | 4 => e | _ => G)

/-- Literal weighted three-replica integration equals SIX times the signed
moment determinant on the original surviving polynomial carrier. -/
theorem weighted_replica_integral_pin (heads : Nat) (q P d dd phi : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (heads+(heads+heads)) (weightedReplica heads q P d dd phi))
      (polyMul (cap 6) (momentDeterminant
        (momentA heads q P) (momentB heads q P phi) (momentD heads q d)
        (momentV heads q P phi) (momentE heads q d phi) (momentG heads q dd))) :=
  (partialHaarHeads_congr (heads+(heads+heads)) (weighted_expansion_pin heads q P d dd phi)).trans
    ((expanded_integral_pin heads (integrand q P d dd phi)).trans
      (expanded_determinant_pin _ _ _ _ _ _))

end YMGap.Continuum.SU2QuaternionConditionalSignedGramReplica

#print axioms YMGap.Continuum.SU2QuaternionConditionalSignedGramReplica.symTensor_integral_pin
#print axioms YMGap.Continuum.SU2QuaternionConditionalSignedGramReplica.weighted_replica_integral_pin
