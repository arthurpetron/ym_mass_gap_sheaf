/-
# A square completion in the complete full-heat source remainder

The bare angular first-order cost pairs the source-observable product with
the exact Casimir commutator. Completing that pairing against the negative
commutator square costs only one quarter of the source-observable Haar square.
The original cubic and finite-cutoff terms remain explicit and unchanged.
-/

import YMGap.Continuum.SU2QuaternionCompleteRemainderCancellation

namespace YMGap.Continuum.SU2QuaternionCompleteRemainderSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairCasimir pairBudget pairRemainder)
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder (sourceErrorBudget)
open YMGap.Continuum.SU2QuaternionSecondOrderCancellation
  (commutatorPolynomial)
open YMGap.Continuum.SU2QuaternionLiteralCasimirPairing (pairCasimir_eq_literal)
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor (sourceFirstOrder)
open YMGap.Continuum.SU2QuaternionCompleteRemainderCancellation
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

def quarter : Q' := Q'.mkPos 1 4 (by decide)
def eighth : Q' := Q'.mkPos 1 8 (by decide)
def squareQuarter : Q' := quarter

private theorem haar_neg (n : Nat) (p : RatPoly) : H n (polyNeg p) ≈ -(H n p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (neg_smul p))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-1) p)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
        (.neg (.var 0)) (by decide) (fun _ => H n p)))

/-- The source-observable square is raw Haar, not the interacting variance. -/
def observableSquare (tail : Nat) (q f : RatPoly) : Q' :=
  let v := polyMul q f
  H (tail+1) (polyMul v v)

def sourceSquareMass (tail : Nat) (q f : RatPoly) : Q' :=
  observableSquare tail q f

/-- The actual commutator with half of the source-observable product removed. -/
def completedCommutator (tail : Nat) (q f : RatPoly) : RatPoly :=
  polyAdd (commutatorPolynomial (List.range (tail+1)) q f)
    (polySmul (-HalfPow.half) (polyMul q f))

private theorem supported_smul {n : Nat} (c : Q') {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem completedCommutator_supported (tail : Nat) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    SupportedQuaternionBlocks (tail+1) (completedCommutator tail q f) := by
  let active := List.range (tail+1)
  have hactive : ∀ i, i ∈ active → i < tail+1 :=
    fun i hi => List.mem_range.mp hi
  have hB : SupportedQuaternionBlocks (tail+1)
      (commutatorPolynomial active q f) := by
    unfold commutatorPolynomial
    exact supported_add
      (supported_polyMul hq (activeCasimirPolynomial_supported active hactive hf))
      (supported_smul (-2) (activeGamma_supported active hactive hq hf))
  exact supported_add hB (supported_smul (-HalfPow.half) (supported_polyMul hq hf))

/-- The explicit Type-level Haar certificate for the completed square. -/
def completedSquareCertificate (tail : Nat) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    Certificate (tail+1) (polyMul (completedCommutator tail q f)
      (completedCommutator tail q f)) :=
  Certificate.square _ (completedCommutator_supported tail q f hq hf)

def squareCompletionMass (tail : Nat) (q f : RatPoly) : Q' :=
  H (tail+1) (polyMul (completedCommutator tail q f)
    (completedCommutator tail q f))

theorem squareCompletionMass_nonnegative (tail : Nat) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    (0 : Q') ≤ squareCompletionMass tail q f :=
  (completedSquareCertificate tail q f hq hf).haar_nonnegative

/-- No eigenpin is used: the two literal Casimir pairings defining the
first-order source term are precisely the Haar pairing with the commutator. -/
theorem sourceFirstOrder_commutator_pair (tail : Nat) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceFirstOrder tail q f ≈
      H (tail+1) (polyMul (polyMul q f)
        (commutatorPolynomial (List.range (tail+1)) q f)) := by
  let n := tail+1
  let active := List.range n
  let v := polyMul q f
  let Cq := activeCasimirPolynomial active q
  let Cf := activeCasimirPolynomial active f
  let Cv := activeCasimirPolynomial active v
  let G := activeGamma active q f
  let B := commutatorPolynomial active q f
  have hv : SupportedQuaternionBlocks n v := supported_polyMul hq hf
  have hqff : SupportedQuaternionBlocks n (polyMul q (polyMul f f)) :=
    supported_polyMul hq (supported_polyMul hf hf)
  have hp := pairCasimir_eq_literal tail v v hv hv
  have hd := pairCasimir_eq_literal tail q (polyMul q (polyMul f f)) hq hqff
  have hcas : sourceFirstOrder tail q f ≈
      H n (polyMul v Cv) -
        H n (polyMul (polyMul q (polyMul f f)) Cq) :=
    Q'.add_eqv_congr' hp (Q'.neg_eqv_congr _ _ hd)
  have hproduct := activeCasimirPolynomial_mul active q f
  have hcancel : RatPolyCoeffEqv
      (polyAdd Cv (polyNeg (polyMul Cq f))) B := by
    unfold B commutatorPolynomial
    exact (hproduct.add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add
          (.add
            (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
            (.var 4))
          (.neg (.mul (.var 0) (.var 1))))
        (.add (.mul (.var 2) (.var 3)) (.var 4))
        (by decide) (fun
          | 0 => Cq | 1 => f | 2 => q | 3 => Cf | _ => polySmul (-2) G))
  have hpoly : RatPolyCoeffEqv
      (polyAdd (polyMul v Cv)
        (polyNeg (polyMul (polyMul q (polyMul f f)) Cq)))
      (polyMul v B) := by
    refine (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.neg (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 3))))
      (.mul (.mul (.var 0) (.var 1))
        (.add (.var 2) (.neg (.mul (.var 3) (.var 1)))))
      (by decide) (fun | 0 => q | 1 => f | 2 => Cv | _ => Cq)).trans ?_
    exact hcancel.mul_left v
  have hsum : H n (polyMul v Cv) -
      H n (polyMul (polyMul q (polyMul f f)) Cq) ≈ H n (polyMul v B) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (haar_neg n (polyMul (polyMul q (polyMul f f)) Cq)))))
      (haar_of_coeff hpoly)
  exact Q'.eqv_trans _ _ _ hcas hsum

/-- Exact square completion. The quarter square is raw Haar, not `qPq`
and not a centered/interacting variance. -/
theorem sourceFirstOrder_sub_square_complete (tail : Nat) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceFirstOrder tail q f - squareMass tail q f ≈
      quarter*observableSquare tail q f-squareCompletionMass tail q f := by
  let n := tail+1
  let v := polyMul q f
  let B := commutatorPolynomial (List.range n) q f
  let T := completedCommutator tail q f
  let A := H n (polyMul v B)
  let S := H n (polyMul B B)
  let Q := H n (polyMul v v)
  have hpair := sourceFirstOrder_commutator_pair tail q f hq hf
  let c := -HalfPow.half
  let z := polySmul c v
  have hm : RatPolyCoeffEqv (polySmul 2 (polyMul B z))
      (polySmul (-1) (polyMul v B)) :=
    (((RatPolyCoeffEqv.polyMul_smul_right c B v).trans
      ((RatPolyCoeffEqv.mul_comm B v).smul c)).smul 2).trans
      ((RatPolyCoeffEqv.smul_assoc 2 c _).trans
        (RatPolyCoeffEqv.smul_coefficient (by decide : (2 : Q')*c ≈ -1) _))
  have hz : RatPolyCoeffEqv (polyMul z z) (polySmul quarter (polyMul v v)) :=
    (RatPolyCoeffEqv.polyMul_smul_left c v z).trans
      (((RatPolyCoeffEqv.polyMul_smul_right c v v).smul c).trans
        ((RatPolyCoeffEqv.smul_assoc c c _).trans
          (RatPolyCoeffEqv.smul_coefficient (by decide : c*c ≈ quarter) _)))
  have hpoly : RatPolyCoeffEqv (polyMul T T)
      (polyAdd (polyAdd (polyMul B B) (polySmul (-1) (polyMul v B)))
        (polySmul quarter (polyMul v v))) := by
    exact (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
      (.add (.add (.mul (.var 0) (.var 0))
          (.mul (.const 2) (.mul (.var 0) (.var 1))))
        (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => B | _ => z)).trans
      ((((RatPolyCoeffEqv.refl _).add (cap_mul_left 2 _)).add
        (RatPolyCoeffEqv.refl _)).trans
        (((RatPolyCoeffEqv.refl _).add hm).add hz))
  have hsquare : squareCompletionMass tail q f ≈ S-A+quarter*Q := by
    exact Q'.eqv_trans _ _ _ (haar_of_coeff hpoly)
      (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
            (Q'.add_eqv_congr' (Q'.eqv_refl _)
              (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-1) _)
                (poly_identity_of_normal_eq
                  (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
                  (by decide) (fun _ => A)))))
          (quaternionHaar_polySmul n quarter _)))
  have hring : A-S ≈ quarter*Q-(S-A+quarter*Q) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.var 1)))
      (.add (.mul (.var 2) (.var 3))
        (.neg (.add (.add (.var 1) (.neg (.var 0)))
          (.mul (.var 2) (.var 3)))))
      (by decide) (fun | 0 => A | 1 => S | 2 => quarter | _ => Q)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hpair (Q'.eqv_refl _))
    (Q'.eqv_trans _ _ _ hring
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _ hsquare.symm)))

theorem sourceFirstOrder_sub_square_le_quarter (tail : Nat) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceFirstOrder tail q f - squareMass tail q f ≤
      quarter*observableSquare tail q f := by
  have hs := squareCompletionMass_nonnegative tail q f hq hf
  have h := Q'.add_le_add_left (quarter*observableSquare tail q f) _ _
    (Q'.neg_le_neg hs)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (sourceFirstOrder_sub_square_complete tail q f hq hf))
    (Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.var 0) (.neg (.const 0))) (.var 0)
        (by decide) (fun _ => quarter*observableSquare tail q f))))

/-- The exact cancelled remainder with its completed negative square. -/
def completedRemainder (tail : Nat) (w : Q') (K : Nat) (q f : RatPoly) : Q' :=
  let h := (1 : Q')-w
  let G := angularSquare tail f
  (HalfPow.half*(h*h))*
      (quarter*observableSquare tail q f-squareCompletionMass tail q f) +
    SU2QuaternionCyclicSecondOrder.sourceCubic tail w q f -
      SU2QuaternionCyclicSecondOrder.sourceOmitted tail w K q f -
      h*pairRemainder tail w K q (polyMul q G)

theorem completeRemainder_square_completion (tail : Nat) (w : Q') (K : Nat)
    (q f : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    completeRemainder tail w K q f ≈ completedRemainder tail w K q f :=
  Q'.eqv_trans _ _ _ (completeRemainder_cancellation tail w K q f hq hf)
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _
            (sourceFirstOrder_sub_square_complete tail q f hq hf))
          (Q'.eqv_refl _)) (Q'.eqv_refl _)) (Q'.eqv_refl _))

/-- Computed eighth coefficient, with the source-dependent cubic/omitted
and angular-pair budgets paid exactly as in the retained ceiling. -/
def squareCeiling (tail : Nat) (w : Q') (K : Nat) (q f : RatPoly) : Q' :=
  let h := (1 : Q')-w
  let G := angularSquare tail f
  (HalfPow.half*(h*h))*(squareQuarter*sourceSquareMass tail q f) +
    sourceErrorBudget tail w K q f +
      h*((h*h)*pairBudget tail q (polyMul q G))

theorem completeRemainder_le_squareCeiling (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    completeRemainder tail w K q f ≤ squareCeiling tail w K q f := by
  have hbase := completeRemainder_le_retained tail hw0 hw1 K hK q f hq hf
  have hquarter := sourceFirstOrder_sub_square_le_quarter tail q f hq hf
  have hh : (0 : Q') ≤ HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)) :=
    Q'.mul_nonneg _ _ HalfPow.half_nonneg
      (Q'.mul_nonneg _ _
        (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
        (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hquarter hh
  have hsum := Q'.add_le_add_right _ _
    (((1 : Q')-w)*((((1 : Q')-w)*((1 : Q')-w))*
      pairBudget tail q (polyMul q (angularSquare tail f))))
    (Q'.add_le_add_right _ _ (sourceErrorBudget tail w K q f) hscaled)
  have hright : retainedCeiling tail w K q f ≤ squareCeiling tail w K q f := hsum
  exact Q'.le_trans' _ _ _ hbase hright

#print axioms quarter
#print axioms eighth
#print axioms squareQuarter
#print axioms observableSquare
#print axioms sourceSquareMass
#print axioms completedCommutator
#print axioms completedCommutator_supported
#print axioms completedSquareCertificate
#print axioms squareCompletionMass
#print axioms squareCompletionMass_nonnegative
#print axioms sourceFirstOrder_commutator_pair
#print axioms sourceFirstOrder_sub_square_complete
#print axioms sourceFirstOrder_sub_square_le_quarter
#print axioms completedRemainder
#print axioms completeRemainder_square_completion
#print axioms squareCeiling
#print axioms completeRemainder_le_squareCeiling

end YMGap.Continuum.SU2QuaternionCompleteRemainderSquare
