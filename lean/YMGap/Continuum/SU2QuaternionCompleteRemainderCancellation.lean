/-
# Complete source Taylor cancellation at the original full product heat

The second-order source flux cancels the first Taylor coefficient of the
change from the bare source square to the interacting angular weight. The
result retains the commutator square, both signed cubic/cutoff terms, and the
remaining angular Taylor remainder. No source-dependent budget is compared
with an interacting variance here.
-/

import YMGap.Continuum.SU2QuaternionCyclicSecondOrder
import YMGap.Continuum.SU2QuaternionSecondOrderCancellation
import YMGap.Continuum.SU2QuaternionLiteralCasimirPairing
import YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor

namespace YMGap.Continuum.SU2QuaternionCompleteRemainderCancellation

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
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap)
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
  (activeCasimirPolynomial activeCasimirPolynomial_supported)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder
open YMGap.Continuum.SU2QuaternionSecondOrderCancellation
open YMGap.Continuum.SU2QuaternionLiteralCasimirPairing
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The full active angular square of the unchanged observable. -/
def angularSquare (tail : Nat) (f : RatPoly) : RatPoly :=
  activeGamma (List.range (tail+1)) f f

/-- Literal change from `q²` to `q * P(q)`, before any normalization. -/
def angularWeightChange (tail : Nat) (w : Q') (K : Nat) (q f : RatPoly) : Q' :=
  let n := tail+1
  let G := angularSquare tail f
  H n (polyMul (polyMul q
    (polyAdd (productMap n w K (List.range n) q) (polyNeg q))) G)

/-- The complete mixed-minus-diagonal source remainder and angular change. -/
def completeRemainder (tail : Nat) (w : Q') (K : Nat) (q f : RatPoly) : Q' :=
  (pairRemainder tail w K q (polyMul q (polyMul f f)) -
    pairRemainder tail w K (polyMul q f) (polyMul q f)) -
    ((1 : Q')-w)*angularWeightChange tail w K q f

/-- The surviving nonnegative square is kept with the original source and
the entire signed observable, including every cross term. -/
def squareMass (tail : Nat) (q f : RatPoly) : Q' :=
  let n := tail+1
  let C := commutatorPolynomial (List.range n) q f
  H n (polyMul C C)

/-- Actual supported square data for the retained contribution, with no
positivity assumption on the source or observable. -/
def squareMassCertificate (tail : Nat) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    Certificate (tail+1)
      (polyMul (commutatorPolynomial (List.range (tail+1)) q f)
        (commutatorPolynomial (List.range (tail+1)) q f)) := by
  let active := List.range (tail+1)
  have hactive : ∀ i, i ∈ active → i < tail+1 := fun i hi => List.mem_range.mp hi
  have hg := activeGamma_supported active hactive hq hf
  have hs : SupportedQuaternionBlocks (tail+1) (polySmul (-2) (activeGamma active q f)) := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact hg s hs
  exact Certificate.square _ (supported_add
    (supported_polyMul hq (activeCasimirPolynomial_supported active hactive hf)) hs)

theorem squareMass_nonnegative (tail : Nat) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    (0 : Q') ≤ squareMass tail q f :=
  (squareMassCertificate tail q f hq hf).haar_nonnegative

/-- The exact cancelled expression, with actual signed cubic, omitted-mode,
and angular Taylor terms still present. -/
def cancelledRemainder (tail : Nat) (w : Q') (K : Nat) (q f : RatPoly) : Q' :=
  let h := (1 : Q')-w
  let G := angularSquare tail f
  (HalfPow.half*(h*h))*(sourceFirstOrder tail q f - squareMass tail q f) +
    sourceCubic tail w q f - sourceOmitted tail w K q f -
      h*pairRemainder tail w K q (polyMul q G)

private theorem haar_neg (n : Nat) (p : RatPoly) :
    H n (polyNeg p) ≈ -(H n p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (neg_smul p))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-1) p)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
        (.neg (.var 0)) (by decide) (fun _ => H n p)))

/-- The first angular-weight Taylor coefficient is exactly the flux that
appears with opposite sign in the source's quadratic coefficient. -/
theorem angularWeightChange_taylor (tail : Nat) (w : Q') (K : Nat)
    (q f : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    angularWeightChange tail w K q f ≈
      -(((1 : Q')-w)*H (tail+1)
        (curvatureFlux (List.range (tail+1)) q f)) +
      pairRemainder tail w K q (polyMul q (angularSquare tail f)) := by
  let n := tail+1
  let G := angularSquare tail f
  let t := polyMul q G
  let Pq := productMap n w K (List.range n) q
  let F := H n (curvatureFlux (List.range n) q f)
  let A := H n (polyMul t q)
  let R := pairRemainder tail w K q t
  have hG : SupportedQuaternionBlocks n G :=
    activeGamma_supported (List.range n) (fun i hi => List.mem_range.mp hi) hf hf
  have ht : SupportedQuaternionBlocks n t := supported_polyMul hq hG
  have hcoeff : RatPolyCoeffEqv
      (polyMul (polyMul q (polyAdd Pq (polyNeg q))) G)
      (polyAdd (polyMul t Pq) (polyNeg (polyMul t q))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.add (.var 1) (.neg (.var 0)))) (.var 2))
      (.add (.mul (.mul (.var 0) (.var 2)) (.var 1))
        (.neg (.mul (.mul (.var 0) (.var 2)) (.var 0))))
      (by decide) (fun | 0 => q | 1 => Pq | _ => G)
  have hchange : angularWeightChange tail w K q f ≈
      H n (polyMul t Pq) - A :=
    Q'.eqv_trans _ _ _ (haar_of_coeff hcoeff)
      (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg n (polyMul t q))))
  have hTaylor := productPair_taylor tail w K q t hq
  have hCasimir := pairCasimir_eq_literal tail q t hq ht
  have hflux : H n (polyMul t (activeCasimirPolynomial (List.range n) q)) ≈ F := by
    unfold F curvatureFlux t G angularSquare
    exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun
        | 0 => q
        | 1 => activeGamma (List.range n) f f
        | _ => activeCasimirPolynomial (List.range n) q))
  have hC : pairCasimir tail q t ≈ F :=
    Q'.eqv_trans _ _ _ hCasimir hflux
  have halg : (A + -(((1 : Q')-w)*F) + R) - A ≈
      -(((1 : Q')-w)*F) + R :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.neg (.mul (.var 1) (.var 2)))) (.var 3))
        (.neg (.var 0)))
      (.add (.neg (.mul (.var 1) (.var 2))) (.var 3))
      (by decide) (fun | 0 => A | 1 => (1 : Q')-w | 2 => F | _ => R)
  exact Q'.eqv_trans _ _ _ hchange
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hTaylor (Q'.eqv_refl _))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' (Q'.add_eqv_congr' (Q'.eqv_refl _)
            (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ hC)))
            (Q'.eqv_refl _)) (Q'.eqv_refl _))
        halg))

/-- The full quadratic source flux cancels, leaving only the first-order
angular square and a negative commutator square. This is an exact finite
identity for the actual cutoff operator, not an asymptotic statement. -/
theorem completeRemainder_cancellation (tail : Nat) (w : Q') (K : Nat)
    (q f : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    completeRemainder tail w K q f ≈ cancelledRemainder tail w K q f := by
  let h := (1 : Q')-w
  let F := H (tail+1) (curvatureFlux (List.range (tail+1)) q f)
  let S := squareMass tail q f
  let A := sourceFirstOrder tail q f
  let B := sourceCubic tail w q f
  let D := sourceOmitted tail w K q f
  let R := pairRemainder tail w K q (polyMul q (angularSquare tail f))
  have hsecond := sourceSecondMoment_cancellation tail q f hq hf
  have hsource := sourceRemainder_secondOrder tail w K q f
  have hangular := angularWeightChange_taylor tail w K q f hq hf
  have hbase : completeRemainder tail w K q f ≈
      (HalfPow.half*(h*h))*(((-2 : Q')*F-S)+A) + B-D - h*(-(h*F)+R) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hsource
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left h _ _ hangular)))
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.add_eqv_congr' hsecond (Q'.eqv_refl _)))
            (Q'.eqv_refl _))
          (Q'.eqv_refl _)) (Q'.eqv_refl _))
  have hcancel :
      (HalfPow.half*(h*h))*(((-2 : Q')*F-S)+A) + B-D - h*(-(h*F)+R) ≈
      ((HalfPow.half*(h*h))*(A-S) + B-D-h*R) +
        (((1 : Q')+(-2)*HalfPow.half)*((h*h)*F)) :=
    poly_identity_of_normal_eq
      (.add
        (.add
          (.add
            (.mul (.mul (.var 7) (.mul (.var 0) (.var 0)))
              (.add (.add (.mul (.const (-2)) (.var 1)) (.neg (.var 2))) (.var 3)))
            (.var 4)) (.neg (.var 5)))
        (.neg (.mul (.var 0)
          (.add (.neg (.mul (.var 0) (.var 1))) (.var 6)))))
      (.add
        (.add
          (.add
            (.add
              (.mul (.mul (.var 7) (.mul (.var 0) (.var 0)))
                (.add (.var 3) (.neg (.var 2)))) (.var 4))
            (.neg (.var 5))) (.neg (.mul (.var 0) (.var 6))))
        (.mul (.add (.const 1) (.mul (.const (-2)) (.var 7)))
          (.mul (.mul (.var 0) (.var 0)) (.var 1))))
      (by decide)
      (fun
        | 0 => h
        | 1 => F
        | 2 => S
        | 3 => A
        | 4 => B
        | 5 => D
        | 6 => R
        | _ => HalfPow.half)
  have hzero : (((1 : Q')+(-2)*HalfPow.half)*((h*h)*F)) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (by decide : (1 : Q')+(-2)*HalfPow.half ≈ 0)) (Q'.zero_mul_eqv _)
  exact Q'.eqv_trans _ _ _ hbase (Q'.eqv_trans _ _ _ hcancel
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) hzero)
      (Q'.eqv_of_eq (Q'.add_zero' _))))

/-- A ceiling retaining the negative commutator square. Cubic and omitted
cutoff data and the angular Taylor debt receive explicit source-dependent
absolute budgets; none is claimed uniformly small on changing sources. -/
def retainedCeiling (tail : Nat) (w : Q') (K : Nat) (q f : RatPoly) : Q' :=
  let h := (1 : Q')-w
  let G := angularSquare tail f
  (HalfPow.half*(h*h))*(sourceFirstOrder tail q f-squareMass tail q f) +
    sourceErrorBudget tail w K q f +
      h*((h*h)*pairBudget tail q (polyMul q G))

theorem completeRemainder_le_retained (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    completeRemainder tail w K q f ≤ retainedCeiling tail w K q f := by
  let h := (1 : Q')-w
  let R := pairRemainder tail w K q (polyMul q (angularSquare tail f))
  let B := (HalfPow.half*(h*h))*(sourceFirstOrder tail q f-squareMass tail q f)
  let E := sourceErrorBudget tail w K q f
  let T := (h*h)*pairBudget tail q (polyMul q (angularSquare tail f))
  have hh : (0 : Q') ≤ h := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have he := sourceError_bound tail hw0 (Q'.le_of_lt hw1) K q f
  have hr := neg_pairRemainder_le_quadratic tail hw0 hw1 K hK
    q (polyMul q (angularSquare tail f))
  have hscaled : -(h*R) ≤ h*T :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.neg (.mul (.var 0) (.var 1)))
        (.mul (.var 0) (.neg (.var 1)))
        (by decide) (fun | 0 => h | _ => R)))
      (Q'.mul_le_mul_of_nonneg_left _ _ h hr hh)
  have hsum := Q'.add_le_add
    (Q'.add_le_add_left B _ _ he) hscaled
  have hleft : cancelledRemainder tail w K q f ≈
      (B+(sourceCubic tail w q f-sourceOmitted tail w K q f)) + -(h*R) :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1)) (.neg (.var 2)))
        (.neg (.mul (.var 3) (.var 4))))
      (.add (.add (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.neg (.mul (.var 3) (.var 4))))
      (by decide) (fun
        | 0 => B
        | 1 => sourceCubic tail w q f
        | 2 => sourceOmitted tail w K q f
        | 3 => h
        | _ => R)
  have hright : (B+E)+h*T ≈ retainedCeiling tail w K q f :=
    Q'.eqv_refl _
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (completeRemainder_cancellation tail w K q f hq hf))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hright)))

#print axioms angularSquare
#print axioms angularWeightChange
#print axioms completeRemainder
#print axioms squareMass
#print axioms squareMassCertificate
#print axioms squareMass_nonnegative
#print axioms cancelledRemainder
#print axioms angularWeightChange_taylor
#print axioms completeRemainder_cancellation
#print axioms retainedCeiling
#print axioms completeRemainder_le_retained

end YMGap.Continuum.SU2QuaternionCompleteRemainderCancellation
