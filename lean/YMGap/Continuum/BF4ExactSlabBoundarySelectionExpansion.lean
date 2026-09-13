/-
# Exact selection expansion of the EXISTING original bulk boundary numerator

The previously constructed boundaryNumerator is expanded only in its actual
exterior faces. The interior action, insertion, cutoff and target Haar
carrier remain unchanged. Each term is its actual centered exterior-selection
response. Empty selections vanish, and a selection disjoint from the entire
interior/probe region vanishes by proved Haar factorization.

This is a pin to the active boundary-response object, not a new proposed
correlator. General connecting-cluster reorganization, normalized summability
and decay with the probe's distance from the boundary remain open.
-/

import YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
import YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse

namespace YMGap.Continuum.BF4ExactSlabBoundarySelectionExpansion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabRemainderExpansion
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem swap_right (p a b : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul p a) b) (polyMul (polyMul p b) a) :=
  coeffEvalExpr_eqv_of_normalize_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
    (fun i => if i = 0 then p else if i = 1 then a else b)

def selectionMoment (w : Q') (K half padding : Nat) (p : RatPoly) (ids : List Nat) : Q' :=
  interiorSequence w half padding (polyMul p (remainderProduct w K (centralExtent (half+padding)) ids)) K

def selectionResponse (w : Q') (K half padding : Nat) (p : RatPoly) (ids : List Nat) : Q' :=
  selectionMoment w K half padding p ids * interiorSequence w half padding polyOne K +
    -(interiorSequence w half padding p K * selectionMoment w K half padding polyOne ids)

theorem fullMoment_expansion (w : Q') (K half padding : Nat) (p : RatPoly) :
    fullMoment w K half padding p ≈
      listQSum (selectionMoment w K half padding p) (selections (exteriorIds half padding)) := by
  let extent := centralExtent (half+padding)
  let I := polynomialProduct (faceHeatPolynomial w K extent) (interiorIds half padding)
  have he := ((RatPolyCoeffEqv.refl p).mul
    ((polynomialProduct_perm (faceHeatPolynomial w K extent) (face_partition half padding).symm).trans
      (polynomialProduct_append _ _ _))).trans (RatPolyCoeffEqv.mul_assoc p I _).symm
  have hf := haar_expansion (boundaryCompleteSlabLinks extent).length (faceHeatPolynomial w K extent)
    (fun id => faceHeatTail w extent id 1 K) (fun id => faceHeat_eq_one_add w extent id K)
    (polyMul p I) (exteriorIds half padding)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he) (Q'.eqv_trans _ _ _ hf
    (listQSum_congr_on _ _ _ (fun ids _ => haar_of_coeff (swap_right p I (remainderProduct w K extent ids)))))

private theorem sum_response {A : Type} (f g : A → Q') (a b : Q') : ∀ xs : List A,
    listQSum (fun x => f x*b + -(a*g x)) xs ≈ listQSum f xs*b + -(a*listQSum g xs)
  | [] => poly_identity_of_normal_eq (.const 0)
      (.add (.mul (.const 0) (.var 1)) (.neg (.mul (.var 0) (.const 0)))) (by decide)
      (fun i => if i = 0 then a else b)
  | x :: xs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_response f g a b xs))
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.var 0) (.var 5)) (.neg (.mul (.var 4) (.var 1))))
          (.add (.mul (.var 2) (.var 5)) (.neg (.mul (.var 4) (.var 3)))))
        (.add (.mul (.add (.var 0) (.var 2)) (.var 5)) (.neg (.mul (.var 4) (.add (.var 1) (.var 3)))))
        (by decide) (fun i => if i = 0 then f x else if i = 1 then g x else if i = 2 then listQSum f xs
          else if i = 3 then listQSum g xs else if i = 4 then a else b))

/-- EXACT pin to the existing boundary numerator, with a single common cutoff. -/
theorem boundaryNumerator_expansion (w : Q') (K half padding : Nat) (p : RatPoly) :
    boundaryNumerator w half padding p K ≈
      listQSum (selectionResponse w K half padding p) (selections (exteriorIds half padding)) :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ _ (fullMoment_expansion w K half padding p))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ (fullMoment_expansion w K half padding polyOne))))
    (Q'.eqv_symm (sum_response _ _ _ _ _))

private theorem selectionMoment_empty (w : Q') (K half padding : Nat) (p : RatPoly) :
    selectionMoment w K half padding p [] ≈ interiorSequence w half padding p K :=
  haar_of_coeff ((RatPolyCoeffEqv.mul_one p).mul (RatPolyCoeffEqv.refl _))

theorem selectionResponse_empty (w : Q') (K half padding : Nat) (p : RatPoly) :
    selectionResponse w K half padding p [] ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (selectionMoment_empty w K half padding p))
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ (selectionMoment_empty w K half padding polyOne))))
    (Q'.add_neg_self_eqv _)

private theorem selectionMoment_disjoint (w : Q') (K half padding : Nat) (p : RatPoly) (ids : List Nat)
    (links : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p)
    (hl : LinkLocal (centralExtent (half+padding)) links p)
    (hd : LinksDisjoint (links++faceLinks (centralExtent (half+padding)) (interiorIds half padding))
      (faceLinks (centralExtent (half+padding)) ids)) :
    selectionMoment w K half padding p ids ≈
      interiorSequence w half padding p K * activity w K (centralExtent (half+padding)) ids := by
  let extent := centralExtent (half+padding)
  let I := polynomialProduct (faceHeatPolynomial w K extent) (interiorIds half padding)
  have hlocal : LinkLocal extent (links++faceLinks extent (interiorIds half padding)) (polyMul p I) :=
    BlockLocal.mul (hl.mono (fun _ h => List.mem_append.mpr (Or.inl h)))
      ((heatProduct_local w K extent _).mono (fun _ h => List.mem_append.mpr (Or.inr h)))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (swap_right p (remainderProduct w K extent ids) I))
    (haar_product (supported_polyMul hp (heatProduct_supported w K extent _)) (remainderProduct_supported w K extent ids)
      (linkLocal_disjoint hlocal (remainderProduct_local w K extent ids) hd))

/-- A selection detached from the ENTIRE interior/probe region contributes zero.
This is weaker than proving decay with the probe-to-boundary distance. -/
theorem selectionResponse_disjoint_zero (w : Q') (K half padding : Nat) (p : RatPoly) (ids : List Nat)
    (links : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p)
    (hl : LinkLocal (centralExtent (half+padding)) links p)
    (hd : LinksDisjoint (links++faceLinks (centralExtent (half+padding)) (interiorIds half padding))
      (faceLinks (centralExtent (half+padding)) ids)) :
    selectionResponse w K half padding p ids ≈ 0 := by
  have h := Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ (interiorSequence w half padding polyOne K)
      (selectionMoment_disjoint w K half padding p ids links hp hl hd))
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left (interiorSequence w half padding p K) _ _
      (selectionMoment_disjoint w K half padding polyOne ids links (supported_one _) (BlockLocal.one _ _) hd)))
  exact Q'.eqv_trans _ _ _ h (poly_identity_of_normal_eq
    (.add (.mul (.mul (.var 0) (.var 2)) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 1) (.var 2)))))
    (.const 0) (by decide) (fun i => if i = 0 then interiorSequence w half padding p K
      else if i = 1 then interiorSequence w half padding polyOne K else activity w K (centralExtent (half+padding)) ids))

end YMGap.Continuum.BF4ExactSlabBoundarySelectionExpansion

#print axioms YMGap.Continuum.BF4ExactSlabBoundarySelectionExpansion.selectionMoment
#print axioms YMGap.Continuum.BF4ExactSlabBoundarySelectionExpansion.selectionResponse
#print axioms YMGap.Continuum.BF4ExactSlabBoundarySelectionExpansion.fullMoment_expansion
#print axioms YMGap.Continuum.BF4ExactSlabBoundarySelectionExpansion.boundaryNumerator_expansion
#print axioms YMGap.Continuum.BF4ExactSlabBoundarySelectionExpansion.selectionResponse_empty
#print axioms YMGap.Continuum.BF4ExactSlabBoundarySelectionExpansion.selectionResponse_disjoint_zero
