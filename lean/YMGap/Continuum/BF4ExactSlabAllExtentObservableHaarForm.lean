/-
# Every original signed slab bilinear is its literal observable Haar form

The full existing exactCorrectedSlabReflectedKernel, at every odd extent,
is expanded under its SAME product-Haar integral. Lower and reflected-upper
observables retain all signed coefficients and their original heat dressing.
The central label sum is exactly the product of actual face heat polynomials.

This is an original-law identity, not a positivity assumption or a transfer.
It exposes the complete observable for the all-extent temporal-gauge proof.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
import YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit

namespace YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem sum_congr {A : Type} (f g : A → RatPoly) (h : ∀ a, RatPolyCoeffEqv (f a) (g a)) :
    ∀ xs : List A, RatPolyCoeffEqv (finitePolySum f xs) (finitePolySum g xs)
  | [] => RatPolyCoeffEqv.refl _
  | a :: xs => (h a).add (sum_congr f g h xs)

private theorem sum_mul {A : Type} (f : A → RatPoly) (p : RatPoly) : ∀ xs : List A,
    RatPolyCoeffEqv (polyMul (finitePolySum f xs) p) (finitePolySum (fun a => polyMul (f a) p) xs)
  | [] => RatPolyCoeffEqv.refl _
  | a :: xs => by
      change RatPolyCoeffEqv (polyMul (polyAdd (f a) (finitePolySum f xs)) p) _
      rw [polyMul_add_left_exact]
      exact (RatPolyCoeffEqv.refl _).add (sum_mul f p xs)

private theorem mul_sum {A : Type} (p : RatPoly) (f : A → RatPoly) : ∀ xs : List A,
    RatPolyCoeffEqv (polyMul p (finitePolySum f xs)) (finitePolySum (fun a => polyMul p (f a)) xs)
  | [] => RatPolyCoeffEqv.mul_zero_right p
  | _ :: xs => (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      ((RatPolyCoeffEqv.refl _).add (mul_sum p f xs))

private theorem three_sums {A B C : Type} (l : A → RatPoly) (m : B → RatPoly) (r : C → RatPoly)
    (ls : List A) (ms : List B) (rs : List C) :
    RatPolyCoeffEqv (polyMul (finitePolySum l ls) (polyMul (finitePolySum m ms) (finitePolySum r rs)))
      (finitePolySum (fun a => finitePolySum (fun c => finitePolySum
        (fun b => polyMul (l a) (polyMul (m b) (r c))) ms) rs) ls) := by
  let mr := fun c => polyMul (finitePolySum m ms) (r c)
  refine ((mul_sum (finitePolySum m ms) r rs).mul_left _).trans ?_
  refine (sum_mul l (finitePolySum mr rs) ls).trans ?_
  apply sum_congr
  intro a
  refine (mul_sum (l a) mr rs).trans ?_
  apply sum_congr
  intro c
  exact ((sum_mul m (r c) ms).mul_left (l a)).trans (mul_sum (l a) (fun b => polyMul (m b) (r c)) ms)

private theorem scaled_three (a b : Q') (l m r : RatPoly) :
    RatPolyCoeffEqv (polyMul (polySmul a l) (polyMul m (polySmul b r)))
      (polySmul (a * b) (polyMul l (polyMul m r))) :=
  ((RatPolyCoeffEqv.polyMul_smul_right _ _ _).mul_left _).trans
    ((RatPolyCoeffEqv.polyMul_smul_left _ _ _).trans
      (((RatPolyCoeffEqv.polyMul_smul_right _ _ _).smul _).trans (RatPolyCoeffEqv.smul_assoc _ _ _)))

def lowerObservable (w : Q') (K half : Nat) (c : EdgeLabelling → Q') : RatPoly :=
  finitePolySum (fun s => polySmul (c s) (lowerPolynomial w K half s)) (centralHalfStates K half)

def upperObservable (w : Q') (K half : Nat) (c : EdgeLabelling → Q') : RatPoly :=
  finitePolySum (fun s => polySmul (c s) (upperPolynomial w K half s)) (centralHalfStates K half)

def interfaceHeatInsertion (w : Q') (K half : Nat) : RatPoly :=
  finitePolySum (interfaceLabelPolynomial w K half) (centralBoundaryChannels K half)

def observableIntegrand (w : Q') (K half : Nat) (left right : EdgeLabelling → Q') : RatPoly :=
  polyMul (lowerObservable w K half left) (polyMul (interfaceHeatInsertion w K half) (upperObservable w K half right))

theorem observableIntegrand_haar_expansion (w : Q') (K half : Nat) (left right : EdgeLabelling → Q') :
    quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (observableIntegrand w K half left right) ≈
      listQSum (fun l => listQSum (fun r => listQSum
        (fun b => (left l * right r) * quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
          (polyMul (lowerPolynomial w K half l) (polyMul (interfaceLabelPolynomial w K half b) (upperPolynomial w K half r))))
        (centralBoundaryChannels K half)) (centralHalfStates K half)) (centralHalfStates K half) := by
  refine Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _ (three_sums
    (fun l => polySmul (left l) (lowerPolynomial w K half l)) (interfaceLabelPolynomial w K half)
    (fun r => polySmul (right r) (upperPolynomial w K half r))
    (centralHalfStates K half) (centralBoundaryChannels K half) (centralHalfStates K half))) ?_
  refine Q'.eqv_trans _ _ _ (quaternionHaar_finitePolySum₃ _ _
    (centralHalfStates K half) (centralHalfStates K half) (centralBoundaryChannels K half)) ?_
  apply listQSum_congr
  intro l
  apply listQSum_congr
  intro r
  apply listQSum_congr
  intro b
  exact Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _ (scaled_three _ _ _ _ _)) (quaternionHaar_polySmul _ _ _)

/-- SAME existing signed reflected kernel, all odd extents and all signed
boundary coefficient functions, without any positivity assumption. -/
theorem exact_bilinear_eq_haar (w : Q') (K half : Nat) (left right : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates K half) left right (exactCorrectedSlabReflectedKernel w K half) ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (observableIntegrand w K half left right) := by
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (observableIntegrand_haar_expansion w K half left right))
  unfold finiteJointBilinear
  apply listQSum_congr
  intro l
  apply listQSum_congr
  intro r
  unfold exactCorrectedSlabReflectedKernel
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (listQSum_mul_left (left l * right r) _ (centralBoundaryChannels K half))) ?_
  apply listQSum_congr
  intro b
  exact Q'.mul_eqv_congr_left _ _ _ (dualTerm_eq_threeFactorHaar w K half l b r)

def localFaceTerm (w : Q') (K extent id spin : Nat) : RatPoly :=
  polySmul (coeffAt (heatKernelPacket K w) spin)
    (characterPolynomial (correctedSlabPlaquettePolynomial extent (slabPlaquetteAt extent id)).scalar spin)

def faceHeatPolynomial (w : Q') (K extent id : Nat) : RatPoly :=
  finitePolySum (localFaceTerm w K extent id) (List.range (K + 1))

def interfaceHeatProduct (w : Q') (K half : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K (centralExtent half)) (centralFixedFaceIds half)

private theorem labelProduct_fold (f : Nat → Nat → RatPoly) (s : EdgeLabelling) : ∀ ids : List Nat,
    labelProduct f s ids = polynomialProduct (fun id => f id (s id)) ids
  | [] => rfl
  | _ :: ids => by simp only [labelProduct, polynomialProduct, List.foldr, labelProduct_fold f s ids]

private theorem facewiseProduct_fold (K : Nat) (f : Nat → Nat → RatPoly) : ∀ ids : List Nat,
    facewiseProduct K f ids = polynomialProduct (fun id => finitePolySum (f id) (List.range (K + 1))) ids
  | [] => rfl
  | _ :: ids => by simp only [facewiseProduct, polynomialProduct, List.foldr, facewiseProduct_fold K f ids]

/-- Exact Cartesian resummation on the existing central boundary carrier;
no extent-specific enumeration is evaluated. -/
theorem interfaceHeatInsertion_eq_product (w : Q') (K half : Nat) :
    RatPolyCoeffEqv (interfaceHeatInsertion w K half) (interfaceHeatProduct w K half) := by
  have hlabel (s : EdgeLabelling) : interfaceLabelPolynomial w K half s =
      labelProduct (localFaceTerm w K (centralExtent half)) s (centralFixedFaceIds half) := by
    rw [labelProduct_fold]
    rfl
  unfold interfaceHeatInsertion centralBoundaryChannels
  rw [funext hlabel]
  have h := bounded_label_sum_product K (localFaceTerm w K (centralExtent half)) (centralFixedFaceIds half)
    (BF4ExactSlabAnchoredCutoffLimit.fixedFaceIds_nodup half)
  rw [facewiseProduct_fold] at h
  exact h

theorem observableIntegrand_eq_product (w : Q') (K half : Nat) (left right : EdgeLabelling → Q') :
    RatPolyCoeffEqv (observableIntegrand w K half left right)
      (polyMul (lowerObservable w K half left) (polyMul (interfaceHeatProduct w K half) (upperObservable w K half right))) :=
  ((interfaceHeatInsertion_eq_product w K half).mul_right _).mul_left _

/-- Full ORIGINAL signed bilinear = Haar of the full heat-dressed boundary
observables and the product of actual crossing heat characters. -/
theorem exact_bilinear_eq_productHaar (w : Q') (K half : Nat) (left right : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates K half) left right (exactCorrectedSlabReflectedKernel w K half) ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
        (polyMul (lowerObservable w K half left) (polyMul (interfaceHeatProduct w K half) (upperObservable w K half right))) :=
  Q'.eqv_trans _ _ _ (exact_bilinear_eq_haar w K half left right)
    (haar_of_coeff_eqv _ (observableIntegrand_eq_product w K half left right))

end YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm.lowerObservable
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm.upperObservable
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm.interfaceHeatInsertion
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm.observableIntegrand
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm.observableIntegrand_haar_expansion
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm.exact_bilinear_eq_haar
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm.localFaceTerm
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm.faceHeatPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm.interfaceHeatProduct
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm.interfaceHeatInsertion_eq_product
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm.observableIntegrand_eq_product
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm.exact_bilinear_eq_productHaar
