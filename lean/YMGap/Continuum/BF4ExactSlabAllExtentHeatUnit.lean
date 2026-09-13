/-
# Full heat-dressed unit codes on the original completed slab carriers

The all-label coefficient one is resummed over the actual bounded lower
carrier, not replaced by the trivial-representation delta. Both boundary
observables become products of ORIGINAL plaquette heat factors. The exact
pairing keeps the left, interface and right cutoffs separate.

At equal finite cutoffs the quadratic is the full original slab heat-product
Haar integral. In the common completion the interface is instead evaluated
at an explicit common stage, with the two boundary anchors retained.
This pins a concrete sequence of full heat-dressed unit codes; it does NOT
assert that the moving-anchor sequence is Cauchy. Its convergence, physical
vacuum stationarity, inter-slab compatibility and physical time remain open.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS

namespace YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentObservableReflection
open YMGap.Continuum.BF4ExactSlabAllExtentBoundaryCutoffRecoding
open YMGap.Continuum.BF4ExactSlabAllExtentFiniteBoundaryObservable
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS
open YMGap.Continuum.BF4ExactSlabAllExtentVacuumNormalization
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem sum_congr {A : Type} (f g : A → RatPoly) (h : ∀ a, RatPolyCoeffEqv (f a) (g a)) :
    ∀ xs : List A, RatPolyCoeffEqv (finitePolySum f xs) (finitePolySum g xs)
  | [] => RatPolyCoeffEqv.refl _
  | a :: xs => (h a).add (sum_congr f g h xs)

private theorem labelProduct_fold (f : Nat → Nat → RatPoly) (s : EdgeLabelling) : ∀ ids : List Nat,
    labelProduct f s ids = polynomialProduct (fun id => f id (s id)) ids
  | [] => rfl
  | _ :: ids => by simp only [labelProduct, polynomialProduct, List.foldr, labelProduct_fold f s ids]

private theorem facewiseProduct_fold (K : Nat) (f : Nat → Nat → RatPoly) : ∀ ids : List Nat,
    facewiseProduct K f ids = polynomialProduct (fun id => finitePolySum (f id) (List.range (K + 1))) ids
  | [] => rfl
  | _ :: ids => by simp only [facewiseProduct, polynomialProduct, List.foldr, facewiseProduct_fold K f ids]

theorem original_label_product_sum (K : Nat) (f : Nat → Nat → RatPoly) (ids : List Nat) (hn : ids.Nodup) :
    RatPolyCoeffEqv
      (finitePolySum (fun s => polynomialProduct (fun id => f id (s id)) ids) (boundedEdgeLabellings K ids))
      (polynomialProduct (fun id => finitePolySum (f id) (List.range (K + 1))) ids) := by
  have h := bounded_label_sum_product K f ids hn
  rw [facewiseProduct_fold, funext (fun s => labelProduct_fold f s ids)] at h
  exact h

def lowerHeatProduct (w : Q') (K half : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K (centralExtent half)) (centralLowerFaceIds half)

def upperHeatProduct (w : Q') (K half : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K (centralExtent half)) (centralUpperFaceIds half)

theorem lowerObservable_one (w : Q') (K half : Nat) :
    RatPolyCoeffEqv (lowerObservable w K half (fun _ => 1)) (lowerHeatProduct w K half) :=
  (sum_congr _ _ (fun _ => RatPolyCoeffEqv.one_smul _) _).trans
    (original_label_product_sum K (localFaceTerm w K (centralExtent half)) (centralLowerFaceIds half)
      (BF4ExactSlabBoundaryCutoffRecoding.lowerFaceIds_nodup half))

/-- Reindex the actual upper face product onto the original lower label carrier. -/
theorem upperPolynomial_reindexed (w : Q') (K half : Nat) (s : EdgeLabelling) :
    RatPolyCoeffEqv (upperPolynomial w K half s)
      (polynomialProduct (fun id => localFaceTerm w K (centralExtent half)
        (slabFaceReflectId (centralExtent half) id) (s id)) (centralLowerFaceIds half)) := by
  let f := weightedFacePolynomial w K (centralExtent half)
    (fun j => s (slabFaceReflectId (centralExtent half) j))
  have hp : RatPolyCoeffEqv (polynomialProduct f (centralUpperFaceIds half))
      (polynomialProduct (fun id => f (slabFaceReflectId (centralExtent half) id)) (centralLowerFaceIds half)) := by
    have h := polynomialProduct_perm f (reflected_lower_ids half)
    simpa only [polynomialProduct, List.foldr_map] using h.symm
  have he := polynomialProduct_congr
    (fun id => f (slabFaceReflectId (centralExtent half) id))
    (fun id => localFaceTerm w K (centralExtent half) (slabFaceReflectId (centralExtent half) id) (s id))
    (centralLowerFaceIds half) (fun id hi => by
      unfold f weightedFacePolynomial localFaceTerm
      dsimp only
      rw [slabFaceReflectId_involutive (mem_centralLowerFaceIds.mp hi).1])
  rw [he] at hp
  exact hp

theorem upperObservable_one (w : Q') (K half : Nat) :
    RatPolyCoeffEqv (upperObservable w K half (fun _ => 1)) (upperHeatProduct w K half) := by
  have h := (sum_congr _ _ (fun s => (RatPolyCoeffEqv.one_smul _).trans
    (upperPolynomial_reindexed w K half s)) (centralHalfStates K half)).trans
    (original_label_product_sum K
      (fun id => localFaceTerm w K (centralExtent half) (slabFaceReflectId (centralExtent half) id))
      (centralLowerFaceIds half) (BF4ExactSlabBoundaryCutoffRecoding.lowerFaceIds_nodup half))
  have hp := polynomialProduct_perm (faceHeatPolynomial w K (centralExtent half)) (reflected_lower_ids half)
  simp only [polynomialProduct, List.foldr_map] at hp
  exact h.trans hp

/-- All retained boundary coefficients are one, not only the zero label. -/
def heatUnitCode (K half : Nat) : BoundaryObservable half :=
  BoundaryObservable.ofCoefficients half K (fun _ => 1)

theorem heatUnitCode_on_carrier (K half : Nat) {s : EdgeLabelling} (hs : s ∈ centralHalfStates K half) :
    (heatUnitCode K half).coefficient s = 1 :=
  BoundaryObservable.ofCoefficients_on_anchor half K _ hs

theorem heatUnitCode_zero (half : Nat) : heatUnitCode 0 half = vacuumCode half := rfl

/-- Left and right anchors stay fixed while the original interface cutoff varies. -/
def mixedHeatProduct (w : Q') (left interface right half : Nat) : RatPoly :=
  polyMul (lowerHeatProduct w left half) (polyMul (interfaceHeatProduct w interface half) (upperHeatProduct w right half))

theorem heatUnitCode_finite_pairing (w : Q') (K left right half : Nat) (hl : left ≤ K) (hr : right ≤ K) :
    finiteForm w K (heatUnitCode left half) (heatUnitCode right half) ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (mixedHeatProduct w left K right half) := by
  have hleft := (lowerObservable_extension w hl half (fun _ => 1)).trans (lowerObservable_one w left half)
  have hright := (upperObservable_extension w hr half (fun _ => 1)).trans (upperObservable_one w right half)
  exact Q'.eqv_trans _ _ _ (exact_bilinear_eq_haar w K half _ _)
    (haar_of_coeff_eqv _ (hleft.mul ((interfaceHeatInsertion_eq_product w K half).mul hright)))

def fullHeatProduct (w : Q') (K half : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K (centralExtent half)) (slabPhysicalFaceEdges (centralExtent half))

/-- At equal finite cutoffs the all-label unit quadratic is the FULL original action integral. -/
theorem heatUnitCode_full_action (w : Q') (K half : Nat) :
    finiteForm w K (heatUnitCode K half) (heatUnitCode K half) ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (fullHeatProduct w K half) :=
  Q'.eqv_trans _ _ _ (heatUnitCode_finite_pairing w K K K half (Nat.le_refl _) (Nat.le_refl _))
    (haar_of_coeff_eqv _ (central_product_factorization half (faceHeatPolynomial w K (centralExtent half))).symm)

/-- The explicit stage must clear BOTH anchors and their original common-form modulus. -/
def heatUnitPairingStage (w : Q') (left right half : Nat) : Nat :=
  max (max left right) (formModulus w (heatUnitCode left half) (heatUnitCode right half))

theorem heatUnitCode_limit_pairing (w : Q') (left right half : Nat) :
    limitForm w (heatUnitCode left half) (heatUnitCode right half) ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
        (mixedHeatProduct w left (heatUnitPairingStage w left right half) right half) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (finiteForm_stable w _ _ _ (Nat.le_max_right _ _)))
    (heatUnitCode_finite_pairing w _ left right half
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)))

theorem heatUnitCode_completed_pairing (w : Q') (hw : (0 : Q') ≤ w) (left right half : Nat) :
    (cutoffLimitCompletion w hw half).hilbert.cinner
      (cutoffLimitEmbed w hw (heatUnitCode left half)) (cutoffLimitEmbed w hw (heatUnitCode right half)) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ'
        (quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
          (mixedHeatProduct w left (heatUnitPairingStage w left right half) right half))) :=
  (cutoffLimitEmbed_pairing w hw _ _).trans
    (Quotient.sound (CReal.ofQ'_equiv_of_eqv (heatUnitCode_limit_pairing w left right half)))

end YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit.original_label_product_sum
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit.lowerObservable_one
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit.upperPolynomial_reindexed
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit.upperObservable_one
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit.heatUnitCode
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit.heatUnitCode_on_carrier
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit.heatUnitCode_zero
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit.mixedHeatProduct
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit.heatUnitCode_finite_pairing
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit.fullHeatProduct
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit.heatUnitCode_full_action
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit.heatUnitPairingStage
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit.heatUnitCode_limit_pairing
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit.heatUnitCode_completed_pairing
