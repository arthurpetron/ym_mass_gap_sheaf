/-
# ORIGINAL action and boundary determinant for an off-center slab placement

The translated source faces and their actual target complement partition
the original target action. Coefficientwise dressing keeps every shared
link. The resulting determinant and its two distinct partition factors
are pinned to the EXISTING arbitrary-keep mixed-action functional, so its
proved analytic estimates can be reused without changing probability law.
The centered specialization is the previous original boundary determinant.
-/

import YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding
import YMGap.Continuum.BF4ExactSlabMixedAction
import YMGap.Continuum.CayleyParentInj

namespace YMGap.Continuum.BF4ExactSlabOffsetAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

def embeddedIds (P : Placement) : List Nat := (slabPhysicalFaceEdges P.source).map P.faceId
def keep (P : Placement) (id : Nat) : Bool := decide (id ∈ embeddedIds P)
def interiorIds (P : Placement) : List Nat := (slabPhysicalFaceEdges P.target).filter (keep P)
def exteriorIds (P : Placement) : List Nat := (slabPhysicalFaceEdges P.target).filter (fun id => !(keep P id))

theorem embeddedIds_physical (P : Placement) {id : Nat} (hi : id ∈ embeddedIds P) :
    id ∈ slabPhysicalFaceEdges P.target := by
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hi
  exact P.faceId_physical hs

theorem embeddedIds_nodup (P : Placement) : (embeddedIds P).Nodup :=
  nodup_map_of_injOn _ _ (CayleyParentInj.range_nodup _) (fun _ hi _ hj he => P.faceId_injective hi hj he)

theorem interiorIds_perm (P : Placement) : (interiorIds P).Perm (embeddedIds P) := by
  apply perm_of_nodup_mem_iff _ _ (List.filter_sublist.nodup (CayleyParentInj.range_nodup _)) (embeddedIds_nodup P)
  intro id
  constructor
  · intro hi
    exact of_decide_eq_true (List.mem_filter.mp hi).2
  · intro hi
    exact List.mem_filter.mpr ⟨embeddedIds_physical P hi, decide_eq_true hi⟩

theorem face_partition (P : Placement) :
    (interiorIds P ++ exteriorIds P).Perm (slabPhysicalFaceEdges P.target) :=
  List.filter_append_perm (keep P) _

def embeddedHeat (P : Placement) (w : Q') (K : Nat) : RatPoly :=
  polynomialProduct (fun id => faceHeatPolynomial w K P.target (P.faceId id)) (slabPhysicalFaceEdges P.source)

def exteriorHeat (P : Placement) (w : Q') (K : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K P.target) (exteriorIds P)

theorem interiorHeat_pin (P : Placement) (w : Q') (K : Nat) :
    RatPolyCoeffEqv (polynomialProduct (faceHeatPolynomial w K P.target) (interiorIds P)) (embeddedHeat P w K) := by
  have h := polynomialProduct_perm (faceHeatPolynomial w K P.target) (interiorIds_perm P)
  simpa only [embeddedHeat, embeddedIds, polynomialProduct, List.foldr_map] using h

theorem fullHeatProduct_dressing (P : Placement) (w : Q') (K : Nat) :
    RatPolyCoeffEqv (fullHeatProduct w K (P.half+P.padding))
      (polyMul (embeddedHeat P w K) (exteriorHeat P w K)) :=
  (polynomialProduct_perm (faceHeatPolynomial w K P.target) (face_partition P).symm).trans
    ((polynomialProduct_append _ _ _).trans ((interiorHeat_pin P w K).mul (RatPolyCoeffEqv.refl _)))

def fullMoment (P : Placement) (w : Q') (K : Nat) (p : RatPoly) : Q' :=
  numerator w (boundaryCompleteSlabLinks P.target).length P.target (slabPhysicalFaceEdges P.target) p K

def interiorMoment (P : Placement) (w : Q') (K : Nat) (p : RatPoly) : Q' :=
  numerator w (boundaryCompleteSlabLinks P.target).length P.target (interiorIds P) p K

theorem fullMoment_dressed (P : Placement) (w : Q') (K : Nat) (p : RatPoly) :
    fullMoment P w K p ≈ quaternionHaar (boundaryCompleteSlabLinks P.target).length
      (polyMul p (polyMul (embeddedHeat P w K) (exteriorHeat P w K))) :=
  haar_of_coeff_eqv _ ((fullHeatProduct_dressing P w K).mul_left p)

theorem interiorMoment_pin (P : Placement) (w : Q') (K : Nat) (p : RatPoly) :
    interiorMoment P w K p ≈ quaternionHaar (boundaryCompleteSlabLinks P.target).length
      (polyMul p (embeddedHeat P w K)) :=
  haar_of_coeff_eqv _ ((interiorHeat_pin P w K).mul_left p)

def boundaryNumerator (P : Placement) (w : Q') (K : Nat) (p : RatPoly) : Q' :=
  fullMoment P w K p * interiorMoment P w K polyOne +
    -(interiorMoment P w K p * fullMoment P w K polyOne)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

/-- The same arbitrary-keep determinant whose core estimates are already proved. -/
theorem boundary_mixedNumerator (P : Placement) (w : Q') (K : Nat) (p : RatPoly) :
    boundaryNumerator P w K p ≈ mixedNumerator w K P.target (keep P) p (slabPhysicalFaceEdges P.target) :=
  Q'.add_eqv_congr'
    (qmul (Q'.eqv_refl _) (unit_numerator w K P.target (interiorIds P)))
    (Q'.neg_eqv_congr _ _ (qmul (Q'.eqv_refl _) (unit_numerator w K P.target (slabPhysicalFaceEdges P.target))))

theorem boundary_mixedPartition (P : Placement) (w : Q') (K : Nat) :
    mixedPartition w K P.target (keep P) (slabPhysicalFaceEdges P.target) ≈
      fullMoment P w K polyOne * interiorMoment P w K polyOne :=
  qmul (Q'.eqv_symm (unit_numerator w K P.target _)) (Q'.eqv_symm (unit_numerator w K P.target _))

theorem centered_embeddedIds (half padding : Nat) :
    embeddedIds (centered half padding) = BF4ExactSlabBulkActionDressing.embeddedIds half padding := rfl

theorem centered_boundaryNumerator (half padding : Nat) (w : Q') (K : Nat) (p : RatPoly) :
    boundaryNumerator (centered half padding) w K p = BF4ExactSlabBulkBoundaryResponse.boundaryNumerator w half padding p K := rfl

end YMGap.Continuum.BF4ExactSlabOffsetAction

#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.embeddedIds
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.keep
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.interiorIds
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.exteriorIds
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.embeddedIds_physical
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.embeddedIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.interiorIds_perm
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.face_partition
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.embeddedHeat
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.exteriorHeat
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.interiorHeat_pin
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.fullHeatProduct_dressing
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.fullMoment
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.interiorMoment
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.fullMoment_dressed
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.interiorMoment_pin
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.boundaryNumerator
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.boundary_mixedNumerator
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.boundary_mixedPartition
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.centered_embeddedIds
#print axioms YMGap.Continuum.BF4ExactSlabOffsetAction.centered_boundaryNumerator
