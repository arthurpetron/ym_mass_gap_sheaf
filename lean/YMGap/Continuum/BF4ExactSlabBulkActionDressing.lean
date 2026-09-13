/-
# Exact exterior dressing of a bulk-embedded ORIGINAL slab action

The full source face list is embedded in the center of the larger slab.
The target face list is partitioned into that image and its complement.
No face is omitted, duplicated or replaced by an independent copy. The
original finite heat product factors coefficientwise into the translated
source action and the actual exterior-face heat product, on the SAME target
link variables. Exterior faces can share links with the embedded faces.

Every original polynomial numerator therefore equals a Haar moment dressed
by that exterior product. The undressed interior moment is also pinned to
the existing arbitrary-face-list numerator. This is the exact comparison
identity BEFORE a boundary-decay estimate, normalization, or padding limit.
No equality with the smaller-carrier Haar integral is assumed here.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
import YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit

namespace YMGap.Continuum.BF4ExactSlabBulkActionDressing

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
open YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

local infix:50 " ≈ " => Q'.eqv

private theorem range_nodup : ∀ n : Nat, (List.range n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
    rw [List.range_succ]
    refine List.nodup_append.mpr ⟨range_nodup n,
      List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro x hx y hy hxy
    have hy' := List.mem_singleton.mp hy
    subst y
    subst x
    exact Nat.lt_irrefl n (List.mem_range.mp hx)

def embeddedIds (half padding : Nat) : List Nat :=
  (slabPhysicalFaceEdges (centralExtent half)).map (bulkFaceId half padding 0)

def interiorIds (half padding : Nat) : List Nat :=
  (slabPhysicalFaceEdges (centralExtent (half+padding))).filter (fun id => decide (id ∈ embeddedIds half padding))

def exteriorIds (half padding : Nat) : List Nat :=
  (slabPhysicalFaceEdges (centralExtent (half+padding))).filter (fun id => !(decide (id ∈ embeddedIds half padding)))

theorem embeddedIds_physical {half padding id : Nat} (hi : id ∈ embeddedIds half padding) :
    id ∈ slabPhysicalFaceEdges (centralExtent (half+padding)) := by
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hi
  exact bulkFaceId_physical hs

theorem embeddedIds_nodup (half padding : Nat) : (embeddedIds half padding).Nodup :=
  nodup_map_of_injOn _ _ (range_nodup _) (fun i hi j hj h =>
    shiftFaceId_injective (central_room (by omega)) (central_room (by omega)) hi hj h)

theorem interiorIds_perm (half padding : Nat) : (interiorIds half padding).Perm (embeddedIds half padding) := by
  apply perm_of_nodup_mem_iff _ _ (List.filter_sublist.nodup (range_nodup _)) (embeddedIds_nodup half padding)
  intro id
  constructor
  · intro hi
    exact of_decide_eq_true (List.mem_filter.mp hi).2
  · intro hi
    exact List.mem_filter.mpr ⟨embeddedIds_physical hi, decide_eq_true hi⟩

theorem face_partition (half padding : Nat) :
    (interiorIds half padding ++ exteriorIds half padding).Perm (slabPhysicalFaceEdges (centralExtent (half+padding))) :=
  List.filter_append_perm (fun id => decide (id ∈ embeddedIds half padding)) _

/-- All source face factors, evaluated on their actual translated target links. -/
def embeddedHeat (w : Q') (K half padding : Nat) : RatPoly :=
  polynomialProduct (fun id => faceHeatPolynomial w K (centralExtent (half+padding)) (bulkFaceId half padding 0 id))
    (slabPhysicalFaceEdges (centralExtent half))

def exteriorHeat (w : Q') (K half padding : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K (centralExtent (half+padding))) (exteriorIds half padding)

theorem interiorHeat_pin (w : Q') (K half padding : Nat) :
    RatPolyCoeffEqv (polynomialProduct (faceHeatPolynomial w K (centralExtent (half+padding))) (interiorIds half padding))
      (embeddedHeat w K half padding) := by
  have h := polynomialProduct_perm (faceHeatPolynomial w K (centralExtent (half+padding))) (interiorIds_perm half padding)
  simpa only [embeddedHeat, embeddedIds, polynomialProduct, List.foldr_map] using h

/-- The complete ORIGINAL target action, with shared-link dependence retained. -/
theorem fullHeatProduct_dressing (w : Q') (K half padding : Nat) :
    RatPolyCoeffEqv (fullHeatProduct w K (half+padding))
      (polyMul (embeddedHeat w K half padding) (exteriorHeat w K half padding)) :=
  (polynomialProduct_perm (faceHeatPolynomial w K (centralExtent (half+padding))) (face_partition half padding).symm).trans
    ((polynomialProduct_append _ _ _).trans ((interiorHeat_pin w K half padding).mul (RatPolyCoeffEqv.refl _)))

def geometricHeat (w : Q') (K extent : Nat) (face : ClusterCount4DProgress.Z4Plaq) : RatPoly :=
  finitePolySum (fun spin => polySmul (coeffAt (heatKernelPacket K w) spin)
    (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin)) (List.range (K+1))

theorem embeddedHeat_geometric (w : Q') (K half padding : Nat) :
    embeddedHeat w K half padding =
      polynomialProduct (fun id => geometricHeat w K (centralExtent (half+padding))
        (shiftFace padding padding (slabPlaquetteAt (centralExtent half) id))) (slabPhysicalFaceEdges (centralExtent half)) := by
  apply polynomialProduct_congr
  intro id hi
  exact congrArg (geometricHeat w K (centralExtent (half+padding))) (bulkFaceId_pin (padding := padding) (lag := 0) hi)

def fullMoment (w : Q') (K half padding : Nat) (p : RatPoly) : Q' :=
  numerator w (boundaryCompleteSlabLinks (centralExtent (half+padding))).length (centralExtent (half+padding))
    (slabPhysicalFaceEdges (centralExtent (half+padding))) p K

def interiorMoment (w : Q') (K half padding : Nat) (p : RatPoly) : Q' :=
  quaternionHaar (boundaryCompleteSlabLinks (centralExtent (half+padding))).length (polyMul p (embeddedHeat w K half padding))

def dressedMoment (w : Q') (K half padding : Nat) (p : RatPoly) : Q' :=
  quaternionHaar (boundaryCompleteSlabLinks (centralExtent (half+padding))).length
    (polyMul p (polyMul (embeddedHeat w K half padding) (exteriorHeat w K half padding)))

theorem fullMoment_dressed (w : Q') (K half padding : Nat) (p : RatPoly) :
    fullMoment w K half padding p ≈ dressedMoment w K half padding p :=
  haar_of_coeff_eqv _ ((fullHeatProduct_dressing w K half padding).mul_left p)

theorem interiorMoment_numerator (w : Q') (K half padding : Nat) (p : RatPoly) :
    numerator w (boundaryCompleteSlabLinks (centralExtent (half+padding))).length (centralExtent (half+padding))
      (interiorIds half padding) p K ≈ interiorMoment w K half padding p :=
  haar_of_coeff_eqv _ ((interiorHeat_pin w K half padding).mul_left p)

theorem interiorMoment_congr (w : Q') (K half padding : Nat) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    interiorMoment w K half padding p ≈ interiorMoment w K half padding q :=
  haar_of_coeff_eqv _ (h.mul_right _)

/-- The exterior action is an insertion in the interior-weighted Haar moment;
this is not independence of the two factors. -/
theorem fullMoment_insertExterior (w : Q') (K half padding : Nat) (p : RatPoly) :
    fullMoment w K half padding p ≈
      interiorMoment w K half padding (polyMul p (exteriorHeat w K half padding)) :=
  Q'.eqv_trans _ _ _ (fullMoment_dressed w K half padding p)
    (haar_of_coeff_eqv _ (((RatPolyCoeffEqv.mul_comm _ _).mul_left p).trans
      (RatPolyCoeffEqv.mul_assoc _ _ _).symm))

theorem fullMoment_exterior (w : Q') (K half padding : Nat) :
    fullMoment w K half padding polyOne ≈ interiorMoment w K half padding (exteriorHeat w K half padding) :=
  Q'.eqv_trans _ _ _ (fullMoment_insertExterior w K half padding polyOne)
    (interiorMoment_congr w K half padding (RatPolyCoeffEqv.one_mul _))

end YMGap.Continuum.BF4ExactSlabBulkActionDressing

#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.embeddedIds
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.interiorIds
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.exteriorIds
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.embeddedIds_physical
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.embeddedIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.interiorIds_perm
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.face_partition
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.embeddedHeat
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.exteriorHeat
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.interiorHeat_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.fullHeatProduct_dressing
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.geometricHeat
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.embeddedHeat_geometric
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.fullMoment
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.interiorMoment
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.dressedMoment
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.fullMoment_dressed
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.interiorMoment_numerator
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.interiorMoment_congr
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.fullMoment_insertExterior
#print axioms YMGap.Continuum.BF4ExactSlabBulkActionDressing.fullMoment_exterior
