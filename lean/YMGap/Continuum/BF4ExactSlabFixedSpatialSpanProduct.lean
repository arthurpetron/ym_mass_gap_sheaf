/-
# Literal products of the original signed spatial-face presentations

The product pairs every signed term from the first presentation with every
term from the second, multiplies their rational coefficients, and appends
their ordered schedules. Both the chronological source polynomial and its
literal original-slab placement are coefficient-equivalent to the product of
the two original polynomials. Physical support and a common time window are
preserved; physical time, chart encoding and base inclusion commute with the
construction.

This is multiplication of dense observable presentations. It is not general
Wilson-observable coverage, a bounded multiplier on the reflected OS norm,
a radical-ideal theorem, or an algebra structure on the completion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpanProduct

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters (sweptCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (physicalTime)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (inclusion)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

/-- Literal ordered cross product; no term is discarded or merged. -/
def spanProduct (xs ys : Span) : Span :=
  xs.flatMap (fun x => ys.map (fun y => (x.1*y.1, x.2++y.2)))

theorem spanProduct_physical {width : Nat} {xs ys : Span}
    (hx : Physical width xs) (hy : Physical width ys) :
    Physical width (spanProduct xs ys) := by
  intro z hz e he f hf
  obtain ⟨x, hxmem, hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨y, hymem, rfl⟩ := List.mem_map.mp hz
  rcases List.mem_append.mp he with he | he
  · exact hx x hxmem e he f hf
  · exact hy y hymem e he f hf

theorem spanProduct_within {H : Nat} {xs ys : Span}
    (hx : Within H xs) (hy : Within H ys) : Within H (spanProduct xs ys) := by
  intro z hz e he
  obtain ⟨x, hxmem, hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨y, hymem, rfl⟩ := List.mem_map.mp hz
  rcases List.mem_append.mp he with he | he
  · exact hx x hxmem e he
  · exact hy y hymem e he

private theorem finiteSum_append {A : Type} (f : A → RatPoly) :
    (xs ys : List A) → finitePolySum f (xs++ys) =
      polyAdd (finitePolySum f xs) (finitePolySum f ys)
  | [], _ => rfl
  | x::xs, ys => by
      change polyAdd (f x) (finitePolySum f (xs++ys)) = _
      rw [finiteSum_append f xs ys]
      exact (List.append_assoc _ _ _).symm

private theorem scaled_product (a b : Q') (p q : RatPoly) :
    RatPolyCoeffEqv (polyMul (polySmul a p) (polySmul b q))
      (polySmul (a*b) (polyMul p q)) :=
  ((RatPolyCoeffEqv.polyMul_smul_left a p (polySmul b q)).trans
    ((RatPolyCoeffEqv.polyMul_smul_right b p q).smul a)).trans
      (RatPolyCoeffEqv.smul_assoc a b (polyMul p q))

private theorem evaluation_row (F : List (Nat × List FaceFactor) → RatPoly)
    (hF : ∀ fs gs, RatPolyCoeffEqv (F (fs++gs)) (polyMul (F fs) (F gs)))
    (x : Q' × List (Nat × List FaceFactor)) : (ys : Span) →
    RatPolyCoeffEqv
      (finitePolySum (fun z => polySmul z.1 (F z.2))
        (ys.map (fun y => (x.1*y.1, x.2++y.2))))
      (polyMul (polySmul x.1 (F x.2))
        (finitePolySum (fun y => polySmul y.1 (F y.2)) ys))
  | [] => (RatPolyCoeffEqv.mul_zero_right _).symm
  | y::ys => by
      change RatPolyCoeffEqv
        (polyAdd (polySmul (x.1*y.1) (F (x.2++y.2))) _)
        (polyMul _ (polyAdd (polySmul y.1 (F y.2)) _))
      exact ((((hF x.2 y.2).smul (x.1*y.1)).trans
        (scaled_product x.1 y.1 (F x.2) (F y.2)).symm).add
          (evaluation_row F hF x ys)).trans
            (RatPolyCoeffEqv.mul_add_right _ _ _).symm

private theorem evaluation_product (F : List (Nat × List FaceFactor) → RatPoly)
    (hF : ∀ fs gs, RatPolyCoeffEqv (F (fs++gs)) (polyMul (F fs) (F gs))) :
    (xs ys : Span) → RatPolyCoeffEqv
      (finitePolySum (fun z => polySmul z.1 (F z.2)) (spanProduct xs ys))
      (polyMul (finitePolySum (fun x => polySmul x.1 (F x.2)) xs)
        (finitePolySum (fun y => polySmul y.1 (F y.2)) ys))
  | [], _ => RatPolyCoeffEqv.refl _
  | x::xs, ys => by
      change RatPolyCoeffEqv
        (finitePolySum (fun z => polySmul z.1 (F z.2))
          (ys.map (fun y => (x.1*y.1, x.2++y.2)) ++ spanProduct xs ys))
        (polyMul (polyAdd (polySmul x.1 (F x.2)) _) _)
      rw [finiteSum_append, polyMul_add_left_exact]
      exact (evaluation_row F hF x ys).add (evaluation_product F hF xs ys)

/-- Every signed source cross term is retained, before Haar integration. -/
theorem sourceSpan_spanProduct (width : Nat) (xs ys : Span) :
    RatPolyCoeffEqv (sourceSpan width (spanProduct xs ys))
      (polyMul (sourceSpan width xs) (sourceSpan width ys)) :=
  evaluation_product (windowProbe width) (fun _ _ => polynomialProduct_append _ _ _) xs ys

/-- The same product on the literal original slab, not merely on swept source
coordinates. No physical guard is needed for this polynomial identity. -/
theorem placedSpan_spanProduct (extent start : Nat) (xs ys : Span) :
    RatPolyCoeffEqv (placedSpan extent start (spanProduct xs ys))
      (polyMul (placedSpan extent start xs) (placedSpan extent start ys)) := by
  apply evaluation_product (fun fs => sweptProduct extent 0 (placeWindowProbes start fs)) _ xs ys
  intro fs gs
  simp only [placeWindowProbes, List.flatMap_append]
  exact polynomialProduct_append (factor (sweptCharacter extent 0)) _ _

/-- A concrete product in the existing physical presentation carrier. -/
def mulSpan {width : Nat} (x y : PhysicalSpan width) : PhysicalSpan width :=
  ⟨spanProduct x.val y.val, spanProduct_physical x.property y.property⟩

theorem mulSpan_val {width : Nat} (x y : PhysicalSpan width) :
    (mulSpan x y).val = spanProduct x.val y.val := rfl

/-- Encoding a common distance chart preserves the literal product. -/
theorem encodeChart_spanProduct (H : Nat) (xs ys : Span) :
    encodeChart H (spanProduct xs ys) =
      spanProduct (encodeChart H xs) (encodeChart H ys) := by
  simp only [encodeChart, encodeSchedule, spanProduct, List.map_flatMap,
    List.flatMap_map, List.map_map, List.map_append, Function.comp_def]

theorem advanceSpan_spanProduct (n : Nat) (xs ys : Span) :
    advanceSpan n (spanProduct xs ys) =
      spanProduct (advanceSpan n xs) (advanceSpan n ys) := by
  simp only [advanceSpan, spanProduct, List.map_flatMap, List.flatMap_map,
    List.map_map, Function.comp_def, advanceSchedule_append]

/-- Physical advancement acts on the SAME multiplied schedules. -/
theorem physicalTime_mulSpan {width : Nat} (n : Nat) (x y : PhysicalSpan width) :
    physicalTime n (mulSpan x y) = mulSpan (physicalTime n x) (physicalTime n y) :=
  Subtype.ext (advanceSpan_spanProduct n x.val y.val)

/-- Base enlargement changes only support evidence and keeps the product. -/
theorem inclusion_mulSpan {base larger : Nat} (h : base ≤ larger)
    (x y : PhysicalSpan base) :
    inclusion h (mulSpan x y) = mulSpan (inclusion h x) (inclusion h y) :=
  Subtype.ext rfl

#print axioms spanProduct
#print axioms spanProduct_physical
#print axioms spanProduct_within
#print axioms sourceSpan_spanProduct
#print axioms placedSpan_spanProduct
#print axioms mulSpan
#print axioms mulSpan_val
#print axioms encodeChart_spanProduct
#print axioms advanceSpan_spanProduct
#print axioms physicalTime_mulSpan
#print axioms inclusion_mulSpan

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpanProduct
