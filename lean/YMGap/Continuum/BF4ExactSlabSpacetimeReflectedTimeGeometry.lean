/-
# Literal reflected time geometry of the ORIGINAL spacetime expressions

Reflection reverses the temporal offset of an embedded slab. Two successive
placements with the same total time offset produce the same expression.
These exact identities pin the already-defined lower bulk translation and
its upper reflected image. The final mixed products differ by one common
time shift; no state invariance or spectral assumption is used here.
-/

import YMGap.Continuum.BF4ExactSlabOffsetSpacetimeExpression

namespace YMGap.Continuum.BF4ExactSlabSpacetimeReflectedTimeGeometry

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding
open YMGap.Continuum.BF4ExactSlabOffsetSpacetimeExpression (embed)
open YMGap.Continuum.BF4ExactSlabSpacetimeExpression
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression)
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

private theorem congrTwo {A B C : Type} (f : A → B → C) {a a' : A} {b b' : B}
    (ha : a=a') (hb : b=b') : f a b = f a' b' := by cases ha; cases hb; rfl

def reflectedPlacement (P : Placement) : Placement :=
  ⟨P.half, P.padding, P.padding+P.padding-P.time, Nat.sub_le _ _⟩

theorem reflect_embed (P : Placement) : ∀ e : SpacetimeExpression P.half,
    reflect (embed P e) = embed (reflectedPlacement P) (reflect e)
  | .unit => rfl
  | .character face hf spin => by
      simp only [reflect, embed, reflectedPlacement,
        shiftFace_reflection P.time_le ((mem_boundaryCompleteSlabPlaquettes _ _).mp hf).2]
  | .add e f => congrTwo SpacetimeExpression.add (reflect_embed P e) (reflect_embed P f)
  | .mul e f => congrTwo SpacetimeExpression.mul (reflect_embed P e) (reflect_embed P f)
  | .smul c e => congrArg (SpacetimeExpression.smul c) (reflect_embed P e)

def bulkPlacement (base padding : Nat) (lag : Fin (padding+1)) : Placement :=
  ⟨base, padding, padding-lag.val, by omega⟩

theorem fromLower_bulkAtTime {base : Nat} (padding : Nat) (lag : Fin (padding+1)) :
    ∀ e : PlaquetteExpression base,
    fromLower (bulkAtTime padding lag e) = embed (bulkPlacement base padding lag) (fromLower e)
  | .unit => rfl
  | .character id hi spin => by
      simp only [bulkAtTime, fromLower, embed, bulkPlacement, bulkFaceId_pin (mem_centralLowerFaceIds.mp hi).1]
  | .add e f => congrTwo SpacetimeExpression.add (fromLower_bulkAtTime padding lag e) (fromLower_bulkAtTime padding lag f)
  | .mul e f => congrTwo SpacetimeExpression.mul (fromLower_bulkAtTime padding lag e) (fromLower_bulkAtTime padding lag f)
  | .smul c e => congrArg (SpacetimeExpression.smul c) (fromLower_bulkAtTime padding lag e)

theorem fromUpper_bulkAtTime {base : Nat} (padding : Nat) (lag : Fin (padding+1)) (e : PlaquetteExpression base) :
    fromUpper (bulkAtTime padding lag e) = embed (reflectedPlacement (bulkPlacement base padding lag)) (fromUpper e) := by
  unfold fromUpper
  rw [fromLower_bulkAtTime padding lag e]
  exact reflect_embed (bulkPlacement base padding lag) (fromLower e)

/-- The data-bearing expressions, including their actual generators, are equal. -/
theorem embed_comp_time (base padding outer time time' offset offset' : Nat)
    (ht : time ≤ padding+padding) (ht' : time' ≤ padding+padding)
    (ho : offset ≤ outer+outer) (ho' : offset' ≤ outer+outer) (he : time+offset=time'+offset') :
    ∀ e : SpacetimeExpression base,
    embed ⟨base+padding, outer, offset, ho⟩ (embed ⟨base, padding, time, ht⟩ e) =
      embed ⟨base+padding, outer, offset', ho'⟩ (embed ⟨base, padding, time', ht'⟩ e)
  | .unit => rfl
  | .character face hf spin => by simp only [embed, shiftFace_comp, he]
  | .add e f => congrTwo SpacetimeExpression.add
      (embed_comp_time base padding outer time time' offset offset' ht ht' ho ho' he e)
      (embed_comp_time base padding outer time time' offset offset' ht ht' ho ho' he f)
  | .mul e f => congrTwo SpacetimeExpression.mul
      (embed_comp_time base padding outer time time' offset offset' ht ht' ho ho' he e)
      (embed_comp_time base padding outer time time' offset offset' ht ht' ho ho' he f)
  | .smul c e => congrArg (SpacetimeExpression.smul c)
      (embed_comp_time base padding outer time time' offset offset' ht ht' ho ho' he e)

def outerLeft (base : Nat) : Placement := ⟨base+1, 1, 0, by decide⟩
def outerRight (base : Nat) : Placement := ⟨base+1, 1, 1, by decide⟩

/-- One reflected step on the first factor equals one step on the second,
after a common whole-expression shift by one time unit. -/
theorem reflectedProduct_balance {base : Nat} (e f : PlaquetteExpression base) :
    embed (outerLeft base) (reflectedProduct (bulkAtTime 1 ⟨1, by decide⟩ e) (bulkAtTime 1 ⟨0, by decide⟩ f)) =
      embed (outerRight base) (reflectedProduct (bulkAtTime 1 ⟨0, by decide⟩ e) (bulkAtTime 1 ⟨1, by decide⟩ f)) := by
  change SpacetimeExpression.mul (embed (outerLeft base) (fromUpper (bulkAtTime 1 ⟨1, by decide⟩ e)))
    (embed (outerLeft base) (fromLower (bulkAtTime 1 ⟨0, by decide⟩ f))) =
      SpacetimeExpression.mul (embed (outerRight base) (fromUpper (bulkAtTime 1 ⟨0, by decide⟩ e)))
        (embed (outerRight base) (fromLower (bulkAtTime 1 ⟨1, by decide⟩ f)))
  apply congrTwo SpacetimeExpression.mul
  · exact (congrArg (embed (outerLeft base)) (fromUpper_bulkAtTime 1 ⟨1, by decide⟩ e)).trans
      ((embed_comp_time base 1 1 2 1 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (fromUpper e)).trans
        (congrArg (embed (outerRight base)) (fromUpper_bulkAtTime 1 ⟨0, by decide⟩ e)).symm)
  · exact (congrArg (embed (outerLeft base)) (fromLower_bulkAtTime 1 ⟨0, by decide⟩ f)).trans
      ((embed_comp_time base 1 1 1 0 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (fromLower f)).trans
        (congrArg (embed (outerRight base)) (fromLower_bulkAtTime 1 ⟨1, by decide⟩ f)).symm)

end YMGap.Continuum.BF4ExactSlabSpacetimeReflectedTimeGeometry

#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeReflectedTimeGeometry.reflectedPlacement
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeReflectedTimeGeometry.reflect_embed
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeReflectedTimeGeometry.bulkPlacement
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeReflectedTimeGeometry.fromLower_bulkAtTime
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeReflectedTimeGeometry.fromUpper_bulkAtTime
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeReflectedTimeGeometry.embed_comp_time
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeReflectedTimeGeometry.outerLeft
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeReflectedTimeGeometry.outerRight
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeReflectedTimeGeometry.reflectedProduct_balance
