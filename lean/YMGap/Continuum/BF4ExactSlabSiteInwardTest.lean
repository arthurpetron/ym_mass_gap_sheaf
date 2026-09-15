/-
# An inward dual test at the adjacent site reflection plane

An arbitrary original lower expression is moved one step toward the site
plane. Spatial faces may lie ON the fixed slice; temporal faces still end
there. Thus the test is one-sided, including boundary-touching generators.
Its site reflection is exactly the original upper insertion at zero lag.
The mixed site product is therefore the ORIGINAL zero-lag reflected product,
with all signs and the original square cap retained.

This supplies the geometric test for a transfer-relative Cauchy--Schwarz
estimate. It does not yet prove that estimate, range density, time-zero
continuity, a physical Hamiltonian or the continuum/all-group Clay target.
-/

import YMGap.Continuum.BF4ExactSlabSiteOneStepForm

namespace YMGap.Continuum.BF4ExactSlabSiteInwardTest

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay (shiftedFace_physical)
open YMGap.Continuum.BF4ExactSlabCoordinateInclusion
open YMGap.Continuum.BF4ExactSlabSpacetimeExpression
open YMGap.Continuum.BF4ExactSlabSpacetimeEvenComparison
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression)
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
open YMGap.Continuum.BF4ExactSlabSiteConditionalSquare
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOuterFactorLocality

/-- Space padding one, time shift two: one step inward relative to bulk lag zero. -/
def inward {base : Nat} : PlaquetteExpression base → SpacetimeExpression (base+1)
  | .unit => .unit
  | .character id hi spin => .character (shiftFace 1 2 (slabPlaquetteAt (centralExtent base) id))
      (shiftFace_mem (by unfold centralExtent; omega) (by unfold centralExtent; omega)
        (slabPlaquetteAt_mem (mem_centralLowerFaceIds.mp hi).1)) spin
  | .add e f => .add (inward e) (inward f)
  | .mul e f => .mul (inward e) (inward f)
  | .smul c e => .smul c (inward e)

theorem inward_bound {base : Nat} : ∀ e : PlaquetteExpression base,
    bound (inward e) = BF4ExactSlabPlaquetteUniformSquareBound.bound e
  | .unit => rfl
  | .character _ _ _ => rfl
  | .add e f => by simp only [inward, bound, BF4ExactSlabPlaquetteUniformSquareBound.bound, inward_bound e, inward_bound f]
  | .mul e f => by simp only [inward, bound, BF4ExactSlabPlaquetteUniformSquareBound.bound, inward_bound e, inward_bound f]
  | .smul c e => by simp only [inward, bound, BF4ExactSlabPlaquetteUniformSquareBound.bound, inward_bound e]

/-- The bound is independent of padding, volume and both heat cutoffs. -/
def inwardSquareBound {base : Nat} (margin : Nat) (e : PlaquetteExpression base) :
    SquareBound (blockCount (base+1+margin)) (evenEvaluate margin (inward e))
      (BF4ExactSlabPlaquetteUniformSquareBound.bound e) := by
  rw [← inward_bound e]
  exact evenSquareBound margin (inward e)

theorem inward_face_not_upper {base : Nat} (margin : Nat) {face : Z4Plaq}
    (hf : plaquetteHalfSide base face = .lower) :
    adjacentEvenPlaquetteSide (base+1+margin) (shiftFace margin margin (shiftFace 1 2 face)) ≠ .upper := by
  obtain ⟨⟨a,b,c,t⟩, plane⟩ := face
  cases plane <;> simp only [plaquetteHalfSide, spatialHalfSide, temporalHalfSide] at hf
  all_goals split at hf
  all_goals first | contradiction | skip
  all_goals try split at hf
  all_goals first | contradiction | skip
  all_goals simp only [adjacentEvenPlaquetteSide, adjacentEvenSpatialSide, adjacentEvenTemporalSide,
    adjacentEvenCenter, shiftFace, shiftVertex]
  all_goals split
  all_goals first | (intro h; cases h) | skip
  all_goals first | omega | skip
  all_goals split
  all_goals first | (intro h; cases h <;> omega) | omega

/-- Fixed-slice spatial links are permitted; no upper link enters the test. -/
theorem inward_oneSided {base : Nat} (margin : Nat) : ∀ e : PlaquetteExpression base,
    OneSided (base+1+margin) (evenEvaluate margin (inward e))
  | .unit => BlockLocal.one _ _
  | .character id hi spin => by
      have hside := inward_face_not_upper margin (mem_centralLowerFaceIds.mp hi).2
      intro term ht b hb hn
      apply ((face_scalar_local (adjacentEvenExtent (base+1+margin))
        (shiftFace margin margin (shiftFace 1 2 (slabPlaquetteAt (centralExtent base) id)))).character spin) term ht b hb
      intro hm
      apply hn
      intro hu
      exact hside (adjacentEven_upper_link_incident_face_upper hu hm)
  | .add e f => (inward_oneSided margin e).add (inward_oneSided margin f)
  | .mul e f => (inward_oneSided margin e).mul (inward_oneSided margin f)
  | .smul c e => (inward_oneSided margin e).smul c

theorem inward_face_reflection (base margin : Nat) (face : Z4Plaq)
    (hf : plaquetteTimeAdmissible (centralExtent base) face) :
    timeReflectPlaquette (adjacentEvenExtent (base+1+margin))
      (shiftFace margin margin (shiftFace 1 2 face)) =
      shiftFace margin margin (timeReflectPlaquette (centralExtent (base+1)) (shiftFace 1 1 face)) := by
  obtain ⟨⟨a,b,c,t⟩, plane⟩ := face
  cases plane <;> simp only [timeReflectPlaquette, shiftFace, shiftVertex,
    adjacentEvenExtent, centralExtent, plaquetteTimeAdmissible, Prod.mk.injEq,
    true_and, and_true] at hf ⊢ <;> omega

/-- The site-reflected inward test is the ORIGINAL upper insertion at zero lag. -/
theorem inward_reflection {base : Nat} (margin : Nat) : ∀ e : PlaquetteExpression base,
    ReflectionImage (adjacentEvenExtent (base+1+margin))
      (evenEvaluate margin (inward e))
      (evenEvaluate margin (fromUpper (bulkAtTime 1 ⟨0, by decide⟩ e)))
  | .unit => ReflectionImage.one _
  | .character id hi spin => by
      have hp := (mem_centralLowerFaceIds.mp hi).1
      simp only [inward, bulkAtTime, fromUpper, reflect, fromLower, evenEvaluate,
        bulkFaceId_pin hp, Nat.sub_zero]
      have hm := face_mem (odd_even_room (base+1+margin)) (shiftedFace_physical
        (shiftFace_mem (space := 1) (time := 2) (target := centralExtent (base+1))
          (by unfold centralExtent; omega) (by unfold centralExtent; omega) (slabPlaquetteAt_mem hp)) margin)
      have hr := plaquette_character_reflection hm spin
      rw [inward_face_reflection base margin _ ((mem_boundaryCompleteSlabPlaquettes _ _).mp (slabPlaquetteAt_mem hp)).2] at hr
      exact hr
  | .add e f => (inward_reflection margin e).add (inward_reflection margin f)
  | .mul e f => (inward_reflection margin e).mul (inward_reflection margin f)
  | .smul c e => (inward_reflection margin e).smul c

/-- No action change: the mixed site product is the existing zero-lag product. -/
theorem mixed_insertion_pin {base : Nat} (margin : Nat) (e f : PlaquetteExpression base) :
    PaddedPolynomialCoeffEqv (blockCount (base+1+margin))
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent (base+1+margin))
        (evenEvaluate margin (inward f)))
        (evenEvaluate margin (fromLower (bulkAtTime 1 ⟨0, by decide⟩ e))))
      (evenEvaluate margin (reflectedProduct (bulkAtTime 1 ⟨0, by decide⟩ f) (bulkAtTime 1 ⟨0, by decide⟩ e))) :=
  PaddedPolynomialCoeffEqv.mul (inward_reflection margin f) (.refl _ _)

end YMGap.Continuum.BF4ExactSlabSiteInwardTest

#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTest.inward
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTest.inward_bound
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTest.inwardSquareBound
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTest.inward_face_not_upper
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTest.inward_oneSided
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTest.inward_face_reflection
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTest.inward_reflection
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTest.mixed_insertion_pin
