/-
# Site positivity for the ORIGINAL thermodynamic one-step form

Moving the reflection plane by half a lattice unit compensates exactly
for the one-step difference between the two lower insertions. The actual
even-slab reflected polynomial is therefore the existing mixed one-step
spacetime insertion. The proof uses the original ordered plaquette-word
reflection theorem, including temporal-link orientation, and retains all
signed sums/products in the original syntax.

The lower insertion is one-sided on the actual even carrier. Full-action
site positivity passes through the same cutoff normalization, then through
the proved even/odd comparison to the EXISTING thermodynamic formLimit.
No positive root is substituted for the geometric one-step observable.

This proves the dense one-step quadratic nonnegative at nome 1/1024 and
fixed spacing. Completed extension, root identification and the independent
range/time-zero problem remain separate; physical Hamiltonian, continuum,
other compact simple groups and the Clay target remain open.
-/

import YMGap.Continuum.BF4ExactSlabSpacetimeEvenComparison
import YMGap.Continuum.BF4ExactSlabSiteExpectation
import YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm

namespace YMGap.Continuum.BF4ExactSlabSiteOneStepForm

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
open YMGap.Continuum.BF4ExactSlabSiteExpectation
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm (formLimit)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOuterFactorLocality

theorem odd_lower_even_lower {radius : Nat} {p : Z4Plaq} (hp : plaquetteHalfSide radius p = .lower) :
    adjacentEvenPlaquetteSide radius p = .lower := by
  obtain ⟨⟨a,b,c,t⟩, plane⟩ := p
  cases plane <;> simp only [plaquetteHalfSide, spatialHalfSide, temporalHalfSide] at hp
  all_goals split at hp
  all_goals first | contradiction | skip
  all_goals try split at hp
  all_goals first | contradiction | skip
  all_goals simp only [adjacentEvenPlaquetteSide, adjacentEvenSpatialSide, adjacentEvenTemporalSide,
    adjacentEvenCenter, if_pos (show t < radius+1 by omega)]

/-- The original lower expression, including its boundary-touching generators. -/
theorem lower_oneSided {base : Nat} (margin : Nat) : ∀ e : PlaquetteExpression base,
    OneSided (base+margin) (evenEvaluate margin (fromLower e))
  | .unit => BlockLocal.one _ _
  | .character id hi spin => by
      have hside := odd_lower_even_lower
        (shiftFace_lower (space := margin) (Nat.le_refl margin) (mem_centralLowerFaceIds.mp hi).2)
      intro term ht b hb hn
      apply ((face_scalar_local (adjacentEvenExtent (base+margin))
        (shiftFace margin margin (slabPlaquetteAt (centralExtent base) id))).character spin) term ht b hb
      intro hm
      apply hn
      intro hu
      have hbad := adjacentEven_upper_link_incident_face_upper hu hm
      rw [hside] at hbad
      cases hbad
  | .add e f => (lower_oneSided margin e).add (lower_oneSided margin f)
  | .mul e f => (lower_oneSided margin e).mul (lower_oneSided margin f)
  | .smul c e => (lower_oneSided margin e).smul c

/-- A half-unit plane change compensates for one original lattice-time step. -/
theorem one_step_face (base margin : Nat) (face : Z4Plaq)
    (hf : plaquetteTimeAdmissible (centralExtent base) face) :
    timeReflectPlaquette (adjacentEvenExtent (base+1+margin))
      (shiftFace margin margin (shiftFace 1 1 face)) =
      shiftFace margin margin (timeReflectPlaquette (centralExtent (base+1)) (shiftFace 1 0 face)) := by
  obtain ⟨⟨a,b,c,t⟩, plane⟩ := face
  cases plane <;> simp only [timeReflectPlaquette, shiftFace, shiftVertex,
    adjacentEvenExtent, centralExtent, plaquetteTimeAdmissible, Prod.mk.injEq,
    true_and, and_true, Nat.add_zero] at hf ⊢ <;> omega

theorem one_step_reflection {base : Nat} (margin : Nat) : ∀ e : PlaquetteExpression base,
    ReflectionImage (adjacentEvenExtent (base+1+margin))
      (evenEvaluate margin (fromLower (bulkAtTime 1 ⟨0, by decide⟩ e)))
      (evenEvaluate margin (fromUpper (bulkAtTime 1 ⟨1, by decide⟩ e)))
  | .unit => ReflectionImage.one _
  | .character id hi spin => by
      have hp := (mem_centralLowerFaceIds.mp hi).1
      simp only [bulkAtTime, fromUpper, reflect, fromLower, evenEvaluate,
        bulkFaceId_pin hp, Nat.sub_zero, Nat.sub_self]
      have hm := face_mem (odd_even_room (base+1+margin))
        (shiftedFace_physical (slabPlaquetteAt_mem (bulkFaceId_physical (padding := 1) (lag := 0) hp)) margin)
      rw [bulkFaceId_pin hp, Nat.sub_zero] at hm
      have hr := plaquette_character_reflection hm spin
      rw [one_step_face base margin _ ((mem_boundaryCompleteSlabPlaquettes _ _).mp (slabPlaquetteAt_mem hp)).2] at hr
      exact hr
  | .add e f => (one_step_reflection margin e).add (one_step_reflection margin f)
  | .mul e f => (one_step_reflection margin e).mul (one_step_reflection margin f)
  | .smul c e => (one_step_reflection margin e).smul c

/-- This is the existing mixed insertion consumed by time_inner_bulk. -/
def oneStepExpression {base : Nat} (e : PlaquetteExpression base) : SpacetimeExpression (base+1) :=
  reflectedProduct (bulkAtTime 1 ⟨1, by decide⟩ e) (bulkAtTime 1 ⟨0, by decide⟩ e)

theorem insertion_pin {base : Nat} (margin : Nat) (e : PlaquetteExpression base) :
    PaddedPolynomialCoeffEqv (blockCount (base+1+margin))
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent (base+1+margin))
        (evenEvaluate margin (fromLower (bulkAtTime 1 ⟨0, by decide⟩ e))))
        (evenEvaluate margin (fromLower (bulkAtTime 1 ⟨0, by decide⟩ e))))
      (evenEvaluate margin (oneStepExpression e)) :=
  PaddedPolynomialCoeffEqv.mul (one_step_reflection margin e) (.refl _ _)

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  {base : Nat} (margin : Nat) (e : PlaquetteExpression base)

local notation "radius" => base+1+margin
local notation "extent" => adjacentEvenExtent radius
local notation "faces" => slabPhysicalFaceEdges extent
local notation "lowerInsertion" => evenEvaluate margin (fromLower (bulkAtTime 1 ⟨0, by decide⟩ e))
local notation "siteInsertion" => polyMul (reflectCorrectedSlabPolynomial extent lowerInsertion) lowerInsertion

/-- The original full heat product is retained when integrating the polynomial pin. -/
theorem site_expectation_pin :
    Equiv (expectation w hw0 hw1 hsmall hd extent faces (fun _ hi => hi) siteInsertion)
      (evenMean w hw0 hw1 hsmall hd (oneStepExpression e) margin) := by
  have hn := Equiv_of_ofQ'_limit_close
    (numerator_converges w hw0 hw1 (blockCount radius) extent faces siteInsertion)
    (numerator_converges w hw0 hw1 (blockCount radius) extent faces (evenEvaluate margin (oneStepExpression e)))
    (fun epsilon he => ⟨0, fun K _ => eqv_close
      ((PaddedPolynomialCoeffEqv.mul (insertion_pin margin e)
        (.refl _ (polynomialProduct (faceHeatPolynomial w K extent) faces))).haar
        (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _)
          (evenSquareBound margin (fromLower (bulkAtTime 1 ⟨0, by decide⟩ e))).support) (heatProduct_supported w K _ _))
        (supported_polyMul (evenSquareBound margin (oneStepExpression e)).support (heatProduct_supported w K _ _)))
      epsilon he⟩)
  exact Pivot2.mul_congr_left hn

/-- Full-action site positivity for the literal one-step insertion at fixed volume. -/
theorem even_one_step_nonnegative :
    leEv (ofQ' 0) (evenMean w hw0 hw1 hsmall hd (oneStepExpression e) margin) :=
  leEv_trans (site_nonnegative w hw0 hw1 hsmall hd radius lowerInsertion
    (lower_oneSided margin _) (evenSquareBound margin (fromLower (bulkAtTime 1 ⟨0, by decide⟩ e))).support)
    (leEv_of_equiv (site_expectation_pin w hw0 hw1 hsmall hd margin e))

/-- Positivity of the EXISTING original thermodynamic one-step quadratic. -/
theorem one_step_form_nonnegative {base : Nat} (e : PlaquetteExpression base) :
    leEv (ofQ' 0) (formLimit (bulkAtTime 1 ⟨1, by decide⟩ e) (bulkAtTime 1 ⟨0, by decide⟩ e)) :=
  leEv_of_convergesTo_le (convergesTo_const _) (evenSequence_converges (oneStepExpression e))
    (fun margin => even_one_step_nonnegative nome nome_pos nome_lt_one existingNome_guards.1 existingNome_guards.2 margin e)

end YMGap.Continuum.BF4ExactSlabSiteOneStepForm

#print axioms YMGap.Continuum.BF4ExactSlabSiteOneStepForm.odd_lower_even_lower
#print axioms YMGap.Continuum.BF4ExactSlabSiteOneStepForm.lower_oneSided
#print axioms YMGap.Continuum.BF4ExactSlabSiteOneStepForm.one_step_face
#print axioms YMGap.Continuum.BF4ExactSlabSiteOneStepForm.one_step_reflection
#print axioms YMGap.Continuum.BF4ExactSlabSiteOneStepForm.oneStepExpression
#print axioms YMGap.Continuum.BF4ExactSlabSiteOneStepForm.insertion_pin
#print axioms YMGap.Continuum.BF4ExactSlabSiteOneStepForm.site_expectation_pin
#print axioms YMGap.Continuum.BF4ExactSlabSiteOneStepForm.even_one_step_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabSiteOneStepForm.one_step_form_nonnegative
