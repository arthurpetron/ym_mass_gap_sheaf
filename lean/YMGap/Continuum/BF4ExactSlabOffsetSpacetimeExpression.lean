/-
# Off-center placement of the ORIGINAL spacetime expression

Every generator is moved to its actual physical face. Sums, products and
signed scales are retained. The square cap is unchanged, and the actual
link locality uses the original base box shifted in space and time.

Growing both slabs around this placement identifies its literal polynomial
with the original source polynomial under the off-center Haar embedding.
These are observable identities, not invariance of an interacting measure.
-/

import YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding
import YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier
import YMGap.Continuum.BF4ExactSlabSpacetimeExpression

namespace YMGap.Continuum.BF4ExactSlabOffsetSpacetimeExpression

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding
open YMGap.Continuum.BF4ExactSlabSpacetimeExpression
open YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay (shiftedCharacter shiftedFace_physical)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

def embed (P : Placement) : SpacetimeExpression P.half → SpacetimeExpression (P.half+P.padding)
  | .unit => .unit
  | .character face hf spin => .character (shiftFace P.padding P.time face)
      (shiftFace_mem P.space_room P.time_room hf) spin
  | .add e f => .add (embed P e) (embed P f)
  | .mul e f => .mul (embed P e) (embed P f)
  | .smul c e => .smul c (embed P e)

theorem bound_embed (P : Placement) : ∀ e : SpacetimeExpression P.half, bound (embed P e) = bound e
  | .unit => rfl
  | .character _ _ _ => rfl
  | .add e f => by simp only [embed, bound, bound_embed P e, bound_embed P f]
  | .mul e f => by simp only [embed, bound, bound_embed P e, bound_embed P f]
  | .smul c e => by simp only [embed, bound, bound_embed P e]

/-- Grow the interior while retaining the SAME outer placement. -/
def grow (P : Placement) (margin : Nat) : Placement :=
  ⟨P.half+margin, P.padding, P.time, P.time_le⟩

theorem shifted_face_links {base : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (space time : Nat)
    (link : Z4Link) (hl : link ∈ edgesOf (shiftFace space time face)) :
    link ∈ (boxLinks (centralExtent base+1)).map (shiftLink space time) := by
  rw [edgesOf_shiftFace] at hl
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hl
  exact List.mem_map.mpr ⟨source,
    boundary_mem_boxLinks ((mem_boundaryCompleteSlabPlaquettes _ _).mp hf).1 hs, rfl⟩

/-- Locality uses the ORIGINAL base box, not the padded base presentation. -/
theorem evaluate_embed_local (P : Placement) (margin : Nat) : ∀ e : SpacetimeExpression P.half,
    LinkLocal (centralExtent ((P.half+P.padding)+margin))
      ((boxLinks (centralExtent P.half+1)).map (shiftLink (P.padding+margin) (P.time+margin)))
      (evaluate margin (embed P e))
  | .unit => BlockLocal.one _ _
  | .character face hf spin => by
      change LinkLocal _ _ (characterPolynomial (correctedSlabPlaquettePolynomial _
        (shiftFace margin margin (shiftFace P.padding P.time face))).scalar spin)
      rw [shiftFace_comp]
      exact LinkLocal.mono ((face_scalar_local _ _).character spin)
        (shifted_face_links hf (P.padding+margin) (P.time+margin))
  | .add e f => (evaluate_embed_local P margin e).add (evaluate_embed_local P margin f)
  | .mul e f => (evaluate_embed_local P margin e).mul (evaluate_embed_local P margin f)
  | .smul c e => (evaluate_embed_local P margin e).smul c

/-- Actual source and target holonomies agree through the SAME block map. -/
theorem image_prefix (P : Placement) (margin : Nat) : ∀ e : SpacetimeExpression P.half,
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (grow P margin).target).length
      ((grow P margin).embedding.polynomial (evaluate margin e)) (evaluate margin (embed P e))
  | .unit => (grow P margin).embedding.polynomial_one_prefix
  | .character face hf spin => by
      have h := (grow P margin).character_pin (shiftedFace_physical hf margin) spin
      simpa only [evaluate, embed, shiftedCharacter, grow, Placement.source, Placement.target,
        shiftFace_comp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  | .add e f => by
      change QuaternionPrefixPolynomialEqv _ ((grow P margin).embedding.polynomial
        (polyAdd (evaluate margin e) (evaluate margin f))) _
      rw [BlockEmbedding.polynomial_add]
      exact (image_prefix P margin e).append (image_prefix P margin f)
  | .mul e f => by
      change QuaternionPrefixPolynomialEqv _ ((grow P margin).embedding.polynomial
        (polyMul (evaluate margin e) (evaluate margin f))) _
      rw [BlockEmbedding.polynomial_mul]
      exact (image_prefix P margin e).mul (image_prefix P margin f)
  | .smul c e => by
      change QuaternionPrefixPolynomialEqv _ ((grow P margin).embedding.polynomial (polySmul c (evaluate margin e))) _
      rw [BlockEmbedding.polynomial_smul]
      exact (image_prefix P margin e).smul c

end YMGap.Continuum.BF4ExactSlabOffsetSpacetimeExpression

#print axioms YMGap.Continuum.BF4ExactSlabOffsetSpacetimeExpression.embed
#print axioms YMGap.Continuum.BF4ExactSlabOffsetSpacetimeExpression.bound_embed
#print axioms YMGap.Continuum.BF4ExactSlabOffsetSpacetimeExpression.grow
#print axioms YMGap.Continuum.BF4ExactSlabOffsetSpacetimeExpression.shifted_face_links
#print axioms YMGap.Continuum.BF4ExactSlabOffsetSpacetimeExpression.evaluate_embed_local
#print axioms YMGap.Continuum.BF4ExactSlabOffsetSpacetimeExpression.image_prefix
