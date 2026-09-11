/-
# Weighted edge-touching double-cube activity and the factor-512 fence

The literal outward trace network of the two face-disjoint elementary cubes
meeting along one edge has normalized Haar value `1/256`.  Selecting the
fundamental heat-kernel coefficient on all twelve faces therefore gives the
honest scalar sector

    (coeffW coupling 1)^12 * (1/256).

This file encodes the same twelve geometric faces as a genuine cutoff-one
box-3 support.  The current production carrier multiplies its face monomial
by the *dimension* of the invariant space at each touched link.  Twenty-two
links are bivalent and the shared link is four-valent, so that carrier is

    (coeffW coupling 1)^12 * 2.

Consequently the honest local Haar sector is the production scalar times
`1/512`, and multiplying the honest sector by `512` recovers the exact
cutoff-one physical term.  This is a diagnostic fence for the eventual
channel-resolved production kernel, not a proposal to divide every surface
activity by one universal scalar: the elementary cube needs `1/16`, and the
square of that Haar normalization is `1/256`, not `1/512`.

The numerical support is obtained from the geometric faces through the
production box decoder.  No bounded labelling family, Boolean assignment
carrier, trajectory, or length family is materialized here.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeLiteralTraceNetwork
import YMGap.Continuum.SU2QuaternionElementaryCubeWeightedActivityNormalization
import YMGap.Continuum.Z4AxisCubeSixFaceActivity
import YMGap.Continuum.Z4CanonicalPolymerTransport
import YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
import YMGap.Continuum.Z4SingleFourIncidenceActivity

namespace YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeWeightedActivityNormalization

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeLiteralTraceNetwork
open YMGap.Continuum.SU2QuaternionElementaryCubeWeightedActivityNormalization
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.Z4AxisCubeSixFaceActivity
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenRadiusZeroClosedGeometryFence
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4SingleFourIncidenceActivity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The literal double cube as a production box-3 support -/

/-- Production numerical face identifiers for the literal double-cube
surface, decoded in box 3.  The slab identifiers used by the trace audit are
not reused as box identifiers. -/
def radiusZeroEdgeTouchingDoubleCubeBoxSupport : List Nat :=
  geometricSupportIds 3 radiusZeroEdgeTouchingDoubleCubeFaces

/-- Every literal face fits in box 3.  This is the finite geometric input to
the production decoder. -/
theorem radiusZeroEdgeTouchingDoubleCubeFaces_subset_box_three :
    ∀ plaquette, plaquette ∈ radiusZeroEdgeTouchingDoubleCubeFaces →
      plaquette ∈ boxPlaquettes 3 := by
  intro plaquette hplaquette
  rw [mem_boxPlaquettes]
  simp only [radiusZeroEdgeTouchingDoubleCubeFaces, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem radiusZeroEdgeTouchingDoubleCubeBoxSupport_mem_cutoffOneFaceSupports :
    radiusZeroEdgeTouchingDoubleCubeBoxSupport ∈
      cutoffOneFaceSupports 3 := by
  unfold radiusZeroEdgeTouchingDoubleCubeBoxSupport
  exact geometricSupportIds_mem_cutoffOneFaceSupports 3
    radiusZeroEdgeTouchingDoubleCubeFaces

/-- Decoding the production box support recovers exactly the twelve literal
plaquettes, independently of their numerical order. -/
theorem radiusZeroEdgeTouchingDoubleCubeBoxSupport_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 3 radiusZeroEdgeTouchingDoubleCubeBoxSupport)
      radiusZeroEdgeTouchingDoubleCubeFaces := by
  unfold radiusZeroEdgeTouchingDoubleCubeBoxSupport
  exact geometricSupportIds_sameSupport
    radiusZeroEdgeTouchingDoubleCubeFaces_subset_box_three

/-- The production support contains twelve distinct numerical faces.  The
proof is structural: it compares two duplicate-free supports and never
evaluates the decoder output. -/
theorem radiusZeroEdgeTouchingDoubleCubeBoxSupport_length :
    radiusZeroEdgeTouchingDoubleCubeBoxSupport.length = 12 := by
  have hlength := sameSupport_length_eq_of_nodup
    radiusZeroEdgeTouchingDoubleCubeBoxSupport_sameSupport
    (geometricPolymer_nodup
      radiusZeroEdgeTouchingDoubleCubeBoxSupport_mem_cutoffOneFaceSupports)
    radiusZeroEdgeTouchingDoubleCubeFaces_nodup
  rw [geometricPolymer_length_eq_support_length] at hlength
  exact hlength.trans radiusZeroEdgeTouchingDoubleCubeFaces_length

private theorem doubleCubeBox_touched_mem_literal
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 3
      (componentLabel radiusZeroEdgeTouchingDoubleCubeBoxSupport)) :
    link ∈ radiusZeroEdgeTouchingDoubleCubeTouchedLinks := by
  unfold radiusZeroEdgeTouchingDoubleCubeTouchedLinks
  exact touchedSurface_of_sameSupport
    radiusZeroEdgeTouchingDoubleCubeBoxSupport_mem_cutoffOneFaceSupports
    radiusZeroEdgeTouchingDoubleCubeBoxSupport_sameSupport hlink

theorem radiusZeroEdgeTouchingDoubleCubeSharedLink_mem_box_touched :
    radiusZeroEdgeTouchingDoubleCubeSharedLink ∈
      touchedPhysicalLinks 3
        (componentLabel radiusZeroEdgeTouchingDoubleCubeBoxSupport) := by
  apply (mem_touchedPhysicalLinks_iff_geometric
    radiusZeroEdgeTouchingDoubleCubeBoxSupport_mem_cutoffOneFaceSupports
    radiusZeroEdgeTouchingDoubleCubeSharedLink).2
  have hsurface : radiusZeroEdgeTouchingDoubleCubeSharedLink ∈
      geometricTouchedLinks radiusZeroEdgeTouchingDoubleCubeFaces := by
    exact radiusZeroEdgeTouchingDoubleCubeSharedLink_mem_touched
  obtain ⟨plaquette, hplaquette, hedge⟩ :=
    mem_geometricTouchedLinks.mp hsurface
  exact mem_geometricTouchedLinks.mpr
    ⟨plaquette,
      radiusZeroEdgeTouchingDoubleCubeBoxSupport_sameSupport.2
        plaquette hplaquette,
      hedge⟩

private theorem doubleCubeBox_incidence_length_eq_literal
    (link : Z4Link) :
    (geometricIncidentPlaquettes
      (geometricPolymer 3 radiusZeroEdgeTouchingDoubleCubeBoxSupport)
      link).length =
    (geometricIncidentPlaquettes
      radiusZeroEdgeTouchingDoubleCubeFaces link).length := by
  have hsame := geometricIncidentPlaquettes_sameSupport
    radiusZeroEdgeTouchingDoubleCubeBoxSupport_sameSupport link
  have hleft := geometricIncidentPlaquettes_nodup
    radiusZeroEdgeTouchingDoubleCubeBoxSupport_mem_cutoffOneFaceSupports link
  have hright :
      (geometricIncidentPlaquettes
        radiusZeroEdgeTouchingDoubleCubeFaces link).Nodup := by
    unfold geometricIncidentPlaquettes
    exact List.filter_sublist.nodup
      radiusZeroEdgeTouchingDoubleCubeFaces_nodup
  exact sameSupport_length_eq_of_nodup hsame hleft hright

theorem radiusZeroEdgeTouchingDoubleCubeBoxSupport_shared_incidence_four :
    (geometricIncidentPlaquettes
      (geometricPolymer 3 radiusZeroEdgeTouchingDoubleCubeBoxSupport)
      radiusZeroEdgeTouchingDoubleCubeSharedLink).length = 4 :=
  (doubleCubeBox_incidence_length_eq_literal
    radiusZeroEdgeTouchingDoubleCubeSharedLink).trans
      radiusZeroEdgeTouchingDoubleCubeSharedLink_incidence_four

theorem radiusZeroEdgeTouchingDoubleCubeBoxSupport_other_incidence_two
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 3
      (componentLabel radiusZeroEdgeTouchingDoubleCubeBoxSupport))
    (hne : link ≠ radiusZeroEdgeTouchingDoubleCubeSharedLink) :
    (geometricIncidentPlaquettes
      (geometricPolymer 3 radiusZeroEdgeTouchingDoubleCubeBoxSupport)
      link).length = 2 :=
  (doubleCubeBox_incidence_length_eq_literal link).trans
    (radiusZeroEdgeTouchingDoubleCube_other_incidence_two
      (doubleCubeBox_touched_mem_literal hlink) hne)

/-! ## 2. Exact value of the current production scalar -/

/-- The current production activity sees the four-valent invariant-space
dimension `2`; all other touched-link dimensions are `1`. -/
theorem radiusZeroEdgeTouchingDoubleCube_canonicalSurfaceActivity_eqv
    (coupling : Q') :
    canonicalSurfaceActivity coupling 3
        radiusZeroEdgeTouchingDoubleCubeBoxSupport ≈
      (coeffW coupling 1) ^ 12 * 2 := by
  have h := canonicalSurfaceActivity_eqv_two_mul_pow_length_of_single_four
    coupling radiusZeroEdgeTouchingDoubleCubeSharedLink
    radiusZeroEdgeTouchingDoubleCubeBoxSupport_mem_cutoffOneFaceSupports
    radiusZeroEdgeTouchingDoubleCubeSharedLink_mem_box_touched
    radiusZeroEdgeTouchingDoubleCubeBoxSupport_shared_incidence_four
    radiusZeroEdgeTouchingDoubleCubeBoxSupport_other_incidence_two
  rw [radiusZeroEdgeTouchingDoubleCubeBoxSupport_length] at h
  exact h

/-- The cutoff-one physical-term API is definitionally the same localized
production scalar. -/
theorem radiusZeroEdgeTouchingDoubleCube_canonicalSurfaceActivity_eqv_parametricKPhysicalTerm_one
    (coupling : Q') :
    canonicalSurfaceActivity coupling 3
        radiusZeroEdgeTouchingDoubleCubeBoxSupport ≈
      parametricKPhysicalTerm coupling 1 3
        (componentLabel radiusZeroEdgeTouchingDoubleCubeBoxSupport) := by
  unfold canonicalSurfaceActivity
  exact Q'.eqv_symm
    (parametricKPhysicalTerm_one_eqv_localized coupling 3
      (componentLabel radiusZeroEdgeTouchingDoubleCubeBoxSupport))

theorem radiusZeroEdgeTouchingDoubleCube_parametricKPhysicalTerm_one_eqv
    (coupling : Q') :
    parametricKPhysicalTerm coupling 1 3
        (componentLabel radiusZeroEdgeTouchingDoubleCubeBoxSupport) ≈
      (coeffW coupling 1) ^ 12 * 2 :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (radiusZeroEdgeTouchingDoubleCube_canonicalSurfaceActivity_eqv_parametricKPhysicalTerm_one
        coupling))
    (radiusZeroEdgeTouchingDoubleCube_canonicalSurfaceActivity_eqv coupling)

/-! ## 3. The honestly weighted literal Haar sector -/

/-- The normalized Haar factor of the literal twelve-trace network. -/
def edgeTouchingDoubleCubeHaarNormalization : Q' :=
  Q'.mkPos 1 256 (by decide)

/-- The correction relating the current dimension-counting surrogate to the
honest local Haar value on this support. -/
def edgeTouchingDoubleCubeSurrogateCorrection : Q' :=
  Q'.mkPos 1 512 (by decide)

/-- Twelve selected fundamental heat-kernel coefficients multiplying the
literal orientation-faithful double-cube trace product. -/
def radiusZeroEdgeTouchingDoubleCubeWeightedOutwardTraceExpansionProduct
    (coupling : Q') : ComplexRatPoly :=
  complexRatPolyMul
    (complexRatPolyRealScalar ((coeffW coupling 1) ^ 12))
    radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct

/-- The honest scalar value of the weighted double-cube sector. -/
def radiusZeroEdgeTouchingDoubleCubeHonestHaarActivity
    (coupling : Q') : Q' :=
  (coeffW coupling 1) ^ 12 * edgeTouchingDoubleCubeHaarNormalization

/-- The current production scalar with its support-specific correction. -/
def radiusZeroEdgeTouchingDoubleCubeCorrectedSurrogateActivity
    (coupling : Q') : Q' :=
  canonicalSurfaceActivity coupling 3
      radiusZeroEdgeTouchingDoubleCubeBoxSupport *
    edgeTouchingDoubleCubeSurrogateCorrection

/-- **Exact honestly weighted double-cube integral.** -/
theorem finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeWeighted_exact
    (coupling : Q') :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroEdgeTouchingDoubleCubeWeightedOutwardTraceExpansionProduct
          coupling))
      (radiusZeroEdgeTouchingDoubleCubeHonestHaarActivity coupling, 0) := by
  unfold radiusZeroEdgeTouchingDoubleCubeWeightedOutwardTraceExpansionProduct
    radiusZeroEdgeTouchingDoubleCubeHonestHaarActivity
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_realScalar_mul
      (adjacentEvenActiveLinks 0).length ((coeffW coupling 1) ^ 12)
      radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct) ?_
  refine rationalComplexEqv_trans
    (rationalComplexMul_congr_right (((coeffW coupling 1) ^ 12), 0)
      finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeOutwardTraceExpansionProduct_exact) ?_
  unfold edgeTouchingDoubleCubeHaarNormalization
  exact rationalComplexMul_real_real_eqv
    ((coeffW coupling 1) ^ 12) (Q'.mkPos 1 256 (by decide))

/-! ## 4. Exact factor-512 production fences -/

/-- The honest scalar is exactly the current production scalar times
`1/512`. -/
theorem radiusZeroEdgeTouchingDoubleCube_honest_eqv_correctedSurrogate
    (coupling : Q') :
    radiusZeroEdgeTouchingDoubleCubeHonestHaarActivity coupling ≈
      radiusZeroEdgeTouchingDoubleCubeCorrectedSurrogateActivity coupling := by
  unfold radiusZeroEdgeTouchingDoubleCubeHonestHaarActivity
    radiusZeroEdgeTouchingDoubleCubeCorrectedSurrogateActivity
    edgeTouchingDoubleCubeHaarNormalization
    edgeTouchingDoubleCubeSurrogateCorrection
  refine Q'.eqv_trans _
    ((coeffW coupling 1) ^ 12 *
      (2 * Q'.mkPos 1 512 (by decide))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left ((coeffW coupling 1) ^ 12) _ _ (by decide)
  · refine Q'.eqv_trans _
      (((coeffW coupling 1) ^ 12 * 2) *
        Q'.mkPos 1 512 (by decide)) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv ((coeffW coupling 1) ^ 12) 2
          (Q'.mkPos 1 512 (by decide)))) ?_
    exact Q'.mul_eqv_congr_right _ _ (Q'.mkPos 1 512 (by decide))
      (Q'.eqv_symm
        (radiusZeroEdgeTouchingDoubleCube_canonicalSurfaceActivity_eqv
          coupling))

/-- Multiplication by `512` recovers the exact current production activity. -/
theorem radiusZeroEdgeTouchingDoubleCube_honest_mul_fiveHundredTwelve_eqv_surrogate
    (coupling : Q') :
    radiusZeroEdgeTouchingDoubleCubeHonestHaarActivity coupling *
        (512 : Q') ≈
      canonicalSurfaceActivity coupling 3
        radiusZeroEdgeTouchingDoubleCubeBoxSupport := by
  unfold radiusZeroEdgeTouchingDoubleCubeHonestHaarActivity
    edgeTouchingDoubleCubeHaarNormalization
  refine Q'.eqv_trans _
    ((coeffW coupling 1) ^ 12 *
      (Q'.mkPos 1 256 (by decide) * (512 : Q'))) _
    (Q'.mul_assoc_eqv ((coeffW coupling 1) ^ 12)
      (Q'.mkPos 1 256 (by decide)) (512 : Q')) ?_
  refine Q'.eqv_trans _ ((coeffW coupling 1) ^ 12 * 2) _
    (Q'.mul_eqv_congr_left ((coeffW coupling 1) ^ 12) _ _ (by decide)) ?_
  exact Q'.eqv_symm
    (radiusZeroEdgeTouchingDoubleCube_canonicalSurfaceActivity_eqv coupling)

/-- The same factor-512 fence stated directly against the cutoff-one
physical term used by the production partition. -/
theorem radiusZeroEdgeTouchingDoubleCube_honest_mul_fiveHundredTwelve_eqv_parametricKPhysicalTerm_one
    (coupling : Q') :
    radiusZeroEdgeTouchingDoubleCubeHonestHaarActivity coupling *
        (512 : Q') ≈
      parametricKPhysicalTerm coupling 1 3
        (componentLabel radiusZeroEdgeTouchingDoubleCubeBoxSupport) :=
  Q'.eqv_trans _ _ _
    (radiusZeroEdgeTouchingDoubleCube_honest_mul_fiveHundredTwelve_eqv_surrogate
      coupling)
    (radiusZeroEdgeTouchingDoubleCube_canonicalSurfaceActivity_eqv_parametricKPhysicalTerm_one
      coupling)

/-- Equivalently, applying the support-specific correction to the actual
cutoff-one physical term yields the honest scalar sector. -/
theorem radiusZeroEdgeTouchingDoubleCube_parametricKPhysicalTerm_one_mul_correction_eqv_honest
    (coupling : Q') :
    parametricKPhysicalTerm coupling 1 3
        (componentLabel radiusZeroEdgeTouchingDoubleCubeBoxSupport) *
        edgeTouchingDoubleCubeSurrogateCorrection ≈
      radiusZeroEdgeTouchingDoubleCubeHonestHaarActivity coupling := by
  refine Q'.eqv_trans _
    (canonicalSurfaceActivity coupling 3
        radiusZeroEdgeTouchingDoubleCubeBoxSupport *
      edgeTouchingDoubleCubeSurrogateCorrection) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _
      edgeTouchingDoubleCubeSurrogateCorrection
      (Q'.eqv_symm
        (radiusZeroEdgeTouchingDoubleCube_canonicalSurfaceActivity_eqv_parametricKPhysicalTerm_one
          coupling))
  · exact Q'.eqv_symm
      (radiusZeroEdgeTouchingDoubleCube_honest_eqv_correctedSurrogate coupling)

/-- The weighted literal Haar value is therefore also exactly the corrected
production scalar, as a rational-complex value. -/
theorem finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeWeighted_eq_correctedSurrogate
    (coupling : Q') :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroEdgeTouchingDoubleCubeWeightedOutwardTraceExpansionProduct
          coupling))
      (radiusZeroEdgeTouchingDoubleCubeCorrectedSurrogateActivity coupling,
        0) :=
  rationalComplexEqv_trans
    (finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeWeighted_exact
      coupling)
    ⟨radiusZeroEdgeTouchingDoubleCube_honest_eqv_correctedSurrogate coupling,
      Q'.eqv_refl 0⟩

/-- Direct end-to-end fence from the literal weighted trace network to the
actual cutoff-one physical term with its exact support-specific correction. -/
theorem finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeWeighted_eq_parametricKPhysicalTerm_one_mul_correction
    (coupling : Q') :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroEdgeTouchingDoubleCubeWeightedOutwardTraceExpansionProduct
          coupling))
      (parametricKPhysicalTerm coupling 1 3
          (componentLabel radiusZeroEdgeTouchingDoubleCubeBoxSupport) *
        edgeTouchingDoubleCubeSurrogateCorrection,
        0) :=
  rationalComplexEqv_trans
    (finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeWeighted_exact
      coupling)
    ⟨Q'.eqv_symm
        (radiusZeroEdgeTouchingDoubleCube_parametricKPhysicalTerm_one_mul_correction_eqv_honest
          coupling),
      Q'.eqv_refl 0⟩

/-! ## 5. Why this is not a universal scalar patch -/

/-- The product of the two scalar elementary-cube Haar normalizations is the
double-cube Haar normalization `1/256`.  This scalar identity does not assert
independence of the two networks, which share one Haar variable. -/
theorem elementaryCubeHaarNormalization_sq_eqv_doubleCubeHaarNormalization :
    elementaryCubeHaarNormalization * elementaryCubeHaarNormalization ≈
      edgeTouchingDoubleCubeHaarNormalization := by
  decide

/-- But that product is not the correction `1/512` required by the current
dimension-counting production scalar at a four-valent link. -/
theorem elementaryCubeHaarNormalization_sq_not_eqv_doubleCubeSurrogateCorrection :
    ¬ (elementaryCubeHaarNormalization * elementaryCubeHaarNormalization ≈
      edgeTouchingDoubleCubeSurrogateCorrection) := by
  decide

#print axioms radiusZeroEdgeTouchingDoubleCubeFaces_subset_box_three
#print axioms radiusZeroEdgeTouchingDoubleCubeBoxSupport_sameSupport
#print axioms radiusZeroEdgeTouchingDoubleCubeBoxSupport_length
#print axioms radiusZeroEdgeTouchingDoubleCubeBoxSupport_shared_incidence_four
#print axioms radiusZeroEdgeTouchingDoubleCubeBoxSupport_other_incidence_two
#print axioms radiusZeroEdgeTouchingDoubleCube_canonicalSurfaceActivity_eqv
#print axioms radiusZeroEdgeTouchingDoubleCube_parametricKPhysicalTerm_one_eqv
#print axioms finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeWeighted_exact
#print axioms radiusZeroEdgeTouchingDoubleCube_honest_eqv_correctedSurrogate
#print axioms radiusZeroEdgeTouchingDoubleCube_honest_mul_fiveHundredTwelve_eqv_parametricKPhysicalTerm_one
#print axioms radiusZeroEdgeTouchingDoubleCube_parametricKPhysicalTerm_one_mul_correction_eqv_honest
#print axioms finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeWeighted_eq_parametricKPhysicalTerm_one_mul_correction
#print axioms elementaryCubeHaarNormalization_sq_not_eqv_doubleCubeSurrogateCorrection

end YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeWeightedActivityNormalization
