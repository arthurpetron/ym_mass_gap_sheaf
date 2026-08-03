/-
# Exact corrected-slab Haar-network carrier

The nonnegative multiplicity-product spin foam records only the ranks of the
link invariant spaces.  It is not the exact dual Wilson/heat-kernel
coefficient: the invariant projectors must still be contracted, and that
contraction can have signs.

This file defines the missing finite object directly.  Every link of the
boundary-complete slab receives its own polynomial `SU(2)` quaternion.  The
four oriented link variables around each plaquette are multiplied in their
noncommutative Hamilton order, the requested all-spin character is applied,
and the resulting polynomial is integrated by exact normalized product Haar
over every slab link.

At extent one the carrier is the literal 72-face/116-link corrected slab.
The reflected kernel below is therefore an exact finite dual Haar-network
kernel, not a product of local multiplicities.  No positivity is asserted:
signed recoupling coefficients are retained.  Comparison with the contracted
five-holonomy compact reference remains a separate theorem.

## Axiom gate

Finite lists, exact rational polynomial algebra, and normalized quaternion
Haar moments only.  No `Classical.*`, `native_decide`, `sorry`, custom axiom,
choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PositivePolynomialCauchyMertens
import YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

namespace YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalClassCoordinateCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal slab link carrier -/

/-- One independent polynomial quaternion for every link of the
boundary-complete slab.  The identity fallback is outside the physical link
list and is never used by a physical plaquette. -/
def correctedSlabLinkPolynomial
    (extent : Nat) (link : Z4Link) : PolyQuaternion :=
  if link ∈ boundaryCompleteSlabLinks extent then
    PolyQuaternion.coordinateVariable
      ((boundaryCompleteSlabLinks extent).idxOf link)
  else PolyQuaternion.one

theorem correctedSlabLinkPolynomial_of_mem
    {extent : Nat} {link : Z4Link}
    (hlink : link ∈ boundaryCompleteSlabLinks extent) :
    correctedSlabLinkPolynomial extent link =
      PolyQuaternion.coordinateVariable
        ((boundaryCompleteSlabLinks extent).idxOf link) := by
  unfold correctedSlabLinkPolynomial
  rw [if_pos hlink]

theorem correctedSlabLinkPolynomial_of_not_mem
    {extent : Nat} {link : Z4Link}
    (hlink : link ∉ boundaryCompleteSlabLinks extent) :
    correctedSlabLinkPolynomial extent link =
      PolyQuaternion.one := by
  unfold correctedSlabLinkPolynomial
  rw [if_neg hlink]

/-- Every oriented incidence of a physical slab plaquette names one of the
four links in `edgesOf`. -/
theorem orientedPlaquetteBoundary_link_mem_edgesOf
    {face : Z4Plaq} {entry : OrientedBF4Link}
    (hentry : entry ∈ orientedPlaquetteBoundary face) :
    entry.link ∈ edgesOf face := by
  unfold orientedPlaquetteBoundary at hentry
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry
  rcases hentry with hentry | hentry | hentry | hentry <;>
    subst entry <;> simp [edgesOf]

/-- Hence the identity fallback in `correctedSlabLinkPolynomial` is never
used by a physical plaquette incidence. -/
theorem orientedPlaquetteBoundary_link_mem_slab
    {extent : Nat} {face : Z4Plaq} {entry : OrientedBF4Link}
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent)
    (hentry : entry ∈ orientedPlaquetteBoundary face) :
    entry.link ∈ boundaryCompleteSlabLinks extent := by
  apply (mem_boundaryCompleteSlabLinks_iff extent entry.link).mpr
  exact ⟨face, hface,
    orientedPlaquetteBoundary_link_mem_edgesOf hentry⟩

/-- Apply the orientation of one plaquette incidence to its literal slab
link variable. -/
def orientedCorrectedSlabLinkPolynomial
    (extent : Nat) (entry : OrientedBF4Link) : PolyQuaternion :=
  if entry.reverse then
    PolyQuaternion.conj
      (correctedSlabLinkPolynomial extent entry.link)
  else correctedSlabLinkPolynomial extent entry.link

/-- Exact noncommutative plaquette holonomy on the full slab link carrier. -/
def correctedSlabPlaquettePolynomial
    (extent : Nat) (face : Z4Plaq) : PolyQuaternion :=
  (orientedPlaquetteBoundary face).foldl
    (fun total entry =>
      PolyQuaternion.mul total
        (orientedCorrectedSlabLinkPolynomial extent entry))
    PolyQuaternion.one

/-! ## 2. All-spin Haar-network coefficient -/

/-- Character factor of one labelled corrected-slab plaquette. -/
def correctedSlabPlaquetteSpinFactor
    (extent : Nat) (faceLabel : EdgeLabelling)
    (face : Z4Plaq) : RatPoly :=
  characterPolynomial
    (correctedSlabPlaquettePolynomial extent face).scalar
    (faceLabel
      ((boundaryCompleteSlabPlaquettes extent).idxOf face))

/-- Product of all 72 plaquette characters before any link Haar integral at
extent one, and its exact extent-dependent analogue generally. -/
def exactCorrectedSlabSpinNetworkIntegrand
    (extent : Nat) (faceLabel : EdgeLabelling) : RatPoly :=
  (boundaryCompleteSlabPlaquettes extent).foldr
    (fun face total =>
      polyMul
        (correctedSlabPlaquetteSpinFactor extent faceLabel face)
        total)
    polyOne

/-- Exact normalized product-Haar coefficient of one complete face
labelling.  Unlike the multiplicity product, this retains all signed
intertwiner/vertex contractions. -/
def exactCorrectedSlabHaarCoefficient
    (extent : Nat) (faceLabel : EdgeLabelling) : Q' :=
  quaternionHaar
    (boundaryCompleteSlabLinks extent).length
    (exactCorrectedSlabSpinNetworkIntegrand extent faceLabel)

/-- The extent-one carrier is the actual 72-face corrected slab. -/
theorem correctedSlabPlaquettes_extent_one_length :
    (boundaryCompleteSlabPlaquettes 1).length = 72 := by
  decide

/-- The extent-one Haar integral uses all 116 physical slab links. -/
theorem correctedSlabLinks_extent_one_length :
    (boundaryCompleteSlabLinks 1).length = 116 := by
  decide

private theorem vacuum_integrand_on
    (extent : Nat) :
    ∀ faces : List Z4Plaq,
      faces.foldr
          (fun face total =>
            polyMul
              (correctedSlabPlaquetteSpinFactor
                extent zeroEdgeLabelling face)
              total)
          polyOne = polyOne
  | [] => rfl
  | face :: rest => by
      simp only [List.foldr]
      unfold correctedSlabPlaquetteSpinFactor
      change polyMul polyOne
        (rest.foldr
          (fun face total =>
            polyMul
              (correctedSlabPlaquetteSpinFactor
                extent zeroEdgeLabelling face)
              total)
          polyOne) = polyOne
      rw [vacuum_integrand_on extent rest]
      rfl

/-- The all-vacuum face labelling is the literal constant network. -/
theorem exactCorrectedSlabSpinNetworkIntegrand_vacuum
    (extent : Nat) :
    exactCorrectedSlabSpinNetworkIntegrand
        extent zeroEdgeLabelling = polyOne := by
  unfold exactCorrectedSlabSpinNetworkIntegrand
  exact vacuum_integrand_on extent
    (boundaryCompleteSlabPlaquettes extent)

private theorem quaternionHaar_one (blocks : Nat) :
    quaternionHaar blocks polyOne ≈ 1 := by
  change
    (1 : Q') * quaternionHaarMono blocks [] + 0 ≈ 1
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_trans _
      (1 * quaternionHaarMono blocks []) _
      (QPoly.q_add_zero_eqv _)
      (Q'.one_mul_eqv _))
    (quaternionHaarMono_one blocks)

/-- Normalized Haar gives the exact vacuum network coefficient one. -/
theorem exactCorrectedSlabHaarCoefficient_vacuum
    (extent : Nat) :
    exactCorrectedSlabHaarCoefficient
        extent zeroEdgeLabelling ≈ 1 := by
  unfold exactCorrectedSlabHaarCoefficient
  rw [exactCorrectedSlabSpinNetworkIntegrand_vacuum]
  exact quaternionHaar_one _

/-! ## 3. Exact lower-boundary gauge fixing to five holonomies -/

/-- Literal faces selected by the reflection lower-half partition at the
extent-one BF4 slab. -/
def exactCorrectedSlabLowerSpatialFaces : List Z4Plaq :=
  (centralLowerFaceIds 0).map (slabPlaquetteAt 1)

/-- Literal reflected upper spatial faces of the same slab. -/
def exactCorrectedSlabUpperSpatialFaces : List Z4Plaq :=
  (centralUpperFaceIds 0).map (slabPlaquetteAt 1)

/-- Literal cross-plane plaquettes.  At extent one these are precisely the
24 time-oriented faces based on the reflection plane. -/
def exactCorrectedSlabFixedFaces : List Z4Plaq :=
  (centralFixedFaceIds 0).map (slabPlaquetteAt 1)

/-- The geometric lower/interface/upper ordering used for conditional
integration.  It is a permutation, rather than an asserted reordering by
definitional equality, of the original corrected-slab enumeration. -/
def exactCorrectedSlabPartitionedFaces : List Z4Plaq :=
  exactCorrectedSlabLowerSpatialFaces ++
    exactCorrectedSlabFixedFaces ++
      exactCorrectedSlabUpperSpatialFaces

/-- The independently defined BF4 source boundary is exactly the lower part
of the corrected-slab reflection partition, including list order. -/
theorem exactCorrectedSlabLowerSpatialFaces_eq_source :
    exactCorrectedSlabLowerSpatialFaces =
      bf4SourceSpatialFaces := by
  decide

/-- The upper part is the literal time reflection of the source spatial
boundary. -/
theorem exactCorrectedSlabUpperSpatialFaces_eq_reflected_source :
    exactCorrectedSlabUpperSpatialFaces =
      bf4SourceSpatialFaces.map (timeReflectPlaquette 1) := by
  decide

/-- The remaining fixed-plane portion also has 24 plaquettes. -/
theorem exactCorrectedSlabFixedFaces_length :
    (centralFixedFaceIds 0).length = 24 := by
  decide

theorem exactCorrectedSlabLowerSpatialFaces_length :
    exactCorrectedSlabLowerSpatialFaces.length = 24 := by
  rw [exactCorrectedSlabLowerSpatialFaces_eq_source]
  exact bf4SourceSpatialFaces_length

theorem exactCorrectedSlabUpperSpatialFaces_length :
    exactCorrectedSlabUpperSpatialFaces.length = 24 := by
  rw [exactCorrectedSlabUpperSpatialFaces_eq_reflected_source,
    List.length_map]
  exact bf4SourceSpatialFaces_length

theorem exactCorrectedSlabLiteralFixedFaces_length :
    exactCorrectedSlabFixedFaces.length = 24 := by
  unfold exactCorrectedSlabFixedFaces
  rw [List.length_map]
  exact exactCorrectedSlabFixedFaces_length

/-- The three literal 24-face pieces cover every corrected-slab plaquette
exactly once.  This is the finite geometric Fubini carrier for the remaining
interior gluing theorem. -/
private theorem slabPhysicalFaces_extent_one_map :
    (slabPhysicalFaceEdges 1).map (slabPlaquetteAt 1) =
      boundaryCompleteSlabPlaquettes 1 := by
  decide

theorem exactCorrectedSlabPartitionedFaces_perm :
    exactCorrectedSlabPartitionedFaces.Perm
      (boundaryCompleteSlabPlaquettes 1) := by
  unfold exactCorrectedSlabPartitionedFaces
    exactCorrectedSlabLowerSpatialFaces
    exactCorrectedSlabFixedFaces
    exactCorrectedSlabUpperSpatialFaces
  rw [← List.map_append, ← List.map_append]
  have h := (centralSlabFaceIdParts_perm 0).map (slabPlaquetteAt 1)
  change
    ((centralLowerFaceIds 0 ++ centralFixedFaceIds 0 ++
        centralUpperFaceIds 0).map (slabPlaquetteAt 1)).Perm
      ((slabPhysicalFaceEdges 1).map (slabPlaquetteAt 1)) at h
  rw [slabPhysicalFaces_extent_one_map] at h
  exact h

theorem exactCorrectedSlabPartitionedFaces_nodup :
    exactCorrectedSlabPartitionedFaces.Nodup :=
  exactCorrectedSlabPartitionedFaces_perm.symm.nodup
    (boundaryCompleteSlabPlaquettes_nodup 1)

/-- The actual 24-face cross-plane insertion before any of its link variables
are integrated.  It retains the same 116-link polynomial coordinates as the
complete signed Haar network. -/
def exactCorrectedSlabInteriorInsertion
    (faceLabel : EdgeLabelling) : RatPoly :=
  exactCorrectedSlabFixedFaces.foldr
    (fun face total =>
      polyMul
        (correctedSlabPlaquetteSpinFactor 1 faceLabel face)
        total)
    polyOne

/-- The vacuum cross-plane insertion is the carrier unit. -/
theorem exactCorrectedSlabInteriorInsertion_vacuum :
    exactCorrectedSlabInteriorInsertion zeroEdgeLabelling = polyOne := by
  unfold exactCorrectedSlabInteriorInsertion
  exact vacuum_integrand_on 1 exactCorrectedSlabFixedFaces

/-- Restrict the extent-one slab to its literal 24 lower spatial faces and
apply the proved 25-tree/23-chord gauge fixing.  This is the source boundary
factor of the full slab, prior to integrating the non-transmitted chords. -/
def exactCorrectedSlabGaugeFixedSourceIntegrand
    (state : EdgeLabelling) : RatPoly :=
  bf4SourceSpatialFaces.foldr
    (fun face total =>
      polyMul
        (characterPolynomial
          (treeGaugePlaquettePolynomial face).scalar
          (state
            ((boundaryCompleteSlabPlaquettes 1).idxOf face)))
        total)
    polyOne

/-- The gauge-fixed source restriction is definitionally the existing
24-face BF4 spatial spin network on the same physical face labels. -/
theorem exactCorrectedSlabGaugeFixedSourceIntegrand_eq_spatial
    (state : EdgeLabelling) :
    exactCorrectedSlabGaugeFixedSourceIntegrand state =
      bf4SpatialSpinNetworkIntegrand
        (fun face =>
          state
            ((boundaryCompleteSlabPlaquettes 1).idxOf face)) := by
  rfl

/-- Integrate the eighteen non-transmitted source chords and retain exactly
the five physical holonomy coordinates. -/
def exactCorrectedSlabSourceFiveHolonomyBoundary
    (state : EdgeLabelling) : RatPoly :=
  integrateEighteenChords
    (exactCorrectedSlabGaugeFixedSourceIntegrand state)

/-- **Exact source carrier map.**  Conditional Haar integration of the
gauge-fixed lower spatial restriction is the geometric BF4 five-holonomy
wavefunction used by the all-label packet endpoint. -/
theorem exactCorrectedSlabSourceFiveHolonomyBoundary_eq_geometric
    (state : EdgeLabelling) :
    exactCorrectedSlabSourceFiveHolonomyBoundary state =
      geometricBF4WavefunctionOfState state := by
  rfl

/-- The reflected target occupies the second disjoint five-holonomy block. -/
def exactCorrectedSlabTargetFiveHolonomyBoundary
    (state : EdgeLabelling) : RatPoly :=
  shiftPolynomial 20
    (exactCorrectedSlabSourceFiveHolonomyBoundary state)

theorem exactCorrectedSlabTargetFiveHolonomyBoundary_eq_geometric
    (state : EdgeLabelling) :
    exactCorrectedSlabTargetFiveHolonomyBoundary state =
      targetGeometricWavefunction state := by
  rfl

/-! ## 4. Heat-weighted exact dual term and reflected kernel -/

/-- The exact finite dual heat-kernel term: the positive Peter--Weyl face
coefficient multiplies the signed complete Haar-network contraction. -/
def exactCorrectedSlabDualTerm
    (w : Q') (K extent : Nat)
    (faceLabel : EdgeLabelling) : Q' :=
  slabParametricKPhysicalFaceFactor w K extent faceLabel *
    exactCorrectedSlabHaarCoefficient extent faceLabel

/-- The vacuum dual term is exactly one for every coupling and cutoff. -/
theorem exactCorrectedSlabDualTerm_vacuum
    (w : Q') (K extent : Nat) :
    exactCorrectedSlabDualTerm
        w K extent zeroEdgeLabelling ≈ 1 := by
  unfold exactCorrectedSlabDualTerm
  refine Q'.eqv_trans _
    (1 * exactCorrectedSlabHaarCoefficient
      extent zeroEdgeLabelling) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (slabParametricKPhysicalFaceFactor_zero_eqv_one
        w K extent)
  · exact Q'.eqv_trans _ _ _
      (Q'.one_mul_eqv _)
      (exactCorrectedSlabHaarCoefficient_vacuum extent)

/-- Exact finite reflected dual kernel on the same bounded lower/fixed face
labellings as the corrected-slab reflection construction.  The summand is
the full Haar-network coefficient, not `centralHalfAmplitude` or a local
multiplicity product. -/
def exactCorrectedSlabReflectedKernel
    (w : Q') (K half : Nat)
    (left right : EdgeLabelling) : Q' :=
  listQSum
    (fun boundary =>
      exactCorrectedSlabDualTerm
        w K (centralExtent half)
        (assembleReflectedSlabLabelling
          half left boundary right))
    (centralBoundaryChannels K half)

end YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork.correctedSlabPlaquettes_extent_one_length
#print axioms YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork.correctedSlabLinks_extent_one_length
#print axioms YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork.exactCorrectedSlabLowerSpatialFaces_eq_source
#print axioms YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork.exactCorrectedSlabUpperSpatialFaces_eq_reflected_source
#print axioms YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork.exactCorrectedSlabPartitionedFaces_perm
#print axioms YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork.exactCorrectedSlabPartitionedFaces_nodup
#print axioms YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork.exactCorrectedSlabInteriorInsertion_vacuum
#print axioms YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork.exactCorrectedSlabSpinNetworkIntegrand_vacuum
#print axioms YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork.exactCorrectedSlabHaarCoefficient_vacuum
#print axioms YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork.exactCorrectedSlabSourceFiveHolonomyBoundary_eq_geometric
#print axioms YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork.exactCorrectedSlabTargetFiveHolonomyBoundary_eq_geometric
#print axioms YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork.exactCorrectedSlabDualTerm_vacuum
