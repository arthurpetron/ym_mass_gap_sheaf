/-
# The original conditional projection fixes independent local polynomials

Deleting the selected zero-degree quaternion block constructs an exterior
polynomial. Its lifted probe is equal to the original polynomial in the
SAME full-action completion, by exact Haar pairings against every dense
test. No literal coefficient equality after padded reindexing is asserted.

Every lifted exterior probe excludes the selected physical link. These
facts support non-neighbor conditional commutation, not a spatial rate,
an OS estimate, or a physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabStarConditionalLocality

namespace YMGap.Continuum.BF4ExactSlabStarIndependentProbe

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold (blockDegree_reindex)
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

/-- The actual full physical link list, with only the selected link removed. -/
def independentLinks (extent : Nat) (link : Z4Link) : List Z4Link :=
  (boundaryCompleteSlabLinks extent).filter (fun j => decide (j ≠ link))

private theorem reindex_supported {n : Nat} (swap : QuaternionBlockInvolution n) (p : RatPoly) :
    SupportedQuaternionBlocks n (reindexQuaternionPolynomial swap p) :=
  BF4ExactPhysicalCenteredVacuumTransmittedMarginal.reindexQuaternionPolynomial_supported swap p

private theorem drop_supported {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks (n-1) (dropHeadPolynomial p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  have h := hp s hs
  change (s.1.drop 4).length ≤ 4*(n-1)
  rw [List.length_drop]
  omega

private theorem local_headIndependent (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (support : List Z4Link) {p : RatPoly}
    (hp : LinkLocal extent support p) (hnot : link ∉ support) :
    HeadQuaternionIndependent (reindexQuaternionPolynomial (linkHeadSwap extent link hl) p) := by
  change HasQuaternionBlockDegree 0 0 _
  have hk := List.idxOf_lt_length_of_mem hl
  exact blockDegree_reindex (linkHeadSwap extent link hl) (by omega)
    (headSwapBlockInvolution_map_zero _ _ hk)
    (BF4ExactSlabSingleLinkCharacterSelection.linkLocal_degree_zero hp link hl hnot)

private theorem independent_haar_pair {n : Nat} (hn : 0 < n)
    (swap : QuaternionBlockInvolution n) (p t : RatPoly)
    (hp : SupportedQuaternionBlocks n p) (ht : SupportedQuaternionBlocks n t)
    (hind : HeadQuaternionIndependent (reindexQuaternionPolynomial swap p)) :
    quaternionHaar n (polyMul p t) ≈ quaternionHaar n
      (polyMul (headProbe swap (dropHeadPolynomial (reindexQuaternionPolynomial swap p))) t) := by
  have hs := quaternionHaar_reindex swap (polyMul t p) (supported_polyMul ht hp)
  rw [reindexQuaternionPolynomial_mul] at hs
  have hf := quaternionHaar_polyMul_headIndependent (n-1)
    (reindexQuaternionPolynomial swap t) (reindexQuaternionPolynomial swap p) hind
  rw [show n-1+1=n by omega] at hf
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm p t))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hs)
      (Q'.eqv_trans _ _ _ hf
        (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
          (Q'.eqv_symm (headProbe_pair hn swap _ t
            (drop_supported (reindex_supported swap p)) ht)))))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "G" => exteriorData hw0 hw1 K extent hK link hl
local notation "J" => probeMap hw0 hw1 K extent hK link hl
local notation "C" => conditionalProjection hw0 hw1 K extent hK link hl

/-- Computed exterior data; independence is needed only for its recovery pin. -/
def independentExterior (p : (F).V) : (G).V :=
  ⟨dropHeadPolynomial (reindexQuaternionPolynomial (linkHeadSwap extent link hl) p.val),
    drop_supported (reindex_supported _ _)⟩

/-- All full-action pairings agree, despite possible zero padding in coefficients. -/
theorem independent_pair (support : List Z4Link) (p q : (F).V)
    (hp : LinkLocal extent support p.val) (hnot : link ∉ support) :
    (F).B p q ≈ (F).B (J (independentExterior hw0 hw1 K extent hK link hl p)) q := by
  have hn : 0 < blocks extent := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  let W := polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)
  have ht : SupportedQuaternionBlocks (blocks extent) (polyMul q.val W) :=
    supported_polyMul q.property (heatProduct_supported w K extent _)
  have he := independent_haar_pair hn (linkHeadSwap extent link hl) p.val (polyMul q.val W)
    p.property ht (local_headIndependent extent link hl support hp hnot)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
    (Q'.eqv_trans _ _ _ he (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm))

/-- The original independent polynomial is realized by a constructed exterior probe. -/
theorem independent_embed (support : List Z4Link) (p : (F).V)
    (hp : LinkLocal extent support p.val) (hnot : link ∉ support) :
    embedV F p = embedV F (J (independentExterior hw0 hw1 K extent hK link hl p)) := by
  apply GNSDenseCompletionLaws.eq_of_dense_pairings
  intro q
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv
    (fun _ => independent_pair hw0 hw1 K extent hK link hl support p q hp hnot)

/-- The actual original conditional projection fixes every such local input. -/
theorem conditionalProjection_fix_local (support : List Z4Link) (p : (F).V)
    (hp : LinkLocal extent support p.val) (hnot : link ∉ support) :
    C (embedV F p) = embedV F p := by
  have he := independent_embed hw0 hw1 K extent hK link hl support p hp hnot
  let r := independentExterior hw0 hw1 K extent hK link hl p
  have hre : embedV F p = probeCompletion hw0 hw1 K extent hK link hl (embedV G r) :=
    he.trans (probeCompletion_embed hw0 hw1 K extent hK link hl r).symm
  exact (congrArg C hre).trans
    ((conditionalProjection_fix_exterior hw0 hw1 K extent hK link hl (embedV G r)).trans hre.symm)

/-- Every original exterior lift omits the selected link, without a premise on its other variables. -/
theorem probeMap_local (r : (G).V) :
    LinkLocal extent (independentLinks extent link) (J r).val := by
  let swap := linkHeadSwap extent link hl
  have hr : BlockLocal (blocks extent-1) (fun _ => True) r.val :=
    fun _ _ _ _ hn => False.elim (hn True.intro)
  apply (BlockLocal.liftHead (blocks := blocks extent) hr).reindex swap
  intro b hb h
  apply List.mem_filter.mpr
  refine ⟨correctedSlabLinkAt_mem (List.mem_range.mpr hb), ?_⟩
  apply decide_eq_true
  intro he
  have hk := List.idxOf_lt_length_of_mem hl
  have hbk : b = (boundaryCompleteSlabLinks extent).idxOf link :=
    correctedSlabLinkAt_injective_on_physical (List.mem_range.mpr hb) (List.mem_range.mpr hk)
      (he.trans (correctedSlabLinkAt_idxOf hl).symm)
  have hz : swap.map b = 0 := by
    rw [hbk]
    exact headSwapBlockInvolution_map_selected _ _ hk
  omega

end YMGap.Continuum.BF4ExactSlabStarIndependentProbe

#print axioms YMGap.Continuum.BF4ExactSlabStarIndependentProbe.independentLinks
#print axioms YMGap.Continuum.BF4ExactSlabStarIndependentProbe.independentExterior
#print axioms YMGap.Continuum.BF4ExactSlabStarIndependentProbe.independent_pair
#print axioms YMGap.Continuum.BF4ExactSlabStarIndependentProbe.independent_embed
#print axioms YMGap.Continuum.BF4ExactSlabStarIndependentProbe.conditionalProjection_fix_local
#print axioms YMGap.Continuum.BF4ExactSlabStarIndependentProbe.probeMap_local
