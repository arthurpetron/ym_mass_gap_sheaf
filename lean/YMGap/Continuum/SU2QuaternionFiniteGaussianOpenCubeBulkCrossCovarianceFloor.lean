/-
# Positive exact cross-time floor for the rational open-cube bulk source

The lower `p01` face of every positive-side bulk source has an explicit
upper-`x`, `y`-directed chord in the standard comb gauge.  Its restricted curl
coefficient is exactly one.  The constructive two-slice inverse therefore
gives a strictly positive exact covariance between that face curl at times
zero and one.  Multiplying its square by the positive lower-face source
weight produces an explicit side-dependent rational floor for the weighted
cross-covariance-square trace.

This finite floor is not yet uniform in the side.  It proves no Heron-stage
error comparison, original-law estimate, continuum limit, Hamiltonian gap,
or Clay theorem.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombTwoSliceCrossCovariance

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCrossCovarianceFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombTwoSliceCrossCovariance

local infix:50 " ≈ " => Q'.eqv

private def faceLinkB (face : Z4Plaq) : Z4Link :=
  (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)

private theorem addE_ne_self_local
    (vertex : Z4Vertex) (direction : Dir4) :
    addE vertex direction ≠ vertex := by
  rcases vertex with ⟨x, y, z, time⟩
  cases direction
  · intro heq
    have hx : x + 1 = x := congrArg (fun v : Z4Vertex => v.1) heq
    omega
  · intro heq
    have hy : y + 1 = y := congrArg (fun v : Z4Vertex => v.2.1) heq
    omega
  · intro heq
    have hz : z + 1 = z := congrArg (fun v : Z4Vertex => v.2.2.1) heq
    omega
  · intro heq
    have ht : time + 1 = time := congrArg (fun v : Z4Vertex => v.2.2.2) heq
    omega

private theorem internalBoundaryCoefficient_faceLinkB_eq_one
    (face : Z4Plaq) :
    internalBoundaryCoefficient face (faceLinkB face) = 1 := by
  have hdirections := dirsOf_ne face.2
  have hfirst : faceLinkB face ≠
      (face.1, (dirsOf face.2).1) := by
    intro heq
    exact hdirections (congrArg Prod.snd heq).symm
  have hsecond : faceLinkB face ≠
      (face.1, (dirsOf face.2).2) := by
    intro heq
    exact addE_ne_self_local face.1 (dirsOf face.2).1
      (congrArg Prod.fst heq)
  have hthird : faceLinkB face ≠
      (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1) := by
    intro heq
    exact hdirections (congrArg Prod.snd heq).symm
  have hfourth : faceLinkB face =
      (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2) := rfl
  unfold internalBoundaryCoefficient orientedBoundaryCoefficient
  rw [if_neg hfirst, if_neg hsecond, if_neg hthird, if_pos hfourth]
  exact RingNormaliser.ofInt_one

/-- Position of the concrete lower face in the enumerated bulk source. -/
def bulkSourceLowerFaceIndex (s : Nat) : Nat :=
  (bulkSourceFaces s).idxOf (bulkSourceLowerFace s)

theorem bulkSourceLowerFaceIndex_lt (s : Nat) (hs : 0 < s) :
    bulkSourceLowerFaceIndex s < (bulkSourceFaces s).length :=
  List.idxOf_lt_length_of_mem (bulkSourceLowerFace_mem s hs)

theorem selectedBulkSourceFace_lowerFaceIndex (s : Nat) (hs : 0 < s) :
    selectedBulkSourceFace s (bulkSourceLowerFaceIndex s) =
      bulkSourceLowerFace s := by
  have hindex := bulkSourceLowerFaceIndex_lt s hs
  rw [selectedBulkSourceFace, ← List.getElem_eq_getD (h := hindex)]
  exact LawfulBEq.eq_of_beq (List.findIdx_getElem (w := hindex))

/-- The upper-`x`, `y`-directed edge of the lower `p01` source face. -/
def bulkSourceLowerChordLink (s : Nat) : Z4Link :=
  (addE (bulkSourceLowerFace s).1 .x0, .x1)

/-- The chosen lower-face edge is an actual comb-gauge chord. -/
theorem bulkSourceLowerChordLink_mem (s : Nat) (hs : 0 < s) :
    bulkSourceLowerChordLink s ∈
      combGaugeLinks (bulkSourceWidth s) := by
  have hfaceMem := bulkSourceLowerFace_mem s hs
  have hfaceInternal := bulkSourceFace_internal hfaceMem
  have hfaceProperty :=
    (internalOpenCubeFaces_mem_iff (bulkSourceWidth s)
      (bulkSourceLowerFace s)).mp hfaceInternal
  have hedge : bulkSourceLowerChordLink s ∈
      edgesOf (bulkSourceLowerFace s) := by
    simp [bulkSourceLowerChordLink, bulkSourceLowerFace, edgesOf, dirsOf]
  apply (combGaugeLinks_mem_iff
    (bulkSourceWidth s) (bulkSourceLowerChordLink s)).mpr
  refine ⟨internalOpenCubeFace_edge_property hfaceProperty hedge, ?_⟩
  rintro ⟨_hinternal, hshape⟩
  unfold bulkSourceLowerChordLink bulkSourceLowerFace at hshape
  simp only [addE] at hshape
  omega

/-- Comb-coordinate index of the explicit lower-face chord. -/
def bulkSourceLowerChordIndex (s : Nat) : Nat :=
  (combGaugeLinks (bulkSourceWidth s)).idxOf (bulkSourceLowerChordLink s)

theorem bulkSourceLowerChordIndex_lt (s : Nat) (hs : 0 < s) :
    bulkSourceLowerChordIndex s < combGaugeEdgeCount (bulkSourceWidth s) := by
  exact List.idxOf_lt_length_of_mem (bulkSourceLowerChordLink_mem s hs)

theorem bulkSourceCombGaugeEdgeCount_pos (s : Nat) (hs : 0 < s) :
    0 < combGaugeEdgeCount (bulkSourceWidth s) := by
  have hindex := bulkSourceLowerChordIndex_lt s hs
  omega

/-- The selected lower-face chord carries the exact oriented curl coefficient
one at the bulk source's internal face index. -/
theorem bulkSourceLowerFace_curl_chord_eq_one (s : Nat) (hs : 0 < s) :
    combGaugeCurl (bulkSourceWidth s)
        (bulkSourceInternalFaceIndex s (bulkSourceLowerFaceIndex s))
        (bulkSourceLowerChordIndex s) = 1 := by
  have hface := bulkSourceFace_internal (bulkSourceLowerFace_mem s hs)
  have hlink := bulkSourceLowerChordLink_mem s hs
  have hcurl := combGaugeCurl_idxOf hface hlink
  unfold bulkSourceInternalFaceIndex bulkSourceLowerChordIndex
  rw [selectedBulkSourceFace_lowerFaceIndex s hs]
  refine Eq.trans hcurl ?_
  have hboundary :=
    internalBoundaryCoefficient_faceLinkB_eq_one (bulkSourceLowerFace s)
  change internalBoundaryCoefficient (bulkSourceLowerFace s)
    (bulkSourceLowerChordLink s) = 1 at hboundary
  exact hboundary

/-- Exact one-bond covariance of the concrete lower bulk face curl. -/
def bulkSourceLowerFaceOneBondCovariance (s : Nat) : Q' :=
  let width := bulkSourceWidth s
  let faceIndex := bulkSourceInternalFaceIndex s (bulkSourceLowerFaceIndex s)
  combGaugeFreeHistoryCovarianceBilinear 1 width
    (combGaugeFreeHistoryCurlRow width 0 faceIndex)
    (combGaugeFreeHistoryCurlRow width 1 faceIndex)

theorem bulkSourceLowerFaceOneBondCovariance_pos
    (s : Nat) (hs : 0 < s) :
    (0 : Q') < bulkSourceLowerFaceOneBondCovariance s := by
  have hcurl :
      ¬combGaugeCurl (bulkSourceWidth s)
          (bulkSourceInternalFaceIndex s (bulkSourceLowerFaceIndex s))
          (bulkSourceLowerChordIndex s) ≈ 0 := by
    rw [bulkSourceLowerFace_curl_chord_eq_one s hs]
    decide
  exact combGaugeFreeHistoryCurlCrossBilinear_pos_of_coordinate_not_eqv_zero
    (bulkSourceWidth s)
    (bulkSourceInternalFaceIndex s (bulkSourceLowerFaceIndex s))
    (bulkSourceCombGaugeEdgeCount_pos s hs)
    (bulkSourceLowerChordIndex_lt s hs) hcurl

/-- Exact one-bond mixed covariance between two enumerated bulk curl rows. -/
def bulkSourceOneBondMixedCovariance
    (s sourceIndex directionIndex : Nat) : Q' :=
  let width := bulkSourceWidth s
  combGaugeFreeHistoryCovarianceBilinear 1 width
    (combGaugeFreeHistoryCurlRow width 0
      (bulkSourceInternalFaceIndex s sourceIndex))
    (combGaugeFreeHistoryCurlRow width 1
      (bulkSourceInternalFaceIndex s directionIndex))

/-- One nonnegative weighted square in the exact cross-time source trace. -/
def bulkSourceExactCrossCovarianceSummand
    (s : Nat) (hs : 0 < s) (sourceIndex directionIndex : Nat) : Q' :=
  (bulkSourceIndexWeight s hs sourceIndex *
      bulkSourceIndexWeight s hs directionIndex) *
    (bulkSourceOneBondMixedCovariance s sourceIndex directionIndex *
      bulkSourceOneBondMixedCovariance s sourceIndex directionIndex)

theorem bulkSourceExactCrossCovarianceSummand_nonnegative
    {s sourceIndex directionIndex : Nat} (hs : 0 < s)
    (hsource : sourceIndex < (bulkSourceFaces s).length)
    (hdirection : directionIndex < (bulkSourceFaces s).length) :
    (0 : Q') ≤ bulkSourceExactCrossCovarianceSummand
      s hs sourceIndex directionIndex := by
  have hsourceWeight := bulkSourceIndexWeight_pos hs hsource
  have hdirectionWeight := bulkSourceIndexWeight_pos hs hdirection
  unfold bulkSourceExactCrossCovarianceSummand
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.le_of_lt hsourceWeight)
      (Q'.le_of_lt hdirectionWeight))
    (SumOfSquares.q_mul_self_nonneg
      (bulkSourceOneBondMixedCovariance s sourceIndex directionIndex))

/-- Complete exact weighted cross-covariance-square trace for the bulk source
placed at the endpoints of one time bond. -/
def bulkSourceExactCrossCovarianceSquareTrace
    (s : Nat) (hs : 0 < s) : Q' :=
  listQSum
    (fun sourceIndex =>
      listQSum
        (fun directionIndex =>
          bulkSourceExactCrossCovarianceSummand
            s hs sourceIndex directionIndex)
        (List.range (bulkSourceFaces s).length))
    (List.range (bulkSourceFaces s).length)

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A → Q') :
    ∀ (items : List A) {witness : A},
      (∀ item, item ∈ items → (0 : Q') ≤ value item) →
      witness ∈ items →
      value witness ≤ listQSum value items
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, witness, hnonnegative, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst witness
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun item hitem =>
              hnonnegative item (List.mem_cons_of_mem head hitem)))
      · have htailLe := listQSum_member_le_nonnegative_local
          value tail
          (fun item hitem =>
            hnonnegative item (List.mem_cons_of_mem head hitem))
          htail
        have hsumLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail)
            (hnonnegative head List.mem_cons_self)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ htailLe hsumLe

/-- Explicit positive rational term reserved for the exact weighted
cross-covariance-square trace. -/
def bulkSourceExactCrossCovarianceFloor (s : Nat) (hs : 0 < s) : Q' :=
  let weight := bulkSourceIndexWeight s hs (bulkSourceLowerFaceIndex s)
  let mixed := bulkSourceLowerFaceOneBondCovariance s
  (weight * weight) * (mixed * mixed)

theorem bulkSourceExactCrossCovarianceFloor_pos
    (s : Nat) (hs : 0 < s) :
    (0 : Q') < bulkSourceExactCrossCovarianceFloor s hs := by
  have hweight := bulkSourceIndexWeight_pos hs
    (bulkSourceLowerFaceIndex_lt s hs)
  have hmixed := bulkSourceLowerFaceOneBondCovariance_pos s hs
  unfold bulkSourceExactCrossCovarianceFloor
  exact Q'.mul_pos (Q'.mul_pos hweight hweight)
    (Q'.mul_pos hmixed hmixed)

/-- The complete exact weighted trace dominates the explicit lower-face
positive term. -/
theorem bulkSourceExactCrossCovarianceFloor_le_trace
    (s : Nat) (hs : 0 < s) :
    bulkSourceExactCrossCovarianceFloor s hs ≤
      bulkSourceExactCrossCovarianceSquareTrace s hs := by
  let witness := bulkSourceLowerFaceIndex s
  have hwitness : witness < (bulkSourceFaces s).length :=
    bulkSourceLowerFaceIndex_lt s hs
  have hinner :
      bulkSourceExactCrossCovarianceSummand s hs witness witness ≤
        listQSum
          (fun directionIndex =>
            bulkSourceExactCrossCovarianceSummand
              s hs witness directionIndex)
          (List.range (bulkSourceFaces s).length) := by
    apply listQSum_member_le_nonnegative_local
    · intro directionIndex hdirection
      exact bulkSourceExactCrossCovarianceSummand_nonnegative hs
        hwitness (List.mem_range.mp hdirection)
    · exact List.mem_range.mpr hwitness
  have houter :
      listQSum
          (fun directionIndex =>
            bulkSourceExactCrossCovarianceSummand
              s hs witness directionIndex)
          (List.range (bulkSourceFaces s).length) ≤
        bulkSourceExactCrossCovarianceSquareTrace s hs := by
    unfold bulkSourceExactCrossCovarianceSquareTrace
    apply listQSum_member_le_nonnegative_local
    · intro sourceIndex hsource
      apply listQSum_nonnegative_on
      intro directionIndex hdirection
      exact bulkSourceExactCrossCovarianceSummand_nonnegative hs
        (List.mem_range.mp hsource) (List.mem_range.mp hdirection)
    · exact List.mem_range.mpr hwitness
  have hfloor :
      bulkSourceExactCrossCovarianceFloor s hs =
        bulkSourceExactCrossCovarianceSummand s hs witness witness := rfl
  rw [hfloor]
  exact Q'.le_trans' _ _ _ hinner houter

/-- The full exact weighted endpoint cross-covariance-square trace is
strictly positive for every positive bulk side. -/
theorem bulkSourceExactCrossCovarianceSquareTrace_pos
    (s : Nat) (hs : 0 < s) :
    (0 : Q') < bulkSourceExactCrossCovarianceSquareTrace s hs :=
  Q'.pos_of_lt_of_le (bulkSourceExactCrossCovarianceFloor_pos s hs)
    (bulkSourceExactCrossCovarianceFloor_le_trace s hs)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCrossCovarianceFloor

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCrossCovarianceFloor.bulkSourceLowerChordLink_mem
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCrossCovarianceFloor.bulkSourceLowerFace_curl_chord_eq_one
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCrossCovarianceFloor.bulkSourceLowerFaceOneBondCovariance_pos
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCrossCovarianceFloor.bulkSourceExactCrossCovarianceFloor_pos
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCrossCovarianceFloor.bulkSourceExactCrossCovarianceFloor_le_trace
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCrossCovarianceFloor.bulkSourceExactCrossCovarianceSquareTrace_pos
