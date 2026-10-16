/-
# Central positive cross-time witness for the rational open-cube bulk source

The lower-corner face used by the first positive cross-time witness has a
source coefficient that decays with the side.  This leaf replaces that
boundary witness by the explicit central `p01` face at offset `(m,m,m)` for
side `4*m`.  Its upper-`x`, `y`-directed edge is again a comb-gauge chord with
curl coefficient one, so its exact one-bond covariance is strictly positive.
The central profile theorem additionally gives the side-independent
coefficient-square floor `3^(-36)` for this same enumerated face.

The covariance factor itself is still side-dependent.  Thus the resulting
trace floor is finite and strictly positive, with a uniform source-coefficient
factor, but is not yet a cutoff-uniform covariance floor, an original-law
estimate, a continuum limit, a Hamiltonian gap, or a Clay theorem.
-/

import YMGap.Constructive.Sqrt
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCrossCovarianceFloor
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkProfileFloor

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralCrossCovarianceFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCrossCovarianceFloor
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkProfileFloor
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombTwoSliceCrossCovariance

local infix:50 " ≈ " => Q'.eqv

/-- The selected central `p01` source face at side `4*m`. -/
def bulkSourceCentralFace (m : Nat) : Z4Plaq :=
  bulkSourceFaceAt (4 * m) m m m .p01

/-- The selected face belongs to the central half-carrier. -/
theorem bulkSourceCentralFace_mem_central (m : Nat) (hm : 0 < m) :
    bulkSourceCentralFace m ∈ centralBulkSourceFaces m := by
  unfold bulkSourceCentralFace centralBulkSourceFaces centralBulkOffsets
  apply List.mem_flatMap.mpr
  refine ⟨m, List.mem_range'_1.mpr ⟨Nat.le_refl _, by omega⟩, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨m, List.mem_range'_1.mpr ⟨Nat.le_refl _, by omega⟩, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨m, List.mem_range'_1.mpr ⟨Nat.le_refl _, by omega⟩, ?_⟩
  apply List.mem_map.mpr
  exact ⟨.p01, by simp [bulkSourcePlanes], rfl⟩

/-- The selected central face belongs to the full formula-level source. -/
theorem bulkSourceCentralFace_mem_source (m : Nat) (hm : 0 < m) :
    bulkSourceCentralFace m ∈ bulkSourceFaces (4 * m) :=
  (centralBulkSourceFaces_sublist m).mem
    (bulkSourceCentralFace_mem_central m hm)

/-- Position of the selected central face in the full bulk enumeration. -/
def bulkSourceCentralFaceIndex (m : Nat) : Nat :=
  (bulkSourceFaces (4 * m)).idxOf (bulkSourceCentralFace m)

theorem bulkSourceCentralFaceIndex_lt (m : Nat) (hm : 0 < m) :
    bulkSourceCentralFaceIndex m < (bulkSourceFaces (4 * m)).length :=
  List.idxOf_lt_length_of_mem (bulkSourceCentralFace_mem_source m hm)

theorem selectedBulkSourceFace_centralFaceIndex (m : Nat) (hm : 0 < m) :
    selectedBulkSourceFace (4 * m) (bulkSourceCentralFaceIndex m) =
      bulkSourceCentralFace m := by
  have hindex := bulkSourceCentralFaceIndex_lt m hm
  rw [selectedBulkSourceFace, ← List.getElem_eq_getD (h := hindex)]
  exact LawfulBEq.eq_of_beq (List.findIdx_getElem (w := hindex))

/-- The upper-`x`, `y`-directed edge of the selected central face. -/
def bulkSourceCentralChordLink (m : Nat) : Z4Link :=
  (addE (bulkSourceCentralFace m).1 .x0, .x1)

/-- The central-face edge is an actual comb-gauge chord. -/
theorem bulkSourceCentralChordLink_mem (m : Nat) (hm : 0 < m) :
    bulkSourceCentralChordLink m ∈
      combGaugeLinks (bulkSourceWidth (4 * m)) := by
  have hfaceMem := bulkSourceCentralFace_mem_source m hm
  have hfaceInternal := bulkSourceFace_internal hfaceMem
  have hfaceProperty :=
    (internalOpenCubeFaces_mem_iff (bulkSourceWidth (4 * m))
      (bulkSourceCentralFace m)).mp hfaceInternal
  have hedge : bulkSourceCentralChordLink m ∈
      edgesOf (bulkSourceCentralFace m) := by
    simp [bulkSourceCentralChordLink, bulkSourceCentralFace,
      bulkSourceFaceAt, edgesOf, dirsOf]
  apply (combGaugeLinks_mem_iff
    (bulkSourceWidth (4 * m)) (bulkSourceCentralChordLink m)).mpr
  refine ⟨internalOpenCubeFace_edge_property hfaceProperty hedge, ?_⟩
  rintro ⟨_hinternal, hshape⟩
  unfold bulkSourceCentralChordLink bulkSourceCentralFace bulkSourceFaceAt at hshape
  simp only [addE] at hshape
  omega

/-- Comb-coordinate index of the selected central-face chord. -/
def bulkSourceCentralChordIndex (m : Nat) : Nat :=
  (combGaugeLinks (bulkSourceWidth (4 * m))).idxOf
    (bulkSourceCentralChordLink m)

theorem bulkSourceCentralChordIndex_lt (m : Nat) (hm : 0 < m) :
    bulkSourceCentralChordIndex m <
      combGaugeEdgeCount (bulkSourceWidth (4 * m)) :=
  List.idxOf_lt_length_of_mem (bulkSourceCentralChordLink_mem m hm)

theorem bulkSourceCentralCombGaugeEdgeCount_pos (m : Nat) (hm : 0 < m) :
    0 < combGaugeEdgeCount (bulkSourceWidth (4 * m)) := by
  have hindex := bulkSourceCentralChordIndex_lt m hm
  omega

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

/-- The selected central-face chord carries oriented curl coefficient one. -/
theorem bulkSourceCentralFace_curl_chord_eq_one (m : Nat) (hm : 0 < m) :
    combGaugeCurl (bulkSourceWidth (4 * m))
        (bulkSourceInternalFaceIndex (4 * m)
          (bulkSourceCentralFaceIndex m))
        (bulkSourceCentralChordIndex m) = 1 := by
  have hface := bulkSourceFace_internal
    (bulkSourceCentralFace_mem_source m hm)
  have hlink := bulkSourceCentralChordLink_mem m hm
  have hcurl := combGaugeCurl_idxOf hface hlink
  unfold bulkSourceInternalFaceIndex bulkSourceCentralChordIndex
  rw [selectedBulkSourceFace_centralFaceIndex m hm]
  refine Eq.trans hcurl ?_
  have hboundary :=
    internalBoundaryCoefficient_faceLinkB_eq_one (bulkSourceCentralFace m)
  change internalBoundaryCoefficient (bulkSourceCentralFace m)
    (bulkSourceCentralChordLink m) = 1 at hboundary
  exact hboundary

/-- Exact one-bond covariance of the selected central bulk face curl. -/
def bulkSourceCentralOneBondCovariance (m : Nat) : Q' :=
  bulkSourceOneBondMixedCovariance (4 * m)
    (bulkSourceCentralFaceIndex m) (bulkSourceCentralFaceIndex m)

theorem bulkSourceCentralOneBondCovariance_pos
    (m : Nat) (hm : 0 < m) :
    (0 : Q') < bulkSourceCentralOneBondCovariance m := by
  have hcurl :
      ¬combGaugeCurl (bulkSourceWidth (4 * m))
          (bulkSourceInternalFaceIndex (4 * m)
            (bulkSourceCentralFaceIndex m))
          (bulkSourceCentralChordIndex m) ≈ 0 := by
    rw [bulkSourceCentralFace_curl_chord_eq_one m hm]
    decide
  unfold bulkSourceCentralOneBondCovariance bulkSourceOneBondMixedCovariance
  exact combGaugeFreeHistoryCurlCrossBilinear_pos_of_coordinate_not_eqv_zero
    (bulkSourceWidth (4 * m))
    (bulkSourceInternalFaceIndex (4 * m)
      (bulkSourceCentralFaceIndex m))
    (bulkSourceCentralCombGaugeEdgeCount_pos m hm)
    (bulkSourceCentralChordIndex_lt m hm) hcurl

/-- The exact selected index weight has the uniform central square floor. -/
theorem bulkSourceCentralIndexWeight_square_floor
    (m : Nat) (hm : 0 < m) :
    bulkCoefficientSquareFloor <=
      bulkSourceIndexWeight (4 * m) (Nat.mul_pos (by decide) hm)
          (bulkSourceCentralFaceIndex m) *
        bulkSourceIndexWeight (4 * m) (Nat.mul_pos (by decide) hm)
          (bulkSourceCentralFaceIndex m) := by
  unfold bulkSourceIndexWeight
  rw [selectedBulkSourceFace_centralFaceIndex m hm]
  exact centralBulkSourceCoefficient_square_floor m hm
    (bulkSourceCentralFace_mem_central m hm)

/-- Uniform central coefficient floor `3^(-18)`. -/
def bulkCoefficientFloor : Q' := Q'.mkPos 1 (3 ^ 18) (by decide)

private theorem bulkCoefficientFloor_square_eqv :
    bulkCoefficientFloor * bulkCoefficientFloor ≈
      bulkCoefficientSquareFloor := by
  decide

/-- The selected central source weight itself is bounded below by `3^(-18)`.
This is the single-weight form needed by the weighted row-trace consumer. -/
theorem bulkSourceCentralIndexWeight_floor
    (m : Nat) (hm : 0 < m) :
    bulkCoefficientFloor <=
      bulkSourceIndexWeight (4 * m) (Nat.mul_pos (by decide) hm)
        (bulkSourceCentralFaceIndex m) := by
  let weight := bulkSourceIndexWeight (4 * m)
    (Nat.mul_pos (by decide) hm) (bulkSourceCentralFaceIndex m)
  have hweight : (0 : Q') < weight :=
    bulkSourceIndexWeight_pos (Nat.mul_pos (by decide) hm)
      (bulkSourceCentralFaceIndex_lt m hm)
  have hfloor : (0 : Q') <= bulkCoefficientFloor := by decide
  have hsquare :
      bulkCoefficientFloor * bulkCoefficientFloor <= weight * weight :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv bulkCoefficientFloor_square_eqv)
      (bulkSourceCentralIndexWeight_square_floor m hm)
  exact CReal.le_of_sq_le_sq hweight hfloor hsquare

/-- The central selected term in the exact weighted cross-covariance trace. -/
def bulkSourceCentralExactCrossCovarianceFloor
    (m : Nat) (hm : 0 < m) : Q' :=
  let weight := bulkSourceIndexWeight (4 * m)
    (Nat.mul_pos (by decide) hm) (bulkSourceCentralFaceIndex m)
  let mixed := bulkSourceCentralOneBondCovariance m
  (weight * weight) * (mixed * mixed)

theorem bulkSourceCentralExactCrossCovarianceFloor_pos
    (m : Nat) (hm : 0 < m) :
    (0 : Q') < bulkSourceCentralExactCrossCovarianceFloor m hm := by
  have hweight := bulkSourceIndexWeight_pos
    (Nat.mul_pos (by decide) hm) (bulkSourceCentralFaceIndex_lt m hm)
  have hmixed := bulkSourceCentralOneBondCovariance_pos m hm
  unfold bulkSourceCentralExactCrossCovarianceFloor
  exact Q'.mul_pos (Q'.mul_pos hweight hweight)
    (Q'.mul_pos hmixed hmixed)

/-- The same selected term retains the uniform central coefficient-square
factor; only its exact covariance square remains side-dependent. -/
theorem bulkCoefficientSquareFloor_mul_centralCovarianceSquare_le_floor
    (m : Nat) (hm : 0 < m) :
    bulkCoefficientSquareFloor *
        (bulkSourceCentralOneBondCovariance m *
          bulkSourceCentralOneBondCovariance m) <=
      bulkSourceCentralExactCrossCovarianceFloor m hm := by
  unfold bulkSourceCentralExactCrossCovarianceFloor
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (bulkSourceCentralIndexWeight_square_floor m hm)
    (SumOfSquares.q_mul_self_nonneg
      (bulkSourceCentralOneBondCovariance m))

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

/-- The complete exact weighted cross-covariance trace dominates the selected
central term. -/
theorem bulkSourceCentralExactCrossCovarianceFloor_le_trace
    (m : Nat) (hm : 0 < m) :
    bulkSourceCentralExactCrossCovarianceFloor m hm <=
      bulkSourceExactCrossCovarianceSquareTrace
        (4 * m) (Nat.mul_pos (by decide) hm) := by
  let witness := bulkSourceCentralFaceIndex m
  have hwitness : witness < (bulkSourceFaces (4 * m)).length :=
    bulkSourceCentralFaceIndex_lt m hm
  have hinner :
      bulkSourceExactCrossCovarianceSummand
          (4 * m) (Nat.mul_pos (by decide) hm) witness witness <=
        listQSum
          (fun directionIndex =>
            bulkSourceExactCrossCovarianceSummand
              (4 * m) (Nat.mul_pos (by decide) hm)
              witness directionIndex)
          (List.range (bulkSourceFaces (4 * m)).length) := by
    apply listQSum_member_le_nonnegative_local
    · intro directionIndex hdirection
      exact bulkSourceExactCrossCovarianceSummand_nonnegative
        (Nat.mul_pos (by decide) hm) hwitness
        (List.mem_range.mp hdirection)
    · exact List.mem_range.mpr hwitness
  have houter :
      listQSum
          (fun directionIndex =>
            bulkSourceExactCrossCovarianceSummand
              (4 * m) (Nat.mul_pos (by decide) hm)
              witness directionIndex)
          (List.range (bulkSourceFaces (4 * m)).length) <=
        bulkSourceExactCrossCovarianceSquareTrace
          (4 * m) (Nat.mul_pos (by decide) hm) := by
    unfold bulkSourceExactCrossCovarianceSquareTrace
    apply listQSum_member_le_nonnegative_local
    · intro sourceIndex hsource
      apply listQSum_nonnegative_on
      intro directionIndex hdirection
      exact bulkSourceExactCrossCovarianceSummand_nonnegative
        (Nat.mul_pos (by decide) hm)
        (List.mem_range.mp hsource) (List.mem_range.mp hdirection)
    · exact List.mem_range.mpr hwitness
  have hfloor :
      bulkSourceCentralExactCrossCovarianceFloor m hm =
        bulkSourceExactCrossCovarianceSummand
          (4 * m) (Nat.mul_pos (by decide) hm) witness witness := rfl
  rw [hfloor]
  exact Q'.le_trans' _ _ _ hinner houter

/-- Uniform central coefficient-square times the explicit covariance square
is a checked lower bound for the complete exact trace. -/
theorem bulkCoefficientSquareFloor_mul_centralCovarianceSquare_le_trace
    (m : Nat) (hm : 0 < m) :
    bulkCoefficientSquareFloor *
        (bulkSourceCentralOneBondCovariance m *
          bulkSourceCentralOneBondCovariance m) <=
      bulkSourceExactCrossCovarianceSquareTrace
        (4 * m) (Nat.mul_pos (by decide) hm) :=
  Q'.le_trans' _ _ _
    (bulkCoefficientSquareFloor_mul_centralCovarianceSquare_le_floor m hm)
    (bulkSourceCentralExactCrossCovarianceFloor_le_trace m hm)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralCrossCovarianceFloor

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralCrossCovarianceFloor.bulkSourceCentralFace_mem_central
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralCrossCovarianceFloor.bulkSourceCentralChordLink_mem
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralCrossCovarianceFloor.bulkSourceCentralFace_curl_chord_eq_one
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralCrossCovarianceFloor.bulkSourceCentralOneBondCovariance_pos
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralCrossCovarianceFloor.bulkSourceCentralIndexWeight_square_floor
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralCrossCovarianceFloor.bulkSourceCentralIndexWeight_floor
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralCrossCovarianceFloor.bulkSourceCentralExactCrossCovarianceFloor_pos
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralCrossCovarianceFloor.bulkCoefficientSquareFloor_mul_centralCovarianceSquare_le_trace
