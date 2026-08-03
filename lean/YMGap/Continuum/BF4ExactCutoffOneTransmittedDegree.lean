/-
# Cutoff-one degree certificate for the five transmitted BF4 chords

At cutoff one every face spin is zero or one.  Hence a link block occurs in
the exact slab integrand with degree at most its literal plaquette-incidence
count.  This module proves that statement structurally, evaluates the five
relevant counts as `[4,4,4,5,5]`, transports the bound through the explicit
116-block carrier adaptation, and applies the degree-certified tree-gauge
bridge to both resummed centered-vacuum polynomials.

## Axiom gate

Finite geometry, exact polynomial block degrees, decidable incidence tables,
and the constructive Haar bridge only.  No `Classical.*`, `native_decide`,
`sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier

namespace YMGap.Continuum.BF4ExactCutoffOneTransmittedDegree

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalClassCoordinateCarrier
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationDegree
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal block-incidence degree -/

def slabEntryBlockDegree (block : Nat) (entry : OrientedBF4Link) : Nat :=
  if block = (boundaryCompleteSlabLinks 1).idxOf entry.link then 1 else 0

def slabWordBlockDegree (block : Nat) : List OrientedBF4Link → Nat
  | [] => 0
  | entry :: rest =>
      slabEntryBlockDegree block entry + slabWordBlockDegree block rest

def slabFaceBlockDegree (block : Nat) (face : Z4Plaq) : Nat :=
  slabWordBlockDegree block (orientedPlaquetteBoundary face)

def slabFacesBlockDegree (block : Nat) : List Z4Plaq → Nat
  | [] => 0
  | face :: rest =>
      slabFaceBlockDegree block face + slabFacesBlockDegree block rest

def exactSlabBlockIncidenceDegree (block : Nat) : Nat :=
  slabFacesBlockDegree block (boundaryCompleteSlabPlaquettes 1)

private theorem polyQuaternionOne_blockDegree_zero (block : Nat) :
    HasPolyQuaternionBlockDegree block 0 PolyQuaternion.one := by
  constructor
  · exact hasQuaternionBlockDegree_one block
  · exact hasQuaternionBlockDegree_zero block 0
  · exact hasQuaternionBlockDegree_zero block 0
  · exact hasQuaternionBlockDegree_zero block 0

private theorem orientedSlabLink_blockDegree
    (block : Nat) {face : Z4Plaq} {entry : OrientedBF4Link}
    (hface : face ∈ boundaryCompleteSlabPlaquettes 1)
    (hentry : entry ∈ orientedPlaquetteBoundary face) :
    HasPolyQuaternionBlockDegree block
      (slabEntryBlockDegree block entry)
      (orientedCorrectedSlabLinkPolynomial 1 entry) := by
  have hlink := orientedPlaquetteBoundary_link_mem_slab hface hentry
  have hcoordinate := hasPolyQuaternionBlockDegree_coordinateVariable
    ((boundaryCompleteSlabLinks 1).idxOf entry.link) block
  unfold slabEntryBlockDegree
  unfold orientedCorrectedSlabLinkPolynomial
  rw [correctedSlabLinkPolynomial_of_mem hlink]
  cases hreverse : entry.reverse with
  | false => simpa [hreverse] using hcoordinate
  | true => simpa [hreverse] using hcoordinate.conj

private theorem orientedSlabWordFold_blockDegree
    (block : Nat) {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes 1) :
    ∀ (entries : List OrientedBF4Link) (total : PolyQuaternion)
      (startDegree : Nat),
      HasPolyQuaternionBlockDegree block startDegree total →
      (∀ entry, entry ∈ entries →
        entry ∈ orientedPlaquetteBoundary face) →
      HasPolyQuaternionBlockDegree block
        (startDegree + slabWordBlockDegree block entries)
        (entries.foldl
          (fun product entry => PolyQuaternion.mul product
            (orientedCorrectedSlabLinkPolynomial 1 entry)) total)
  | [], total, startDegree, htotal, _ => by
      simpa [slabWordBlockDegree] using htotal
  | entry :: rest, total, startDegree, htotal, hentries => by
      simp only [List.foldl_cons, slabWordBlockDegree]
      exact HasPolyQuaternionBlockDegree.relabel
        (Nat.add_assoc startDegree
          (slabEntryBlockDegree block entry)
          (slabWordBlockDegree block rest))
        (orientedSlabWordFold_blockDegree block hface rest
          (PolyQuaternion.mul total
            (orientedCorrectedSlabLinkPolynomial 1 entry))
          (startDegree + slabEntryBlockDegree block entry)
          (htotal.mul
            (orientedSlabLink_blockDegree block hface
              (hentries entry List.mem_cons_self)))
          (fun other hother =>
            hentries other (List.mem_cons_of_mem entry hother)))

private theorem correctedSlabPlaquetteScalar_blockDegree
    (block : Nat) {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes 1) :
    HasQuaternionBlockDegree block (slabFaceBlockDegree block face)
      (correctedSlabPlaquettePolynomial 1 face).scalar := by
  have hword := orientedSlabWordFold_blockDegree block hface
    (orientedPlaquetteBoundary face) PolyQuaternion.one 0
    (polyQuaternionOne_blockDegree_zero block)
    (fun entry hentry => hentry)
  simpa [correctedSlabPlaquettePolynomial, slabFaceBlockDegree] using
    hword.scalar

private theorem cutoffOneFaceFactor_degreeAtMost
    (block : Nat) (faceLabel : EdgeLabelling)
    (hlabel : ∀ id, faceLabel id ≤ 1)
    {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes 1) :
    QuaternionBlockDegreeAtMost block (slabFaceBlockDegree block face)
      (correctedSlabPlaquetteSpinFactor 1 faceLabel face) := by
  let faceId := (boundaryCompleteSlabPlaquettes 1).idxOf face
  have hspin := hlabel faceId
  have hcases : faceLabel faceId = 0 ∨ faceLabel faceId = 1 := by omega
  rcases hcases with hzero | hone
  · unfold correctedSlabPlaquetteSpinFactor
    rw [show (boundaryCompleteSlabPlaquettes 1).idxOf face = faceId from rfl,
      hzero]
    exact quaternionBlockDegreeAtMost_one block _
  · unfold correctedSlabPlaquetteSpinFactor
    rw [show (boundaryCompleteSlabPlaquettes 1).idxOf face = faceId from rfl,
      hone]
    exact hasDegree_to_degreeAtMost
      ((correctedSlabPlaquetteScalar_blockDegree block hface).smul 2)
      (Nat.le_refl _)

private theorem cutoffOneIntegrandOn_degreeAtMost
    (block : Nat) (faceLabel : EdgeLabelling)
    (hlabel : ∀ id, faceLabel id ≤ 1) :
    ∀ faces : List Z4Plaq,
      (∀ face, face ∈ faces →
        face ∈ boundaryCompleteSlabPlaquettes 1) →
      QuaternionBlockDegreeAtMost block
        (slabFacesBlockDegree block faces)
        (faces.foldr
          (fun face total =>
            polyMul
              (correctedSlabPlaquetteSpinFactor 1 faceLabel face)
              total)
          polyOne)
  | [], _ => by
      simpa [slabFacesBlockDegree] using
        quaternionBlockDegreeAtMost_one block 0
  | face :: rest, hfaces => by
      simp only [List.foldr, slabFacesBlockDegree]
      exact (cutoffOneFaceFactor_degreeAtMost block faceLabel hlabel
          (hfaces face List.mem_cons_self)).mul
        (cutoffOneIntegrandOn_degreeAtMost block faceLabel hlabel rest
          (fun other hother =>
            hfaces other (List.mem_cons_of_mem face hother)))

/-- Every literal cutoff-one slab integrand has block degree bounded by the
geometric plaquette-incidence count, before multiplication by its heat
coefficient.  This public form is the pointwise input needed to send an
individual binary surface through the 116-link-to-five-cycle bridge. -/
theorem exactCorrectedSlabSpinNetworkIntegrand_cutoffOne_degreeAtMost
    (block : Nat) (faceLabel : EdgeLabelling)
    (hlabel : ∀ id, faceLabel id ≤ 1) :
    QuaternionBlockDegreeAtMost block
      (exactSlabBlockIncidenceDegree block)
      (exactCorrectedSlabSpinNetworkIntegrand 1 faceLabel) := by
  simpa [exactCorrectedSlabSpinNetworkIntegrand,
    exactSlabBlockIncidenceDegree] using
    cutoffOneIntegrandOn_degreeAtMost block faceLabel hlabel
      (boundaryCompleteSlabPlaquettes 1)
      (fun face hface => hface)

theorem exactCorrectedSlabWeightedIntegrand_cutoffOne_degreeAtMost
    (block : Nat) (w : Q') (faceLabel : EdgeLabelling)
    (hlabel : ∀ id, faceLabel id ≤ 1) :
    QuaternionBlockDegreeAtMost block
      (exactSlabBlockIncidenceDegree block)
      (exactCorrectedSlabWeightedIntegrand w 1 faceLabel) := by
  unfold exactCorrectedSlabWeightedIntegrand
  apply QuaternionBlockDegreeAtMost.smul
  exact exactCorrectedSlabSpinNetworkIntegrand_cutoffOne_degreeAtMost
    block faceLabel hlabel

/-! ## 2. The five incidence counts are at most five -/

def bf4TransmittedRawChordBlocks : List Nat :=
  [11, 3, 6, 23, 42]

theorem bf4TransmittedRawChordBlocks_eq_adaptation_sources :
    bf4TransmittedAdaptedChordBlocks.map
        (quaternionBlockSwapChainSource bf4RawCarrierAdaptationSteps) =
      bf4TransmittedRawChordBlocks := by
  rw [bf4TransmittedAdaptedChordBlocks_eq]
  decide

theorem bf4TransmittedRawChordIncidenceDegrees_eq :
    bf4TransmittedRawChordBlocks.map exactSlabBlockIncidenceDegree =
      [4, 4, 4, 5, 5] := by
  decide

theorem bf4TransmittedRawChordIncidenceDegree_le_five
    {block : Nat} (hblock : block ∈ bf4TransmittedRawChordBlocks) :
    exactSlabBlockIncidenceDegree block ≤ 5 := by
  rw [show bf4TransmittedRawChordBlocks = [11, 3, 6, 23, 42] from rfl]
    at hblock
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
  rcases hblock with rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## 3. Cutoff-one resummed polynomials inherit the five-block bound -/

private theorem zeroEdgeLabelling_mem_bounded_one (ids : List Nat) :
    zeroEdgeLabelling ∈ boundedEdgeLabellings 1 ids := by
  refine boundedEdgeLabellings_complete 1 ids zeroEdgeLabelling ?_ ?_
  · intro _ _
    change 0 < 2
    decide
  · intro _ _
    rfl

private theorem assembledCutoffOne_le_one
    {left boundary right : EdgeLabelling}
    (hleft : left ∈ centralHalfStates 1 0)
    (hboundary : boundary ∈ centralBoundaryChannels 1 0)
    (hright : right ∈ centralHalfStates 1 0) :
    ∀ id, assembleReflectedSlabLabelling 0 left boundary right id ≤ 1 := by
  have hbounded := assembleReflectedSlabLabelling_bounded
    hleft hboundary hright
  intro id
  by_cases hid : id ∈ slabPhysicalFaceEdges (centralExtent 0)
  · exact hbounded id hid
  · rw [assembleReflectedSlabLabelling_zero_off_physical
      0 left boundary right hid]
    decide

private theorem finitePolySum_degreeAtMost
    {Index : Type} {block maxDegree : Nat}
    (polynomial : Index → RatPoly)
    (items : List Index)
    (hdegree : ∀ item, item ∈ items →
      QuaternionBlockDegreeAtMost block maxDegree (polynomial item)) :
      QuaternionBlockDegreeAtMost block maxDegree
        (finitePolySum polynomial items) := by
  induction items with
  | nil => exact quaternionBlockDegreeAtMost_zero block maxDegree
  | cons head tail ih =>
      exact (hdegree head List.mem_cons_self).add
        (ih (fun item hitem =>
          hdegree item (List.mem_cons_of_mem head hitem)))

private theorem exactVacuumRowResummedPolynomial_cutoffOne_rawDegree
    (w : Q') {block : Nat}
    (hblock : block ∈ bf4TransmittedRawChordBlocks) :
    QuaternionBlockDegreeAtMost block 5
      (exactVacuumRowResummedPolynomial w 1) := by
  unfold exactVacuumRowResummedPolynomial
  apply finitePolySum_degreeAtMost
  intro right hright
  apply finitePolySum_degreeAtMost
  intro boundary hboundary
  exact (exactCorrectedSlabWeightedIntegrand_cutoffOne_degreeAtMost
      block w _
      (assembledCutoffOne_le_one
        (zeroEdgeLabelling_mem_bounded_one (centralLowerFaceIds 0))
        hboundary hright)).mono
    (bf4TransmittedRawChordIncidenceDegree_le_five hblock)

private theorem exactConstantMomentResummedPolynomial_cutoffOne_rawDegree
    (w : Q') {block : Nat}
    (hblock : block ∈ bf4TransmittedRawChordBlocks) :
    QuaternionBlockDegreeAtMost block 5
      (exactConstantMomentResummedPolynomial w 1) := by
  unfold exactConstantMomentResummedPolynomial
  apply finitePolySum_degreeAtMost
  intro left hleft
  apply finitePolySum_degreeAtMost
  intro right hright
  apply finitePolySum_degreeAtMost
  intro boundary hboundary
  exact (exactCorrectedSlabWeightedIntegrand_cutoffOne_degreeAtMost
      block w _ (assembledCutoffOne_le_one hleft hboundary hright)).mono
    (bf4TransmittedRawChordIncidenceDegree_le_five hblock)

theorem adaptedVacuumRowResummedPolynomial_cutoffOne_degree_five
    (w : Q') :
    QuaternionBlocksDegreeAtMost bf4TransmittedAdaptedChordBlocks 5
      (adaptBF4RawCarrier (exactVacuumRowResummedPolynomial w 1)) := by
  intro block hblock
  apply applyQuaternionBlockSwapChain_degreeAtMost
    bf4RawCarrierAdaptationSteps
  · rw [bf4TransmittedAdaptedChordBlocks_eq] at hblock
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
    omega
  · apply exactVacuumRowResummedPolynomial_cutoffOne_rawDegree w
    rw [← bf4TransmittedRawChordBlocks_eq_adaptation_sources]
    exact List.mem_map.mpr ⟨block, hblock, rfl⟩

theorem adaptedConstantMomentResummedPolynomial_cutoffOne_degree_five
    (w : Q') :
    QuaternionBlocksDegreeAtMost bf4TransmittedAdaptedChordBlocks 5
      (adaptBF4RawCarrier (exactConstantMomentResummedPolynomial w 1)) := by
  intro block hblock
  apply applyQuaternionBlockSwapChain_degreeAtMost
    bf4RawCarrierAdaptationSteps
  · rw [bf4TransmittedAdaptedChordBlocks_eq] at hblock
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
    omega
  · apply exactConstantMomentResummedPolynomial_cutoffOne_rawDegree w
    rw [← bf4TransmittedRawChordBlocks_eq_adaptation_sources]
    exact List.mem_map.mpr ⟨block, hblock, rfl⟩

/-! ## 4. The exact fivefold based-cycle endpoint -/

def exactVacuumRowBasedCycleFivePolynomialCutoffOne (w : Q') : RatPoly :=
  exactRawTreeGaugeBasedCycleFiveHaarMarginal
    (exactVacuumRowResummedPolynomial w 1)

def exactConstantMomentBasedCycleFivePolynomialCutoffOne
    (w : Q') : RatPoly :=
  exactRawTreeGaugeBasedCycleFiveHaarMarginal
    (exactConstantMomentResummedPolynomial w 1)

theorem exactVacuumRightConstantCrossMoment_cutoffOne_eq_basedCycleFiveHaar
    (w : Q') :
    exactVacuumRightConstantCrossMoment w 1 ≈
      quaternionHaar 5
        (exactVacuumRowBasedCycleFivePolynomialCutoffOne w) := by
  exact Q'.eqv_trans _
    (quaternionHaar 116 (exactVacuumRowResummedPolynomial w 1)) _
    (exactVacuumRightConstantCrossMoment_eq_resummedHaar w 1)
    (quaternionHaar_116_eq_rawTreeGaugeBasedCycleFiveHaarMarginal _
      (exactVacuumRowResummedPolynomial_supported_116 w 1)
      (adaptedVacuumRowResummedPolynomial_cutoffOne_degree_five w))

theorem exactConstantQuadraticMoment_cutoffOne_eq_basedCycleFiveHaar
    (w : Q') :
    exactConstantQuadraticMoment w 1 ≈
      quaternionHaar 5
        (exactConstantMomentBasedCycleFivePolynomialCutoffOne w) := by
  exact Q'.eqv_trans _
    (quaternionHaar 116 (exactConstantMomentResummedPolynomial w 1)) _
    (exactConstantQuadraticMoment_eq_resummedHaar w 1)
    (quaternionHaar_116_eq_rawTreeGaugeBasedCycleFiveHaarMarginal _
      (exactConstantMomentResummedPolynomial_supported_116 w 1)
      (adaptedConstantMomentResummedPolynomial_cutoffOne_degree_five w))

/-- The five surviving Haar variables are exactly the rooted based cycles in
the requested order. -/
theorem cutoffOne_basedCycleFive_order :
    bf4TransmittedCycleTable.map (fun cycle => cycle.val) =
      [0, 4, 5, 6, 10] := by
  rfl

end YMGap.Continuum.BF4ExactCutoffOneTransmittedDegree

#print axioms YMGap.Continuum.BF4ExactCutoffOneTransmittedDegree.bf4TransmittedRawChordIncidenceDegrees_eq
#print axioms YMGap.Continuum.BF4ExactCutoffOneTransmittedDegree.exactCorrectedSlabSpinNetworkIntegrand_cutoffOne_degreeAtMost
#print axioms YMGap.Continuum.BF4ExactCutoffOneTransmittedDegree.adaptedVacuumRowResummedPolynomial_cutoffOne_degree_five
#print axioms YMGap.Continuum.BF4ExactCutoffOneTransmittedDegree.exactVacuumRightConstantCrossMoment_cutoffOne_eq_basedCycleFiveHaar
#print axioms YMGap.Continuum.BF4ExactCutoffOneTransmittedDegree.exactConstantQuadraticMoment_cutoffOne_eq_basedCycleFiveHaar
