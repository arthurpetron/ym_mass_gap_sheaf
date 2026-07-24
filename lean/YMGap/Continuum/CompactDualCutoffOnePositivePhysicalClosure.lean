/-
# Positive cutoff-one Gibbs terms are closed cellular surfaces

The cutoff-one whole-slab parity target previously required even incidence
of the fine odd-spin support as an explicit hypothesis.  Here that
hypothesis is derived from the actual corrected-slab physical Gibbs term.

A cutoff-one listed physical labelling is exactly the zero-one indicator of
its geometric odd-spin support.  Strict positivity of its physical term
forces the complete product of SU(2) link multiplicities to be nonzero, hence
every corrected-slab link multiplicity is nonzero.  The production parity
selection rule then forbids odd incidence at every such link.  Links outside
the corrected slab have zero incidence directly.

Thus every strictly positive cutoff-one physical Gibbs summand supplies the
globally coherent coarse parity target constructed in
`CompactDualCutoffOneParitySlabTarget`.

## Axiom gate

Finite list algebra and the audited production multiplicities only.  No
`Classical.*`, `sorry`, `native_decide`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.CompactDualCutoffOneParitySlabTarget

namespace YMGap.Continuum.CompactDualCutoffOnePositivePhysicalClosure

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualCutoffOneParitySlabTarget
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4UnitCubeIncidenceParity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A listed cutoff-one state is its binary geometric support -/

theorem listIndexOf_slabPlaquetteAt
    {extent id : Nat} (hid : id ∈ slabPhysicalFaceEdges extent) :
    listIndexOf (slabPlaquetteAt extent id)
        (boundaryCompleteSlabPlaquettes extent) = id := by
  have hplaquette := slabPlaquetteAt_mem hid
  have hindexPhysical :
      listIndexOf (slabPlaquetteAt extent id)
          (boundaryCompleteSlabPlaquettes extent) ∈
        slabPhysicalFaceEdges extent := by
    unfold slabPhysicalFaceEdges
    exact List.mem_range.mpr
      (listIndexOf_lt_of_mem
        (slabPlaquetteAt extent id)
        (boundaryCompleteSlabPlaquettes extent) hplaquette)
  apply slabPlaquetteAt_injective_on_physical hindexPhysical hid
  unfold slabPlaquetteAt
  exact getD_listIndexOf_of_mem fallbackPlaquette
    (slabPlaquetteAt extent id)
    (boundaryCompleteSlabPlaquettes extent) hplaquette

theorem slabSpinAtPlaquette_slabPlaquetteAt
    (extent : Nat) (physical : EdgeLabelling)
    {id : Nat} (hid : id ∈ slabPhysicalFaceEdges extent) :
    slabSpinAtPlaquette extent physical (slabPlaquetteAt extent id) =
      physical id := by
  rw [slabSpinAtPlaquette_eq_of_mem (slabPlaquetteAt_mem hid)]
  rw [listIndexOf_slabPlaquetteAt hid]

theorem cutoffOneFineState_eq_oddSupportLabelling
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    {fineState : EdgeLabelling}
    (hfineMem : fineState ∈ S.fine.physicalLabellings) :
    fineState =
      slabBinarySupportLabelling S.fine.extent
        (fineOddSlabSupport S fineState) := by
  funext id
  by_cases hid : id ∈ slabPhysicalFaceEdges S.fine.extent
  · have hbound :=
      (boundedEdgeLabellings_sound
        S.fine.cutoff (slabPhysicalFaceEdges S.fine.extent)
        fineState hfineMem).1 id hid
    rw [hfineCutoff] at hbound
    have hsupport :
        slabPlaquetteAt S.fine.extent id ∈ fineOddSlabSupport S fineState ↔
          fineState id % 2 = 1 := by
      unfold fineOddSlabSupport
      simp only [List.mem_filter, slabPlaquetteAt_mem hid,
        decide_eq_true_eq, true_and]
      rw [slabSpinAtPlaquette_slabPlaquetteAt S.fine.extent fineState hid]
    rw [slabBinarySupportLabelling_eq_indicator hid]
    by_cases hodd : fineState id % 2 = 1
    · rw [if_pos (hsupport.mpr hodd)]
      omega
    · rw [if_neg (fun hmem => hodd (hsupport.mp hmem))]
      have hmodLt : fineState id % 2 < 2 :=
        Nat.mod_lt _ (by omega)
      omega
  · rw [slabBinarySupportLabelling_eq_zero_of_not_physical hid]
    exact (boundedEdgeLabellings_sound
      S.fine.cutoff (slabPhysicalFaceEdges S.fine.extent)
      fineState hfineMem).2 id hid

/-! ## 2. Positive physical mass forces every local multiplicity nonzero -/

private theorem pos_not_eqv_zero {a : Q'} (ha : (0 : Q') < a) :
    ¬ a ≈ 0 := by
  intro hzero
  exact (Int.not_lt_of_ge (Q'.le_of_eqv hzero)) ha

theorem positivePhysicalTerm_linkProduct_ne_zero
    (D : SlabPhysicalData) (physical : EdgeLabelling)
    (hpositive : (0 : Q') < D.physicalTerm physical) :
    slabExplicitLinkMultiplicityProduct
        D.cutoff D.extent physical ≠ 0 := by
  intro hzero
  have htermZero : D.physicalTerm physical ≈ 0 := by
    unfold SlabPhysicalData.physicalTerm slabParametricKPhysicalTerm
    rw [hzero]
    exact Q'.mul_zero_eqv _
  exact (pos_not_eqv_zero hpositive) htermZero

private theorem natListProduct_member_ne_zero {A : Type}
    (value : A → Nat) :
    ∀ {xs : List A}, natListProduct value xs ≠ 0 →
      ∀ {x : A}, x ∈ xs → value x ≠ 0
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hproduct, x, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · intro hzero
        apply hproduct
        simp [natListProduct, hzero]
      · apply natListProduct_member_ne_zero value
          (xs := tail) (x := x)
        · intro htailZero
          apply hproduct
          simp [natListProduct, htailZero]
        · exact htail

theorem positivePhysicalTerm_localMultiplicity_ne_zero
    (D : SlabPhysicalData) (physical : EdgeLabelling)
    (hpositive : (0 : Q') < D.physicalTerm physical)
    {link : Z4Link}
    (hlink : link ∈ boundaryCompleteSlabLinks D.extent) :
    slabExplicitLinkMultiplicity
        D.cutoff D.extent physical link ≠ 0 := by
  apply natListProduct_member_ne_zero
    (slabExplicitLinkMultiplicity D.cutoff D.extent physical)
    (positivePhysicalTerm_linkProduct_ne_zero D physical hpositive)
    hlink

/-! ## 3. The physical positivity constraint closes the fine surface -/

private theorem faceIncidenceCount_eq_zero_of_no_incidence
    (link : Z4Link) :
    ∀ support : List Z4Plaq,
      (∀ plaquette, plaquette ∈ support → link ∉ edgesOf plaquette) →
        faceIncidenceCount link support = 0
  | [], _ => rfl
  | head :: tail, hnone => by
      have hhead := hnone head List.mem_cons_self
      have htail : ∀ plaquette, plaquette ∈ tail →
          link ∉ edgesOf plaquette :=
        fun plaquette hmem =>
          hnone plaquette (List.mem_cons_of_mem head hmem)
      simp [faceIncidenceCount, hhead,
        faceIncidenceCount_eq_zero_of_no_incidence link tail htail]

theorem positiveCutoffOnePhysicalTerm_fineOddSupport_even
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    {fineState : EdgeLabelling}
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState) :
    EvenFaceIncidence (fineOddSlabSupport S fineState) := by
  intro link
  by_cases hlink :
      link ∈ boundaryCompleteSlabLinks S.fine.extent
  · have hlocal :=
      positivePhysicalTerm_localMultiplicity_ne_zero
        S.fine fineState hpositive hlink
    have hstate :=
      cutoffOneFineState_eq_oddSupportLabelling hfineCutoff hfineMem
    have hsum :=
      slabBinarySupport_localExternalSpinSum
        (fun _ hmem => fineOddSlabSupport_subset hmem)
        (fineOddSlabSupport_nodup S fineState) link
    rw [← hstate] at hsum
    have hnotOdd :
        faceIncidenceCount link (fineOddSlabSupport S fineState) % 2 ≠ 1 := by
      intro hodd
      apply hlocal
      unfold slabExplicitLinkMultiplicity
      apply explicitValenceMultiplicity_eq_zero_of_odd_sum
      · simpa only [List.length_map] using
          slabIncidentPlaqIds_length_le_six S.fine.extent link
      · rw [List.length_map]
        rw [hsum]
        exact hodd
    have hlt :
        faceIncidenceCount link (fineOddSlabSupport S fineState) % 2 < 2 :=
      Nat.mod_lt _ (by omega)
    omega
  · rw [faceIncidenceCount_eq_zero_of_no_incidence]
    intro plaquette hmem hincident
    apply hlink
    exact (mem_boundaryCompleteSlabLinks_iff
      S.fine.extent link).mpr
        ⟨plaquette, fineOddSlabSupport_subset hmem, hincident⟩

/-! ## 4. Every positive cutoff-one Gibbs source reaches the coherent row -/

structure CutoffOnePositivePhysicalSource (S : SlabScalePair) : Type where
  fineState : EdgeLabelling
  fine_mem : fineState ∈ S.fine.physicalLabellings
  fine_cutoff : S.fine.cutoff = 1
  fine_positive : (0 : Q') < S.fine.physicalTerm fineState
  coarse_coupling_positive : (0 : Q') < S.coarse.coupling

def CutoffOnePositivePhysicalSource.toEvenSlabSource
    {S : SlabScalePair} (source : CutoffOnePositivePhysicalSource S) :
    CutoffOneEvenSlabSource S where
  fineState := source.fineState
  fine_mem := source.fine_mem
  fine_cutoff := source.fine_cutoff
  fineOddSupport_even :=
    positiveCutoffOnePhysicalTerm_fineOddSupport_even
      source.fine_cutoff source.fine_mem source.fine_positive
  coarse_coupling_positive := source.coarse_coupling_positive

def CutoffOnePositivePhysicalSource.toCoherentSlabRecouplingSource
    {S : SlabScalePair} (source : CutoffOnePositivePhysicalSource S) :
    CoherentSlabRecouplingSource S :=
  source.toEvenSlabSource.toCoherentSlabRecouplingSource

theorem cutoffOnePositivePhysicalSource_row_normalized
    {S : SlabScalePair} (source : CutoffOnePositivePhysicalSource S) :
    listQSum
        (wholeSlabRecouplingConditionalKernel
          source.toCoherentSlabRecouplingSource)
        S.coarse.physicalLabellings ≈ 1 := by
  exact cutoffOneWholeSlabConditionalKernel_row_normalized
    source.toEvenSlabSource

#print axioms listIndexOf_slabPlaquetteAt
#print axioms slabSpinAtPlaquette_slabPlaquetteAt
#print axioms cutoffOneFineState_eq_oddSupportLabelling
#print axioms positivePhysicalTerm_linkProduct_ne_zero
#print axioms positivePhysicalTerm_localMultiplicity_ne_zero
#print axioms positiveCutoffOnePhysicalTerm_fineOddSupport_even
#print axioms CutoffOnePositivePhysicalSource.toEvenSlabSource
#print axioms CutoffOnePositivePhysicalSource.toCoherentSlabRecouplingSource
#print axioms cutoffOnePositivePhysicalSource_row_normalized

end YMGap.Continuum.CompactDualCutoffOnePositivePhysicalClosure
