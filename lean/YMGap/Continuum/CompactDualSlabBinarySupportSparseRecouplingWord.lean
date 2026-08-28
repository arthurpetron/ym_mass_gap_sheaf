/-
# Binary surface incidence supplies the sparse recoupling word

The binary-support geometry already proves that the numerical external-spin
sum at a corrected-slab link equals the support's geometric face-incidence
count.  This module packages that equality with the pointwise zero-one bound.
Whenever a link meets the support at most twice, its production external word
is exactly a `SparseFundamentalWord` and hence its higher-valence recoupling
coordinate is deterministic.

This is the direct geometry-to-representation-theory bridge for every
non-pivot link of a prospective switching surface.  It does not construct the
surface or identify its unique four-incidence pivot.

Constructive contract: finite-list membership and exact natural arithmetic
only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or enlarged heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
import YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity

namespace YMGap.Continuum.CompactDualSlabBinarySupportSparseRecouplingWord

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4UnitCubeIncidenceParity

/-- A binary geometric support with incidence at most two at a displayed link
produces a literal sparse fundamental recoupling word at that link. -/
theorem slabBinarySupport_sparseFundamentalWord
    {extent : Nat} {support : List Z4Plaq}
    (hsubset : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boundaryCompleteSlabPlaquettes extent)
    (hsupport : support.Nodup) (heven : EvenFaceIncidence support)
    (link : Z4Link)
    (hincidence : faceIncidenceCount link support ≤ 2) :
    SparseFundamentalWord
      (slabIncidentPlaqIds extent link).length
      (slabLinkExternalSpins extent
        (slabBinarySupportLabelling extent support) link) := by
  constructor
  · intro position hposition
    let spins :=
      (slabIncidentPlaqIds extent link).map
        (slabBinarySupportLabelling extent support)
    have hposition' : position < spins.length := by
      simpa only [spins, List.length_map] using hposition
    change spins.getD position 0 ≤ 1
    rw [← List.getElem_eq_getD (l := spins)
      (i := position) (h := hposition') 0]
    have hmem : spins[position] ∈ spins := List.getElem_mem hposition'
    obtain ⟨id, _, hvalue⟩ := List.mem_map.mp hmem
    rw [← hvalue]
    exact slabBinarySupportLabelling_le_one extent support id
  · unfold slabLinkExternalSpins
    rw [slabBinarySupport_localExternalSpinSum hsubset hsupport link]
    generalize hcount : faceIncidenceCount link support = count at hincidence ⊢
    have hparity := heven link
    rw [hcount] at hparity
    cases count with
    | zero => exact Or.inl rfl
    | succ remainder =>
      cases remainder with
      | zero => omega
      | succ tail =>
        have htail : tail = 0 := by omega
        subst tail
        exact Or.inr rfl

end YMGap.Continuum.CompactDualSlabBinarySupportSparseRecouplingWord

#print axioms YMGap.Continuum.CompactDualSlabBinarySupportSparseRecouplingWord.slabBinarySupport_sparseFundamentalWord
