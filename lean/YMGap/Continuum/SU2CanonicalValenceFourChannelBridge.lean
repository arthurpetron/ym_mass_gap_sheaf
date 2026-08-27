/-
# From the production valence-four resolver to a physical SU(2) channel

The corrected-slab spin-foam enumerator stores a four-valent link intertwiner
as one auxiliary twice-spin together with the two Boolean fusion checks

  fusionOK a b x,    fusionOK x c d.

The analytic recoupling development instead uses `FixedLeftCGChannel`, whose
data are the two Cayley transvectant orders and their degree equations.  This
module gives the missing constructive change of presentation.  Each accepted
production witness is sent to the channel whose contraction orders are the
explicit `couplingOrder`s; the channel's intermediate degree is proved to be
the production auxiliary label itself.

This is a carrier bridge only.  It does not assert a Gibbs-weight comparison,
an OS form bound, a spectral gap, or a continuum limit.

Constructive contract: Mathlib-free, no choice, no `Classical`, no `sorry`,
and no new axiom.
-/

import YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
import YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
import YMGap.Continuum.SU2TransvectantAdmissibleExtremal

namespace YMGap.Continuum.SU2CanonicalValenceFourChannelBridge

open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2TransvectantAdmissibleExtremal
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness

/-! ## 1. Two fusion witnesses construct the analytic channel -/

/-- The two Boolean SU(2) fusion witnesses determine an explicit
left-associated fixed-output channel. -/
def fixedLeftChannelOfFusion
    (a b c d x : Nat)
    (hinner : fusionOK a b x = true)
    (houter : fusionOK x c d = true) :
    FixedLeftCGChannel a b c d := by
  have hi := fusionOK_couplingOrder_spec a b x hinner
  have ho := fusionOK_couplingOrder_spec x c d houter
  dsimp only at hi ho
  exact
    { k := couplingOrder a b x
      k_le := Nat.le_min.mpr ⟨hi.2.1, hi.2.2.1⟩
      r := couplingOrder x c d
      r_le := by
        apply Nat.le_min.mpr
        constructor
        · have hintermediate :
              a + b - 2 * couplingOrder a b x = x := by
            omega
          simpa only [hintermediate] using ho.2.1
        · exact ho.2.2.1
      degree_eq := by omega }

/-- The constructed analytic channel remembers the production intermediate
twice-spin literally, rather than merely up to a later fusion test. -/
theorem fixedLeftChannelOfFusion_intermediate
    (a b c d x : Nat)
    (hinner : fusionOK a b x = true)
    (houter : fusionOK x c d = true) :
    (fixedLeftChannelOfFusion a b c d x hinner houter).intermediate = x := by
  have hi := fusionOK_couplingOrder_spec a b x hinner
  dsimp only at hi
  change a + b - 2 * couplingOrder a b x = x
  omega

/-! ## 2. The literal canonical four-valent production resolver -/

/-- Public exact expansion of the production resolver at valence four.  The
only free auxiliary coordinate is position five, the intermediate twice-spin
of the left-associated fusion tree. -/
theorem canonicalLinkConditionalAllowedB_four
    (external auxiliary : EdgeLabelling) :
    canonicalLinkConditionalAllowedB 4 external auxiliary =
      (fusionOK (external 0) (external 1) (auxiliary 5) &&
        fusionOK (auxiliary 5) (external 2) (external 3)) := by
  unfold canonicalLinkConditionalAllowedB
  change
    (let label := overlayOn [0, 1, 2, 3] external auxiliary;
      verticesAdmissibleB (fuseLabels 4 5 [0, 1, 2, 3]) label &&
        (canonicalUsedAuxiliaryCoordinates 4).all
          (canonicalAuxiliaryEdgeAllowedB 4 label)) = _
  simp [fuseLabels, fuseChain, verticesAdmissibleB,
    canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    canonicalAuxiliaryEdgeAllowedB, overlayOn]

/-- An accepted canonical four-valent auxiliary labelling becomes the exact
analytic left-associated channel on the four external spins. -/
def fixedLeftChannelOfCanonicalFour
    (external auxiliary : EdgeLabelling)
    (hallowed : canonicalLinkConditionalAllowedB 4 external auxiliary = true) :
    FixedLeftCGChannel
      (external 0) (external 1) (external 2) (external 3) := by
  rw [canonicalLinkConditionalAllowedB_four] at hallowed
  simp only [Bool.and_eq_true] at hallowed
  exact fixedLeftChannelOfFusion
    (external 0) (external 1) (external 2) (external 3) (auxiliary 5)
    hallowed.1 hallowed.2

/-- The canonical auxiliary coordinate five is exactly the channel's
intermediate representation label. -/
theorem fixedLeftChannelOfCanonicalFour_intermediate
    (external auxiliary : EdgeLabelling)
    (hallowed : canonicalLinkConditionalAllowedB 4 external auxiliary = true) :
    (fixedLeftChannelOfCanonicalFour external auxiliary hallowed).intermediate =
      auxiliary 5 := by
  rw [canonicalLinkConditionalAllowedB_four] at hallowed
  simp only [Bool.and_eq_true] at hallowed
  exact fixedLeftChannelOfFusion_intermediate
    (external 0) (external 1) (external 2) (external 3) (auxiliary 5)
    hallowed.1 hallowed.2

/-! ## 3. An actual corrected-slab link witness -/

/-- Membership in the production witness list exposes its Boolean resolver
certificate. -/
theorem slabLinkFusionWitness_allowed
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link) :
    canonicalLinkConditionalAllowedB
      (slabIncidentPlaqIds extent link).length
      (slabLinkExternalSpins extent physical link) auxiliary = true := by
  unfold slabLinkFusionWitnesses at hmem
  exact (List.mem_filter.mp hmem).2

/-- Every accepted production witness at an actual valence-four slab link
constructs the analytic channel required by physical Schur recoupling. -/
def fixedLeftChannelOfSlabValenceFour
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hdegree : (slabIncidentPlaqIds extent link).length = 4)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link) :
    FixedLeftCGChannel
      ((slabLinkExternalSpins extent physical link) 0)
      ((slabLinkExternalSpins extent physical link) 1)
      ((slabLinkExternalSpins extent physical link) 2)
      ((slabLinkExternalSpins extent physical link) 3) := by
  have hallowed := slabLinkFusionWitness_allowed
    K extent physical link auxiliary hmem
  rw [hdegree] at hallowed
  exact fixedLeftChannelOfCanonicalFour
    (slabLinkExternalSpins extent physical link) auxiliary hallowed

/-- The analytic channel extracted from an actual slab witness retains the
production auxiliary label at coordinate five. -/
theorem fixedLeftChannelOfSlabValenceFour_intermediate
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hdegree : (slabIncidentPlaqIds extent link).length = 4)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link) :
    (fixedLeftChannelOfSlabValenceFour
      K extent physical link auxiliary hdegree hmem).intermediate = auxiliary 5 := by
  have hallowed := slabLinkFusionWitness_allowed
    K extent physical link auxiliary hmem
  rw [hdegree] at hallowed
  exact fixedLeftChannelOfCanonicalFour_intermediate
    (slabLinkExternalSpins extent physical link) auxiliary hallowed

#print axioms fixedLeftChannelOfFusion
#print axioms fixedLeftChannelOfFusion_intermediate
#print axioms canonicalLinkConditionalAllowedB_four
#print axioms fixedLeftChannelOfCanonicalFour
#print axioms fixedLeftChannelOfCanonicalFour_intermediate
#print axioms slabLinkFusionWitness_allowed
#print axioms fixedLeftChannelOfSlabValenceFour
#print axioms fixedLeftChannelOfSlabValenceFour_intermediate

end YMGap.Continuum.SU2CanonicalValenceFourChannelBridge
