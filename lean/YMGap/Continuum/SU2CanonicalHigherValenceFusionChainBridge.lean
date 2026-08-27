/-
# Production valence-five and valence-six SU(2) fusion chains

Interior links of the four-dimensional cubical lattice have six incident
plaquettes.  A four-valent recoupling carrier therefore covers only a proper
boundary case.  The production resolver represents the higher-valence link
by a left-associated sequence of auxiliary twice-spins.

This module turns every accepted valence-five or valence-six production
witness into an explicit analytic Cayley chain.  Each trivalent step stores
its constructive transvectant order, its two physical bounds, and its exact
output-degree equation.  Every internal output is definitionally the same
auxiliary coordinate used by the production enumerator.

The first two steps also produce the `FixedLeftCGChannel` consumed by the
physical Schur kernel.  Iterating that kernel through the remaining steps is
left to the next module.

Constructive contract: Mathlib-free natural arithmetic and Boolean fusion
certificates, no choice, no `Classical`, no `sorry`, and no new axiom.
-/

import YMGap.Continuum.SU2CanonicalValenceFourChannelBridge

namespace YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge

open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.SU2CanonicalValenceFourChannelBridge
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2TransvectantAdmissibleExtremal
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. One analytic trivalent fusion step -/

/-- A proof-carrying Cayley transvectant step from input degrees `a,b` to
output degree `c`. -/
structure CGFusionStep (a b c : Nat) where
  order : Nat
  order_le : order ≤ min a b
  output_eq : a + b - 2 * order = c

/-- The Boolean production fusion certificate determines its analytic
transvectant step constructively. -/
def cgFusionStepOfFusionOK (a b c : Nat)
    (h : fusionOK a b c = true) : CGFusionStep a b c := by
  have hs := fusionOK_couplingOrder_spec a b c h
  dsimp only at hs
  exact
    { order := couplingOrder a b c
      order_le := Nat.le_min.mpr ⟨hs.2.1, hs.2.2.1⟩
      output_eq := by omega }

theorem cgFusionStepOfFusionOK_order (a b c : Nat)
    (h : fusionOK a b c = true) :
    (cgFusionStepOfFusionOK a b c h).order = couplingOrder a b c := rfl

/-- Conversely, the proof-carrying analytic step recovers the exact
production fusion guard. -/
theorem CGFusionStep.fusionOK {a b c : Nat} (step : CGFusionStep a b c) :
    fusionOK a b c = true := by
  apply (YMGap.Continuum.FusionBratteli.fusionOK_iff_ladder a b c).mpr
  have horder := Nat.le_min.mp step.order_le
  have htwice : 2 * step.order ≤ a + b := by omega
  have houtput := step.output_eq
  exact ⟨step.order, horder.1, horder.2, by omega⟩

/-! ## 2. Specialized higher-valence left chains -/

/-- Left-associated four-input/five-valent production chain:
`a,b -> x`, `x,c -> y`, `y,d -> e`. -/
structure FixedLeftCGValenceFive (a b c d e : Nat) where
  x : Nat
  y : Nat
  first : CGFusionStep a b x
  second : CGFusionStep x c y
  third : CGFusionStep y d e

/-- Left-associated five-input/six-valent production chain:
`a,b -> x`, `x,c -> y`, `y,d -> z`, `z,e -> f`. -/
structure FixedLeftCGValenceSix (a b c d e f : Nat) where
  x : Nat
  y : Nat
  z : Nat
  first : CGFusionStep a b x
  second : CGFusionStep x c y
  third : CGFusionStep y d z
  fourth : CGFusionStep z e f

/-- The first two steps of a five-valent chain are exactly a physical Schur
left channel with final degree `y`. -/
def FixedLeftCGValenceFive.prefixChannel {a b c d e : Nat}
    (chain : FixedLeftCGValenceFive a b c d e) :
    FixedLeftCGChannel a b c chain.y :=
  fixedLeftChannelOfFusion a b c chain.y chain.x
    chain.first.fusionOK chain.second.fusionOK

theorem FixedLeftCGValenceFive.prefixChannel_intermediate
    {a b c d e : Nat} (chain : FixedLeftCGValenceFive a b c d e) :
    chain.prefixChannel.intermediate = chain.x := by
  exact fixedLeftChannelOfFusion_intermediate a b c chain.y chain.x
    chain.first.fusionOK chain.second.fusionOK

/-- The corresponding first Schur window of a six-valent chain. -/
def FixedLeftCGValenceSix.prefixChannel {a b c d e f : Nat}
    (chain : FixedLeftCGValenceSix a b c d e f) :
    FixedLeftCGChannel a b c chain.y :=
  fixedLeftChannelOfFusion a b c chain.y chain.x
    chain.first.fusionOK chain.second.fusionOK

theorem FixedLeftCGValenceSix.prefixChannel_intermediate
    {a b c d e f : Nat} (chain : FixedLeftCGValenceSix a b c d e f) :
    chain.prefixChannel.intermediate = chain.x := by
  exact fixedLeftChannelOfFusion_intermediate a b c chain.y chain.x
    chain.first.fusionOK chain.second.fusionOK

/-! ## 3. Public expansions of the production resolver -/

theorem canonicalLinkConditionalAllowedB_five
    (external auxiliary : EdgeLabelling) :
    canonicalLinkConditionalAllowedB 5 external auxiliary =
      (fusionOK (external 0) (external 1) (auxiliary 6) &&
        (fusionOK (auxiliary 6) (external 2) (auxiliary 7) &&
          fusionOK (auxiliary 7) (external 3) (external 4))) := by
  unfold canonicalLinkConditionalAllowedB
  change
    (let label := overlayOn [0, 1, 2, 3, 4] external auxiliary;
      verticesAdmissibleB (fuseLabels 5 6 [0, 1, 2, 3, 4]) label &&
        (canonicalUsedAuxiliaryCoordinates 5).all
          (canonicalAuxiliaryEdgeAllowedB 5 label)) = _
  simp [fuseLabels, fuseChain, verticesAdmissibleB,
    canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    canonicalAuxiliaryEdgeAllowedB, overlayOn]

theorem canonicalLinkConditionalAllowedB_six
    (external auxiliary : EdgeLabelling) :
    canonicalLinkConditionalAllowedB 6 external auxiliary =
      (fusionOK (external 0) (external 1) (auxiliary 7) &&
        (fusionOK (auxiliary 7) (external 2) (auxiliary 8) &&
          (fusionOK (auxiliary 8) (external 3) (auxiliary 9) &&
            fusionOK (auxiliary 9) (external 4) (external 5)))) := by
  unfold canonicalLinkConditionalAllowedB
  change
    (let label := overlayOn [0, 1, 2, 3, 4, 5] external auxiliary;
      verticesAdmissibleB (fuseLabels 6 7 [0, 1, 2, 3, 4, 5]) label &&
        (canonicalUsedAuxiliaryCoordinates 6).all
          (canonicalAuxiliaryEdgeAllowedB 6 label)) = _
  simp [fuseLabels, fuseChain, verticesAdmissibleB,
    canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    canonicalAuxiliaryEdgeAllowedB, overlayOn]

/-! ## 4. Canonical accepted witnesses construct the full chains -/

def fixedLeftCGValenceFiveOfCanonical
    (external auxiliary : EdgeLabelling)
    (hallowed : canonicalLinkConditionalAllowedB 5 external auxiliary = true) :
    FixedLeftCGValenceFive
      (external 0) (external 1) (external 2) (external 3) (external 4) := by
  rw [canonicalLinkConditionalAllowedB_five] at hallowed
  simp only [Bool.and_eq_true] at hallowed
  exact
    { x := auxiliary 6
      y := auxiliary 7
      first := cgFusionStepOfFusionOK _ _ _ hallowed.1
      second := cgFusionStepOfFusionOK _ _ _ hallowed.2.1
      third := cgFusionStepOfFusionOK _ _ _ hallowed.2.2 }

def fixedLeftCGValenceSixOfCanonical
    (external auxiliary : EdgeLabelling)
    (hallowed : canonicalLinkConditionalAllowedB 6 external auxiliary = true) :
    FixedLeftCGValenceSix
      (external 0) (external 1) (external 2) (external 3)
      (external 4) (external 5) := by
  rw [canonicalLinkConditionalAllowedB_six] at hallowed
  simp only [Bool.and_eq_true] at hallowed
  exact
    { x := auxiliary 7
      y := auxiliary 8
      z := auxiliary 9
      first := cgFusionStepOfFusionOK _ _ _ hallowed.1
      second := cgFusionStepOfFusionOK _ _ _ hallowed.2.1
      third := cgFusionStepOfFusionOK _ _ _ hallowed.2.2.1
      fourth := cgFusionStepOfFusionOK _ _ _ hallowed.2.2.2 }

theorem fixedLeftCGValenceFiveOfCanonical_labels
    (external auxiliary : EdgeLabelling)
    (hallowed : canonicalLinkConditionalAllowedB 5 external auxiliary = true) :
    let chain := fixedLeftCGValenceFiveOfCanonical external auxiliary hallowed
    chain.x = auxiliary 6 ∧ chain.y = auxiliary 7 := by
  exact ⟨rfl, rfl⟩

theorem fixedLeftCGValenceSixOfCanonical_labels
    (external auxiliary : EdgeLabelling)
    (hallowed : canonicalLinkConditionalAllowedB 6 external auxiliary = true) :
    let chain := fixedLeftCGValenceSixOfCanonical external auxiliary hallowed
    chain.x = auxiliary 7 ∧ chain.y = auxiliary 8 ∧
      chain.z = auxiliary 9 := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## 5. Actual corrected-slab higher-valence witnesses -/

def fixedLeftCGValenceFiveOfSlab
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hdegree : (slabIncidentPlaqIds extent link).length = 5)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link) :
    FixedLeftCGValenceFive
      ((slabLinkExternalSpins extent physical link) 0)
      ((slabLinkExternalSpins extent physical link) 1)
      ((slabLinkExternalSpins extent physical link) 2)
      ((slabLinkExternalSpins extent physical link) 3)
      ((slabLinkExternalSpins extent physical link) 4) := by
  have hallowed := slabLinkFusionWitness_allowed
    K extent physical link auxiliary hmem
  rw [hdegree] at hallowed
  exact fixedLeftCGValenceFiveOfCanonical
    (slabLinkExternalSpins extent physical link) auxiliary hallowed

def fixedLeftCGValenceSixOfSlab
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hdegree : (slabIncidentPlaqIds extent link).length = 6)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link) :
    FixedLeftCGValenceSix
      ((slabLinkExternalSpins extent physical link) 0)
      ((slabLinkExternalSpins extent physical link) 1)
      ((slabLinkExternalSpins extent physical link) 2)
      ((slabLinkExternalSpins extent physical link) 3)
      ((slabLinkExternalSpins extent physical link) 4)
      ((slabLinkExternalSpins extent physical link) 5) := by
  have hallowed := slabLinkFusionWitness_allowed
    K extent physical link auxiliary hmem
  rw [hdegree] at hallowed
  exact fixedLeftCGValenceSixOfCanonical
    (slabLinkExternalSpins extent physical link) auxiliary hallowed

theorem fixedLeftCGValenceFiveOfSlab_labels
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hdegree : (slabIncidentPlaqIds extent link).length = 5)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link) :
    let chain := fixedLeftCGValenceFiveOfSlab
      K extent physical link auxiliary hdegree hmem
    chain.x = auxiliary 6 ∧ chain.y = auxiliary 7 := by
  exact ⟨rfl, rfl⟩

theorem fixedLeftCGValenceSixOfSlab_labels
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hdegree : (slabIncidentPlaqIds extent link).length = 6)
    (hmem : auxiliary ∈ slabLinkFusionWitnesses K extent physical link) :
    let chain := fixedLeftCGValenceSixOfSlab
      K extent physical link auxiliary hdegree hmem
    chain.x = auxiliary 7 ∧ chain.y = auxiliary 8 ∧
      chain.z = auxiliary 9 := by
  exact ⟨rfl, rfl, rfl⟩

#print axioms cgFusionStepOfFusionOK
#print axioms CGFusionStep.fusionOK
#print axioms FixedLeftCGValenceFive.prefixChannel
#print axioms FixedLeftCGValenceFive.prefixChannel_intermediate
#print axioms FixedLeftCGValenceSix.prefixChannel
#print axioms FixedLeftCGValenceSix.prefixChannel_intermediate
#print axioms canonicalLinkConditionalAllowedB_five
#print axioms canonicalLinkConditionalAllowedB_six
#print axioms fixedLeftCGValenceFiveOfCanonical
#print axioms fixedLeftCGValenceSixOfCanonical
#print axioms fixedLeftCGValenceFiveOfCanonical_labels
#print axioms fixedLeftCGValenceSixOfCanonical_labels
#print axioms fixedLeftCGValenceFiveOfSlab
#print axioms fixedLeftCGValenceSixOfSlab
#print axioms fixedLeftCGValenceFiveOfSlab_labels
#print axioms fixedLeftCGValenceSixOfSlab_labels

end YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
