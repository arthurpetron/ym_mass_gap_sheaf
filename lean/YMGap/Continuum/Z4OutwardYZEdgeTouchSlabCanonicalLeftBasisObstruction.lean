/-
# Exhaustion of the outward Y/Z canonical-left pivot basis

The outward Y/Z cut meets its unique degree-five pivot in physical side order
`Z,Y,Y,Z,0`.  The local production carrier is
`ValenceFiveLeftCarrier 1 1 1 1 0`.  This file classifies that carrier exactly:
there are only two canonical-left fusion states.

Their already compiled terminal pairings are respectively

* `0 <-> 2` and `1 <-> 3`,
* `0 <-> 1` and `2 <-> 3`.

Every one of these edges crosses from the Y side to the Z side in the literal
pivot ordering.  Thus the native right-tree pairing `0 <-> 3`, `1 <-> 2` is
not merely different from the previously chosen equal-rank representative:
it is absent from the entire canonical-left local carrier.

Constructive contract: finite carrier exhaustion and the previously checked
terminal paths only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNativeRightPairing

namespace YMGap.Continuum.Z4OutwardYZEdgeTouchSlabCanonicalLeftBasisObstruction

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Continuum.CanonicalLinkPhysicalTerminalPartner
open YMGap.Continuum.CanonicalLinkStrandStep
open YMGap.Continuum.CanonicalLinkStrandTerminal
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2CanonicalLeftCarrierWitnessReconstruction
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNativeRightPairing
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabWholeProductPositivity

/-! ## 1. The canonical-left carrier has exactly two members -/

/-- Exhaustion of the proof-carrying canonical-left carrier at external word
`[1,1,1,1,0]`. -/
theorem outwardYZPivotLeftCarrier_eq_first_or_second
    (source : ValenceFiveLeftCarrier 1 1 1 1 0) :
    source = outwardYZPivotLeftSource ∨
      source = outwardYZPivotNativeRightAsLeftSource := by
  rcases source with ⟨y, first, suffix⟩
  rcases first with ⟨k, hk, r, hr, hdegree⟩
  rcases suffix with ⟨order, horder, houtput⟩
  have hy : y = 1 := by omega
  subst y
  have hkCases : k = 0 ∨ k = 1 := by omega
  rcases hkCases with hkZero | hkOne
  · subst k
    have hrOne : r = 1 := by omega
    subst r
    have horderOne : order = 1 := by omega
    subst order
    exact Or.inl rfl
  · subst k
    have hrZero : r = 0 := by omega
    subst r
    have horderOne : order = 1 := by omega
    subst order
    exact Or.inr rfl

/-! ## 2. Resolve an arbitrary carrier in the production basis -/

def outwardYZPivotLeftAuxiliaryOfCarrier
    (source : ValenceFiveLeftCarrier 1 1 1 1 0) : SlabLabelling :=
  valenceFiveLeftAuxiliary source

theorem outwardYZPivotLeftAuxiliaryOfCarrier_mem
    (source : ValenceFiveLeftCarrier 1 1 1 1 0) :
    outwardYZPivotLeftAuxiliaryOfCarrier source ∈
      slabLinkFusionWitnesses 1 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot :=
  valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
    outwardYZSwitchLeftPhysical_bounded
    outwardYZSwitchPivot_degree_five source

def outwardYZPivotLeftAllowedOfCarrier
    (source : ValenceFiveLeftCarrier 1 1 1 1 0) :
    YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
      5
      (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot)
      (outwardYZPivotLeftAuxiliaryOfCarrier source) = true :=
  slabLinkFusionWitness_mem_allowed 1 5 outwardYZSwitchLeftPhysical
    outwardYZSwitchPivot (outwardYZPivotLeftAuxiliaryOfCarrier source)
      (outwardYZPivotLeftAuxiliaryOfCarrier_mem source)

def outwardYZPivotCanonicalPhysicalTerminalsOfCarrier
    (source : ValenceFiveLeftCarrier 1 1 1 1 0) :
    List (CanonicalPhysicalStrandPort
      (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot)
      (outwardYZPivotLeftAuxiliaryOfCarrier source)
      (outwardYZPivotLeftAllowedOfCarrier source)) :=
  (allResolvedNetworkPorts
    (canonicalLinkResolvedStrandNetwork 5
      (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot)
      (outwardYZPivotLeftAuxiliaryOfCarrier source)
      (outwardYZPivotLeftAllowedOfCarrier source))).filterMap
        fun occurrence =>
          if hphysical : occurrence.edgeId < 5 then
            some ⟨occurrence, hphysical⟩
          else none

def outwardYZPivotCanonicalEdgeIdPairsOfCarrier
    (source : ValenceFiveLeftCarrier 1 1 1 1 0) : List (Nat × Nat) :=
  (outwardYZPivotCanonicalPhysicalTerminalsOfCarrier source).map
    fun terminal =>
      (terminal.1.edgeId,
        (canonicalPhysicalStrandPartner outwardYZPivot_degree_le
          (outwardYZPivotLeftAllowedOfCarrier source) terminal).1.edgeId)

/-- Every canonical-left carrier realizes one of the two previously compiled
pair lists. -/
theorem outwardYZPivotCanonicalEdgeIdPairsOfCarrier_cases
    (source : ValenceFiveLeftCarrier 1 1 1 1 0) :
    outwardYZPivotCanonicalEdgeIdPairsOfCarrier source =
        [(0, 2), (1, 3), (2, 0), (3, 1)] ∨
      outwardYZPivotCanonicalEdgeIdPairsOfCarrier source =
        [(0, 1), (1, 0), (2, 3), (3, 2)] := by
  rcases outwardYZPivotLeftCarrier_eq_first_or_second source with
      hfirst | hsecond
  · subst source
    apply Or.inl
    simpa only [outwardYZPivotCanonicalEdgeIdPairsOfCarrier,
      outwardYZPivotCanonicalPhysicalTerminalsOfCarrier,
      outwardYZPivotLeftAuxiliaryOfCarrier]
      using outwardYZPivotCanonicalEdgeIdPairs_eq
  · subst source
    apply Or.inr
    simpa only [outwardYZPivotCanonicalEdgeIdPairsOfCarrier,
      outwardYZPivotCanonicalPhysicalTerminalsOfCarrier,
      outwardYZPivotLeftAuxiliaryOfCarrier]
      using outwardYZPivotNativeRightCanonicalEdgeIdPairs_eq

/-! ## 3. Both complete pairings cross the geometric cut -/

def outwardYZPivotYSideB (position : Nat) : Bool :=
  position == 1 || position == 2

def outwardYZPivotPairCrossesCutB (pair : Nat × Nat) : Bool :=
  outwardYZPivotYSideB pair.1 != outwardYZPivotYSideB pair.2

private theorem firstPairing_crosses
    (pair : Nat × Nat)
    (hpair : pair ∈ [(0, 2), (1, 3), (2, 0), (3, 1)]) :
    outwardYZPivotPairCrossesCutB pair = true := by
  rcases List.mem_cons.mp hpair with rfl | hpair
  · decide
  rcases List.mem_cons.mp hpair with rfl | hpair
  · decide
  rcases List.mem_cons.mp hpair with rfl | hpair
  · decide
  rcases List.mem_cons.mp hpair with rfl | hpair
  · decide
  exact False.elim (List.not_mem_nil hpair)

private theorem secondPairing_crosses
    (pair : Nat × Nat)
    (hpair : pair ∈ [(0, 1), (1, 0), (2, 3), (3, 2)]) :
    outwardYZPivotPairCrossesCutB pair = true := by
  rcases List.mem_cons.mp hpair with rfl | hpair
  · decide
  rcases List.mem_cons.mp hpair with rfl | hpair
  · decide
  rcases List.mem_cons.mp hpair with rfl | hpair
  · decide
  rcases List.mem_cons.mp hpair with rfl | hpair
  · decide
  exact False.elim (List.not_mem_nil hpair)

/-- Every directed physical terminal edge in every canonical-left carrier at
the pivot crosses between the two geometric sides. -/
theorem outwardYZPivotCanonicalLeftPairing_all_cross
    (source : ValenceFiveLeftCarrier 1 1 1 1 0)
    (pair : Nat × Nat)
    (hpair : pair ∈ outwardYZPivotCanonicalEdgeIdPairsOfCarrier source) :
    outwardYZPivotPairCrossesCutB pair = true := by
  rcases outwardYZPivotCanonicalEdgeIdPairsOfCarrier_cases source with
      hfirst | hsecond
  · apply firstPairing_crosses pair
    rw [← hfirst]
    exact hpair
  · apply secondPairing_crosses pair
    rw [← hsecond]
    exact hpair

/-- The disconnecting native right-tree pair list is absent from every
canonical-left carrier, so no change of the equal-rank enumeration bijection
can realize it as a canonical-left basis vector. -/
theorem outwardYZPivotCanonicalEdgeIdPairsOfCarrier_ne_native
    (source : ValenceFiveLeftCarrier 1 1 1 1 0) :
    outwardYZPivotCanonicalEdgeIdPairsOfCarrier source ≠
      outwardYZPivotNativeRightEdgeIdPairs := by
  rcases outwardYZPivotCanonicalEdgeIdPairsOfCarrier_cases source with
      hfirst | hsecond
  · rw [hfirst]
    decide
  · rw [hsecond]
    decide

#print axioms outwardYZPivotLeftCarrier_eq_first_or_second
#print axioms outwardYZPivotLeftAuxiliaryOfCarrier_mem
#print axioms outwardYZPivotCanonicalEdgeIdPairsOfCarrier_cases
#print axioms outwardYZPivotCanonicalLeftPairing_all_cross
#print axioms outwardYZPivotCanonicalEdgeIdPairsOfCarrier_ne_native

end YMGap.Continuum.Z4OutwardYZEdgeTouchSlabCanonicalLeftBasisObstruction
