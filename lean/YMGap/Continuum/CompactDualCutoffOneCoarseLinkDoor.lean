/-
# Cutoff-one coarse-link coherence door

At cutoff one the parity-selected coarse face labels are binary.  Mod-two
closure says their sum around every coarse link is even.  This module proves
the exact local representation-theoretic statement needed to turn that
condition into positive SU(2) link mass: for valence at most six, any binary
external word of even parity has a positive vacuum-ending fusion
multiplicity at the production auxiliary cutoff.

Together with `CompactDualCutoffOneCoarseFaceDoor` and the existing theorem
that cellular dyadic pushforward preserves mod-two closure, this closes the
local algebra of the cutoff-one coherent target.  The remaining work is the
corrected-slab geometric assembly and then the arbitrary-cutoff recoupling
isomorphism.
-/

import YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection

namespace YMGap.Continuum.CompactDualCutoffOneCoarseLinkDoor

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-- At the minimal production auxiliary cutoff for binary external spins,
every even word of geometric valence at most six has positive invariant
multiplicity. -/
theorem binaryEvenExplicitValenceMultiplicity_pos
    {degree : Nat} (external : EdgeLabelling)
    (hdegree : degree ≤ linkIncidenceBound)
    (hbinary : ExternalSpinsBounded 1 degree external)
    (heven : localExternalSpinSum degree external % 2 = 0) :
    0 < explicitValenceMultiplicity
      (linkAuxiliaryCutoff 1) degree external := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨
      degree = 3 ∨ degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change 0 < 1
    decide
  · have h0 : external 0 = 0 ∨ external 0 = 1 := by
      have := hbinary 0 (by omega)
      omega
    change external 0 % 2 = 0 at heven
    change 0 < oneValentMultiplicity
      (linkAuxiliaryCutoff 1) (external 0)
    rcases h0 with h0 | h0 <;>
      rw [h0] at heven <;> rw [h0] <;> simp at heven <;> decide
  · have h0 : external 0 = 0 ∨ external 0 = 1 := by
      have := hbinary 0 (by omega)
      omega
    have h1 : external 1 = 0 ∨ external 1 = 1 := by
      have := hbinary 1 (by omega)
      omega
    change (external 0 + external 1) % 2 = 0 at heven
    change 0 < twoValentMultiplicity
      (linkAuxiliaryCutoff 1) (external 0) (external 1)
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      rw [h0, h1] at heven <;> rw [h0, h1] <;>
      simp at heven <;> decide
  · have h0 : external 0 = 0 ∨ external 0 = 1 := by
      have := hbinary 0 (by omega)
      omega
    have h1 : external 1 = 0 ∨ external 1 = 1 := by
      have := hbinary 1 (by omega)
      omega
    have h2 : external 2 = 0 ∨ external 2 = 1 := by
      have := hbinary 2 (by omega)
      omega
    change (external 0 + (external 1 + external 2)) % 2 = 0 at heven
    change 0 < boolMultiplicity
      (BondMovingStep.fusionOK (external 0) (external 1) (external 2))
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;>
      rw [h0, h1, h2] at heven <;> rw [h0, h1, h2] <;>
      simp at heven <;> decide
  · have h0 : external 0 = 0 ∨ external 0 = 1 := by
      have := hbinary 0 (by omega)
      omega
    have h1 : external 1 = 0 ∨ external 1 = 1 := by
      have := hbinary 1 (by omega)
      omega
    have h2 : external 2 = 0 ∨ external 2 = 1 := by
      have := hbinary 2 (by omega)
      omega
    have h3 : external 3 = 0 ∨ external 3 = 1 := by
      have := hbinary 3 (by omega)
      omega
    change
      (external 0 + (external 1 + (external 2 + external 3))) % 2 = 0
      at heven
    change 0 < oneChannelMultiplicity (linkAuxiliaryCutoff 1)
      (external 0) (external 1) (external 2) (external 3)
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      rw [h0, h1, h2, h3] at heven <;>
      rw [h0, h1, h2, h3] <;> simp at heven <;> decide
  · have h0 : external 0 = 0 ∨ external 0 = 1 := by
      have := hbinary 0 (by omega)
      omega
    have h1 : external 1 = 0 ∨ external 1 = 1 := by
      have := hbinary 1 (by omega)
      omega
    have h2 : external 2 = 0 ∨ external 2 = 1 := by
      have := hbinary 2 (by omega)
      omega
    have h3 : external 3 = 0 ∨ external 3 = 1 := by
      have := hbinary 3 (by omega)
      omega
    have h4 : external 4 = 0 ∨ external 4 = 1 := by
      have := hbinary 4 (by omega)
      omega
    change
      (external 0 +
        (external 1 + (external 2 + (external 3 + external 4)))) % 2 = 0
      at heven
    change 0 < twoChannelMultiplicity (linkAuxiliaryCutoff 1)
      (external 0) (external 1) (external 2) (external 3) (external 4)
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      rcases h4 with h4 | h4 <;>
      rw [h0, h1, h2, h3, h4] at heven <;>
      rw [h0, h1, h2, h3, h4] <;> simp at heven <;> decide
  · have h0 : external 0 = 0 ∨ external 0 = 1 := by
      have := hbinary 0 (by omega)
      omega
    have h1 : external 1 = 0 ∨ external 1 = 1 := by
      have := hbinary 1 (by omega)
      omega
    have h2 : external 2 = 0 ∨ external 2 = 1 := by
      have := hbinary 2 (by omega)
      omega
    have h3 : external 3 = 0 ∨ external 3 = 1 := by
      have := hbinary 3 (by omega)
      omega
    have h4 : external 4 = 0 ∨ external 4 = 1 := by
      have := hbinary 4 (by omega)
      omega
    have h5 : external 5 = 0 ∨ external 5 = 1 := by
      have := hbinary 5 (by omega)
      omega
    change
      (external 0 + (external 1 +
        (external 2 + (external 3 + (external 4 + external 5))))) % 2 = 0
      at heven
    change 0 < threeChannelMultiplicity (linkAuxiliaryCutoff 1)
      (external 0) (external 1) (external 2)
      (external 3) (external 4) (external 5)
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5 <;>
      rw [h0, h1, h2, h3, h4, h5] at heven <;>
      rw [h0, h1, h2, h3, h4, h5] <;>
      simp at heven <;> decide

/-- The same positivity holds at every larger auxiliary cutoff. -/
theorem binaryEvenExplicitValenceMultiplicity_pos_of_cutoff
    {cutoff degree : Nat} (external : EdgeLabelling)
    (hcutoff : linkAuxiliaryCutoff 1 ≤ cutoff)
    (hdegree : degree ≤ linkIncidenceBound)
    (hbinary : ExternalSpinsBounded 1 degree external)
    (heven : localExternalSpinSum degree external % 2 = 0) :
    0 < explicitValenceMultiplicity cutoff degree external := by
  rw [explicitValenceMultiplicity_cutoff_independent
    external hcutoff hdegree hbinary]
  exact binaryEvenExplicitValenceMultiplicity_pos
    external hdegree hbinary heven

#print axioms binaryEvenExplicitValenceMultiplicity_pos
#print axioms binaryEvenExplicitValenceMultiplicity_pos_of_cutoff

end YMGap.Continuum.CompactDualCutoffOneCoarseLinkDoor
