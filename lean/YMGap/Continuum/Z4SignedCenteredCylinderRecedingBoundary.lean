/-
# Signed-centered finite cylinder laws and the receding-boundary interface

An existing corner-box law can be read on a signed box by the affine cell
reindexing from `Z4SignedCenteredCornerBridge`.  A centered chart therefore
stores the old canonical root identifiers as coordinates relative to its
center.  Translating the center translates every geometric root support and
leaves both the finite physical probability and its already-constructed
joint cutoff/volume value unchanged exactly.

For a fixed absolute observable, however, changing the center changes those
relative root identifiers.  The final section proves a persistent geometric
fence: even for one plaquette and every positive radius, the existing
cross-volume transport keeps the old corner coordinates and cannot produce
the root obtained by recentering one unit in signed time.  Consequently the
current cross-volume stability theorem cannot itself be instantiated as the
needed receding-boundary comparison.  A shifted-subbox stability theorem (or
an equivalent translated carrier estimate) is still required.
-/

import YMGap.Continuum.Z4SignedCenteredCornerBridge

namespace YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCylinderJointFunctional
open YMGap.Continuum.Z4CouplingParametricCylinderCofinal
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredExhaustion
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Relative canonical charts on signed centered boxes -/

structure SignedCenteredCylinderChart where
  center : SignedZ4Vertex
  radius : Nat
  roots : List (List Nat)
  rootsCanonical : ∀ root, root ∈ roots →
    root ∈ canonicalSurfacePolymers (centeredBoxBase radius)

structure SignedCenteredCylinderPresentation where
  chart : SignedCenteredCylinderChart
  predicate : List Bool → Bool

def SignedCenteredCylinderChart.rootSupport
    (chart : SignedCenteredCylinderChart) (root : List Nat) :
    List SignedZ4Plaq :=
  (geometricPolymer (centeredBoxBase chart.radius) root).map
    (fun plaquette =>
      signedTranslatePlaquette chart.center
        (natPlaquetteToCenteredSigned chart.radius plaquette))

def SignedCenteredCylinderChart.translate
    (shift : SignedZ4Vector) (chart : SignedCenteredCylinderChart) :
    SignedCenteredCylinderChart where
  center := signedAdd chart.center shift
  radius := chart.radius
  roots := chart.roots
  rootsCanonical := chart.rootsCanonical

def SignedCenteredCylinderPresentation.translate
    (shift : SignedZ4Vector)
    (presentation : SignedCenteredCylinderPresentation) :
    SignedCenteredCylinderPresentation :=
  ⟨presentation.chart.translate shift, presentation.predicate⟩

theorem SignedCenteredCylinderChart.rootSupport_mem_box
    (chart : SignedCenteredCylinderChart) {root : List Nat}
    (hroot : root ∈ chart.roots) :
    ∀ plaquette, plaquette ∈ chart.rootSupport root →
      plaquette ∈ cornerCenteredBoxPlaquettes
        chart.center chart.radius := by
  intro plaquette hplaquette
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
  unfold cornerCenteredBoxPlaquettes
  apply List.mem_map.mpr
  exact ⟨source,
    geometricPolymer_subset_box
      (canonicalSurfacePolymer_mem_faceSupports
        (chart.rootsCanonical root hroot)) source hsource,
    rfl⟩

theorem SignedCenteredCylinderChart.rootSupport_translate
    (shift : SignedZ4Vector) (chart : SignedCenteredCylinderChart)
    (root : List Nat) :
    (chart.rootSupport root).map (signedTranslatePlaquette shift) =
      (chart.translate shift).rootSupport root := by
  unfold SignedCenteredCylinderChart.rootSupport
    SignedCenteredCylinderChart.translate
  rw [List.map_map]
  apply List.map_congr_left
  intro plaquette _
  simp only [Function.comp_apply, signedTranslatePlaquette]
  apply Prod.ext
  · exact signedTranslateVertex_comp chart.center shift
      (natVertexToCenteredSigned chart.radius plaquette.1)
  · rfl

theorem SignedCenteredCylinderChart.translate_add
    (first second : SignedZ4Vector)
    (chart : SignedCenteredCylinderChart) :
    (chart.translate first).translate second =
      chart.translate (signedAdd first second) := by
  cases chart
  simp only [SignedCenteredCylinderChart.translate]
  exact congrArg
    (fun center => SignedCenteredCylinderChart.mk center _ _ _)
    (signedAdd_assoc _ first second)

theorem SignedCenteredCylinderPresentation.translate_add
    (first second : SignedZ4Vector)
    (presentation : SignedCenteredCylinderPresentation) :
    (presentation.translate first).translate second =
      presentation.translate (signedAdd first second) := by
  cases presentation with
  | mk chart predicate =>
      exact congrArg
        (fun translatedChart =>
          SignedCenteredCylinderPresentation.mk translatedChart predicate)
        (chart.translate_add first second)

/-! ## 2. The pulled-back physical finite and joint-limit values -/

def signedCenteredKCylinderValue
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) (chart : SignedCenteredCylinderChart)
    (predicate : List Bool → Bool) : Q' :=
  couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling cutoff (centeredBoxBase chart.radius)
      (cylinderEvent chart.roots predicate)

def signedCenteredJointCylinderValue
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (chart : SignedCenteredCylinderChart)
    (predicate : List Bool → Bool) : CReal :=
  couplingParametricSpinSummedJointCylinderLimitFunctional
    coupling hcoupling hle chart.rootsCanonical predicate

/-- Exact covariance when the finite volume and all marked supports are moved
together.  This is a change of coordinates, not yet covariance of a fixed
absolute local observable in the infinite-volume state. -/
theorem signedCenteredKCylinderValue_translate
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) (shift : SignedZ4Vector)
    (chart : SignedCenteredCylinderChart)
    (predicate : List Bool → Bool) :
    signedCenteredKCylinderValue coupling hcoupling cutoff
        (chart.translate shift) predicate =
      signedCenteredKCylinderValue coupling hcoupling cutoff
        chart predicate := rfl

theorem signedCenteredJointCylinderValue_translate
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (shift : SignedZ4Vector) (chart : SignedCenteredCylinderChart)
    (predicate : List Bool → Bool) :
    signedCenteredJointCylinderValue coupling hcoupling hle
        (chart.translate shift) predicate =
      signedCenteredJointCylinderValue coupling hcoupling hle
        chart predicate := rfl

theorem signedCenteredKCylinderValue_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) (chart : SignedCenteredCylinderChart)
    (predicate : List Bool → Bool) :
    (0 : Q') ≤ signedCenteredKCylinderValue
      coupling hcoupling cutoff chart predicate :=
  couplingParametricKCompatibleSupportEventProbability_nonnegative
    hcoupling cutoff (centeredBoxBase chart.radius)
      (cylinderEvent chart.roots predicate)

theorem signedCenteredKCylinderValue_le_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) (chart : SignedCenteredCylinderChart)
    (predicate : List Bool → Bool) :
    signedCenteredKCylinderValue coupling hcoupling cutoff chart predicate ≤
      (1 : Q') :=
  couplingParametricKCompatibleSupportEventProbability_le_one
    hcoupling cutoff (centeredBoxBase chart.radius)
      (cylinderEvent chart.roots predicate)

/-! ## 3. Canonical singleton roots -/

def singletonGeometricRoot (base : Nat) (plaquette : Z4Plaq) : List Nat :=
  geometricSupportIds base [plaquette]

theorem singletonGeometricRoot_sameSupport
    {base : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boxPlaquettes base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer base (singletonGeometricRoot base plaquette))
      [plaquette] := by
  apply geometricSupportIds_sameSupport
  intro item hitem
  have heq : item = plaquette := List.mem_singleton.mp hitem
  simpa only [heq] using hplaquette

def singletonGeometricRoot_nonempty
    {base : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boxPlaquettes base) :
    Σ' face : Nat, face ∈ singletonGeometricRoot base plaquette := by
  have hmember :=
    (singletonGeometricRoot_sameSupport hplaquette).2
      plaquette List.mem_cons_self
  have hnonempty : singletonGeometricRoot base plaquette ≠ [] := by
    intro heq
    rw [heq] at hmember
    cases hmember
  exact ⟨(singletonGeometricRoot base plaquette).head hnonempty,
    List.head_mem hnonempty⟩

theorem singletonGeometricRoot_canonical
    {base : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boxPlaquettes base) :
    singletonGeometricRoot base plaquette ∈
      canonicalSurfacePolymers base := by
  apply connectedFaceSupport_mem_canonicalSurfacePolymers
  · exact geometricSupportIds_mem_cutoffOneFaceSupports base [plaquette]
  · exact singletonGeometricRoot_nonempty hplaquette
  · apply geometricSupportIds_connected
    · intro item hitem
      have heq : item = plaquette := List.mem_singleton.mp hitem
      simpa only [heq] using hplaquette
    · exact connectedIn_singleton (L := z4Chain.toLattice) plaquette

theorem singletonGeometricRoots_ne
    {base : Nat} {first second : Z4Plaq}
    (hfirst : first ∈ boxPlaquettes base)
    (hsecond : second ∈ boxPlaquettes base)
    (hne : first ≠ second) :
    singletonGeometricRoot base first ≠
      singletonGeometricRoot base second := by
  intro heq
  have hfirstDecoded :=
    (singletonGeometricRoot_sameSupport hfirst).2
      first List.mem_cons_self
  rw [heq] at hfirstDecoded
  have hfirstInSecond :=
    (singletonGeometricRoot_sameSupport hsecond).1 first hfirstDecoded
  exact hne (List.mem_singleton.mp hfirstInSecond)

/-! ## 4. A persistent obstruction to direct use of zero-extension stability -/

def signedAbsoluteProbe : SignedZ4Plaq := (signedZero, .p01)

def signedNegativeTimeCenter : SignedZ4Vertex := (0, 0, 0, -1)

def absoluteProbeInCenterCoordinates
    (center : SignedZ4Vertex) (radius : Nat) : Z4Plaq :=
  centeredSignedPlaquetteToNat radius
    (signedTranslatePlaquette (signedNeg center) signedAbsoluteProbe)

def zeroCenterProbePlaquette (radius : Nat) : Z4Plaq :=
  ((radius, radius, radius, radius), .p01)

def negativeTimeCenterProbePlaquette (radius : Nat) : Z4Plaq :=
  ((radius, radius, radius, radius + 1), .p01)

theorem absoluteProbeInCenterCoordinates_zero (radius : Nat) :
    absoluteProbeInCenterCoordinates signedZero radius =
      zeroCenterProbePlaquette radius := by
  simp [absoluteProbeInCenterCoordinates, signedAbsoluteProbe,
    centeredSignedPlaquetteToNat, centeredSignedVertexToNat,
    centeredSignedCoordinateToNat, signedTranslatePlaquette,
    signedTranslateVertex, signedNeg, signedAdd, signedZero,
    zeroCenterProbePlaquette]

theorem absoluteProbeInCenterCoordinates_negativeTime (radius : Nat) :
    absoluteProbeInCenterCoordinates signedNegativeTimeCenter radius =
      negativeTimeCenterProbePlaquette radius := by
  simp [absoluteProbeInCenterCoordinates, signedAbsoluteProbe,
    signedNegativeTimeCenter, centeredSignedPlaquetteToNat,
    centeredSignedVertexToNat, centeredSignedCoordinateToNat,
    signedTranslatePlaquette, signedTranslateVertex, signedNeg, signedAdd,
    signedZero, negativeTimeCenterProbePlaquette]
  rw [Int.add_comm 1 (radius : Int), ← Int.natCast_one,
    ← Int.natCast_add]
  rfl

theorem zeroCenterProbePlaquette_mem
    {radius : Nat} :
    zeroCenterProbePlaquette radius ∈
      boxPlaquettes (centeredBoxBase radius) := by
  rw [mem_boxPlaquettes]
  simp only [zeroCenterProbePlaquette, centeredBoxBase]
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem negativeTimeCenterProbePlaquette_mem
    {radius : Nat} (hradius : 0 < radius) :
    negativeTimeCenterProbePlaquette radius ∈
      boxPlaquettes (centeredBoxBase radius) := by
  rw [mem_boxPlaquettes]
  simp only [negativeTimeCenterProbePlaquette, centeredBoxBase]
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem zeroCenterProbePlaquette_ne_negativeTime
    (radius : Nat) :
    zeroCenterProbePlaquette radius ≠
      negativeTimeCenterProbePlaquette radius := by
  intro heq
  have htime := congrArg (fun plaquette => plaquette.1.2.2.2) heq
  simp only [zeroCenterProbePlaquette,
    negativeTimeCenterProbePlaquette] at htime
  omega

theorem zeroCenterProbePlaquette_ne_negativeTime_across
    (sourceRadius targetRadius : Nat) :
    zeroCenterProbePlaquette sourceRadius ≠
      negativeTimeCenterProbePlaquette targetRadius := by
  intro heq
  have hspace := congrArg (fun plaquette => plaquette.1.1) heq
  have htime := congrArg (fun plaquette => plaquette.1.2.2.2) heq
  simp only [zeroCenterProbePlaquette,
    negativeTimeCenterProbePlaquette] at hspace htime
  omega

theorem transportPolymer_self_of_canonical
    {base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    transportPolymer base base root = root := by
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport
  · exact transportPolymer_mem_canonicalSurfacePolymers
      (Nat.le_refl base) hroot
  · exact hroot
  · exact sameSupport_symm
      (transportPolymer_sameSupport (Nat.le_refl base)
        (canonicalSurfacePolymer_mem_faceSupports hroot))

/-- At every positive radius, the exact root transport used by the current
cross-volume stability theorem does not produce the canonical root of the
same absolute plaquette viewed from the time-shifted center. -/
theorem centeredProbe_not_existing_crossVolumeTransport
    {radius : Nat} (hradius : 0 < radius) :
    transportPolymer (centeredBoxBase radius) (centeredBoxBase radius)
        (singletonGeometricRoot (centeredBoxBase radius)
          (zeroCenterProbePlaquette radius)) ≠
      singletonGeometricRoot (centeredBoxBase radius)
        (negativeTimeCenterProbePlaquette radius) := by
  rw [transportPolymer_self_of_canonical
    (singletonGeometricRoot_canonical zeroCenterProbePlaquette_mem)]
  exact singletonGeometricRoots_ne
    zeroCenterProbePlaquette_mem
    (negativeTimeCenterProbePlaquette_mem hradius)
    (zeroCenterProbePlaquette_ne_negativeTime radius)

/-- Enlarging the target volume does not repair the mismatch.  Zero-extension
keeps the source plaquette at its old four coordinates, whereas changing the
signed center changes only its time coordinate relative to the box.  No pair
of source/target radii can make these two coordinate requirements agree. -/
theorem centeredProbe_not_existing_crossVolumeTransport_across
    {sourceRadius targetRadius : Nat}
    (hbase : centeredBoxBase sourceRadius ≤
      centeredBoxBase targetRadius)
    (htargetRadius : 0 < targetRadius) :
    transportPolymer
        (centeredBoxBase sourceRadius) (centeredBoxBase targetRadius)
        (singletonGeometricRoot (centeredBoxBase sourceRadius)
          (zeroCenterProbePlaquette sourceRadius)) ≠
      singletonGeometricRoot (centeredBoxBase targetRadius)
        (negativeTimeCenterProbePlaquette targetRadius) := by
  intro heq
  have hsourceCanonical := singletonGeometricRoot_canonical
    (base := centeredBoxBase sourceRadius)
    (plaquette := zeroCenterProbePlaquette sourceRadius)
    zeroCenterProbePlaquette_mem
  have htransport := transportPolymer_sameSupport hbase
    (canonicalSurfacePolymer_mem_faceSupports hsourceCanonical)
  have hsourceMember :=
    (singletonGeometricRoot_sameSupport
      (base := centeredBoxBase sourceRadius)
      (plaquette := zeroCenterProbePlaquette sourceRadius)
      zeroCenterProbePlaquette_mem).2
      (zeroCenterProbePlaquette sourceRadius) List.mem_cons_self
  have htargetDecoded := htransport.1
    (zeroCenterProbePlaquette sourceRadius) hsourceMember
  rw [heq] at htargetDecoded
  have htargetMember :=
    (singletonGeometricRoot_sameSupport
      (base := centeredBoxBase targetRadius)
      (plaquette := negativeTimeCenterProbePlaquette targetRadius)
      (negativeTimeCenterProbePlaquette_mem htargetRadius)).1
      (zeroCenterProbePlaquette sourceRadius) htargetDecoded
  exact zeroCenterProbePlaquette_ne_negativeTime_across
    sourceRadius targetRadius (List.mem_singleton.mp htargetMember)

theorem centeredProbeCylinder_not_existing_crossVolumeTransport
    {radius : Nat} (hradius : 0 < radius) :
    transportedCylinderRoots
        (centeredBoxBase radius) (centeredBoxBase radius)
        [singletonGeometricRoot (centeredBoxBase radius)
          (zeroCenterProbePlaquette radius)] ≠
      [singletonGeometricRoot (centeredBoxBase radius)
        (negativeTimeCenterProbePlaquette radius)] := by
  unfold transportedCylinderRoots
  simp only [List.map_cons, List.map_nil]
  intro heq
  have hhead := congrArg List.head? heq
  simp only [List.head?_cons] at hhead
  exact centeredProbe_not_existing_crossVolumeTransport hradius
    (Option.some.inj hhead)

#print axioms SignedCenteredCylinderChart.rootSupport_mem_box
#print axioms SignedCenteredCylinderChart.rootSupport_translate
#print axioms SignedCenteredCylinderChart.translate_add
#print axioms SignedCenteredCylinderPresentation.translate_add
#print axioms signedCenteredKCylinderValue_translate
#print axioms signedCenteredJointCylinderValue_translate
#print axioms signedCenteredKCylinderValue_nonnegative
#print axioms signedCenteredKCylinderValue_le_one
#print axioms singletonGeometricRoot_canonical
#print axioms singletonGeometricRoots_ne
#print axioms transportPolymer_self_of_canonical
#print axioms centeredProbe_not_existing_crossVolumeTransport
#print axioms centeredProbe_not_existing_crossVolumeTransport_across
#print axioms centeredProbeCylinder_not_existing_crossVolumeTransport

end YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
