/-
# Temporal carriers for the connected two-block residue

The four-cell switch summation leaves a finite list of connected source
pairs.  This file specializes that residue to the strict doubled-time lower
and upper root blocks.  Every remaining pair constructively supplies a
literal connected cutoff-one face support of length at least
`2 * shift + 6`.

This is a termwise geometric statement.  The next step is a recoverable
weighted encoding of these witnesses, followed by the carrier tail sum.
-/

import YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation

namespace YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteMarkedRootSwitch
open YMGap.Continuum.Z4CanonicalMarkedRootSwitch
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockComponentSwitch
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedEventRecoding
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4PhysicalSurfaceComponents

def strictJointDoubledTimeLowerRootValues
    (radius base shift : Nat) (roots : List (List Nat)) :
    List (List Nat) :=
  roots.map (strictJointDoubledTimeMixedLowerRoot radius base shift)

def strictJointDoubledTimeUpperRootValues
    (radius base shift : Nat) (roots : List (List Nat)) :
    List (List Nat) :=
  roots.map (strictJointDoubledTimeMixedUpperRoot radius base shift)

theorem strictJointDoubledTimeLowerRootValues_canonical
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈ strictJointDoubledTimeLowerRootValues
        radius base shift roots →
      target ∈ canonicalSurfacePolymers (centralAmbient radius) := by
  intro target htarget
  apply strictJointDoubledTimeMixedCylinderRoots_canonical
    hadmissible hroots target
  exact List.mem_append.mpr (Or.inl htarget)

theorem strictJointDoubledTimeUpperRootValues_canonical
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈ strictJointDoubledTimeUpperRootValues
        radius base shift roots →
      target ∈ canonicalSurfacePolymers (centralAmbient radius) := by
  intro target htarget
  apply strictJointDoubledTimeMixedCylinderRoots_canonical
    hadmissible hroots target
  exact List.mem_append.mpr (Or.inr htarget)

def strictJointDoubledTimeLowerRootAtoms
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    List (CanonicalAtom (centralAmbient radius)) :=
  canonicalAtomsOfRoots
    (strictJointDoubledTimeLowerRootValues radius base shift roots)
    (strictJointDoubledTimeLowerRootValues_canonical hadmissible hroots)

def strictJointDoubledTimeUpperRootAtoms
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    List (CanonicalAtom (centralAmbient radius)) :=
  canonicalAtomsOfRoots
    (strictJointDoubledTimeUpperRootValues radius base shift roots)
    (strictJointDoubledTimeUpperRootValues_canonical hadmissible hroots)

theorem strictJointDoubledTimeLowerRootAtoms_values
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (strictJointDoubledTimeLowerRootAtoms hadmissible hroots).map
        Subtype.val =
      strictJointDoubledTimeLowerRootValues radius base shift roots := by
  unfold strictJointDoubledTimeLowerRootAtoms
  exact canonicalAtomsOfRoots_values _ _

theorem strictJointDoubledTimeUpperRootAtoms_values
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (strictJointDoubledTimeUpperRootAtoms hadmissible hroots).map
        Subtype.val =
      strictJointDoubledTimeUpperRootValues radius base shift roots := by
  unfold strictJointDoubledTimeUpperRootAtoms
  exact canonicalAtomsOfRoots_values _ _

@[simp] theorem strictJointDoubledTimeLowerRootAtoms_length
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (strictJointDoubledTimeLowerRootAtoms
      hadmissible hroots).length = roots.length := by
  have hlength := congrArg List.length
    (strictJointDoubledTimeLowerRootAtoms_values
      hadmissible hroots)
  simpa only [List.length_map,
    strictJointDoubledTimeLowerRootValues] using hlength

@[simp] theorem strictJointDoubledTimeUpperRootAtoms_length
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (strictJointDoubledTimeUpperRootAtoms
      hadmissible hroots).length = roots.length := by
  have hlength := congrArg List.length
    (strictJointDoubledTimeUpperRootAtoms_values
      hadmissible hroots)
  simpa only [List.length_map,
    strictJointDoubledTimeUpperRootValues] using hlength

theorem twoBlockConnectedSourcePair_reach_true
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (pair : TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate)
    (hpair : pair ∈ connectedTwoBlockSourcePairs) :
    twoBlockMarkedReachB
      (twoBlockSourceLeftCompatible pair)
      (twoBlockSourceRightCompatible pair)
      firstRoots secondRoots = true := by
  have hnotSeparated := (List.mem_filter.mp hpair).2
  unfold twoBlockSourceSeparatedB at hnotSeparated
  cases hreach : twoBlockMarkedReachB
      (twoBlockSourceLeftCompatible pair)
      (twoBlockSourceRightCompatible pair)
      firstRoots secondRoots <;> simp_all

/-- Choice-free extraction of a witness from a true finite Boolean search. -/
def listAnyTrueWitness {α : Type} :
    (entries : List α) → (test : α → Bool) →
      entries.any test = true →
        Σ' entry : α, (entry ∈ entries) ×' (test entry = true)
  | [], _test, htrue => by
      simp only [List.any_nil] at htrue
      exact False.elim (Bool.false_ne_true htrue)
  | entry :: entries, test, htrue => by
      cases hentry : test entry with
      | true =>
          exact ⟨entry, List.mem_cons_self,
            hentry⟩
      | false =>
          have htail : entries.any test = true := by
            simpa only [List.any_cons, hentry, Bool.false_or] using htrue
          let witness := listAnyTrueWitness entries test htail
          exact ⟨witness.1,
            List.mem_cons_of_mem entry witness.2.1,
            witness.2.2⟩

/-- The true two-block classifier yields computational endpoint data, not a
propositional existential. -/
def twoBlockMarkedReachWitness
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (firstRoots secondRoots : List (CanonicalAtom n))
    (hconnected : twoBlockMarkedReachB hleft hright
      firstRoots secondRoots = true) :
    Σ' first : CanonicalAtom n, Σ' second : CanonicalAtom n,
      (first ∈ firstRoots) ×' (second ∈ secondRoots) ×'
        (canonicalDisagreementCut hleft hright first second = true) := by
  unfold twoBlockMarkedReachB at hconnected
  let secondWitness := listAnyTrueWitness secondRoots
    (canonicalMarkedCut hleft hright firstRoots) hconnected
  have hsecondCut : canonicalMarkedCut hleft hright firstRoots
      secondWitness.1 = true := secondWitness.2.2
  unfold canonicalMarkedCut markedRootCut at hsecondCut
  let firstWitness := listAnyTrueWitness firstRoots
    (canonicalDisagreementCut hleft hright · secondWitness.1) hsecondCut
  exact ⟨firstWitness.1, secondWitness.1,
    firstWitness.2.1, secondWitness.2.1, firstWitness.2.2⟩

/-- Every term in the connected four-cell residue for the strict doubled-time
blocks constructs a connected carrier with the temporal size floor. -/
def strictJointDoubledTimeConnectedResidueCarrier
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    {firstPredicate secondPredicate : List Bool → Bool}
    (pair : TwoBlockSourcePair
      (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
      (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
      firstPredicate secondPredicate)
    (hpair : pair ∈ connectedTwoBlockSourcePairs) :
    Σ' support : List Nat,
      (support ∈ cutoffOneFaceSupports (centralAmbient radius)) ×'
      InternallyConnected
        (faceLinkAdjacentB (centralAmbient radius)) support ×'
      (shift + shift + 6 ≤ support.length) := by
  have hreach := twoBlockConnectedSourcePair_reach_true pair hpair
  let endpoints := twoBlockMarkedReachWitness
      (twoBlockSourceLeftCompatible pair)
      (twoBlockSourceRightCompatible pair)
      (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
      (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
      hreach
  let first := endpoints.1
  let second := endpoints.2.1
  have hfirst : first ∈
      strictJointDoubledTimeLowerRootAtoms hadmissible hroots :=
    endpoints.2.2.1
  have hsecond : second ∈
      strictJointDoubledTimeUpperRootAtoms hadmissible hroots :=
    endpoints.2.2.2.1
  have hfirstSecond : canonicalDisagreementCut
      (twoBlockSourceLeftCompatible pair)
      (twoBlockSourceRightCompatible pair)
      first second = true := endpoints.2.2.2.2
  have hfirstValue : first.val ∈
      roots.map (strictJointDoubledTimeMixedLowerRoot
        radius base shift) := by
    change first.val ∈ strictJointDoubledTimeLowerRootValues
      radius base shift roots
    rw [← strictJointDoubledTimeLowerRootAtoms_values
      hadmissible hroots]
    exact List.mem_map.mpr ⟨first, hfirst, rfl⟩
  have hsecondValue : second.val ∈
      roots.map (strictJointDoubledTimeMixedUpperRoot
        radius base shift) := by
    change second.val ∈ strictJointDoubledTimeUpperRootValues
      radius base shift roots
    rw [← strictJointDoubledTimeUpperRootAtoms_values
      hadmissible hroots]
    exact List.mem_map.mpr ⟨second, hsecond, rfl⟩
  exact strictJointDoubledTimeConnectedBranch_size_floor
    hadmissible hroots
    (twoBlockSourceLeftCompatible pair)
    (twoBlockSourceRightCompatible pair)
    first second hfirstValue hsecondValue hfirstSecond

#print axioms twoBlockConnectedSourcePair_reach_true
#print axioms twoBlockMarkedReachWitness
#print axioms strictJointDoubledTimeConnectedResidueCarrier

end YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
