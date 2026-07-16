/-
# Compatibility fence for the abstract-to-real polymer bridge

The existing abstract hard-core gas declares two polymers compatible when
their plaquette supports are disjoint.  For lattice gauge theory that is too
weak: distinct plaquettes sharing a link are coupled by the same Haar
projector and must belong to one connected polymer component.  This file
gives a closed Z4 witness accepted by the old predicate and rejected by the
link-separated predicate required by the exact spin-foam decomposition.
-/

import YMGap.Continuum.AbstractPolymerXi
import YMGap.Continuum.ClusterCount4DProgress

namespace YMGap.Continuum.Z4AbstractPolymerCompatibilityFence

open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PolymerModel

def origin : Z4Vertex := (0, 0, 0, 0)

def firstPlaquette : Z4Plaq := (origin, Z4Plane.p01)

/-- The next plaquette in the x0 direction; it is distinct from, but shares
an x1-directed edge with, `firstPlaquette`. -/
def secondPlaquette : Z4Plaq :=
  (addE origin Dir4.x0, Z4Plane.p01)

def commonLink : Z4Link := (addE origin Dir4.x0, Dir4.x1)

theorem plaquettes_distinct : firstPlaquette ≠ secondPlaquette := by
  decide

theorem commonLink_mem_first : commonLink ∈ edgesOf firstPlaquette := by
  decide

theorem commonLink_mem_second : commonLink ∈ edgesOf secondPlaquette := by
  decide

def plaquettes_link_adjacent :
    z4Chain.toLattice.Adjacent firstPlaquette secondPlaquette where
  link := commonLink
  on_p := by decide
  on_q := by decide

/-- The old hard-core test accepts the two singleton polymers solely because
the plaquette values themselves are distinct. -/
theorem plaquetteDisjointCompatibility_accepts :
    compatibleB (L := z4Chain.toLattice)
      ([firstPlaquette] : Polymer z4Chain.toLattice)
      ([secondPlaquette] : Polymer z4Chain.toLattice) = true := by
  decide

theorem oldFamilyCompatibility_accepts :
    familyCompatibleB
      ([([firstPlaquette] : Polymer z4Chain.toLattice),
        ([secondPlaquette] : Polymer z4Chain.toLattice)] :
        List (Polymer z4Chain.toLattice)) = true := by
  decide

/-- Thus the old `Xi` enumeration literally retains the family in which the
two link-adjacent singleton supports are treated as independent polymers. -/
theorem adjacentSingletonFamily_mem_oldXiEnumeration :
    [([firstPlaquette] : Polymer z4Chain.toLattice),
      ([secondPlaquette] : Polymer z4Chain.toLattice)] ∈
      (sublists
        ([([firstPlaquette] : Polymer z4Chain.toLattice),
          ([secondPlaquette] : Polymer z4Chain.toLattice)] :
          List (Polymer z4Chain.toLattice))).filter familyCompatibleB := by
  decide

/-! ## Correct link-separated compatibility for the Z4 spin foam -/

def plaquettesLinkDisjointB (p q : Z4Plaq) : Bool :=
  (edgesOf p).all (fun ell => !(decide (ell ∈ edgesOf q)))

def polymersLinkDisjointB
    (X Y : Polymer z4Chain.toLattice) : Bool :=
  X.all (fun p => Y.all (fun q => plaquettesLinkDisjointB p q))

theorem correctedCompatibility_rejects :
    polymersLinkDisjointB
      ([firstPlaquette] : Polymer z4Chain.toLattice)
      ([secondPlaquette] : Polymer z4Chain.toLattice) = false := by
  decide

/-- On this witness, the corrected predicate detects exactly the physical
shared link missed by plaquette-disjointness. -/
theorem compatibility_mismatch :
    compatibleB (L := z4Chain.toLattice)
        ([firstPlaquette] : Polymer z4Chain.toLattice)
        ([secondPlaquette] : Polymer z4Chain.toLattice) = true ∧
      polymersLinkDisjointB
        ([firstPlaquette] : Polymer z4Chain.toLattice)
        ([secondPlaquette] : Polymer z4Chain.toLattice) = false := by
  decide

end YMGap.Continuum.Z4AbstractPolymerCompatibilityFence

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4AbstractPolymerCompatibilityFence.plaquettes_link_adjacent
#print axioms YMGap.Continuum.Z4AbstractPolymerCompatibilityFence.adjacentSingletonFamily_mem_oldXiEnumeration
#print axioms YMGap.Continuum.Z4AbstractPolymerCompatibilityFence.compatibility_mismatch
