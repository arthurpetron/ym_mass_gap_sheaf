/-
# Uniqueness of finite-box Z4 surface components

The canonical union-on-bridge decomposition is unique up to the two irrelevant
list orderings.  Any nonempty, internally link-connected, pairwise
link-separated cover of the same excited face support has exactly the same
component supports in both directions.
-/

import YMGap.Continuum.FiniteBoolGraphComponentUniqueness
import YMGap.Continuum.Z4PhysicalSurfaceComponents

namespace YMGap.Continuum.Z4PhysicalSurfaceComponentUniqueness

open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphComponentUniqueness
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4PhysicalSurfaceComponents

theorem surfaceComponents_unique_up_to_support
    (n : Nat) (physical : EdgeLabelling)
    {candidate : List (List Nat)}
    (hcandidateCover :
      Covers (excitedPlaquetteIds n physical) candidate)
    (hcandidateConnected :
      AllConnected (faceLinkAdjacentB n) candidate)
    (hcandidateNonempty : AllNonempty candidate)
    (hcandidateSeparated :
      DistinctSeparated (faceLinkAdjacentB n) candidate) :
    FamiliesSupportEquivalent (surfaceComponents n physical) candidate :=
  graphComponents_unique_up_to_support
    (faceLinkAdjacentB n) (faceLinkAdjacentB_symmetric n)
    (excitedPlaquetteIds n physical)
    hcandidateCover hcandidateConnected hcandidateNonempty
    hcandidateSeparated

end YMGap.Continuum.Z4PhysicalSurfaceComponentUniqueness

#print axioms YMGap.Continuum.Z4PhysicalSurfaceComponentUniqueness.surfaceComponents_unique_up_to_support
