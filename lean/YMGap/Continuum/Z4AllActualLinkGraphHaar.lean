/-
# Every actual finite-box link resolver is its exact local Haar moment

The seven geometric valences have now been discharged individually.  This
module packages them into one uniform theorem and composes it with exact
unused-coordinate deletion and canonical-to-actual identifier transport.
The conclusion applies directly to an arbitrary enumerated finite-box link.
-/

import YMGap.Continuum.Z4CanonicalSixValentGraphHaar

namespace YMGap.Continuum.Z4AllActualLinkGraphHaar

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.Z4CanonicalFiveValentGraphHaar
open YMGap.Continuum.Z4CanonicalLinkCartesianTransport
open YMGap.Continuum.Z4CanonicalLinkGraphClosedCases
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4CanonicalSixValentGraphHaar
open YMGap.Continuum.Z4CanonicalTrivalentGraphHaar
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4UnitCubeHaarSectorBridge

local infix:50 " ≈ " => Q'.eqv

/-- The complete case split over the only link valences allowed by the
four-dimensional box geometry. -/
theorem canonicalUsedVertexCartesianSum_eq_bareHaar
    {K degree : Nat} (P : CharacterPacket K)
    (hdegree : degree ≤ linkIncidenceBound) :
    canonicalUsedVertexCartesianSum P degree ≈
      bareVacuumHaar (characterPow (synthesis P) degree) := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact canonicalUsed_zero_eq_bareHaar P
  · exact canonicalUsed_one_eq_bareHaar P
  · exact canonicalUsed_two_eq_bareHaar P
  · exact canonicalUsed_three_eq_bareHaar P
  · exact canonicalUsed_four_eq_bareHaar P
  · exact canonicalUsed_five_eq_bareHaar P
  · exact canonicalUsed_six_eq_bareHaar P

/-- The canonical full reserved-coordinate block has exactly the ordinary
local Haar value, with no unused-coordinate multiplicity. -/
theorem canonicalLinkVertexCartesianSum_eq_bareHaar
    {K degree : Nat} (P : CharacterPacket K)
    (hdegree : degree ≤ linkIncidenceBound) :
    canonicalLinkVertexCartesianSum P degree ≈
      bareVacuumHaar (characterPow (synthesis P) degree) := by
  exact Q'.eqv_trans _ (canonicalUsedVertexCartesianSum P degree) _
    (canonicalLinkVertexCartesianSum_eq_used P hdegree)
    (canonicalUsedVertexCartesianSum_eq_bareHaar P hdegree)

/-- **Uniform actual-link graph/Haar theorem.**  The literal production
resolver on arbitrary physical plaquette identifiers and its actual reserved
block is the exact local Haar moment. -/
theorem actualLinkVertexCartesianSum_eq_bareHaar {K : Nat}
    (P : CharacterPacket K) (n i : Nat) (ell : Z4Link) :
    actualLinkVertexCartesianSum P n i ell ≈
      bareVacuumHaar
        (characterPow (synthesis P) (incidentPlaqIds n ell).length) := by
  have hdegree : (incidentPlaqIds n ell).length ≤ linkIncidenceBound :=
    incidentPlaqIds_length_le_six n ell
  exact Q'.eqv_trans _
    (canonicalLinkVertexCartesianSum P (incidentPlaqIds n ell).length) _
    (actualLinkVertexCartesianSum_eq_canonical P n i ell)
    (canonicalLinkVertexCartesianSum_eq_bareHaar P hdegree)

end YMGap.Continuum.Z4AllActualLinkGraphHaar

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4AllActualLinkGraphHaar.canonicalUsedVertexCartesianSum_eq_bareHaar
#print axioms YMGap.Continuum.Z4AllActualLinkGraphHaar.canonicalLinkVertexCartesianSum_eq_bareHaar
#print axioms YMGap.Continuum.Z4AllActualLinkGraphHaar.actualLinkVertexCartesianSum_eq_bareHaar
