/-
# The selected inward-mate OS flow carries a concrete parity demand

Both edge loads of the selected two-step OS flow are now bounded.  This file
identifies a nonconstant observable that the flow genuinely transports.
The rational observable is the parity of central lower face zero.

Every six-face inward mate reverses that endpoint parity.  Since the middle
state also has a Boolean parity, exactly one of the two path edges changes the
observable.  Thus, without a triangle-inequality loss, each selected source
traffic term is exactly the sum of its two edge-gradient energies.  Summing
and using the proved successful-event mass gives the positive lower bound

`41/425 <= selectedFirstParityEnergy + selectedSecondParityEnergy`.

This is a concrete observable demand carried by the actual normalized OS
joint.  It is not an all-vector variance identity, Poincare inequality,
spectral gap, beta/lattice-spacing uniformity statement, continuum limit, or
Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSSecondEdgeLoad

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityDemand

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSEdgeCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSNormalizedFlow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSSecondEdgeLoad
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A Boolean rational observable and its exact path identity -/

/-- Parity of the distinguished central lower face, as a rational zero or
one. -/
def centralFaceZeroParityCoefficient (state : EdgeLabelling) : Q' :=
  Q'.ofNat (state 0 % 2)

def paritySquaredDifference (left right : EdgeLabelling) : Q' :=
  (centralFaceZeroParityCoefficient left +
      -centralFaceZeroParityCoefficient right) *
    (centralFaceZeroParityCoefficient left +
      -centralFaceZeroParityCoefficient right)

private theorem binary_path_square_eqv_of_endpoints_ne
    (source middle target : Nat)
    (hsource : source < 2) (hmiddle : middle < 2)
    (htarget : target < 2) (hne : source ≠ target) :
    (Q'.ofNat source + -Q'.ofNat target) *
        (Q'.ofNat source + -Q'.ofNat target) ≈
      (Q'.ofNat source + -Q'.ofNat middle) *
          (Q'.ofNat source + -Q'.ofNat middle) +
        (Q'.ofNat middle + -Q'.ofNat target) *
          (Q'.ofNat middle + -Q'.ofNat target) := by
  have hs : source = 0 ∨ source = 1 := by omega
  have hm : middle = 0 ∨ middle = 1 := by omega
  have ht : target = 0 ∨ target = 1 := by omega
  rcases hs with rfl | rfl <;>
    rcases hm with rfl | rfl <;>
      rcases ht with rfl | rfl
  all_goals first | contradiction | decide

private theorem binary_endpoint_square_eqv_one
    (source target : Nat)
    (hsource : source < 2) (htarget : target < 2)
    (hne : source ≠ target) :
    (Q'.ofNat source + -Q'.ofNat target) *
        (Q'.ofNat source + -Q'.ofNat target) ≈ 1 := by
  have hs : source = 0 ∨ source = 1 := by omega
  have ht : target = 0 ∨ target = 1 := by omega
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  all_goals first | contradiction | decide

theorem inwardMatePath_endpointParity_ne
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    sourceLower source 0 % 2 ≠ targetLower source 0 % 2 := by
  have hcube : 0 ∈ centralLowerCubeFaceIds := by decide
  have hlower : 0 ∈ centralLowerFaceIds 0 :=
    centralLowerCubeFaceIds_subset_lower 0 hcube
  have hne := targetPhysical_parity_ne source hcube
  unfold sourceLower targetLower centralLowerRestriction
  simp only [if_pos hlower]
  exact fun heq => hne heq.symm

theorem inwardMatePath_paritySquaredDifference_eqv_one
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    paritySquaredDifference (sourceLower source) (targetLower source) ≈ 1 := by
  unfold paritySquaredDifference centralFaceZeroParityCoefficient
  exact binary_endpoint_square_eqv_one
    (sourceLower source 0 % 2) (targetLower source 0 % 2)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (inwardMatePath_endpointParity_ne source)

/-- The parity endpoint square is exactly the sum of the two path-edge
squares: because all three values are Boolean, precisely one edge flips. -/
theorem inwardMatePath_paritySquaredDifference_eqv_edges
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    paritySquaredDifference (sourceLower source) (targetLower source) ≈
      paritySquaredDifference (sourceLower source) (commonRight source) +
        paritySquaredDifference (commonRight source) (targetLower source) := by
  unfold paritySquaredDifference centralFaceZeroParityCoefficient
  exact binary_path_square_eqv_of_endpoints_ne
    (sourceLower source 0 % 2) (commonRight source 0 % 2)
    (targetLower source 0 % 2)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (inwardMatePath_endpointParity_ne source)

/-! ## 2. Sum the exact selected parity demand -/

def globalInwardMateSelectedFirstParityEnergyTerm
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Q' :=
  globalInwardMateSourceTraffic source *
    paritySquaredDifference (sourceLower source) (commonRight source)

def globalInwardMateSelectedSecondParityEnergyTerm
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Q' :=
  globalInwardMateSourceTraffic source *
    paritySquaredDifference (commonRight source) (targetLower source)

def globalInwardMateSelectedFirstParityEnergy
    (K : Nat) (hK : 1 <= K) : Q' :=
  listQSum globalInwardMateSelectedFirstParityEnergyTerm
    (globalCubeInwardMateCertifiedTargetFullSources K hK)

def globalInwardMateSelectedSecondParityEnergy
    (K : Nat) (hK : 1 <= K) : Q' :=
  listQSum globalInwardMateSelectedSecondParityEnergyTerm
    (globalCubeInwardMateCertifiedTargetFullSources K hK)

theorem globalInwardMateSourceTraffic_eqv_parityEdgeTerms
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    globalInwardMateSourceTraffic source ≈
      globalInwardMateSelectedFirstParityEnergyTerm source +
        globalInwardMateSelectedSecondParityEnergyTerm source := by
  refine Q'.eqv_trans _
    (globalInwardMateSourceTraffic source *
      paritySquaredDifference (sourceLower source) (targetLower source)) _ ?_ ?_
  · exact Q'.eqv_trans _ (globalInwardMateSourceTraffic source * 1) _
      (Q'.eqv_symm (Q'.mul_one_eqv _))
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm
          (inwardMatePath_paritySquaredDifference_eqv_one source)))
  · refine Q'.eqv_trans _
      (globalInwardMateSourceTraffic source *
          paritySquaredDifference (sourceLower source) (commonRight source) +
        globalInwardMateSourceTraffic source *
          paritySquaredDifference (commonRight source) (targetLower source)) _ ?_ ?_
    · exact Q'.eqv_trans _
        (globalInwardMateSourceTraffic source *
          (paritySquaredDifference (sourceLower source) (commonRight source) +
            paritySquaredDifference (commonRight source) (targetLower source))) _
        (Q'.mul_eqv_congr_left _ _ _
          (inwardMatePath_paritySquaredDifference_eqv_edges source))
        (Q'.mul_add_eqv _ _ _)
    · exact Q'.eqv_refl _

theorem globalInwardMateAllSourceTraffic_eqv_selectedParityEnergies
    (K : Nat) (hK : 1 <= K) :
    listQSum globalInwardMateSourceTraffic
        (globalCubeInwardMateCertifiedTargetFullSources K hK) ≈
      globalInwardMateSelectedFirstParityEnergy K hK +
        globalInwardMateSelectedSecondParityEnergy K hK := by
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        globalInwardMateSelectedFirstParityEnergyTerm source +
          globalInwardMateSelectedSecondParityEnergyTerm source)
      (globalCubeInwardMateCertifiedTargetFullSources K hK)) _ ?_ ?_
  · apply listQSum_congr
    intro source
    exact globalInwardMateSourceTraffic_eqv_parityEdgeTerms source
  · unfold globalInwardMateSelectedFirstParityEnergy
      globalInwardMateSelectedSecondParityEnergy
    exact listQSum_add _ _ _

/-- **Concrete selected-demand lower bound.**  The actual inward-mate flow
carries at least `41/425` units of central-face parity gradient across its two
OS edges. -/
theorem globalInwardMateSuccessRate_le_selectedParityEnergies
    (K : Nat) (hK : 1 <= K) :
    Q'.mkPos 41 425 (by decide) <=
      globalInwardMateSelectedFirstParityEnergy K hK +
        globalInwardMateSelectedSecondParityEnergy K hK := by
  exact Q'.le_trans' _ _ _
    (globalInwardMateSuccessRate_le_allSourceTraffic K hK)
    (Q'.le_of_eqv
      (globalInwardMateAllSourceTraffic_eqv_selectedParityEnergies K hK))

structure GlobalInwardMateSelectedParityDemandCertificate
    (K : Nat) (hK : 1 <= K) : Type where
  coefficient : EdgeLabelling -> Q'
  coefficient_eq : coefficient = centralFaceZeroParityCoefficient
  endpoint_square_one : forall source :
      GlobalCubeInwardMateCertifiedTargetFullSource K hK,
    paritySquaredDifference (sourceLower source) (targetLower source) ≈ 1
  exact_edge_split : forall source :
      GlobalCubeInwardMateCertifiedTargetFullSource K hK,
    paritySquaredDifference (sourceLower source) (targetLower source) ≈
      paritySquaredDifference (sourceLower source) (commonRight source) +
        paritySquaredDifference (commonRight source) (targetLower source)
  selected_energy_lower : Q'.mkPos 41 425 (by decide) <=
    globalInwardMateSelectedFirstParityEnergy K hK +
      globalInwardMateSelectedSecondParityEnergy K hK

def globalInwardMateSelectedParityDemandCertificate
    (K : Nat) (hK : 1 <= K) :
    GlobalInwardMateSelectedParityDemandCertificate K hK :=
  { coefficient := centralFaceZeroParityCoefficient
    coefficient_eq := rfl
    endpoint_square_one := inwardMatePath_paritySquaredDifference_eqv_one
    exact_edge_split := inwardMatePath_paritySquaredDifference_eqv_edges
    selected_energy_lower :=
      globalInwardMateSuccessRate_le_selectedParityEnergies K hK }

#print axioms centralFaceZeroParityCoefficient
#print axioms inwardMatePath_endpointParity_ne
#print axioms inwardMatePath_paritySquaredDifference_eqv_one
#print axioms inwardMatePath_paritySquaredDifference_eqv_edges
#print axioms globalInwardMateSourceTraffic_eqv_parityEdgeTerms
#print axioms globalInwardMateAllSourceTraffic_eqv_selectedParityEnergies
#print axioms globalInwardMateSuccessRate_le_selectedParityEnergies
#print axioms globalInwardMateSelectedParityDemandCertificate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityDemand
