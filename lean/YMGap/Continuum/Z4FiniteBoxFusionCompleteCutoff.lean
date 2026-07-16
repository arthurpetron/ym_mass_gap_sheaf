/-
# Fusion-complete auxiliary cutoffs on finite Z4 boxes

The fixed-cutoff Haar normalization fence shows that external plaquette
cutoff `K` cannot also be imposed on internal fusion labels.  This module
constructs the first repair rung.  Every physical Z4 link has at most six
incident plaquettes, and a legal SU(2) fusion output is at most the sum of its
two inputs.  Consequently the conservative auxiliary window `6*K` contains
every sequential intermediate label generated from at most six external
labels bounded by `K`.

The packet family below makes the separation literal:

* physical plaquette packets are the cutoff-`K` heat-kernel packets padded by
  zero into cutoff `6*K`;
* vacuum terminators live at cutoff `6*K`;
* internal fusion carriers are all-channel packets through `6*K`.

Thus physical faces do not acquire spurious modes between `K+1` and `6*K`,
while auxiliary edges can retain every channel permitted by the degree
bound.  This file proves the cutoff and coefficient invariants only.  The
successor theorem must still identify the complete local channel sum with
the bare Haar moment before any global box equality is asserted.
-/

import YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
import YMGap.Continuum.Z4FiniteBoxHeatKernelCutoffPersistence
import YMGap.Continuum.FusionBratteli

namespace YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphSupportedRefinementPath
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphWeightedGapTransport
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Geometry-driven auxiliary window -/

/-- Six is the exact uniform upper bound on the number of plaquettes incident
on a positive-direction link in four dimensions. -/
def linkIncidenceBound : Nat := 6

/-- Conservative internal fusion cutoff for external face cutoff `K`. -/
def linkAuxiliaryCutoff (K : Nat) : Nat := linkIncidenceBound * K

theorem externalCutoff_le_linkAuxiliaryCutoff (K : Nat) :
    K ≤ linkAuxiliaryCutoff K := by
  unfold linkAuxiliaryCutoff linkIncidenceBound
  omega

/-- The actual incident-list spin budget of every finite-box link fits in the
auxiliary window. -/
theorem incidentBudget_le_linkAuxiliaryCutoff (K n : Nat) (ell :
    YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    (incidentPlaqIds n ell).length * K ≤ linkAuxiliaryCutoff K := by
  unfold linkAuxiliaryCutoff linkIncidenceBound
  exact Nat.mul_le_mul_right K (incidentPlaqIds_length_le_six n ell)

/-- Any legal SU(2) fusion output is no larger than the sum of its inputs. -/
theorem fusionOK_output_le_add {a b s : Nat}
    (hfusion : fusionOK a b s = true) : s ≤ a + b := by
  obtain ⟨k, _hka, _hkb, heq⟩ :=
    (fusionOK_iff_ladder a b s).1 hfusion
  omega

/-- Sequential fusion preserves the sharp accumulated-prefix budget. -/
theorem fusionOK_prefix_budget {K used a b s : Nat}
    (ha : a ≤ used * K) (hb : b ≤ K)
    (hfusion : fusionOK a b s = true) :
    s ≤ (used + 1) * K := by
  have hs := fusionOK_output_le_add hfusion
  have hab : a + b ≤ used * K + K := Nat.add_le_add ha hb
  have htotal : s ≤ used * K + K := Nat.le_trans hs hab
  simpa [Nat.add_mul] using htotal

/-- Every sequential intermediate generated before the seventh external leg
lies in the conservative `6*K` auxiliary window. -/
theorem fusionOK_prefix_within_linkAuxiliaryCutoff
    {K used a b s : Nat} (hused : used + 1 ≤ linkIncidenceBound)
    (ha : a ≤ used * K) (hb : b ≤ K)
    (hfusion : fusionOK a b s = true) :
    s ≤ linkAuxiliaryCutoff K := by
  have hp := fusionOK_prefix_budget ha hb hfusion
  unfold linkAuxiliaryCutoff
  exact Nat.le_trans hp (Nat.mul_le_mul_right K hused)

/-! ## 2. Zero-padded face packets and enlarged auxiliary packets -/

/-- Heat-kernel packets with external cutoff `K` embedded into a graph whose
internal labels range through `6*K`.  Only auxiliary carriers receive all
coefficients in the enlarged window. -/
def gaugeHeatKernelBoxPacketsFusionComplete (K n : Nat) :
    Nat → CharacterPacket (linkAuxiliaryCutoff K) :=
  fun edge =>
    if edge < plaquetteEdgeCount n then
      padPacket (externalCutoff_le_linkAuxiliaryCutoff K)
        (heatKernelPacket K coupling)
    else if edge ∈ vacuumBaseEdgeIds n then
      vacuumPacket (linkAuxiliaryCutoff K)
    else
      allOnesPacket (linkAuxiliaryCutoff K)

/-- The corresponding actual finite-box packet graph. -/
def gaugeHeatKernelBoxStateFusionComplete (K n : Nat) :
    CompensatedGraphState (linkAuxiliaryCutoff K) where
  edges := usedResolutionEdges n
  vertices := resolutionVertices n
  packet := gaugeHeatKernelBoxPacketsFusionComplete K n
  copiedEdges := []
  copied_mem := by intro edge h; cases h

/-- Enlarging only the auxiliary carrier preserves the generic exact graph
separator. -/
theorem gaugeHeatKernelBoxStateFusionComplete_gap (K n : Nat) :
    SpectralGapBound
      (supportedGraphSpectralModel
        (gaugeHeatKernelBoxStateFusionComplete K n))
      (eighth * eighth) :=
  path_supported_gap_from_uncompensated (.refl _) rfl

/-- On a physical plaquette identifier, the enlarged graph packet reads
exactly the zero-extended original cutoff-`K` heat-kernel coefficients. -/
theorem faceCoefficient_fusionComplete {K n edge spin : Nat}
    (hedge : edge < plaquetteEdgeCount n) :
    coeffAt (gaugeHeatKernelBoxPacketsFusionComplete K n edge) spin =
      coeffAt (heatKernelPacket K coupling) spin := by
  unfold gaugeHeatKernelBoxPacketsFusionComplete
  rw [if_pos hedge, coeffAt_padPacket]

/-- Every retained physical face coefficient is the derived heat-kernel
coefficient. -/
theorem faceCoefficient_fusionComplete_of_le
    {K n edge spin : Nat} (hedge : edge < plaquetteEdgeCount n)
    (hspin : spin ≤ K) :
    coeffAt (gaugeHeatKernelBoxPacketsFusionComplete K n edge) spin =
      coeffW coupling spin := by
  rw [faceCoefficient_fusionComplete hedge]
  exact coeffAt_heatKernelPacket (Nat.lt_succ_of_le hspin)

/-- Physical face modes above the external cutoff remain exactly zero even
though the graph's auxiliary cutoff is larger. -/
theorem faceCoefficient_fusionComplete_zero_above
    {K n edge spin : Nat} (hedge : edge < plaquetteEdgeCount n)
    (hspin : K < spin) :
    coeffAt (gaugeHeatKernelBoxPacketsFusionComplete K n edge) spin = 0 := by
  rw [faceCoefficient_fusionComplete hedge]
  exact coeffAt_of_gt _ hspin

/-- An internal non-terminating fusion edge carries coefficient one on every
label in the enlarged auxiliary window. -/
theorem auxiliaryCoefficient_fusionComplete_one
    {K n edge spin : Nat} (hface : ¬ edge < plaquetteEdgeCount n)
    (hvac : edge ∉ vacuumBaseEdgeIds n)
    (hspin : spin ≤ linkAuxiliaryCutoff K) :
    coeffAt (gaugeHeatKernelBoxPacketsFusionComplete K n edge) spin = 1 := by
  unfold gaugeHeatKernelBoxPacketsFusionComplete
  rw [if_neg hface, if_neg hvac, coeffAt_allOnesPacket]
  omega

/-- Enlarged vacuum terminators still select only representation zero. -/
theorem vacuumCoefficient_fusionComplete
    {K n edge spin : Nat} (hface : ¬ edge < plaquetteEdgeCount n)
    (hvac : edge ∈ vacuumBaseEdgeIds n) :
    coeffAt (gaugeHeatKernelBoxPacketsFusionComplete K n edge) spin =
      if spin = 0 then 1 else 0 := by
  unfold gaugeHeatKernelBoxPacketsFusionComplete
  rw [if_neg hface, if_pos hvac]
  exact
    YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder.coeffAt_vacuumPacket
      (linkAuxiliaryCutoff K) spin

end YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff.externalCutoff_le_linkAuxiliaryCutoff
#print axioms YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff.incidentBudget_le_linkAuxiliaryCutoff
#print axioms YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff.fusionOK_output_le_add
#print axioms YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff.fusionOK_prefix_budget
#print axioms YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff.fusionOK_prefix_within_linkAuxiliaryCutoff
#print axioms YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff.gaugeHeatKernelBoxStateFusionComplete_gap
#print axioms YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff.faceCoefficient_fusionComplete
#print axioms YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff.faceCoefficient_fusionComplete_of_le
#print axioms YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff.faceCoefficient_fusionComplete_zero_above
#print axioms YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff.auxiliaryCoefficient_fusionComplete_one
#print axioms YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff.vacuumCoefficient_fusionComplete
