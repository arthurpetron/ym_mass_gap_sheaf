/-
# Fusion-complete Haar normalization at a four-valent Z4 link

This module closes the first nontrivial local case of the enlarged auxiliary
cutoff repair.  Given any external character packet supported through `K`,
fuse each pair of opposite legs exactly.  The common intermediate channel is
then summed through the geometry-driven window `6*K`.  Since a two-leg
fusion packet is supported through `2*K`, the extra terms vanish exactly.
The surviving diagonal sum is the genuine fusion Haar pairing, and character
synthesis identifies it with the ordinary Haar moment of the four external
class functions.

For the actual four-valent link used by the cutoff-two normalization fence,
this enlarged channel sum restores precisely the previously measured
spin-three/spin-four defect.  This is a local theorem only; links of every
other incidence degree must be closed before a finite-box identity can be
formed.
-/

import YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
import YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence
import YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility

namespace YMGap.Continuum.Z4FourValentFusionCompleteHaar

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility
open YMGap.Continuum.SU2CharacterFusionSynthesis
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2ClassPolynomialHaarDescent
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4FiniteBoxCutoffTwoHaarNormalizationFence
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≈ₚ " => PolyEqv

private theorem fsum_zero_extension {f : Nat → Q'} {n m : Nat}
    (hnm : n ≤ m) (hz : ∀ i, n ≤ i → f i ≈ 0) :
    fsum f m ≈ fsum f n := by
  induction hnm with
  | refl => exact Q'.eqv_refl _
  | @step m hnm ih =>
      rw [fsum_succ]
      exact Q'.eqv_trans _ (fsum f n + 0) _
        (Q'.add_eqv_congr' ih (hz m hnm))
        (q_add_zero_eqv _)

/-! ## 1. Generic four-leg complete channel sum -/

/-- Exact two-leg fusion packet.  Its support is contained in `0,...,2*K`. -/
def pairedPacket {K : Nat} (P : CharacterPacket K) :
    CharacterPacket (2 * K) := fusionPacket P P

/-- Complete intermediate-channel sum inside the conservative Z4 link
window.  Each paired coefficient already contains the exact double sum over
the two external representation labels. -/
def completeFourLegChannelSum {K : Nat} (P : CharacterPacket K) : Q' :=
  fsum (fun channel =>
    coeffAt (pairedPacket P) channel *
      coeffAt (pairedPacket P) channel)
    (linkAuxiliaryCutoff K + 1)

/-- No paired channel survives above the exact two-leg support `2*K`. -/
theorem pairedChannel_zero_above {K channel : Nat}
    (P : CharacterPacket K) (hchannel : 2 * K < channel) :
    coeffAt (pairedPacket P) channel = 0 := by
  exact coeffAt_of_gt _ hchannel

/-- The conservative `6*K` channel sum is exactly the fusion Haar diagonal;
the apparent larger window contributes only literal zeros. -/
theorem completeFourLegChannelSum_eq_fusionHaar {K : Nat}
    (P : CharacterPacket K) :
    completeFourLegChannelSum P ≈
      fusionHaar (pairedPacket P) (pairedPacket P) := by
  let term := fun channel =>
    coeffAt (pairedPacket P) channel *
      coeffAt (pairedPacket P) channel
  have hcut : 2 * K + 1 ≤ linkAuxiliaryCutoff K + 1 := by
    unfold linkAuxiliaryCutoff linkIncidenceBound
    omega
  have hzero : ∀ channel, 2 * K + 1 ≤ channel → term channel ≈ 0 := by
    intro channel hchannel
    have hc : coeffAt (pairedPacket P) channel = 0 :=
      pairedChannel_zero_above P (by omega)
    simp only [term, hc]
    exact Q'.zero_mul_eqv _
  refine Q'.eqv_trans _ (fsum term (2 * K + 1)) _ ?_ ?_
  · exact fsum_zero_extension hcut hzero
  · exact Q'.eqv_symm
      (fusionHaar_eq_diagonal (pairedPacket P) (pairedPacket P))

/-- The literal four-character polynomial associated with the paired
four-leg presentation. -/
def fourLegCharacterProduct {K : Nat} (P : CharacterPacket K) : Poly :=
  pmul (pmul (synthesis P) (synthesis P))
    (pmul (synthesis P) (synthesis P))

/-- **Four-valent local Haar completeness.**  Summing every auxiliary
channel through `6*K` equals the bare Haar moment of all four external
characters. -/
theorem completeFourLegChannelSum_eq_bareHaar {K : Nat}
    (P : CharacterPacket K) :
    completeFourLegChannelSum P ≈
      bareVacuumHaar (fourLegCharacterProduct P) := by
  let F := pairedPacket P
  have hsynth : synthesis F ≈ₚ
      pmul (synthesis P) (synthesis P) :=
    synthesis_fusionPacket_product P P
  have hpoly : pmul (synthesis F) (synthesis F) ≈ₚ
      fourLegCharacterProduct P := pmul_congr hsynth hsynth
  refine Q'.eqv_trans _ (fusionHaar F F) _
    (completeFourLegChannelSum_eq_fusionHaar P) ?_
  refine Q'.eqv_trans _
    (bareVacuumHaar (pmul (synthesis F) (synthesis F))) _
    (Q'.eqv_symm (barePairing_eq_fusionHaar F F)) ?_
  exact bareVacuumHaar_congr hpoly

/-! ## 2. The actual cutoff-two heat-kernel link is repaired -/

def repairedBoxFourValentHeatKernelSum : Q' :=
  completeFourLegChannelSum (heatKernelPacket 2 coupling)

theorem repairedBoxFourValentHeatKernelSum_eq_fullHaar :
    repairedBoxFourValentHeatKernelSum ≈
      bareVacuumHaar localHeatKernelFourthPower := by
  exact completeFourLegChannelSum_eq_bareHaar
    (heatKernelPacket 2 coupling)

/-- The enlarged sum restores exactly the positive defect isolated by the
fixed-cutoff fence, including the separately restored unit vacuum. -/
theorem repairedBoxFourValentHeatKernelSum_eq_old_plus_defect :
    repairedBoxFourValentHeatKernelSum ≈
      boxCutoffTwoHeatKernelVacuumCompletedSum +
        cutoffTwoMissingChannelDefect := by
  exact Q'.eqv_trans _
    (bareVacuumHaar localHeatKernelFourthPower) _
    repairedBoxFourValentHeatKernelSum_eq_fullHaar
    boxCutoffTwoHeatKernel_missing_channel_exact

/-- At external cutoff two the conservative auxiliary window is twelve,
strictly containing the previously omitted channels three and four. -/
theorem repairedBoxFourValent_auxiliaryCutoff_exact :
    linkAuxiliaryCutoff 2 = 12 := by
  decide

end YMGap.Continuum.Z4FourValentFusionCompleteHaar

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4FourValentFusionCompleteHaar.pairedChannel_zero_above
#print axioms YMGap.Continuum.Z4FourValentFusionCompleteHaar.completeFourLegChannelSum_eq_fusionHaar
#print axioms YMGap.Continuum.Z4FourValentFusionCompleteHaar.completeFourLegChannelSum_eq_bareHaar
#print axioms YMGap.Continuum.Z4FourValentFusionCompleteHaar.repairedBoxFourValentHeatKernelSum_eq_fullHaar
#print axioms YMGap.Continuum.Z4FourValentFusionCompleteHaar.repairedBoxFourValentHeatKernelSum_eq_old_plus_defect
#print axioms YMGap.Continuum.Z4FourValentFusionCompleteHaar.repairedBoxFourValent_auxiliaryCutoff_exact
