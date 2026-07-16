/-
# Complete fusion/Haar identification of the actual four-valent graph block

The preceding graph-syntax bridge exposes the production `fuseLabels`
four-leg block as a literal five-fold finite sum.  This module completes that
local interface constructively.

A generic finite-Fubini factorization turns any five-fold left/right kernel
sum into the product of its two pair-channel coefficients.  Applied to the
actual graph guards, full symmetry of `fusionOK` identifies both factors with
the exact Clebsch--Gordan coefficient of the zero-padded external packet.
The resulting diagonal is the Haar pairing of the lossless two-leg packet,
so exact character synthesis identifies it with the four-character Haar
moment and with the canonical sequential fusion channel sum.

Thus, at valence four, the actual vertex-only graph sum and the derived
vacuum-completed nonvacuum graph projection both equal the canonical local
Haar value.  No measured constant or truncated auxiliary channel enters.

Honest scope: valence four is complete.  The same graph-syntax identification
still has to be instantiated uniformly for valences zero through six and
transported from canonical local identifiers to every actual box link.
-/

import YMGap.Continuum.Z4FourValentGraphCartesianBridge
import YMGap.Continuum.FusionCoreStep

namespace YMGap.Continuum.Z4FourValentGraphFusionCompleteHaar

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2ClassPolynomialHaarDescent
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar
open YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FourValentFusionCompleteHaar
open YMGap.Continuum.Z4FourValentGraphCartesianBridge
open YMGap.Continuum.Z4UnitCubeHaarSectorBridge

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≈ₚ " => PolyEqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

def leftPairSum (N : Nat) (left : Nat → Nat → Nat → Q')
    (channel : Nat) : Q' :=
  fsum (fun a => fsum (fun b => left a b channel) N) N

def rightPairSum (N : Nat) (right : Nat → Nat → Nat → Q')
    (channel : Nat) : Q' :=
  fsum (fun c => fsum (fun d => right c d channel) N) N

def fiveFoldProductSum (N : Nat)
    (left right : Nat → Nat → Nat → Q') : Q' :=
  fsum (fun a => fsum (fun b => fsum (fun channel =>
    fsum (fun c => fsum (fun d =>
      left a b channel * right c d channel) N) N) N) N) N

private theorem inner_right_factor (N : Nat)
    (left right : Nat → Nat → Nat → Q')
    (a b channel : Nat) :
    fsum (fun c => fsum (fun d =>
      left a b channel * right c d channel) N) N ≈
      left a b channel * rightPairSum N right channel := by
  refine Q'.eqv_trans _
    (fsum (fun c => left a b channel *
      fsum (fun d => right c d channel) N) N) _ ?_ ?_
  · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    intro c
    exact Q'.eqv_symm
      (YMGap.Continuum.CubeRatioBounds.fsum_const_mul
        (left a b channel) (fun d => right c d channel) N)
  · exact Q'.eqv_symm
      (YMGap.Continuum.CubeRatioBounds.fsum_const_mul
        (left a b channel)
        (fun c => fsum (fun d => right c d channel) N) N)

theorem fiveFoldProductSum_factor (N : Nat)
    (left right : Nat → Nat → Nat → Q') :
    fiveFoldProductSum N left right ≈
      fsum (fun channel =>
        leftPairSum N left channel * rightPairSum N right channel) N := by
  unfold fiveFoldProductSum
  let g := fun a b channel =>
    left a b channel * rightPairSum N right channel
  refine Q'.eqv_trans _
    (fsum (fun a => fsum (fun b => fsum (fun channel =>
      g a b channel) N) N) N) _ ?_ ?_
  · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    intro a
    apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    intro b
    apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    intro channel
    exact inner_right_factor N left right a b channel
  · refine Q'.eqv_trans _
      (fsum (fun a => fsum (fun channel =>
        fsum (fun b => g a b channel) N) N) N) _ ?_ ?_
    · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
      intro a
      exact YMGap.Continuum.CubeRatioBounds.fsum_swap
        (fun b channel => g a b channel) N N
    · refine Q'.eqv_trans _
        (fsum (fun channel => fsum (fun a =>
          fsum (fun b => g a b channel) N) N) N) _ ?_ ?_
      · exact YMGap.Continuum.CubeRatioBounds.fsum_swap
          (fun a channel => fsum (fun b => g a b channel) N) N N
      · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
        intro channel
        refine Q'.eqv_trans _
          (fsum (fun a =>
            fsum (fun b => left a b channel) N *
              rightPairSum N right channel) N) _ ?_ ?_
        · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
          intro a
          exact Q'.eqv_symm
            (YMGap.Continuum.CubeRatioBounds.fsum_mul_const
              (fun b => left a b channel)
              (rightPairSum N right channel) N)
        · exact Q'.eqv_symm
            (YMGap.Continuum.CubeRatioBounds.fsum_mul_const
              (fun a => fsum (fun b => left a b channel) N)
              (rightPairSum N right channel) N)

def graphLeftTerm {K : Nat} (P : CharacterPacket K)
    (a b channel : Nat) : Q' :=
  if fusionOK a b channel = true then
    coeffAt (facePacketAtLinkCutoff P) a *
      coeffAt (facePacketAtLinkCutoff P) b
  else 0

def graphRightTerm {K : Nat} (P : CharacterPacket K)
    (c d channel : Nat) : Q' :=
  if fusionOK channel c d = true then
    coeffAt (facePacketAtLinkCutoff P) c *
      coeffAt (facePacketAtLinkCutoff P) d
  else 0

private theorem four_coeff_reassociate (A B C D : Q') :
    A * (B * (1 * (C * (D * 1)))) ≈ (A * B) * (C * D) := by
  refine Q'.eqv_trans _
    (A * (B * (1 * (C * D)))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv D))))
  · refine Q'.eqv_trans _ (A * (B * (C * D))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv (C * D)))
    · exact Q'.eqv_symm (Q'.mul_assoc_eqv A B (C * D))

theorem fourValentCartesianTerm_eq_pairProduct
    {K a b channel c d : Nat} (P : CharacterPacket K)
    (hchannel : channel < linkAuxiliaryCutoff K + 1) :
    fourValentCartesianTerm P a b channel c d ≈
      graphLeftTerm P a b channel * graphRightTerm P c d channel := by
  have haux := coeffAt_allOnesPacket hchannel
  by_cases hleft : fusionOK a b channel = true
  · by_cases hright : fusionOK channel c d = true
    · unfold fourValentCartesianTerm graphLeftTerm graphRightTerm
      rw [if_pos hleft, if_pos hright, if_pos hleft, if_pos hright, haux]
      exact four_coeff_reassociate _ _ _ _
    · unfold fourValentCartesianTerm graphLeftTerm graphRightTerm
      rw [if_pos hleft, if_neg hright, if_pos hleft, if_neg hright]
      exact Q'.eqv_symm (Q'.mul_zero_eqv _)
  · unfold fourValentCartesianTerm graphLeftTerm graphRightTerm
    rw [if_neg hleft, if_neg hleft]
    exact Q'.eqv_symm (Q'.zero_mul_eqv _)

theorem fourValentExplicitCartesianSum_eq_fiveFold
    {K : Nat} (P : CharacterPacket K) :
    fourValentExplicitCartesianSum P ≈
      fiveFoldProductSum (linkAuxiliaryCutoff K + 1)
        (graphLeftTerm P) (graphRightTerm P) := by
  unfold fourValentExplicitCartesianSum fiveFoldProductSum
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro a
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro b
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr_lt
  intro channel hchannel
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro c
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro d
  exact fourValentCartesianTerm_eq_pairProduct P hchannel

private theorem fusionOK_rotate (a b c : Nat) :
    fusionOK a b c = fusionOK b c a := by
  rw [YMGap.Continuum.FusionCoreStepRoundD.fusionOK_symm_ab a b c,
    YMGap.Continuum.FusionCoreStepRoundD.fusionOK_symm_bt b a c]

private theorem graphLeftTerm_eq_fusionTerm {K : Nat}
    (P : CharacterPacket K) (a b channel : Nat) :
    graphLeftTerm P a b channel ≈
      fusionInd a b channel *
        (coeffAt (facePacketAtLinkCutoff P) a *
          coeffAt (facePacketAtLinkCutoff P) b) := by
  unfold graphLeftTerm fusionInd
  by_cases h : fusionOK a b channel = true
  · rw [if_pos h, if_pos h]
    exact Q'.eqv_symm (Q'.one_mul_eqv _)
  · rw [if_neg h, if_neg h]
    exact Q'.eqv_symm (Q'.zero_mul_eqv _)

private theorem graphRightTerm_eq_fusionTerm {K : Nat}
    (P : CharacterPacket K) (c d channel : Nat) :
    graphRightTerm P c d channel ≈
      fusionInd c d channel *
        (coeffAt (facePacketAtLinkCutoff P) c *
          coeffAt (facePacketAtLinkCutoff P) d) := by
  unfold graphRightTerm fusionInd
  rw [fusionOK_rotate channel c d]
  by_cases h : fusionOK c d channel = true
  · rw [if_pos h, if_pos h]
    exact Q'.eqv_symm (Q'.one_mul_eqv _)
  · rw [if_neg h, if_neg h]
    exact Q'.eqv_symm (Q'.zero_mul_eqv _)

theorem leftPairSum_eq_fusionCoeff {K channel : Nat}
    (P : CharacterPacket K) :
    leftPairSum (linkAuxiliaryCutoff K + 1) (graphLeftTerm P) channel ≈
      fusionCoeff (facePacketAtLinkCutoff P)
        (facePacketAtLinkCutoff P) channel := by
  unfold leftPairSum fusionCoeff fusionProduct
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro a
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro b
  exact graphLeftTerm_eq_fusionTerm P a b channel

theorem rightPairSum_eq_fusionCoeff {K channel : Nat}
    (P : CharacterPacket K) :
    rightPairSum (linkAuxiliaryCutoff K + 1) (graphRightTerm P) channel ≈
      fusionCoeff (facePacketAtLinkCutoff P)
        (facePacketAtLinkCutoff P) channel := by
  unfold rightPairSum fusionCoeff fusionProduct
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro c
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro d
  exact graphRightTerm_eq_fusionTerm P c d channel

theorem fourValentExplicitCartesianSum_eq_fusionDiagonal
    {K : Nat} (P : CharacterPacket K) :
    fourValentExplicitCartesianSum P ≈
      fsum (fun channel =>
        fusionCoeff (facePacketAtLinkCutoff P)
            (facePacketAtLinkCutoff P) channel *
          fusionCoeff (facePacketAtLinkCutoff P)
            (facePacketAtLinkCutoff P) channel)
        (linkAuxiliaryCutoff K + 1) := by
  refine Q'.eqv_trans _
    (fiveFoldProductSum (linkAuxiliaryCutoff K + 1)
      (graphLeftTerm P) (graphRightTerm P)) _
    (fourValentExplicitCartesianSum_eq_fiveFold P) ?_
  refine Q'.eqv_trans _
    (fsum (fun channel =>
      leftPairSum (linkAuxiliaryCutoff K + 1) (graphLeftTerm P) channel *
        rightPairSum (linkAuxiliaryCutoff K + 1)
          (graphRightTerm P) channel)
      (linkAuxiliaryCutoff K + 1)) _
    (fiveFoldProductSum_factor _ _ _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro channel
  exact qmul_congr
    (leftPairSum_eq_fusionCoeff P)
    (rightPairSum_eq_fusionCoeff P)

theorem fourValentFusionDiagonal_eq_bareHaar
    {K : Nat} (P : CharacterPacket K) :
    fsum (fun channel =>
      fusionCoeff (facePacketAtLinkCutoff P)
          (facePacketAtLinkCutoff P) channel *
        fusionCoeff (facePacketAtLinkCutoff P)
          (facePacketAtLinkCutoff P) channel)
      (linkAuxiliaryCutoff K + 1) ≈
      bareVacuumHaar (fourLegCharacterProduct P) := by
  let F := facePacketAtLinkCutoff P
  let T := truncatedFusionPacket F F
  have hdiag :
      fsum (fun channel => fusionCoeff F F channel * fusionCoeff F F channel)
          (linkAuxiliaryCutoff K + 1) ≈
        fsum (fun channel => coeffAt T channel * coeffAt T channel)
          (linkAuxiliaryCutoff K + 1) := by
    apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr_lt
    intro channel hchannel
    have hc : coeffAt T channel = fusionCoeff F F channel := by
      rw [coeffAt_of_lt T hchannel]
      rfl
    rw [hc]
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _
    (fsum (fun channel => coeffAt T channel * coeffAt T channel)
      (linkAuxiliaryCutoff K + 1)) _ hdiag ?_
  refine Q'.eqv_trans _ (fusionHaar T T) _
    (Q'.eqv_symm (fusionHaar_eq_diagonal T T)) ?_
  refine Q'.eqv_trans _
    (bareVacuumHaar (YMGap.Constructive.QPoly.pmul
      (synthesis T) (synthesis T))) _
    (Q'.eqv_symm (barePairing_eq_fusionHaar T T)) ?_
  have hfit : K + K ≤ linkAuxiliaryCutoff K := by
    unfold linkAuxiliaryCutoff linkIncidenceBound
    omega
  have hT : synthesis T ≈ₚ
      YMGap.Constructive.QPoly.pmul (synthesis F) (synthesis F) :=
    synthesis_truncatedFusionPacket F F
      (facePacketAtLinkCutoff_supported P)
      (facePacketAtLinkCutoff_supported P) hfit
  have hF := synthesis_padPacket
    (externalCutoff_le_linkAuxiliaryCutoff K) P
  have hpair : synthesis T ≈ₚ
      YMGap.Constructive.QPoly.pmul (synthesis P) (synthesis P) :=
    peqv_trans hT (pmul_congr hF hF)
  exact bareVacuumHaar_congr
    (pmul_congr hpair hpair)

theorem fourValentVertexSum_eq_canonicalSequential
    {K : Nat} (P : CharacterPacket K) :
    fourValentVertexCartesianSum P ≈
      canonicalSequentialLinkChannelSum P 4 := by
  refine Q'.eqv_trans _ (fourValentExplicitCartesianSum P) _
    (fourValentVertexSum_eq_explicitCartesian P) ?_
  refine Q'.eqv_trans _
    (fsum (fun channel =>
      fusionCoeff (facePacketAtLinkCutoff P)
          (facePacketAtLinkCutoff P) channel *
        fusionCoeff (facePacketAtLinkCutoff P)
          (facePacketAtLinkCutoff P) channel)
      (linkAuxiliaryCutoff K + 1)) _
    (fourValentExplicitCartesianSum_eq_fusionDiagonal P) ?_
  refine Q'.eqv_trans _ (bareVacuumHaar (fourLegCharacterProduct P)) _
    (fourValentFusionDiagonal_eq_bareHaar P) ?_
  refine Q'.eqv_trans _
    (bareVacuumHaar (characterPow (synthesis P) 4)) _
    (Q'.eqv_symm
      (bareVacuumHaar_congr (characterPow_four_eq_fourLegProduct P))) ?_
  exact Q'.eqv_symm
    (canonicalSequentialLinkChannelSum_eq_bareHaar P (by decide))

theorem fourValentVacuumCompletedProjected_eq_canonicalSequential
    {K : Nat} (P : CharacterPacket K) :
    fourValentVacuumCompletedProjectedSum P ≈
      canonicalSequentialLinkChannelSum P 4 := by
  exact Q'.eqv_trans _ (fourValentVertexCartesianSum P) _
    (Q'.eqv_symm (fourValentVertexSum_eq_vacuumCompletedProjected P))
    (fourValentVertexSum_eq_canonicalSequential P)

end YMGap.Continuum.Z4FourValentGraphFusionCompleteHaar

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4FourValentGraphFusionCompleteHaar.fiveFoldProductSum_factor
#print axioms YMGap.Continuum.Z4FourValentGraphFusionCompleteHaar.fourValentCartesianTerm_eq_pairProduct
#print axioms YMGap.Continuum.Z4FourValentGraphFusionCompleteHaar.fourValentExplicitCartesianSum_eq_fiveFold
#print axioms YMGap.Continuum.Z4FourValentGraphFusionCompleteHaar.leftPairSum_eq_fusionCoeff
#print axioms YMGap.Continuum.Z4FourValentGraphFusionCompleteHaar.rightPairSum_eq_fusionCoeff
#print axioms YMGap.Continuum.Z4FourValentGraphFusionCompleteHaar.fourValentExplicitCartesianSum_eq_fusionDiagonal
#print axioms YMGap.Continuum.Z4FourValentGraphFusionCompleteHaar.fourValentFusionDiagonal_eq_bareHaar
#print axioms YMGap.Continuum.Z4FourValentGraphFusionCompleteHaar.fourValentVertexSum_eq_canonicalSequential
#print axioms YMGap.Continuum.Z4FourValentGraphFusionCompleteHaar.fourValentVacuumCompletedProjected_eq_canonicalSequential
