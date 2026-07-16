/-
# Fusion-complete Haar moments for every Z4 link incidence degree

Every physical link of a finite four-dimensional box has between one and six
incident plaquettes.  This module closes the exact local character moment for
all seven possible list lengths `0,...,6` at once.

For an arbitrary external packet `P : CharacterPacket K`, the complete local
channel sum is assembled from exact one-, two-, and three-leg packets.  The
five- and six-leg cases pair a padded two-leg packet with a three-leg packet,
or two three-leg packets.  Their largest intermediate cutoff is `4*K`, hence
it lies inside the conservative Z4 auxiliary window `6*K`.  Exact synthesis
and a general power-addition identity prove that each balanced channel sum is
the bare Haar moment of the corresponding number of external characters.

Specializing the degree to `length (incidentPlaqIds n ell)` therefore proves
local fusion completeness for every actual finite-box link.  This is still a
character-level local identity.  The remaining graph-interface task is to
identify each canonical `fuseLabels` Cartesian enumeration with the balanced
channel presentation before multiplying the local identities across a box.
-/

import YMGap.Continuum.Z4FourValentFusionCompleteHaar

namespace YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2ArbitraryPacketTrivalentVertexCompatibility
open YMGap.Continuum.SU2CharacterFusionSynthesis
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2ClassPolynomialHaarDescent
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FourValentFusionCompleteHaar
open YMGap.Continuum.Z4UnitCubeHaarSectorBridge

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≈ₚ " => PolyEqv

/-! ## 1. Reassociation of finite character powers -/

/-- Character powers split over addition, with no commutativity assumption. -/
theorem characterPow_add (p : Poly) : ∀ m n : Nat,
    characterPow p (m + n) ≈ₚ
      pmul (characterPow p m) (characterPow p n)
  | 0, n => by
      simp only [Nat.zero_add, characterPow]
      exact peqv_symm (pone_pmul (characterPow p n))
  | m + 1, n => by
      simp only [Nat.succ_add, characterPow]
      exact peqv_trans
        (pmul_congr (peqv_refl _) (characterPow_add p m n))
        (peqv_symm
          (pmul_assoc p (characterPow p m) (characterPow p n)))

theorem characterPow_one (p : Poly) :
    characterPow p 1 ≈ₚ p := pmul_pone p

theorem characterPow_two_product (p : Poly) :
    characterPow p 2 ≈ₚ pmul p p := by
  have h := characterPow_add p 1 1
  exact peqv_trans (by simpa using h)
    (pmul_congr (characterPow_one p) (characterPow_one p))

/-! ## 2. Exact balanced packets through degree six -/

def rightTriplePacket {K : Nat} (P : CharacterPacket K) :
    CharacterPacket (trivalentOutputCutoff K) :=
  rightAssociatedPacket P P P

private theorem pairCutoff_le_tripleCutoff (K : Nat) :
    2 * K ≤ trivalentOutputCutoff K := by
  unfold trivalentOutputCutoff
  omega

def pairPacketAtTripleCutoff {K : Nat} (P : CharacterPacket K) :
    CharacterPacket (trivalentOutputCutoff K) :=
  padPacket (pairCutoff_le_tripleCutoff K) (pairedPacket P)

theorem characterPow_two_eq_pairSynthesis {K : Nat}
    (P : CharacterPacket K) :
    characterPow (synthesis P) 2 ≈ₚ synthesis (pairedPacket P) := by
  exact peqv_trans (characterPow_two_product (synthesis P))
    (peqv_symm (synthesis_fusionPacket_product P P))

theorem characterPow_three_eq_tripleSynthesis {K : Nat}
    (P : CharacterPacket K) :
    characterPow (synthesis P) 3 ≈ₚ
      synthesis (rightTriplePacket P) := by
  have hadd := characterPow_add (synthesis P) 1 2
  refine peqv_trans (by simpa using hadd) ?_
  refine peqv_trans
    (pmul_congr (characterPow_one (synthesis P))
      (characterPow_two_product (synthesis P))) ?_
  exact peqv_symm (rightAssociated_synthesis P P P)

theorem characterPow_four_eq_fourLegProduct {K : Nat}
    (P : CharacterPacket K) :
    characterPow (synthesis P) 4 ≈ₚ fourLegCharacterProduct P := by
  have hadd := characterPow_add (synthesis P) 2 2
  exact peqv_trans (by simpa using hadd)
    (pmul_congr (characterPow_two_product (synthesis P))
      (characterPow_two_product (synthesis P)))

theorem characterPow_five_eq_pair_triple {K : Nat}
    (P : CharacterPacket K) :
    characterPow (synthesis P) 5 ≈ₚ
      pmul (synthesis (pairPacketAtTripleCutoff P))
        (synthesis (rightTriplePacket P)) := by
  have hadd := characterPow_add (synthesis P) 2 3
  refine peqv_trans (by simpa using hadd) ?_
  refine peqv_trans
    (pmul_congr (characterPow_two_eq_pairSynthesis P)
      (characterPow_three_eq_tripleSynthesis P)) ?_
  exact pmul_congr
    (peqv_symm
      (synthesis_padPacket (pairCutoff_le_tripleCutoff K) (pairedPacket P)))
    (peqv_refl _)

theorem characterPow_six_eq_triple_square {K : Nat}
    (P : CharacterPacket K) :
    characterPow (synthesis P) 6 ≈ₚ
      pmul (synthesis (rightTriplePacket P))
        (synthesis (rightTriplePacket P)) := by
  have hadd := characterPow_add (synthesis P) 3 3
  exact peqv_trans (by simpa using hadd)
    (pmul_congr (characterPow_three_eq_tripleSynthesis P)
      (characterPow_three_eq_tripleSynthesis P))

/-- Balanced exact local channel sum.  The fallback branch is outside the
geometric degree range and is never used by the actual-link theorem. -/
def completeLocalChannelSum {K : Nat} (P : CharacterPacket K) : Nat → Q'
  | 0 => 1
  | 1 => vacuumHaar P
  | 2 => fusionHaar P P
  | 3 => vacuumHaar (rightTriplePacket P)
  | 4 => completeFourLegChannelSum P
  | 5 => fusionHaar (pairPacketAtTripleCutoff P) (rightTriplePacket P)
  | 6 => fusionHaar (rightTriplePacket P) (rightTriplePacket P)
  | _ => 0

/-! ## 3. Haar identification in every geometric degree -/

theorem completeLocalChannelSum_zero_eq_bareHaar {K : Nat}
    (P : CharacterPacket K) :
    completeLocalChannelSum P 0 ≈
      bareVacuumHaar (characterPow (synthesis P) 0) := by
  change (1 : Q') ≈ bareVacuumHaar
    YMGap.Continuum.SU2ClassPolynomialAlgebra.pone
  decide

theorem completeLocalChannelSum_one_eq_bareHaar {K : Nat}
    (P : CharacterPacket K) :
    completeLocalChannelSum P 1 ≈
      bareVacuumHaar (characterPow (synthesis P) 1) := by
  refine Q'.eqv_trans _ (bareVacuumHaar (synthesis P)) _ ?_ ?_
  · exact Q'.eqv_symm (bareVacuumHaar_synthesis_packet P)
  · exact Q'.eqv_symm
      (bareVacuumHaar_congr (characterPow_one (synthesis P)))

theorem completeLocalChannelSum_two_eq_bareHaar {K : Nat}
    (P : CharacterPacket K) :
    completeLocalChannelSum P 2 ≈
      bareVacuumHaar (characterPow (synthesis P) 2) := by
  refine Q'.eqv_trans _
    (bareVacuumHaar (pmul (synthesis P) (synthesis P))) _ ?_ ?_
  · exact Q'.eqv_symm (barePairing_eq_fusionHaar P P)
  · exact Q'.eqv_symm
      (bareVacuumHaar_congr
        (characterPow_two_product (synthesis P)))

theorem completeLocalChannelSum_three_eq_bareHaar {K : Nat}
    (P : CharacterPacket K) :
    completeLocalChannelSum P 3 ≈
      bareVacuumHaar (characterPow (synthesis P) 3) := by
  refine Q'.eqv_trans _
    (bareVacuumHaar (synthesis (rightTriplePacket P))) _ ?_ ?_
  · exact Q'.eqv_symm
      (bareVacuumHaar_synthesis_packet (rightTriplePacket P))
  · exact Q'.eqv_symm
      (bareVacuumHaar_congr (characterPow_three_eq_tripleSynthesis P))

theorem completeLocalChannelSum_four_eq_bareHaar {K : Nat}
    (P : CharacterPacket K) :
    completeLocalChannelSum P 4 ≈
      bareVacuumHaar (characterPow (synthesis P) 4) := by
  refine Q'.eqv_trans _
    (bareVacuumHaar (fourLegCharacterProduct P)) _
    (completeFourLegChannelSum_eq_bareHaar P) ?_
  exact Q'.eqv_symm
    (bareVacuumHaar_congr (characterPow_four_eq_fourLegProduct P))

theorem completeLocalChannelSum_five_eq_bareHaar {K : Nat}
    (P : CharacterPacket K) :
    completeLocalChannelSum P 5 ≈
      bareVacuumHaar (characterPow (synthesis P) 5) := by
  refine Q'.eqv_trans _
    (bareVacuumHaar
      (pmul (synthesis (pairPacketAtTripleCutoff P))
        (synthesis (rightTriplePacket P)))) _ ?_ ?_
  · exact Q'.eqv_symm
      (barePairing_eq_fusionHaar
        (pairPacketAtTripleCutoff P) (rightTriplePacket P))
  · exact Q'.eqv_symm
      (bareVacuumHaar_congr (characterPow_five_eq_pair_triple P))

theorem completeLocalChannelSum_six_eq_bareHaar {K : Nat}
    (P : CharacterPacket K) :
    completeLocalChannelSum P 6 ≈
      bareVacuumHaar (characterPow (synthesis P) 6) := by
  refine Q'.eqv_trans _
    (bareVacuumHaar
      (pmul (synthesis (rightTriplePacket P))
        (synthesis (rightTriplePacket P)))) _ ?_ ?_
  · exact Q'.eqv_symm
      (barePairing_eq_fusionHaar
        (rightTriplePacket P) (rightTriplePacket P))
  · exact Q'.eqv_symm
      (bareVacuumHaar_congr (characterPow_six_eq_triple_square P))

/-- Uniform local completeness for every degree allowed by four-dimensional
link geometry. -/
theorem completeLocalChannelSum_eq_bareHaar_of_le_six {K degree : Nat}
    (P : CharacterPacket K) (hdegree : degree ≤ 6) :
    completeLocalChannelSum P degree ≈
      bareVacuumHaar (characterPow (synthesis P) degree) := by
  cases degree with
  | zero => exact completeLocalChannelSum_zero_eq_bareHaar P
  | succ d1 =>
      cases d1 with
      | zero => exact completeLocalChannelSum_one_eq_bareHaar P
      | succ d2 =>
          cases d2 with
          | zero => exact completeLocalChannelSum_two_eq_bareHaar P
          | succ d3 =>
              cases d3 with
              | zero => exact completeLocalChannelSum_three_eq_bareHaar P
              | succ d4 =>
                  cases d4 with
                  | zero => exact completeLocalChannelSum_four_eq_bareHaar P
                  | succ d5 =>
                      cases d5 with
                      | zero => exact completeLocalChannelSum_five_eq_bareHaar P
                      | succ d6 =>
                          cases d6 with
                          | zero => exact completeLocalChannelSum_six_eq_bareHaar P
                          | succ beyond => omega

/-! ## 4. Every actual finite-box link -/

def actualLinkCompleteChannelSum (K n : Nat)
    (ell : YMGap.Continuum.ClusterCount4DProgress.Z4Link) : Q' :=
  completeLocalChannelSum (heatKernelPacket K coupling)
    (incidentPlaqIds n ell).length

def actualLinkBareHaarMoment (K n : Nat)
    (ell : YMGap.Continuum.ClusterCount4DProgress.Z4Link) : Q' :=
  bareVacuumHaar
    (characterPow (synthesis (heatKernelPacket K coupling))
      (incidentPlaqIds n ell).length)

/-- **All actual local link moments are fusion-complete.** -/
theorem actualLinkCompleteChannelSum_eq_bareHaar
    (K n : Nat) (ell : YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    actualLinkCompleteChannelSum K n ell ≈
      actualLinkBareHaarMoment K n ell := by
  exact completeLocalChannelSum_eq_bareHaar_of_le_six
    (heatKernelPacket K coupling)
    (incidentPlaqIds_length_le_six n ell)

end YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar.characterPow_add
#print axioms YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar.characterPow_two_eq_pairSynthesis
#print axioms YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar.characterPow_three_eq_tripleSynthesis
#print axioms YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar.characterPow_four_eq_fourLegProduct
#print axioms YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar.characterPow_five_eq_pair_triple
#print axioms YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar.characterPow_six_eq_triple_square
#print axioms YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar.completeLocalChannelSum_zero_eq_bareHaar
#print axioms YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar.completeLocalChannelSum_one_eq_bareHaar
#print axioms YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar.completeLocalChannelSum_two_eq_bareHaar
#print axioms YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar.completeLocalChannelSum_three_eq_bareHaar
#print axioms YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar.completeLocalChannelSum_four_eq_bareHaar
#print axioms YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar.completeLocalChannelSum_five_eq_bareHaar
#print axioms YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar.completeLocalChannelSum_six_eq_bareHaar
#print axioms YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar.completeLocalChannelSum_eq_bareHaar_of_le_six
#print axioms YMGap.Continuum.Z4AllLocalDegreesFusionCompleteHaar.actualLinkCompleteChannelSum_eq_bareHaar
