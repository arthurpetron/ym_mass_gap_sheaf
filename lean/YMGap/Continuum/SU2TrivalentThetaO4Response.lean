/-
# Multi-mode O(4) response on a globally wired trivalent theta state

The one-mode theta response retains only the pure `(2,2,2)` coordinate.  Here
all `4^3` cutoff-three theta labels are flattened into one exact finite
spectral algebra.  Their weights are the actual globally wired Wilson terms:
the common edge eigenvalue product times the square of the amplitude after
both trivalent vertex projectors and global-vacuum removal.

The flattening identity proves that the normalizing partition is exactly the
nested wired theta Gram.  Therefore every positive-norm fused theta state
produces a normalized positive functional and an exact same-state
quarter-turn response on four directional copies.  A concrete even packet
with both vacuum and quadratic edge channels has four nonzero admissible
theta labels, so the checked instance is genuinely multi-mode.

Honest scope: this closes one finite trivalent theta cell.  Compatibility of
overlapping cells, higher-valence F-moves, and the continuum family of
physical rotations remain open.
-/

import YMGap.Continuum.SU2ThetaModeO4Response
import YMGap.Continuum.SchurHadamardTransfer
import YMGap.Continuum.MovingCutoff

namespace YMGap.Continuum.SU2TrivalentThetaO4Response

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RegularLinearScalingLimit
open YMGap.Continuum.O4RestorationAF
open YMGap.Continuum.O4ObservableSymmetryBridge
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2FiniteCharacterPacketO4Response
open YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum
open YMGap.Continuum.SU2TrivalentSharedLinkPacketSpectralBridge
open YMGap.Continuum.SU2TrivalentThetaRecoupling
open YMGap.Continuum.SU2BivalentCycleO4Response
open YMGap.Continuum.SU2TrivalentThetaSharedPacketSpectralGluing
open YMGap.Continuum.SU2ThetaModeO4Response

local infix:50 " ≈ " => Q'.eqv

/-! ## Flatten all `4^3` globally projected theta coordinates -/

/-- Row-major decoder for the three cutoff-three theta labels. -/
def thetaFlatLabel (p : Nat) : TrivalentLabel :=
  (p / 16, ((p % 16) / 4, (p % 16) % 4))

/-- The diagonal same-state weight of a flattened theta coordinate. -/
def thetaFlatWeight (x : ThetaFusedLinks) (p : Nat) : Q' :=
  thetaWiredWilsonTerm x x (thetaFlatLabel p)

theorem thetaPacketEigen_nonneg (j : TrivalentLabel) :
    (0 : Q') ≤ thetaPacketEigen j := by
  unfold thetaPacketEigen
  exact Q'.mul_nonneg _ _ (packetEigen_nonneg j.1)
    (Q'.mul_nonneg _ _ (packetEigen_nonneg j.2.1)
      (packetEigen_nonneg j.2.2))

theorem thetaWiredWilsonTerm_self_nonneg (x : ThetaFusedLinks)
    (j : TrivalentLabel) :
    (0 : Q') ≤ thetaWiredWilsonTerm x x j := by
  unfold thetaWiredWilsonTerm
  exact Q'.mul_nonneg _ _ (thetaPacketEigen_nonneg j)
    (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
      (thetaTwoVertexAmplitude x j))

theorem thetaFlatWeight_nonneg (x : ThetaFusedLinks) :
    ∀ p, (0 : Q') ≤ thetaFlatWeight x p :=
  fun p => thetaWiredWilsonTerm_self_nonneg x (thetaFlatLabel p)

/-- The single `64`-coordinate partition is exactly the original nested
`4·4·4` globally wired theta Gram. -/
theorem thetaFlatWeight_partition (x : ThetaFusedLinks) :
    fsum (thetaFlatWeight x) 64 ≈ thetaWiredWilsonGram x x := by
  unfold thetaFlatWeight thetaFlatLabel thetaWiredWilsonGram
  simp only [MovingCutoff.fsum_eq_finSum]
  refine Q'.eqv_trans _
    (finSum (fun a => finSum (fun p =>
      thetaWiredWilsonTerm x x (a, (p / 4, p % 4))) 16) 4) _ ?_ ?_
  · exact SchurHadamardTransfer.finSum_flatten
      (fun a p => thetaWiredWilsonTerm x x (a, (p / 4, p % 4))) 16 4
  · exact finSum_eqv_congr _ _ (fun a =>
      SchurHadamardTransfer.finSum_flatten
        (fun b c => thetaWiredWilsonTerm x x (a, b, c)) 4 4) 4

/-- Every positive-norm globally wired theta state defines exact positive
weights on all 64 retained labels. -/
def trivalentThetaWeightData (x : ThetaFusedLinks)
    (hpos : (0 : Q') < thetaWiredWilsonGram x x) :
    PositivePacketWeight 63 where
  weight := thetaFlatWeight x
  weight_nonneg := thetaFlatWeight_nonneg x
  partition_pos := Q'.pos_of_lt_of_le hpos
    (Q'.ge_of_eqv (thetaFlatWeight_partition x))

theorem trivalentThetaWeight_partition_is_wired_state (x : ThetaFusedLinks)
    (hpos : (0 : Q') < thetaWiredWilsonGram x x) :
    fsum (trivalentThetaWeightData x hpos).weight 64 ≈
      thetaWiredWilsonGram x x :=
  thetaFlatWeight_partition x

/-! ## A genuinely multi-mode even theta state -/

/-- One edge contains both the vacuum and quadratic retained channels. -/
def vacuumQuadraticIrrep : TripleIrrep := (1, (0, (1, 0)))

def vacuumQuadraticThetaLinks : ThetaFusedLinks :=
  (vacuumQuadraticIrrep,
    (vacuumQuadraticIrrep, vacuumQuadraticIrrep))

/-- Four distinct nonvacuum admissible labels survive both endpoint
projectors, rather than only the pure `(2,2,2)` coordinate. -/
theorem vacuumQuadratic_four_theta_amplitudes :
    thetaTwoVertexAmplitude vacuumQuadraticThetaLinks (0, 2, 2) ≈ 1 ∧
    thetaTwoVertexAmplitude vacuumQuadraticThetaLinks (2, 0, 2) ≈ 1 ∧
    thetaTwoVertexAmplitude vacuumQuadraticThetaLinks (2, 2, 0) ≈ 1 ∧
    thetaTwoVertexAmplitude vacuumQuadraticThetaLinks (2, 2, 2) ≈ 1 := by
  unfold thetaTwoVertexAmplitude thetaNonvacuum thetaTensorAmplitude
    thetaEdgePacket thetaFusedEdge vacuumQuadraticThetaLinks
    vacuumQuadraticIrrep tripleIrrepPacket trivalentMultiplicity fusionInd
    fusionOK coeffAt
  decide

theorem vacuumQuadratic_flat42_is_spinOneEigen :
    thetaFlatWeight vacuumQuadraticThetaLinks 42 ≈
      thetaSpinOneTransferEigen := by
  change thetaWiredWilsonTerm vacuumQuadraticThetaLinks
    vacuumQuadraticThetaLinks (2, 2, 2) ≈ thetaSpinOneTransferEigen
  let a := thetaTwoVertexAmplitude vacuumQuadraticThetaLinks (2, 2, 2)
  have ha : a ≈ 1 := vacuumQuadratic_four_theta_amplitudes.2.2.2
  have haa : a * a ≈ 1 := by
    refine Q'.eqv_trans _ (1 * a) _
      (Q'.mul_eqv_congr_right a 1 a ha) ?_
    refine Q'.eqv_trans _ (1 * 1) _
      (Q'.mul_eqv_congr_left 1 a 1 ha) (Q'.one_mul_eqv 1)
  unfold thetaWiredWilsonTerm thetaSpinOneTransferEigen
  refine Q'.eqv_trans _
    (thetaPacketEigen (2, 2, 2) * 1) _
    (Q'.mul_eqv_congr_left (thetaPacketEigen (2, 2, 2)) (a * a) 1 haa) ?_
  exact Q'.mul_one_eqv _

theorem vacuumQuadratic_thetaGram_pos :
    (0 : Q') < thetaWiredWilsonGram vacuumQuadraticThetaLinks
      vacuumQuadraticThetaLinks := by
  have hflat : (0 : Q') < thetaFlatWeight vacuumQuadraticThetaLinks 42 :=
    Q'.pos_of_lt_of_le thetaSpinOneTransferEigen_pos
      (Q'.ge_of_eqv vacuumQuadratic_flat42_is_spinOneEigen)
  have hterm : thetaFlatWeight vacuumQuadraticThetaLinks 42 ≤
      fsum (thetaFlatWeight vacuumQuadraticThetaLinks) 64 :=
    BondMovingMoment.fsum_term_le_of_nonneg
      (thetaFlatWeight_nonneg vacuumQuadraticThetaLinks) 42 64 (by decide)
  have hsum : (0 : Q') <
      fsum (thetaFlatWeight vacuumQuadraticThetaLinks) 64 :=
    Q'.pos_of_lt_of_le hflat hterm
  exact Q'.pos_of_lt_of_le hsum
    (Q'.le_of_eqv (thetaFlatWeight_partition vacuumQuadraticThetaLinks))

def vacuumQuadraticThetaWeightData : PositivePacketWeight 63 :=
  trivalentThetaWeightData vacuumQuadraticThetaLinks
    vacuumQuadratic_thetaGram_pos

/-! ## Same-state response and limiting invariance -/

theorem trivalentThetaQuarterTurn_same_state_response
    (x : ThetaFusedLinks) (hpos : (0 : Q') < thetaWiredWilsonGram x x)
    (o : PacketDir4 63) (j : Nat) :
    ((weightedDir4Scaling (trivalentThetaWeightData x hpos)).atSpacing j).E
        ((packetQuarterTurnHom 63).map o) ≤
      ((weightedDir4Scaling (trivalentThetaWeightData x hpos)).atSpacing j).E o +
        weightedDir4Response (trivalentThetaWeightData x hpos) o *
          breakCoeff halfScalingDecay j
    /\
    ((weightedDir4Scaling (trivalentThetaWeightData x hpos)).atSpacing j).E o ≤
      ((weightedDir4Scaling (trivalentThetaWeightData x hpos)).atSpacing j).E
          ((packetQuarterTurnHom 63).map o) +
        weightedDir4Response (trivalentThetaWeightData x hpos) o *
          breakCoeff halfScalingDecay j :=
  weightedQuarterTurn_same_state_response
    (trivalentThetaWeightData x hpos) o j

theorem vacuumQuadraticTheta_limit_quarterTurn_invariant
    (o : PacketDir4 63) :
    RegularCReal.Equiv
      (limitE (weightedDir4Scaling vacuumQuadraticThetaWeightData)
        ((packetQuarterTurnHom 63).map o))
      (limitE (weightedDir4Scaling vacuumQuadraticThetaWeightData) o) :=
  weightedDir4_limit_quarterTurn_invariant vacuumQuadraticThetaWeightData o

end YMGap.Continuum.SU2TrivalentThetaO4Response

#print axioms YMGap.Continuum.SU2TrivalentThetaO4Response.thetaFlatWeight_partition
#print axioms YMGap.Continuum.SU2TrivalentThetaO4Response.trivalentThetaWeightData
#print axioms YMGap.Continuum.SU2TrivalentThetaO4Response.vacuumQuadratic_four_theta_amplitudes
#print axioms YMGap.Continuum.SU2TrivalentThetaO4Response.vacuumQuadratic_flat42_is_spinOneEigen
#print axioms YMGap.Continuum.SU2TrivalentThetaO4Response.vacuumQuadratic_thetaGram_pos
#print axioms YMGap.Continuum.SU2TrivalentThetaO4Response.vacuumQuadraticThetaWeightData
#print axioms YMGap.Continuum.SU2TrivalentThetaO4Response.trivalentThetaQuarterTurn_same_state_response
#print axioms YMGap.Continuum.SU2TrivalentThetaO4Response.vacuumQuadraticTheta_limit_quarterTurn_invariant
