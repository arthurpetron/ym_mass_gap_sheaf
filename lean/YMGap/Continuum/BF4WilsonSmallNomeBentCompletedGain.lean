/-
# The original small-nome bent loop has a nonzero completed T1 image

The literal six-edge bent source is placed on the EXISTING width-two
all-nome Wilson completion. At every terminal depth and late finite cutoff,
its actual OWN-centered filtered square divided by its SAME even partition
is at least 2^(-128). Its original chronological lag-two window therefore
has that floor. The existing moving-OWN-center convergence theorem passes
the floor to the SAME centered vector and original completed time map.

This is fixed nome 1/16, width two and the literal bent observable. It is
not a growing-square or changing-family survival estimate, a new normalized
state, a continuum construction, or a physical mass-gap statement.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockWindowPin
import YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows
import YMGap.Continuum.BF4WilsonAllNomeBilinearTime

namespace YMGap.Continuum.BF4WilsonSmallNomeBentCompletedGain

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (link orientedLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
  (cubeLinks cubeLinks_in_carrier bentEdges bentObservable bentObservable_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap
  (smallNome smallNome_pos)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean (originalOddMean)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain
  (relativeSquareFloor originalSquare originalOwn_normalized_square_floor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial (mean_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
  (evenPartition evenPartition_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain (centeredMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockWindowPin (block_window_numerator)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (observedMessage windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference (centeredPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit
  (own_centeredPair_converges)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows (limit_le_of_eventual)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_coeff)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord (wordAt)
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar (orientedCoordinateQuaternion)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector
  (centeredVector centeredExcitation centeredVector_time_pairing)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedInner_time_sum)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedZero)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime (completedInner_zero_left)

local infix:50 " ≈ " => Q'.eqv
local notation "hw0" => smallNome_pos
local notation "hw1" => (by decide : smallNome < (1 : Q'))
local notation "N" => List.length (baseLinks 2)

private theorem bent_physical (e : OrientedBF4Link) (he : e ∈ bentEdges) :
    e.link ∈ baseLinks 2 := by
  apply cubeLinks_in_carrier
  simp only [bentEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/-- The exact original bent path, not a face-span replacement. -/
def bentLoop : SourceLoop 2 where
  start := (0,0,0,0)
  edges := bentEdges
  compatible := by
    simp only [bentEdges, BF4ExactSlabTemporalGaugeWilsonWord.Compatible]
    decide
  closed := by decide
  physical := bent_physical

private theorem wordAt_sourceWord (width : Nat) :
    ∀ (es : List OrientedBF4Link),
      (∀ e, e ∈ es → e.link ∈ baseLinks width) →
      wordAt (fun e => (baseLinks width).idxOf e.link) es = sourceWord width es
  | [], _ => rfl
  | e::es, hphysical => by
      have he := hphysical e List.mem_cons_self
      have ht : ∀ f, f ∈ es → f.link ∈ baseLinks width :=
        fun f hf => hphysical f (List.mem_cons_of_mem e hf)
      change PolyQuaternion.mul
          (orientedCoordinateQuaternion ((baseLinks width).idxOf e.link) e.reverse)
          (wordAt (fun f => (baseLinks width).idxOf f.link) es) =
        PolyQuaternion.mul (orientedLink width e) (sourceWord width es)
      rw [wordAt_sourceWord width es ht]
      unfold orientedLink link
      rw [if_pos he]
      rfl

theorem bentLoop_source_pin : sourceCharacter 2 bentLoop.edges 1 = bentObservable := by
  unfold sourceCharacter bentObservable
  rw [wordAt_sourceWord 2 bentEdges bent_physical]
  rfl

attribute [local irreducible] baseLinks weightedMass terminalMessage bentObservable
  originalOddMean originalSquare evenPartition centeredMessage centeredPair
  windowRatio middleRatio

private theorem normalized_square_window_pin (K : Nat)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) (c : Q') :
    Q'.divPos (originalSquare K n c) (evenPartition smallNome K 2 n)
      (evenPartition_positive hw0 hw1 K 2 hhead n) ≈
    centeredPair hw0 hw1 K 2 hhead n 2 bentObservable c := by
  have hnum : originalSquare K n c ≈ weightedMass smallNome K 2
      (polyMul (observedMessage smallNome K 2 n 2
        (polyMul (shifted bentObservable c)
          (liftBoundary (2*N) (shifted bentObservable c))))
        (terminalMessage smallNome K 2 n)) := by
    simpa only [originalSquare, centeredMessage, originalBlockTransfer,
      iterateStep, transferStep, Nat.add_zero, Nat.mul_one] using
      block_window_numerator smallNome K 2 n 1 0
        (shifted_supported bentObservable_supported c)
  unfold Q'.divPos centeredPair windowRatio massRatio evenPartition
  exact Q'.mul_eqv_congr_right _ _ _ hnum

private theorem centeredPair_center_congr (K : Nat)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) {c d : Q'} (h : c ≈ d) :
    centeredPair hw0 hw1 K 2 hhead n 2 bentObservable c ≈
    centeredPair hw0 hw1 K 2 hhead n 2 bentObservable d := by
  have hs : RatPolyCoeffEqv (shifted bentObservable c) (shifted bentObservable d) := by
    unfold shifted
    exact (RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.smul_coefficient
      (Q'.neg_eqv_congr _ _ h) polyOne)
  unfold centeredPair
  exact windowRatio_congr hw0 hw1 K 2 hhead n 2 n
    (hs.mul (lift_coeff (2*N) hs))

/-- The SAME original even-normalized square is the chronological lag-two
pair, with the actual odd OWN mean transported, not changed. -/
theorem originalOwn_square_chronological_pin (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    Q'.divPos (originalSquare K n (originalOddMean K hK hhead n))
      (evenPartition smallNome K 2 n)
      (evenPartition_positive hw0 hw1 K 2 hhead n) ≈
    centeredPair hw0 hw1 K 2 hhead n 2 bentObservable
      (middleRatio hw0 hw1 K 2 hhead (n+1) n bentObservable) := by
  have hc : originalOddMean K hK hhead n ≈
      middleRatio hw0 hw1 K 2 hhead (n+1) n bentObservable := by
    unfold originalOddMean
    exact mean_pin hw0 hw1 K 2 hhead n bentObservable_supported
  exact Q'.eqv_trans _ _ _
    (normalized_square_window_pin K hhead n (originalOddMean K hK hhead n))
    (centeredPair_center_congr K hhead n hc)

/-- No source, center or norm is selected anew at completion. -/
theorem bent_centered_lag_two_floor :
    leEv (ofQ' relativeSquareFloor)
      (centeredTimeMoment hw0 hw1 2 (loopState bentLoop) (loopState bentLoop)) := by
  apply limit_le_of_eventual (convergesTo_const (ofQ' relativeSquareFloor))
    (own_centeredPair_converges hw0 hw1 bentLoop 2) 1
  intro k hk
  have hK : 1 ≤ headCutoff smallNome+k := by omega
  have hfloor := originalOwn_normalized_square_floor
    (headCutoff smallNome+k) hK (Nat.le_add_right _ _) k
  have hpin := originalOwn_square_chronological_pin
    (headCutoff smallNome+k) hK (Nat.le_add_right _ _) k
  rw [bentLoop_source_pin]
  exact leEv_of_le (ofQ'_le_ofQ'
    (Q'.le_trans' _ _ _ hfloor (Q'.le_of_eqv hpin)))

local notation "v" => centeredVector hw0 hw1 (loopState bentLoop)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

/-- A positive norm on the original one-step image of the constructed
vacuum-complement vector, not on a surrogate normalized state. -/
theorem bent_completed_T1_norm_floor :
    RCle (Rq relativeSquareFloor) (B (T 1 v) (T 1 v)) := by
  rw [completedInner_time_sum, centeredVector_time_pairing]
  exact bent_centered_lag_two_floor

theorem bent_completed_T1_norm_ne_zero : B (T 1 v) (T 1 v) ≠ RCzero := by
  intro hz
  have h := bent_completed_T1_norm_floor
  rw [hz] at h
  have hbad : relativeSquareFloor ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨M, hM⟩ := h epsilon he
    exact hM M (Nat.le_refl M)
  exact (by decide : ¬ relativeSquareFloor ≤ (0 : Q')) hbad

theorem bent_completed_T1_ne_zero : T 1 v ≠ completedZero hw0 hw1 2 := by
  intro hz
  apply bent_completed_T1_norm_ne_zero
  rw [hz, completedInner_zero_left]

#print axioms bentLoop
#print axioms bentLoop_source_pin
#print axioms originalOwn_square_chronological_pin
#print axioms bent_centered_lag_two_floor
#print axioms bent_completed_T1_norm_floor
#print axioms bent_completed_T1_norm_ne_zero
#print axioms bent_completed_T1_ne_zero

end YMGap.Continuum.BF4WilsonSmallNomeBentCompletedGain
