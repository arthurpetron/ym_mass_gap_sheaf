/-
# A favorable ORIGINAL terminal-tested overlap at every depth

Keep the sharper action-channel floor until AFTER the actual terminal
fluctuation is paid. The exact kinetic multiplier remains outside both
errors. The center may be any c with |c|<=1/4; the final consumer uses the
constructed original interacting OWN mean. Haar amplitude is not a partition.
No growing-loop, changing-family, completed survival or continuum claim.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTest
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffChannelFloor
import YMGap.Constructive.ExpAddConv

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOverlap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported plaquette_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence (characterFace_independent_index)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain (centeredMessage)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion (firstFaceTrace)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap (smallNome)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval (cubeInterval actionDifferenceCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffTestedTransfer
  (testedActionRemainder tested_centered_channel tested_centered_cutoff_decomposition)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffChannelFloor (testedActionRemainder_abs_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOddBackgroundInterval (bentObservableInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSharpHeatFloor (actionDeviation sharpCubeRemainder)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalVariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalTerminalShape (original_haar_mass_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean
  (original_terminal_weighted_pin originalOddMean originalOddMean_abs_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTest (terminal_centered_test)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval (sharpCharacterInterval)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.QuaternionHaarRelativeShapePair (single_shape_insertion_bound)
open YMGap.Continuum.BondMovingStep (coeffW)

local notation "N" => List.length (baseLinks 2)
local notation:max "H" p:arg => quaternionHaar N p
local notation "quarter" => Q'.mkPos 1 4 (by decide)
local notation "nineHalves" => Q'.mkPos 9 2 (by decide)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks cubeWeight terminalMessage cubeTerminal centeredMessage

def terminalTestRate : Q' := qpow smallNome 12 * (coeffW smallNome 1 * Q'.mkPos 1 16 (by decide))

private def test (c : Q') : RatPoly := polyMul firstFaceTrace (shifted bentObservable c)
private def testWeight (K : Nat) (c : Q') : RatPoly := polyMul (cubeWeight smallNome K) (test c)

private def firstInterval : Interval N firstFaceTrace 2 :=
  (sharpCharacterInterval (SquareBound.scalar
    (plaquette_supported 2 N (Nat.le_refl _) ((0,0,0,0),.p01))
    (plaquette_unit 2 N (Nat.le_refl _) ((0,0,0,0),.p01))) 1).changeCap (by decide)

private theorem first_independent (i : Nat) (hi : i < N) (hn : i ∉ cubeIndices) :
    QuaternionBlockIndependent i firstFaceTrace := by
  apply characterFace_independent_index 2 ((0,0,0,0),.p01) i 1 hi
  intro l hl _ he
  have hb : (edgesOf ((0,0,0,0),.p01)).all (fun l => decide (l ∈ cubeLinks)) = true := by decide
  have hc : l ∈ cubeLinks := of_decide_eq_true ((List.all_eq_true.mp hb) l hl)
  exact hn (he ▸ List.mem_map.mpr ⟨l, hc, rfl⟩)

private theorem test_independent (c : Q') (i : Nat) (hi : i < N) (hn : i ∉ cubeIndices) :
    QuaternionBlockIndependent i (test c) := by
  unfold test shifted
  exact quaternionBlockIndependent_polyMul (first_independent i hi hn)
    (quaternionBlockIndependent_polyAdd
      (quaternionBlockIndependent_polySmul 1 (bentObservable_cube_independent i hi hn))
      (quaternionBlockIndependent_polySmul (-c) (quaternionBlockIndependent_polyOne i)))

private def minusCenterInterval (c : Q') (hc : Q'.abs c ≤ quarter) :
    Interval N (cap (-c)) quarter where
  support := polySmul_supported (supported_one N) (-c)
  nonnegative := by decide
  upper := by
    have hn : RatPolyCoeffEqv (polyNeg (cap (-c))) (cap c) :=
      (neg_smul _).trans ((RatPolyCoeffEqv.smul_assoc (-1) (-c) polyOne).trans
        (RatPolyCoeffEqv.smul_coefficient (poly_identity_of_normal_eq
          (.mul (.const (-1)) (.neg (.var 0))) (.var 0) (by decide) (fun _ => c)) polyOne))
    have hl : -quarter ≤ c := Q'.le_trans' _ _ _ (Q'.neg_le_neg hc)
      (Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.neg_le_abs c)) (Q'.le_of_eqv (Q'.neg_neg_eqv c)))
    exact .ofCoeff (((RatPolyCoeffEqv.refl _).add hn).trans (cap_add quarter c))
      (.constant N (quarter+c) (Q'.le_trans' _ _ _
        (by decide : (0 : Q') ≤ quarter + -quarter) (Q'.add_le_add_left quarter _ _ hl)))
  lower := .ofCoeff (cap_add quarter (-c))
    (.constant N (quarter + -c) (Q'.sub_nonneg_of_le (Q'.le_trans' _ _ _ (Q'.le_abs_self c) hc)))

/-- Constructed dimension-two trace interval about the supplied bounded
center. The actual OWN mean is supplied separately, not assumed here. -/
def centeredInterval (c : Q') (hc : Q'.abs c ≤ quarter) :
    Interval N (shifted bentObservable c) (Q'.mkPos 9 4 (by decide)) := by
  have hs := shifted_supported bentObservable_supported c
  have hp : RatPolyCoeffEqv (shifted bentObservable c)
      (polyAdd bentObservable (cap (-c))) :=
    (RatPolyCoeffEqv.one_smul bentObservable).add (RatPolyCoeffEqv.refl _)
  exact (Interval.ofCoeff hs hp
    (bentObservableInterval.add (minusCenterInterval c hc))).changeCap (by decide)

private def testInterval (c : Q') (hc : Q'.abs c ≤ quarter) : Interval N (test c) nineHalves :=
  (firstInterval.mul (centeredInterval c hc)).changeCap (by decide)

private def weightInterval (K : Nat) (hK : 1 ≤ K) :
    Interval N (cubeWeight smallNome K) (1+actionDeviation) := by
  have he : RatPolyCoeffEqv (cubeWeight smallNome K)
      (polyAdd (polyAdd (cubeWeight smallNome K) (polyNeg polyOne)) polyOne) :=
    coeffEvalExpr_eqv_of_normalize_eq (.var 0)
      (.add (.add (.var 0) (.neg (.const 1))) (.const 1)) (by decide)
      (fun _ => cubeWeight smallNome K)
  exact (Interval.ofCoeff (cubeInterval K hK).support he
    ((sharpCubeRemainder K hK).add (Interval.one N))).changeCap (by decide)

private def lowChannel (c : Q') : Q' :=
  (coeffW smallNome 1 * HalfPow.half + qpow (coeffW smallNome 1) 5 * Q'.mkPos 1 8 (by decide)) -
    c*(coeffW smallNome 1 + qpow (coeffW smallNome 1) 5 * Q'.mkPos 1 16 (by decide))

private theorem action_test_pin (K : Nat) (c : Q') :
    H (testWeight K c) ≈ H (polyMul (polyMul firstFaceTrace bentObservable) (cubeWeight smallNome K)) -
      c*H (polyMul firstFaceTrace (cubeWeight smallNome K)) := by
  have hp : RatPolyCoeffEqv (testWeight K c)
      (polyAdd (polyMul (polyMul firstFaceTrace bentObservable) (cubeWeight smallNome K))
        (polySmul (-c) (polyMul firstFaceTrace (cubeWeight smallNome K)))) := by
    unfold testWeight test shifted
    exact ((RatPolyCoeffEqv.refl _).mul ((RatPolyCoeffEqv.refl _).mul
      ((RatPolyCoeffEqv.one_smul bentObservable).add (RatPolyCoeffEqv.refl _)))).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.mul (.var 1) (.add (.var 2) (.var 3))))
        (.add (.mul (.mul (.var 1) (.var 2)) (.var 0))
          (.mul (.var 3) (.mul (.var 1) (.var 0)))) (by decide) (fun
            | 0 => cubeWeight smallNome K
            | 1 => firstFaceTrace
            | 2 => bentObservable
            | _ => cap (-c))).trans
        ((RatPolyCoeffEqv.refl _).add (cap_mul_left (-c) _)))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N) hp)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append N _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (quaternionHaar_polySmul N (-c) _))
        (poly_identity_of_normal_eq (.add (.var 0) (.mul (.neg (.var 1)) (.var 2)))
          (.add (.var 0) (.neg (.mul (.var 1) (.var 2)))) (by decide) (fun
            | 0 => H (polyMul (polyMul firstFaceTrace bentObservable) (cubeWeight smallNome K))
            | 1 => c
            | _ => H (polyMul firstFaceTrace (cubeWeight smallNome K))))))

/-- The sharper actual action signal is retained before paying terminal error. -/
theorem action_channel_sharp_lower (K : Nat) (hK : 1 ≤ K) (c : Q') (hc : Q'.abs c ≤ quarter) :
    coeffW smallNome 1*quarter - nineHalves*actionDifferenceCap ≤ H (testWeight K c) := by
  have hraw := Q'.mul_left_cancel_of_pos (by decide : (0 : Q') < qpow smallNome 12)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (tested_centered_channel smallNome K hK c))
      (tested_centered_cutoff_decomposition smallNome K hK c))
  have hpin := Q'.eqv_trans _ _ _ (action_test_pin K c) hraw
  have hl : coeffW smallNome 1*quarter ≤ lowChannel c := by
    have hmono := Q'.add_le_add_left
      (coeffW smallNome 1*HalfPow.half + qpow (coeffW smallNome 1) 5 * Q'.mkPos 1 8 (by decide)) _ _
      (Q'.neg_le_neg (Q'.mul_le_mul_of_nonneg_right _ _ _
        (Q'.le_trans' _ _ _ (Q'.le_abs_self c) hc)
        (by decide : (0 : Q') ≤ coeffW smallNome 1 + qpow (coeffW smallNome 1) 5 * Q'.mkPos 1 16 (by decide))))
    exact Q'.le_trans' _ _ _ (by decide : coeffW smallNome 1*quarter ≤ lowChannel quarter) hmono
  have hr : -(nineHalves*actionDifferenceCap) ≤ testedActionRemainder smallNome K c :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg (testedActionRemainder_abs_le K hK c hc))
      (Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.neg_le_abs _)) (Q'.le_of_eqv (Q'.neg_neg_eqv _)))
  exact Q'.le_trans' _ _ _ (Q'.add_le_add hl hr) (Q'.ge_of_eqv hpin)

private theorem terminal_source_pin (K : Nat) (hK : 1 ≤ K) (n : Nat) (c : Q') :
    H (polyMul firstFaceTrace (centeredMessage smallNome K 2 n bentObservable c)) ≈
      qpow smallNome 12 * H (polyMul (testWeight K c) (cubeTerminal K n)) := by
  -- Support does not depend on a bound for c.
  have hts := supported_polyMul firstInterval.support (shifted_supported bentObservable_supported c)
  have ha : weightedMass smallNome K 2
      (polyMul firstFaceTrace (polyMul (terminalMessage smallNome K 2 n) (shifted bentObservable c))) ≈
      weightedMass smallNome K 2 (polyMul (terminalMessage smallNome K 2 n) (test c)) :=
    weightedMass_congr smallNome K 2 (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => firstFaceTrace | 1 => terminalMessage smallNome K 2 n | _ => shifted bentObservable c))
  have hb := original_terminal_weighted_pin K n hts (test_independent c)
  have he : RatPolyCoeffEqv
      (polyMul (cubeWeight smallNome K) (polyMul (cubeTerminal K n) (test c)))
      (polyMul (testWeight K c) (cubeTerminal K n)) :=
    coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => cubeWeight smallNome K | 1 => cubeTerminal K n | _ => test c)
  exact Q'.eqv_trans _ _ _ (terminal_centered_test smallNome K hK n c)
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ ha
      (Q'.eqv_trans _ _ _ hb (haar_of_coeff (blocks := N) he))))

/-- The actual favorable terminal overlap, uniformly in depth and guarded K,
relative to the ORIGINAL message's own bare Haar amplitude. -/
theorem terminal_tested_floor (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) (c : Q') (hc : Q'.abs c ≤ quarter) :
    terminalTestRate * H (terminalMessage smallNome K 2 n) ≤
      H (polyMul firstFaceTrace (centeredMessage smallNome K 2 n bentObservable c)) := by
  let a := H (cubeTerminal K n)
  let L := H (testWeight K c)
  let J := H (polyMul (testWeight K c) (cubeTerminal K n))
  let e := (1+actionDeviation)*nineHalves*terminalRadius
  have ha := Q'.le_of_lt (cubeTerminal_mass_positive K hK hhead n)
  have herror := single_shape_insertion_bound (cubeTerminal_supported K n)
    ((weightInterval K hK).mul (testInterval c hc))
    (cubeTerminal_mass_positive K hK hhead n) (by decide : (0 : Q') ≤ terminalRadius)
    (cubeTerminal_variance_bound K hK hhead n)
  have hl : -(e*a) ≤ J-a*L := Q'.le_trans' _ _ _ (Q'.neg_le_neg herror)
    (Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.neg_le_abs _)) (Q'.le_of_eqv (Q'.neg_neg_eqv _)))
  have hj : a*L-e*a ≤ J := Q'.le_trans' _ _ _
    (Q'.add_le_add_left (a*L) _ _ hl)
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.add (.var 2) (.neg (.mul (.var 0) (.var 1)))))
      (.var 2) (by decide) (fun | 0 => a | 1 => L | _ => J)))
  have hb := Q'.add_le_add_right _ _ (-(e*a))
    (Q'.mul_le_mul_of_nonneg_left _ _ a (action_channel_sharp_lower K hK c hc) ha)
  have hs : (coeffW smallNome 1 * Q'.mkPos 1 16 (by decide))*a ≤ J :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ a
        (by decide : coeffW smallNome 1 * Q'.mkPos 1 16 (by decide) ≤
          coeffW smallNome 1*quarter - nineHalves*actionDifferenceCap - e) ha)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
        (.add (.mul (.var 2) (.var 0)) (.neg (.mul (.var 1) (.var 2)))) (by decide)
        (fun | 0 => coeffW smallNome 1*quarter-nineHalves*actionDifferenceCap | 1 => e | _ => a)))
        (Q'.le_trans' _ _ _ hb hj))
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (qpow smallNome 12) hs (by decide)
  have hrhs := terminal_source_pin K hK n c
  have hmass := original_haar_mass_pin K n
  unfold terminalTestRate
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hmass))))
    (Q'.le_trans' _ _ _ hm (Q'.ge_of_eqv hrhs))

theorem originalOwn_tested_floor (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    terminalTestRate * H (terminalMessage smallNome K 2 n) ≤
      H (polyMul firstFaceTrace (centeredMessage smallNome K 2 n bentObservable
        (originalOddMean K hK hhead n))) :=
  terminal_tested_floor K hK hhead n _ (originalOddMean_abs_le K hK hhead n)

#print axioms terminalTestRate
#print axioms centeredInterval
#print axioms action_channel_sharp_lower
#print axioms terminal_tested_floor
#print axioms originalOwn_tested_floor

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOverlap
