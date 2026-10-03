/-
# The original signed Stein source reaches the SAME completed gain

The full-source defect pairing uses the actual odd OWN center and the
original even partition. Its finite mean residue is paid by the computed
right-boundary onset, independently of the existing gain representative
threshold. The literal padded-square Green-gradient sum therefore converges
to the already constructed C2-a*C1, not to a new limit object.

Nome, width and observable are fixed. No favorable signed estimate,
changing-family uniformity, response reserve or continuum claim follows.
-/

import YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredMeanResidueBound
import YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainStein
import YMGap.Continuum.ArctanTrigConvergesProof
import YMGap.Continuum.HeatKernelGap

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicSteinGainLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (WindowExpression)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung (ownMean)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain (commutatorGain)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
  (evenPartition evenPartition_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredGainSourcePair
  (fullSourceDefectPair centeredMeanPair commutatorGain_source_pair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredMeanResidueBound
  (meanResidueDepthCutoff own_meanResidue_tolerance_bound)
open YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainApproximation (normalizedFiniteGain)
open YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainLimit
  (gainCutoffThreshold gainTimeThreshold gainRepresentativeThreshold normalizedFiniteGain_approx)
open YMGap.Continuum.BF4WilsonAllNomeFilteredGainLimit
  (gainLimit gainLimit_centered_pin gainLimit_completed_pin)
open YMGap.Continuum.BF4DyadicWilsonSquare (side paddedSquare)
open YMGap.Continuum.BF4DyadicWilsonSquareFilteredGainStein
  (paddedSquareGradient paddedSquare_own_commutatorGain_source_gradient)
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement (state)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector (centeredVector)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)

local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] ownMean evenPartition fullSourceDefectPair
  normalizedFiniteGain commutatorGain paddedSquareGradient gainLimit

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

/-- Divide the literal full-source pairing by its SAME original even mass. -/
def normalizedSourcePair (width stage n : Nat) (loop : SourceLoop width) (a : Q') : Q' :=
  let K := headCutoff w+stage
  let hK := Nat.le_add_right (headCutoff w) stage
  let f := sourceCharacter width loop.edges 1
  let c := ownMean hw0 hw1 K width hK n loop
  fullSourceDefectPair w K width n f c a *
    Q'.recipPos (evenPartition w K width n) (evenPartition_positive hw0 hw1 K width hK n)

/-- Explicit diagonal stage; the CReal representative threshold stays separate. -/
def sourcePairDiagonalModulus (width : Nat) (loop : SourceLoop width) (epsilon : Q') : Nat :=
  max (max (gainCutoffThreshold hw0 hw1 width loop (HalfPow.half*epsilon))
    (gainTimeThreshold hw0 hw1 width loop (HalfPow.half*epsilon)))
    (meanResidueDepthCutoff hw0 hw1 width (HalfPow.half*epsilon))

private theorem residue_normalized_bound (width stage n : Nat) (loop : SourceLoop width)
    (a epsilon : Q') (ha0 : (0 : Q') ≤ a) (ha1 : a ≤ 1)
    (he : (0 : Q') < epsilon)
    (hn : meanResidueDepthCutoff hw0 hw1 width epsilon ≤ n) :
    let K := headCutoff w+stage
    let hK := Nat.le_add_right (headCutoff w) stage
    let c := ownMean hw0 hw1 K width hK n loop
    let E := evenPartition w K width n
    Q'.abs (((a-1)*c*centeredMeanPair w K width n
      (sourceCharacter width loop.edges 1) c)*
      Q'.recipPos E (evenPartition_positive hw0 hw1 K width hK n)) ≤ epsilon := by
  dsimp only
  let K := headCutoff w+stage
  let hK := Nat.le_add_right (headCutoff w) stage
  let c := ownMean hw0 hw1 K width hK n loop
  let E := evenPartition w K width n
  let hE := evenPartition_positive hw0 hw1 K width hK n
  let z := Q'.recipPos E hE
  let r := (a-1)*c*centeredMeanPair w K width n (sourceCharacter width loop.edges 1) c
  have hraw : Q'.abs r ≤ (1-a)*epsilon*E :=
    own_meanResidue_tolerance_bound hw0 hw1 he K width hK n loop a ha1 hn
  have hz := Q'.le_of_lt (Q'.recipPos_pos E hE)
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ z hraw hz
  have hcancel : ((1-a)*epsilon*E)*z ≈ (1-a)*epsilon :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv E hE))
        (Q'.mul_one_eqv _))
  have hneg : -a ≤ (0 : Q') := Q'.le_trans' _ _ _ (Q'.neg_le_neg ha0)
    (Q'.le_of_eqv (by decide : -(0 : Q') ≈ 0))
  have hcoef : 1-a ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.add_le_add_left 1 _ _ hneg)
    (Q'.le_of_eqv (poly_identity_of_normal_eq (.add (.const 1) (.const 0))
      (.const 1) (by decide) (fun _ => a)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (TsumDeriv.abs_mul_nonneg_right r hz))
    (Q'.le_trans' _ _ _ hscaled (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcancel)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ epsilon hcoef (Q'.le_of_lt he))
        (Q'.le_of_eqv (Q'.one_mul_eqv epsilon)))))

private theorem pair_gain_orders (p g r d : Q') (hpin : g ≈ p+r)
    (hr : Q'.abs r ≤ d) : p ≤ g+d ∧ g ≤ p+d := by
  have hplus := Q'.le_trans' _ _ _ (Q'.le_abs_self r) hr
  have hminus := Q'.le_trans' _ _ _ (Q'.neg_le_abs r) hr
  have hp : p ≈ g+(-r) := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0)
      (by decide) (fun | 0 => p | _ => r)))
    (Q'.add_eqv_congr_right _ _ _ hpin.symm)
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) (Q'.add_le_add_left g _ _ hminus),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin) (Q'.add_le_add_left p _ _ hplus)⟩

/-- Both-order approximation of the actual full-source pairing. No favorable
sign or source estimate is supplied; the finite moving mean is paid. -/
theorem normalizedSourcePair_approx (width : Nat) (loop : SourceLoop width)
    (epsilon : Q') (he : (0 : Q') < epsilon) (a : Q')
    (ha0 : (0 : Q') ≤ a) (ha1 : a ≤ 1) (stage n p : Nat)
    (hk : gainCutoffThreshold hw0 hw1 width loop (HalfPow.half*epsilon) ≤ stage)
    (ht : gainTimeThreshold hw0 hw1 width loop (HalfPow.half*epsilon) ≤ n)
    (hn : meanResidueDepthCutoff hw0 hw1 width (HalfPow.half*epsilon) ≤ n)
    (hp : gainRepresentativeThreshold hw0 hw1 width loop (HalfPow.half*epsilon) ≤ p) :
    normalizedSourcePair hw0 hw1 width stage n loop a ≤
        (gainLimit hw0 hw1 (WindowExpression.loop 0 loop 1) (Nat.le_refl 0) a).approx p+epsilon ∧
      (gainLimit hw0 hw1 (WindowExpression.loop 0 loop 1) (Nat.le_refl 0) a).approx p ≤
        normalizedSourcePair hw0 hw1 width stage n loop a+epsilon := by
  let d := HalfPow.half*epsilon
  have hd := ExpNeg.half_mul_pos epsilon he
  let K := headCutoff w+stage
  let hK := Nat.le_add_right (headCutoff w) stage
  let f := sourceCharacter width loop.edges 1
  let c := ownMean hw0 hw1 K width hK n loop
  let z := Q'.recipPos (evenPartition w K width n)
    (evenPartition_positive hw0 hw1 K width hK n)
  let r := (a-1)*c*centeredMeanPair w K width n f c*z
  have hpin : normalizedFiniteGain hw0 hw1 width stage n loop a ≈
      normalizedSourcePair hw0 hw1 width stage n loop a+r := by
    unfold normalizedFiniteGain normalizedSourcePair
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (commutatorGain_source_pair w K width n f c a)) (Q'.add_mul_eqv _ _ _)
  have horders := pair_gain_orders _ _ r d hpin
    (residue_normalized_bound hw0 hw1 width stage n loop a d ha0 ha1 hd hn)
  have hgain := normalizedFiniteGain_approx hw0 hw1 width loop d hd a ha0 ha1 stage n p hk ht hp
  have hh := ExpNeg.two_halves epsilon
  constructor
  · exact Q'.le_trans' _ _ _ horders.1 (Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ d hgain.1)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _ hh))))
  · exact Q'.le_trans' _ _ _ hgain.2 (Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ d horders.2)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _ hh))))

/-- Constructed convergence to the EXISTING gainLimit, for fixed original
nome, width and loop. The modulus is explicit and independent of a in [0,1]. -/
theorem source_pair_diagonal_converges (width : Nat) (loop : SourceLoop width)
    (a : Q') (ha0 : (0 : Q') ≤ a) (ha1 : a ≤ 1) :
    ConvergesTo (fun k => ofQ' (normalizedSourcePair hw0 hw1 width k k loop a))
      (gainLimit hw0 hw1 (WindowExpression.loop 0 loop 1) (Nat.le_refl 0) a) := by
  intro epsilon he
  refine ⟨sourcePairDiagonalModulus hw0 hw1 width loop epsilon, fun k hk =>
    ⟨gainRepresentativeThreshold hw0 hw1 width loop (HalfPow.half*epsilon), fun p hp => ?_⟩⟩
  exact normalizedSourcePair_approx hw0 hw1 width loop epsilon he a ha0 ha1 k k p
    (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hk)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hk)
    (Nat.le_trans (Nat.le_max_right _ _) hk) hp

private theorem qpow_rg (v : Q') : ∀ k, qpow v k = RGTransport.qpow v k
  | 0 => rfl
  | k+1 => congrArg (fun z : Q' => z*v) (qpow_rg v k)

/-- The literal signed Green-gradient sum, at the actual finite OWN mean,
divided by its SAME original even partition. -/
def normalizedSteinGradient (scale width : Nat) (hwidth : side scale < width)
    (stage n : Nat) : Q' :=
  let K := headCutoff w+stage
  let hK := Nat.le_add_right (headCutoff w) stage
  let loop := paddedSquare scale width hwidth
  paddedSquareGradient w K width n scale hwidth (ownMean hw0 hw1 K width hK n loop) *
    Q'.recipPos (evenPartition w K width n) (evenPartition_positive hw0 hw1 K width hK n)

/-- Exact original source identification; only the fundamental kinetic
label guard is added to the unchanged original head guard. -/
theorem paddedSquare_sourcePair_stein_pin (scale width : Nat)
    (hwidth : side scale < width) (stage n : Nat) (hK : 1 ≤ headCutoff w+stage) :
    normalizedSourcePair hw0 hw1 width stage n (paddedSquare scale width hwidth)
      (qpow w (12*side scale)) ≈ normalizedSteinGradient hw0 hw1 scale width hwidth stage n := by
  let K := headCutoff w+stage
  let loop := paddedSquare scale width hwidth
  let f := sourceCharacter width loop.edges 1
  let c := ownMean hw0 hw1 K width (Nat.le_add_right _ _) n loop
  let a := qpow w (12*side scale)
  let r := (a-1)*c*centeredMeanPair w K width n f c
  have hsource : fullSourceDefectPair w K width n f c a ≈
      paddedSquareGradient w K width n scale hwidth c := by
    have h : fullSourceDefectPair w K width n f c a+r ≈
        paddedSquareGradient w K width n scale hwidth c+r :=
      Q'.eqv_trans _ _ _ (commutatorGain_source_pair w K width n f c a).symm
      (paddedSquare_own_commutatorGain_source_gradient hw0 hw1 K width
        (Nat.le_add_right _ _) hK n scale hwidth)
    have hc (v : Q') : (v+r)+(-r) ≈ v := poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0)
      (by decide) (fun | 0 => v | _ => r)
    exact Q'.eqv_trans _ _ _ (hc _).symm
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h) (hc _))
  unfold normalizedSourcePair normalizedSteinGradient
  exact Q'.mul_eqv_congr_right _ _ _ hsource

/-- The computed signed full-source derivatives converge to C2-a*C1 on
the SAME carrier. No sign or uniform scaling estimate is concluded. -/
theorem paddedSquare_stein_diagonal_converges (scale width : Nat)
    (hwidth : side scale < width) :
    ConvergesTo (fun k => ofQ' (normalizedSteinGradient hw0 hw1 scale width hwidth k k))
      (gainLimit hw0 hw1 (WindowExpression.loop 0 (paddedSquare scale width hwidth) 1)
        (Nat.le_refl 0) (qpow w (12*side scale))) := by
  let loop := paddedSquare scale width hwidth
  let a := qpow w (12*side scale)
  have ha0 : (0 : Q') ≤ a := by
    dsimp only [a]
    rw [qpow_rg]; exact RGTransport.qpow_nonneg w (Q'.le_of_lt hw0) _
  have ha1 : a ≤ 1 := by
    dsimp only [a]
    rw [qpow_rg]; exact HeatKernelGap.qpow_le_one (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) _
  intro epsilon he
  refine ⟨max 1 (sourcePairDiagonalModulus hw0 hw1 width loop epsilon), fun k hk =>
    ⟨gainRepresentativeThreshold hw0 hw1 width loop (HalfPow.half*epsilon), fun p hp => ?_⟩⟩
  have hstage := Nat.le_trans (Nat.le_max_right _ _) hk
  have happrox := normalizedSourcePair_approx hw0 hw1 width loop epsilon he a ha0 ha1 k k p
    (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hstage)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hstage)
    (Nat.le_trans (Nat.le_max_right _ _) hstage) hp
  have hpin := paddedSquare_sourcePair_stein_pin hw0 hw1 scale width hwidth k k (by omega)
  exact ⟨Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpin) happrox.1,
    Q'.le_trans' _ _ _ happrox.2 (Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ _ hpin))⟩

/-- The limit is the existing centered chronological gain, not marginal variance. -/
theorem paddedSquare_stein_centered_converges (scale width : Nat)
    (hwidth : side scale < width) :
    let e := WindowExpression.loop 0 (paddedSquare scale width hwidth) 1
    let x := state e (Nat.le_refl 0)
    ConvergesTo (fun k => ofQ' (normalizedSteinGradient hw0 hw1 scale width hwidth k k))
      (sub (centeredTimeMoment hw0 hw1 2 x x)
        (mul (ofQ' (qpow w (12*side scale))) (centeredTimeMoment hw0 hw1 1 x x))) :=
  ArctanTrigConvergesProof.convergesTo_of_equiv
    (paddedSquare_stein_diagonal_converges hw0 hw1 scale width hwidth)
    (gainLimit_centered_pin hw0 hw1
      (WindowExpression.loop 0 (paddedSquare scale width hwidth) 1) (Nat.le_refl 0) _)

/-- Exact completed target of the preceding literal-source convergence. -/
theorem paddedSquare_stein_completed_pin (scale width : Nat)
    (hwidth : side scale < width) :
    let e := WindowExpression.loop 0 (paddedSquare scale width hwidth) 1
    let v := centeredVector hw0 hw1 (state e (Nat.le_refl 0))
    Quotient.mk crealSetoid (gainLimit hw0 hw1 e (Nat.le_refl 0) (qpow w (12*side scale))) =
      RCsub (completedInner hw0 hw1 v (completedTime hw0 hw1 2 v))
        (RCscale (qpow w (12*side scale)) (completedInner hw0 hw1 v (completedTime hw0 hw1 1 v))) :=
  gainLimit_completed_pin hw0 hw1
    (WindowExpression.loop 0 (paddedSquare scale width hwidth) 1) (Nat.le_refl 0) _

#print axioms normalizedSourcePair
#print axioms sourcePairDiagonalModulus
#print axioms normalizedSourcePair_approx
#print axioms source_pair_diagonal_converges
#print axioms normalizedSteinGradient
#print axioms paddedSquare_sourcePair_stein_pin
#print axioms paddedSquare_stein_diagonal_converges
#print axioms paddedSquare_stein_centered_converges
#print axioms paddedSquare_stein_completed_pin

end YMGap.Continuum.BF4WilsonAllNomeDyadicSteinGainLimit
