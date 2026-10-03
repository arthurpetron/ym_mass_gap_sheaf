/-
# Coupled score control from the last ORIGINAL transfer step

Retain both incoming messages a,c, their outputs A=T a,b=T c, and the
complete last K/V window W. The paired residual X=lift(A)*c-lift(b)*a
has I(WX)=0 and I(DW*X)=A*Db-b*DA. The signed dual-square certificate
bounds Score^2 by L(w)^2*(T1)*I(WX^2), without an incoming-message inverse.
This uses the surviving incoming c rather than full accumulated-history
conditional noise. The cross term, T1, and the original action remain.
Its useful relative size on a justified changing family is NOT asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreVariance
import YMGap.Continuum.QuaternionHaarConditionalScoreGradient
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreVariance (halfOpenAction_outputRelative)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadWindowContraction
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (supported_upper_independent)
open YMGap.Continuum.SU2QuaternionMultiHeadSignedDualSquare
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (reciprocal reciprocal_supported)
open YMGap.Continuum.QuaternionHaarReciprocalSensitivity (reciprocalSlope_supported)
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient
open YMGap.Continuum.QuaternionHaarWeightedSquareTriangle

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight kineticWeight terminalMessage

private def action (w : Q') (K width : Nat) : RatPoly :=
  halfOpenAction (N width) (kineticWeight w K width) (spatialWeight w K width) 1

/-- The original incoming pair and BOTH actual outgoing messages. -/
def lastStepPairedResidual (w : Q') (K width : Nat) (a c : RatPoly) : RatPoly :=
  polyAdd (polyMul (liftBoundary (N width) (transferStep w K width a)) c)
    (polyNeg (polyMul (liftBoundary (N width) (transferStep w K width c)) a))

/-- Positive paired-residual budget. T1 is retained, not canceled by a floor. -/
def lastStepScoreBudget (w : Q') (K width : Nat) (a c : RatPoly) : RatPoly :=
  let X := lastStepPairedResidual w K width a c
  polyMul (transferStep w K width polyOne)
    (partialHaarHeads (N width) (polyMul (action w K width) (polyMul X X)))

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term ht => Nat.le_trans (hp term ht) (Nat.mul_le_mul_left 4 h)

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem integral_pin (w : Q') (K width : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (partialHaarHeads (N width) (polyMul (action w K width) p))
      (transferStep w K width p) := by
  refine (partialHaarHeads_congr (N width)
    ((RatPolyCoeffEqv.mul_comm _ p).trans
      ((RatPolyCoeffEqv.mul_one p).symm.mul_right _))).trans ?_
  simpa only [windowMessage, Nat.one_mul, transferStep, iterateStep, action] using
    windowMessage_one (N width) (kineticWeight w K width) (spatialWeight w K width) 1 p

private theorem mass_pin (w : Q') (K width : Nat) :
    RatPolyCoeffEqv (partialHaarHeads (N width) (action w K width))
      (transferStep w K width polyOne) :=
  (partialHaarHeads_congr (N width) (RatPolyCoeffEqv.mul_one _).symm).trans
    (integral_pin w K width polyOne)

private theorem paired_integral (heads : Nat) (P A b a c : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads heads (polyMul P
        (polyAdd (polyMul (liftBoundary heads A) c)
          (polyNeg (polyMul (liftBoundary heads b) a)))))
      (polyAdd (polyMul A (partialHaarHeads heads (polyMul P c)))
        (polyNeg (polyMul b (partialHaarHeads heads (polyMul P a))))) := by
  have hsplit := partialHaarHeads_congr heads
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 3) (.var 4)))))
      (.add (.mul (.mul (.var 0) (.var 2)) (.var 1))
        (.neg (.mul (.mul (.var 0) (.var 4)) (.var 3))))
      (by decide) (fun
        | 0 => P | 1 => liftBoundary heads A | 2 => c
        | 3 => liftBoundary heads b | _ => a))
  change RatPolyCoeffEqv
    (partialHaarHeads heads (polyMul P (polyAdd (polyMul (liftBoundary heads A) c)
      (polyNeg (polyMul (liftBoundary heads b) a)))))
    (partialHaarHeads heads (polyAdd (polyMul (polyMul P c) (liftBoundary heads A))
      (polyNeg (polyMul (polyMul P a) (liftBoundary heads b))))) at hsplit
  rw [partialHaarHeads_add] at hsplit
  exact hsplit.trans
    (((partialHaarHeads_mul_lift heads (polyMul P c) A).trans
      (RatPolyCoeffEqv.mul_comm _ A)).add
      ((partialHaarHeads_neg heads _).trans
        (RatPolyCoeffEqv.neg ((partialHaarHeads_mul_lift heads (polyMul P a) b).trans
          (RatPolyCoeffEqv.mul_comm _ b)))))

/-- The pair is centered by actual transfer identities, not a new premise. -/
theorem lastStepPairedResidual_mean_zero (w : Q') (K width : Nat) (a c : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width)
        (polyMul (action w K width) (lastStepPairedResidual w K width a c))) polyZero :=
  (paired_integral (N width) _ _ _ a c).trans
    ((((integral_pin w K width c).mul_left _).add
      (RatPolyCoeffEqv.neg ((integral_pin w K width a).mul_left _))).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 1) (.var 0)))) (.const 0)
        (by decide) (fun | 0 => transferStep w K width a | _ => transferStep w K width c)).trans
        (RatPolyCoeffEqv.zero_smul polyOne)))

private theorem derivative_integral_pin (w : Q') (K width s i j : Nat)
    (hi : i < 4) (hj : j < 4) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul
        (angularDerivative (4*(N width)+(4*s+i)) (4*(N width)+(4*s+j)) (action w K width)) p))
      (angularDerivative (4*s+i) (4*s+j) (transferStep w K width p)) := by
  have hz := angularDerivative_blockIndependent_zero hi hj (supported_upper_independent hp s)
  have hz' : RatPolyCoeffEqv
      (angularDerivative (4*(N width)+(4*s+i)) (4*(N width)+(4*s+j)) p) polyZero := by
    simpa only [Nat.mul_add, Nat.add_assoc] using hz
  have hd : RatPolyCoeffEqv
      (angularDerivative (4*(N width)+(4*s+i)) (4*(N width)+(4*s+j))
        (polyMul (action w K width) p))
      (polyMul (angularDerivative (4*(N width)+(4*s+i)) (4*(N width)+(4*s+j))
        (action w K width)) p) :=
    (angularDerivative_mul _ _ _ p).trans
      (((RatPolyCoeffEqv.refl _).add
        ((hz'.mul_left _).trans (RatPolyCoeffEqv.mul_zero_right _))).trans
        (RatPolyCoeffEqv.add_zero _))
  exact ((angularDerivative_partialHaarHeads (N width) (4*s+i) (4*s+j) _).trans
    (partialHaarHeads_congr (N width) hd)).symm.trans
      (angularDerivative_congr _ _ (integral_pin w K width p))

/-- Exact mixed-moment expansion of the paired residual. The TWO negative
cross terms remain; neither incoming message is bounded separately. -/
theorem lastStepPairedResidual_square_pin (w : Q') (K width : Nat) (a c : RatPoly) :
    let A := transferStep w K width a
    let b := transferStep w K width c
    let cross := polyMul (polyMul A b) (transferStep w K width (polyMul a c))
    RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul (action w K width)
        (polyMul (lastStepPairedResidual w K width a c) (lastStepPairedResidual w K width a c))))
      (polyAdd (polyMul (polyMul A A) (transferStep w K width (polyMul c c)))
        (polyAdd (polyNeg (polyAdd cross cross))
          (polyMul (polyMul b b) (transferStep w K width (polyMul a a))))) := by
  dsimp only
  let A := transferStep w K width a
  let b := transferStep w K width c
  let W := action w K width
  let X := lastStepPairedResidual w K width a c
  let cross := polyMul (polyMul W (polyMul a c)) (liftBoundary (N width) (polyMul A b))
  have he : RatPolyCoeffEqv (polyMul W (polyMul X X))
      (polyAdd
        (polyMul (polyMul W (polyMul c c)) (liftBoundary (N width) (polyMul A A)))
        (polyAdd (polyNeg (polyAdd cross cross))
          (polyMul (polyMul W (polyMul a a)) (liftBoundary (N width) (polyMul b b))))) := by
    dsimp only [X, lastStepPairedResidual, cross, A, b]
    rw [lift_product, lift_product, lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul
        (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 3) (.var 4))))
        (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 3) (.var 4))))))
      (.add
        (.mul (.mul (.var 0) (.mul (.var 2) (.var 2))) (.mul (.var 1) (.var 1)))
        (.add (.neg (.add
          (.mul (.mul (.var 0) (.mul (.var 4) (.var 2))) (.mul (.var 1) (.var 3)))
          (.mul (.mul (.var 0) (.mul (.var 4) (.var 2))) (.mul (.var 1) (.var 3)))))
          (.mul (.mul (.var 0) (.mul (.var 4) (.var 4))) (.mul (.var 3) (.var 3)))))
      (by decide) (fun
        | 0 => W | 1 => liftBoundary (N width) A | 2 => c
        | 3 => liftBoundary (N width) b | _ => a)
  have hp (p R : RatPoly) : RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul (polyMul W p) (liftBoundary (N width) R)))
      (polyMul R (transferStep w K width p)) :=
    (partialHaarHeads_mul_lift (N width) (polyMul W p) R).trans
      (((integral_pin w K width p).mul_right R).trans (RatPolyCoeffEqv.mul_comm _ R))
  have h := partialHaarHeads_congr (N width) he
  rw [partialHaarHeads_add, partialHaarHeads_add] at h
  have hn := partialHaarHeads_neg (N width) (polyAdd cross cross)
  rw [partialHaarHeads_add] at hn
  exact h.trans ((hp (polyMul c c) (polyMul A A)).add
    ((hn.trans (RatPolyCoeffEqv.neg
      ((hp (polyMul a c) (polyMul A b)).add (hp (polyMul a c) (polyMul A b))))).add
      (hp (polyMul a a) (polyMul b b))))

/-- No incoming-message positivity or inverse is assumed. The ORIGINAL
last-link signed derivative witnesses produce this paired-residual estimate. -/
def lastStep_score_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : relativeCutoff w 32 ≤ K) (s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4)
    {a c : RatPoly} (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) :
    let S := conditionalScore (4*s+i) (4*s+j)
      (transferStep w K width a) (transferStep w K width c)
    Certificate (N width) (polyAdd
      (polyMul (cap (relativeCap w 32*relativeCap w 32)) (lastStepScoreBudget w K width a c))
      (polyNeg (polyMul S S))) := by
  dsimp only
  let W := action w K width
  let X := lastStepPairedResidual w K width a c
  let d := angularDerivative (4*(N width)+(4*s+i)) (4*(N width)+(4*s+j)) W
  have hsn := activeBlocks_lt width s hs
  have hW : SupportedQuaternionBlocks (N width+N width) W := by
    simpa only [Nat.one_add, Nat.two_mul] using
      halfOpenAction_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width) 1
  have hd : SupportedQuaternionBlocks (N width+N width) d :=
    angularDerivative_supported_at (by omega) (by omega) hW
  have hX : SupportedQuaternionBlocks (N width+N width) X :=
    supported_add
      (supported_polyMul (lift_supported (transferStep_supported w K width ha) (N width))
        (support_mono hc (by omega)))
      (support_neg (supported_polyMul (lift_supported (transferStep_supported w K width hc) (N width))
        (support_mono ha (by omega))))
  have P := halfOpenAction_outputRelative hw0 hw1 K width hK s hs hi hj 0
  simp only [Nat.zero_add, Nat.one_mul, Nat.two_mul, Nat.mul_add, Nat.add_assoc] at P
  have C := relativeDualSquare_certificate (N width) (N width) W d X (relativeCap w 32)
    hW hd hX P.lower P.upper
  have hS : RatPolyCoeffEqv (partialHaarHeads (N width) (polyMul d X))
      (conditionalScore (4*s+i) (4*s+j) (transferStep w K width a) (transferStep w K width c)) :=
    (paired_integral (N width) d (transferStep w K width a) (transferStep w K width c) a c).trans
    (((derivative_integral_pin w K width s i j hi hj hc).mul_left _).add
      (RatPolyCoeffEqv.neg ((derivative_integral_pin w K width s i j hi hj ha).mul_left _)))
  exact Certificate.ofCoeff
    ((((mass_pin w K width).mul_right _).mul_left _).add
      (RatPolyCoeffEqv.neg (hS.mul hS))).symm C

/-- Arbitrary output multiplication retains the entire paired budget. No
factor T1, A^2 or global partition is canceled. -/
theorem lastStep_score_weighted_multiplier_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (s : Nat) (hs : s ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) {a c W J : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (hc : SupportedQuaternionBlocks (N width) c)
    (MW : Certificate (N width) W) (hJ : SupportedQuaternionBlocks (N width) J) :
    let S := conditionalScore (4*s+i) (4*s+j) (transferStep w K width a) (transferStep w K width c)
    quaternionHaar (N width) (polyMul W (polyMul (polyMul J S) (polyMul J S))) ≤
      (relativeCap w 32*relativeCap w 32)*quaternionHaar (N width)
        (polyMul (polyMul W (polyMul J J)) (lastStepScoreBudget w K width a c)) := by
  dsimp only
  let S := conditionalScore (4*s+i) (4*s+j) (transferStep w K width a) (transferStep w K width c)
  let B := lastStepScoreBudget w K width a c
  let L := relativeCap w 32*relativeCap w 32
  let E := polyMul (polyMul W (polyMul J J))
    (polyAdd (polyMul (cap L) B) (polyNeg (polyMul S S)))
  have hn := ((MW.mul (Certificate.square J hJ)).mul
    (lastStep_score_certificate hw0 hw1 K width hK s hs hi hj ha hc)).haar_nonnegative
  have hid : RatPolyCoeffEqv
      (polyAdd (polyMul W (polyMul (polyMul J S) (polyMul J S))) E)
      (polyMul (cap L) (polyMul (polyMul W (polyMul J J)) B)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 1)))
          (.add (.mul (.var 3) (.var 4)) (.neg (.mul (.var 2) (.var 2))))))
      (.mul (.var 3) (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 4)))
      (by decide) (fun | 0 => W | 1 => J | 2 => S | 3 => cap L | _ => B)
  have he := Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append (N width) _ _))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (hid.trans (cap_mul_left L _)))
      (quaternionHaar_polySmul (N width) L _))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn) (Q'.le_of_eqv he)

/-- Same-weight finite reciprocal consumer of the last-step paired estimate.
It retains the explicit reciprocal correction, with no full-history Noise. -/
theorem lastStep_reciprocal_gradient_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (s : Nat) (hs : s ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) {a c W : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (hc : SupportedQuaternionBlocks (N width) c)
    (MW : Certificate (N width) W) (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    let A := transferStep w K width a
    let b := transferStep w K width c
    let G := reciprocal A u hu k
    let d := polyMul A (angularDerivative (4*s+i) (4*s+j) (polyMul G b))
    let e := reciprocalScoreCorrection (4*s+i) (4*s+j) A b u hu k
    quaternionHaar (N width) (polyMul W (polyMul d d)) ≤
      sumBound
        ((relativeCap w 32*relativeCap w 32)*quaternionHaar (N width)
          (polyMul (polyMul W (polyMul G G)) (lastStepScoreBudget w K width a c)))
        (quaternionHaar (N width) (polyMul W (polyMul e e))) := by
  dsimp only
  have hA := transferStep_supported w K width ha
  have hb := transferStep_supported w K width hc
  have hsn := activeBlocks_lt width s hs
  have hdA := angularDerivative_supported_at (show 4*s+i < 4*N width by omega)
    (show 4*s+j < 4*N width by omega) hA
  have hdb := angularDerivative_supported_at (show 4*s+i < 4*N width by omega)
    (show 4*s+j < 4*N width by omega) hb
  have hG := reciprocal_supported hA u hu k
  have hS := supported_add (supported_polyMul hA hdb) (support_neg (supported_polyMul hb hdA))
  have he := supported_polyMul hb (supported_polyMul
    (supported_add hG (support_neg (supported_polyMul hA (reciprocalSlope_supported hA u hu k)))) hdA)
  have hlead := lastStep_score_weighted_multiplier_square_le hw0 hw1 K width hK s hs hi hj ha hc MW hG
  have hid := reciprocal_score_cleared_derivative (4*s+i) (4*s+j)
    (transferStep w K width a) (transferStep w K width c) u hu k
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff ((hid.mul hid).mul_left W)))
    (weighted_square_add_bound MW (supported_polyMul hG hS) he hlead (Q'.le_of_eqv (Q'.eqv_refl _)))

#print axioms lastStepPairedResidual
#print axioms lastStepScoreBudget
#print axioms lastStepPairedResidual_mean_zero
#print axioms lastStepPairedResidual_square_pin
#print axioms lastStep_score_certificate
#print axioms lastStep_score_weighted_multiplier_square_le
#print axioms lastStep_reciprocal_gradient_square_le

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance
