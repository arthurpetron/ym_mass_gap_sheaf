/-
# Retain the matched terminal signed Gram in the original score payment

The six original reconstructed plane scores equal the three paired squares,
without a factor two. The matched terminal Gram bounds each constant basis
direction while retaining its signed Hessian and negative marginal-score
square. The actual incoming reconstruction contributes six copies of the
unchanged error payment. The certified output weight stays arbitrary.
No signed-Fisher upper estimate, survival or scaling conclusion is supplied.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioRefinement

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSignedScorePayment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
  (spatialFringeMass spatialFringeMass_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreBudget (exactScoreAngularBudget)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioRefinement
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (conditionalScore)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame
open YMGap.Continuum.QuaternionHaarFrozenCurvatureApproximation (firstJet)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
  (sixValue sixValue_mono sixValue_mul_left haar_six)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (reciprocal_supported)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCutoff headCutoff_le_relativeCutoff)
open YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature (prefixCurvatureCost)
open YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature
  (prefixFrozenCurvatureCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks terminalMessage

/-- Literal constant basis; no output coefficient is differentiated. -/
def constantPairedBasis (i j : Fin 3) : RatPoly :=
  if i=j then polyOne else polyZero

private theorem basis_supported (blocks : Nat) (i j : Fin 3) :
    SupportedQuaternionBlocks blocks (constantPairedBasis i j) := by
  unfold constantPairedBasis
  split
  · exact supported_one blocks
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private theorem basis_first_pin (i : Fin 3) (f : Fin 3 → RatPoly) :
    RatPolyCoeffEqv (firstJet (constantPairedBasis i) f) (f i) := by
  by_cases h0 : i.val=0
  · have hi : i=0 := Fin.ext h0
    subst i
    change RatPolyCoeffEqv
      (polyAdd (polyMul polyOne (f 0))
        (polyAdd (polyMul polyZero (f 1)) (polyMul polyZero (f 2)))) (f 0)
    exact ((RatPolyCoeffEqv.one_mul _).add
      ((RatPolyCoeffEqv.mul_zero_left _).add (RatPolyCoeffEqv.mul_zero_left _))).trans
      (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.zero_add polyZero)).trans
        (RatPolyCoeffEqv.add_zero _))
  · by_cases h1 : i.val=1
    · have hi : i=1 := Fin.ext h1
      subst i
      change RatPolyCoeffEqv
        (polyAdd (polyMul polyZero (f 0))
          (polyAdd (polyMul polyOne (f 1)) (polyMul polyZero (f 2)))) (f 1)
      exact ((RatPolyCoeffEqv.mul_zero_left _).add
        ((RatPolyCoeffEqv.one_mul _).add (RatPolyCoeffEqv.mul_zero_left _))).trans
        (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_zero _)).trans
          (RatPolyCoeffEqv.zero_add _))
    · have hi : i=2 := by
        apply Fin.ext
        have hb := i.isLt
        omega
      subst i
      change RatPolyCoeffEqv
        (polyAdd (polyMul polyZero (f 0))
          (polyAdd (polyMul polyZero (f 1)) (polyMul polyOne (f 2)))) (f 2)
      exact ((RatPolyCoeffEqv.mul_zero_left _).add
        ((RatPolyCoeffEqv.mul_zero_left _).add (RatPolyCoeffEqv.one_mul _))).trans
        (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.zero_add _)).trans
          (RatPolyCoeffEqv.zero_add _))

/-- The literal signed terminal Gram payment for one constant paired direction.
All ordered Hessian entries and the homogeneous curvature cost remain in it. -/
def terminalSignedGramTerm (w : Q') (K width s n r : Nat)
    (phi W : RatPoly) (i : Fin 3) : Q' :=
  let a := terminalMessage w K width (n+r)
  let A := transferStep w K width a
  let B := transferStep w K width (polyMul a phi)
  let u := constantPairedBasis i
  let noise := polyAdd (polyMul A
    (transferStep w K width (polyMul a (polyMul phi phi)))) (polyNeg (polyMul B B))
  let DA := sourceMarginalFirst w K width s a u
  let DDA := sourceMarginalSecond w K width s a u
  let fisher := polyAdd
    (polyMul A (polyAdd DDA
      (polyMul (polyMul (cap (prefixCurvatureCost w)) (threeSquare u)) A)))
    (polyNeg (polyMul DA DA))
  quaternionHaar (N width) (polyMul W (polyMul noise fisher))

/-- Three signed paired payments, not six separately capped Hessians. -/
def terminalSignedGramPayment (w : Q') (K width s n r : Nat) (phi W : RatPoly) : Q' :=
  terminalSignedGramTerm w K width s n r phi W 0 +
    (terminalSignedGramTerm w K width s n r phi W 1 +
      terminalSignedGramTerm w K width s n r phi W 2)

private theorem haar_threeSquare (blocks : Nat) (W : RatPoly) (f : Fin 3 → RatPoly) :
    quaternionHaar blocks (polyMul W (threeSquare f)) ≈
      quaternionHaar blocks (polyMul W (polyMul (f 0) (f 0))) +
        (quaternionHaar blocks (polyMul W (polyMul (f 1) (f 1))) +
          quaternionHaar blocks (polyMul W (polyMul (f 2) (f 2)))) := by
  have h (p q : RatPoly) : quaternionHaar blocks (polyMul W (polyAdd p q)) ≈
      quaternionHaar blocks (polyMul W p)+quaternionHaar blocks (polyMul W q) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right W p q))
      (quaternionHaar_append blocks _ _)
  exact Q'.eqv_trans _ _ _ (h _ _) (Q'.add_eqv_congr' (Q'.eqv_refl _) (h _ _))

private theorem six_payment_pin (f : Nat → Nat → Q') (c e : Q') :
    sixValue (fun i j => c*f i j+e) ≈ c*sixValue f+6*e := by
  exact poly_identity_of_normal_eq
    (.add (.add (.mul (.var 6) (.var 0)) (.var 7))
      (.add (.add (.mul (.var 6) (.var 1)) (.var 7))
        (.add (.add (.mul (.var 6) (.var 2)) (.var 7))
          (.add (.add (.mul (.var 6) (.var 3)) (.var 7))
            (.add (.add (.mul (.var 6) (.var 4)) (.var 7))
              (.add (.mul (.var 6) (.var 5)) (.var 7)))))))
    (.add (.mul (.var 6) (.add (.var 0) (.add (.var 1)
      (.add (.var 2) (.add (.var 3) (.add (.var 4) (.var 5)))))))
      (.mul (.const 6) (.var 7))) (by decide) (fun
        | 0 => f 0 1 | 1 => f 0 2 | 2 => f 0 3
        | 3 => f 1 2 | 4 => f 1 3 | 5 => f 2 3
        | 6 => c | _ => e)

/-- The SAME actual six-plane score is paid by the matched terminal signed
Gram and the existing reconstruction correction. W has no independence or
support premise beyond its certificate; its literal reciprocal may be kept. -/
theorem original_lastStep_terminal_signed_score_payment_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (hcurv : prefixFrozenCurvatureCutoff w ≤ K)
    (n r : Nat) (hdepth : 1 ≤ n+r) (s : Nat) (hs : s ∈ activeBlocks width)
    {psi W : RatPoly} (hpsi : SupportedQuaternionBlocks (N width) psi)
    (MW : Certificate (N width) W) (eta : Q') (heta : (0 : Q') < eta) (k : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let a := terminalMessage w K width (n+r)
    let A := transferStep w K width a
    let b := transferStep w K width (incomingNumerator w K width n r psi)
    let phi := blockConditionalRatio hw0 hw1 K width hhead n r psi k
    sixValue (fun i j => let S := conditionalScore (4*s+i) (4*s+j) A b
      quaternionHaar (N width) (polyMul W (polyMul S S))) ≤
      (1+eta)*terminalSignedGramPayment w K width s n r phi W +
        6*((mixRate hw0 hw1 width)^(2*k)*
          incomingScoreErrorCoefficient w K width n r psi W eta heta) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let a := terminalMessage w K width (n+r)
  let A := transferStep w K width a
  let phi := blockConditionalRatio hw0 hw1 K width hhead n r psi k
  let b0 := transferStep w K width (polyMul a phi)
  let lead := fun i j => let S := conditionalScore (4*s+i) (4*s+j) A b0
    quaternionHaar (N width) (polyMul W (polyMul S S))
  let err := (mixRate hw0 hw1 width)^(2*k)*
    incomingScoreErrorCoefficient w K width n r psi W eta heta
  have hphi := blockConditionalRatio_supported hw0 hw1 K width hhead n r hpsi k
  have hpaired (i : Fin 3) :
      quaternionHaar (N width) (polyMul W
        (polyMul (pairedScorePlus s A b0 i) (pairedScorePlus s A b0 i))) ≤
      terminalSignedGramTerm w K width s n r phi W i := by
    have hg := terminal_local_signed_score_bound hw0 hw1 K width s n r hs hcurv
      hphi (constantPairedBasis i) (basis_supported (N width) i) MW
    have hp := basis_first_pin i (pairedScorePlus s A b0)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (haar_of_coeff ((hp.mul hp).mul_left W).symm)) hg
  have hthree := Q'.add_le_add (hpaired 0) (Q'.add_le_add (hpaired 1) (hpaired 2))
  have hpin : quaternionHaar (N width) (polyMul W (threeSquare (pairedScorePlus s A b0))) ≈
      sixValue lead :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (plusSquare_weighted_pin s A b0 W))
      (haar_six (N width) W _)
  have hlead : sixValue lead ≤ terminalSignedGramPayment w K width s n r phi W :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hpin))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_threeSquare (N width) W _)) hthree)
  have hrec := sixValue_mono _ _ (fun i j hi hj =>
    original_lastStep_incomingRatio_score_reconstruction_le hw0 hw1 K width hK
      n r hdepth s hs hi hj hpsi MW eta heta k)
  exact Q'.le_trans' _ _ _ hrec
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (six_payment_pin lead (1+eta) err))
      (Q'.add_le_add
        (Q'.mul_le_mul_of_nonneg_left _ _ (1+eta) hlead
          (Q'.zero_le_add 1 eta Q'.zero_le_one (Q'.le_of_lt heta)))
        (Q'.le_of_eqv (Q'.eqv_refl _))))

private theorem terminal_output (w : Q') (K width n r : Nat) :
    transferStep w K width (terminalMessage w K width (n+r)) =
      terminalMessage w K width (n+(r+1)) :=
  (terminalMessage_next w K width (n+r)).trans
    (congrArg (terminalMessage w K width) (by omega))

private theorem source_output (w : Q') (K width n r : Nat) (psi : RatPoly) :
    transferStep w K width (incomingNumerator w K width n r psi) =
      originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi) := by
  simpa only [incomingNumerator, originalBlockTransfer, transferStep,
    SU2QuaternionHeadChainComposition.iterateStep] using
    (BF4ExactSlabFixedSpatialMiddlePairing.iterateStep_add (N width)
      (BF4ExactSlabFixedSpatialKineticHeat.kineticWeight w K width)
      (BF4ExactSlabFixedSpatialSliceHeat.spatialWeight w K width) r 1
      (polyMul (terminalMessage w K width n) psi)).symm

/-- The literal global exact-score budget, with its actual Vbar squared and
outgoing reciprocal squared, retains every signed terminal Gram row. Incoming
degree k and outgoing degree l are independent; no scaling estimate is made. -/
theorem exactScoreAngularBudget_terminal_signed_payment_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (hcurv : prefixFrozenCurvatureCutoff w ≤ K)
    (n r : Nat) (hdepth : 1 ≤ n+r) {psi : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi)
    (sigma : Q') (hsigma : (0 : Q') ≤ sigma)
    (eta : Q') (heta : (0 : Q') < eta) (k l : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let phi := blockConditionalRatio hw0 hw1 K width hhead n r psi k
    let G := blockReciprocal hw0 hw1 K width hhead n (r+1) l
    let Vbar := spatialFringeMass w K width
    let W := polyMul (polyMul Vbar Vbar) (polyMul G G)
    exactScoreAngularBudget sigma hw0 hw1 K width hK n r psi l ≤
      finSum (fun s => if s ∈ activeBlocks width then
        (1+sigma)*((1+eta)*terminalSignedGramPayment w K width s n r phi W +
          6*((mixRate hw0 hw1 width)^(2*k)*
            incomingScoreErrorCoefficient w K width n r psi W eta heta))
        else 0) (N width) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) l
  let Vbar := spatialFringeMass w K width
  let W := polyMul (polyMul Vbar Vbar) (polyMul G G)
  have hG : SupportedQuaternionBlocks (N width) G :=
    reciprocal_supported (terminalMessage_supported w K width (n+(r+1)))
      (blockWindowUpper w K width n (r+1))
      (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)) l
  let MW : Certificate (N width) W :=
    (Certificate.square Vbar (spatialFringeMass_supported w K width)).mul
      (Certificate.square G hG)
  have hfactor : (0 : Q') ≤ 1+sigma :=
    Q'.zero_le_add 1 sigma Q'.zero_le_one hsigma
  unfold exactScoreAngularBudget
  refine YMGap.Constructive.ExpNeg.finSum_le_finSum_of_termwise _ _ ?_ (N width)
  intro s
  by_cases hs : s ∈ activeBlocks width
  · simp only [if_pos hs]
    have hrow := original_lastStep_terminal_signed_score_payment_le hw0 hw1 K width
      hK hcurv n r hdepth s hs hpsi MW eta heta k
    dsimp only at hrow
    rw [terminal_output w K width n r, source_output w K width n r psi] at hrow
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (sixValue_mul_left (1+sigma) _)))
      (Q'.mul_le_mul_of_nonneg_left _ _ (1+sigma) hrow hfactor)
  · simp only [if_neg hs]
    exact Q'.le_refl' _

end YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSignedScorePayment

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSignedScorePayment.constantPairedBasis
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSignedScorePayment.terminalSignedGramTerm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSignedScorePayment.terminalSignedGramPayment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSignedScorePayment.original_lastStep_terminal_signed_score_payment_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSignedScorePayment.exactScoreAngularBudget_terminal_signed_payment_le
